/*
 * Licensed to the Apache Software Foundation (ASF) under one or more
 * contributor license agreements.  See the NOTICE file distributed with
 * this work for additional information regarding copyright ownership.
 * The ASF licenses this file to you under the Apache License, Version 2.0
 * (the "License"); you may not use this file except in compliance with
 * the License.  You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package org.apache.calcite.plan.visualizer;

import org.apache.calcite.plan.RelOptCost;
import org.apache.calcite.plan.RelOptListener;
import org.apache.calcite.plan.RelOptPlanner;
import org.apache.calcite.plan.RelOptRuleCall;
import org.apache.calcite.plan.hep.HepRelVertex;
import org.apache.calcite.plan.volcano.RelSubset;
import org.apache.calcite.rel.RelNode;
import org.apache.calcite.rel.metadata.RelMetadataQuery;

import org.apache.commons.io.IOUtils;

import com.fasterxml.jackson.core.JsonProcessingException;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.google.common.base.Charsets;

import org.checkerframework.checker.nullness.qual.Nullable;

import java.io.IOException;
import java.io.InputStream;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;
import java.text.DecimalFormat;
import java.text.MessageFormat;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * This is tool to visualize the rule match process of a RelOptPlanner.
 *
 * TODO: property and documentation, usage example
 *
 * <p>To use the visualizer, add a listener before the  optimization phase.
 * Then writes the output to a file after the optimization ends.
 *
 * <pre>
 * // create the visualizer. This attaches a listener to VolcanoPlanner
 * VolcanoRuleMatchVisualizer visualizer = VolcanoRuleMatchVisualizer.createAndAttach(planner);
 *
 * volcanoPlanner.findBestExpr();
 *
 * // writes the output to files
 * visualizer.writeToFile(outputDirectory, "");
 * </pre>
 */
public class RuleMatchVisualizer implements RelOptListener {

  private static final String INITIAL = "INITIAL";
  private static final String FINAL = "FINAL";
  public static final String DEFAULT_SET = "default";

  // default HTML template can be edited at
  // core/src/main/resources/volcano-viz/viz-template.html
  private final String templateDirectory = "volcano-viz";
  private final String outputDirectory;
  private final String outputSuffix;

  private String latestRuleID = "";
  private int latestRuleTransformCount = 1;
  boolean initialized = false;

  private @Nullable RelOptPlanner planner = null;

  private boolean includeTransitiveEdges = false;
  private boolean includeNonFinalCost = false;

  private final List<StepInfo> steps = new ArrayList<>();
  private final Map<String, NodeUpdateHelper> allNodes = new LinkedHashMap<>();

  public RuleMatchVisualizer(
      String outputDirectory,
      String outputSuffix) {
    this.outputDirectory = outputDirectory;
    this.outputSuffix = outputSuffix;
  }

  public void attachTo(RelOptPlanner planner) {
    planner.addListener(this);
    this.planner = planner;
  }

  public void setIncludeTransitiveEdges(final boolean includeTransitiveEdges) {
    this.includeTransitiveEdges = includeTransitiveEdges;
  }

  public void setIncludeNonFinalCost(final boolean includeNonFinalCost) {
    this.includeNonFinalCost = includeNonFinalCost;
  }

  @Override public void ruleAttempted(RuleAttemptedEvent event) {
    // HepPlanner compatibility
    if(!initialized) {
      initialized = true;
      updateInitialPlan(planner.getRoot());
    }
  }

  private void updateInitialPlan(RelNode node) {
    if(node instanceof HepRelVertex){
      HepRelVertex v = (HepRelVertex) node;
      updateInitialPlan(v.getCurrentRel());
      return;
    }
    this.getNodeUpdateHelper(node);
    for(RelNode input : getInputs(node)) {
      updateInitialPlan(input);
    }
  }

  /**
   * Get the inputs for a node, traversing {@link HepRelVertex}.
   * (Workaround for HepPlanner)
   */
  private Collection<RelNode> getInputs(final RelNode node) {
    return node.getInputs().stream().map(n -> {
      if (n instanceof HepRelVertex) {
        return ((HepRelVertex) n).getCurrentRel();
      }
      return n;
    }).collect(Collectors.toList());
  }

  @Override public void relChosen(RelChosenEvent event) {
    if (event.getRel() == null) {
      assert this.planner != null;
      assert this.planner.getRoot() != null;
      updateFinalPlan(this.planner.getRoot());
      this.addStep(FINAL, null);
      this.writeToFile();
    }
  }

  private void updateFinalPlan(RelNode node) {
    int size = this.steps.size();
    if (size > 0 && FINAL.equals(this.steps.get(size - 1).id)) {
      return;
    }

    this.getNodeUpdateHelper(node).updateNodeInfo("inFinalPlan", Boolean.TRUE);
    if (node instanceof RelSubset) {
      RelSubset subset = (RelSubset) node;
      if (subset.getBest() == null) {
        return;
      }
      updateFinalPlan(subset.getBest());
    } else {
      for (RelNode input : getInputs(node)) {
        updateFinalPlan(input);
      }
    }
  }

  @Override public void ruleProductionSucceeded(RuleProductionEvent event) {
    // method is called once before ruleMatch, and once after ruleMatch
    if (event.isBefore()) {
      // add the initialState
      if (latestRuleID.isEmpty()) {
        this.addStep(INITIAL, null);
        this.latestRuleID = INITIAL;
      }
      return;
    }

    // we add the state after the rule is applied
    RelOptRuleCall ruleCall = event.getRuleCall();
    String ruleID = Integer.toString(ruleCall.id);
    String displayRuleName = ruleCall.id + "-" + ruleCall.getRule();

    // a rule might call transform to multiple times, handle it by modifying the rule name
    if (ruleID.equals(this.latestRuleID)) {
      latestRuleTransformCount++;
      displayRuleName += "-" + latestRuleTransformCount;
    } else {
      latestRuleTransformCount = 1;
    }
    this.latestRuleID = ruleID;

    this.addStep(displayRuleName, ruleCall);
  }

  @Override public void relDiscarded(RelDiscardedEvent event) {
  }

  @Override public void relEquivalenceFound(RelEquivalenceEvent event) {
    assert event.getRel() != null;
    Object eqClass = event.getEquivalenceClass();
    if (eqClass instanceof String) {
      String eqClassStr = (String) eqClass;
      eqClassStr = eqClassStr.replace("equivalence class ", "");
      String setId = "set-" + eqClassStr;
      registerSet(setId);
      getNodeUpdateHelper(event.getRel()).updateNodeInfo("set", setId);
    }
    // register node
    this.getNodeUpdateHelper(event.getRel());
  }

  private void registerSet(final String setID) {
    this.allNodes.computeIfAbsent(setID, k -> {
      NodeUpdateHelper h = new NodeUpdateHelper(setID, null);
      h.updateNodeInfo("label", DEFAULT_SET.equals(setID) ? "" : setID);
      h.updateNodeInfo("kind", "set");
      return h;
    });
  }

  private NodeUpdateHelper getNodeUpdateHelper(final RelNode rel) {
    return this.allNodes.computeIfAbsent(key(rel), k -> {
      NodeUpdateHelper h = new NodeUpdateHelper(key(rel), rel);
      // attributes that need to be set only once
      h.updateNodeInfo("label", getNodeLabel(rel));
      h.updateNodeInfo("explanation", getNodeExplanation(rel));
      h.updateNodeInfo("set", DEFAULT_SET);

      if (rel instanceof RelSubset) {
        h.updateNodeInfo("kind", "subset");
      }
      return h;
    });
  }

  private void updateNodeInfo(final RelNode rel, final boolean finalPlan) {
    NodeUpdateHelper helper = getNodeUpdateHelper(rel);
    if (this.includeNonFinalCost || finalPlan) {
      assert planner != null;
      RelMetadataQuery mq = rel.getCluster().getMetadataQuery();
      RelOptCost cost = planner.getCost(rel, mq);
      Double rowCount = mq.getRowCount(rel);
      helper.updateNodeInfo("cost", formatCost(rowCount, cost));
    }

    List<String> inputs = new ArrayList<>();
    if (rel instanceof RelSubset) {
      RelSubset relSubset = (RelSubset) rel;
      relSubset.getRels().forEach(input -> inputs.add(key(input)));
      Set<String> transitive = new HashSet<>();
      relSubset.getSubsetsSatisfyingThis()
          .filter(other -> !other.equals(relSubset))
          .forEach(input -> {
            inputs.add(key(input));
            if (!includeTransitiveEdges) {
              input.getRels().forEach(r -> transitive.add(key(r)));
            }
          });
      inputs.removeAll(transitive);
    } else {
      getInputs(rel).forEach(input -> inputs.add(key(input)));
    }

    helper.updateNodeInfo("inputs", inputs);
  }


  private String key(final RelNode rel) {
    return "" + rel.getId();
  }

  private void addStep(String stepID, @Nullable RelOptRuleCall ruleCall) {
    Map<String, NodeUpdateInfo> nextNodeUpdates = new LinkedHashMap<>();

    // HepPlanner compatibility
    boolean usesDefaultSet = this.allNodes.values().stream().anyMatch(h -> DEFAULT_SET.equals(h.state.get("set")));
    if(usesDefaultSet)
      this.registerSet(DEFAULT_SET);

    for (NodeUpdateHelper h : allNodes.values()) {
      if (h.rel != null) {
        updateNodeInfo(h.rel, FINAL.equals(stepID));
      }
      if (h.isEmptyUpdate()) {
        continue;
      }
      nextNodeUpdates.put(h.key, h.update);
      h.update = null;
    }

    List<String> matchedRels = ruleCall == null
        ? Collections.emptyList()
        : Arrays.stream(ruleCall.rels).map(this::key).collect(Collectors.toList());
    this.steps.add(new StepInfo(stepID, nextNodeUpdates, matchedRels));
  }



  private String getJsonStringResult() {
    try {
      LinkedHashMap<String, Object> data = new LinkedHashMap<>();
      data.put("steps", steps);

      ObjectMapper objectMapper = new ObjectMapper();
      return objectMapper.writerWithDefaultPrettyPrinter().writeValueAsString(data);
    } catch (JsonProcessingException e) {
      throw new RuntimeException(e);
    }
  }

  private String getNodeLabel(final RelNode relNode) {
    if (relNode instanceof RelSubset) {
      final RelSubset relSubset = (RelSubset) relNode;
      String setId = getSetId(relSubset);
      return "subset#" + relSubset.getId() + "-set" + setId + "-\n"
          + relSubset.getTraitSet();
    }

    return "#" + relNode.getId() + "-" + relNode.getRelTypeName();
  }

  private String getSetId(final RelSubset relSubset) {
    String explanation = getNodeExplanation(relSubset);
    int start = explanation.indexOf("RelSubset") + "RelSubset".length();
    if(start < 0) {
      return "";
    }
    int end = explanation.indexOf(".", start);
    if(end < 0) {
      return "";
    }
    return explanation.substring(start, end);
  }

  private String getNodeExplanation(final RelNode relNode) {
    InputExcludedRelWriter relWriter = new InputExcludedRelWriter();
    relNode.explain(relWriter);
    return relWriter.toString();
  }

  /**
   * Writes the HTML and JS files of the rule match visualization.
   * <p>
   * The old files with the same name will be replaced.
   */
  public void writeToFile() {
    try {
      String templatePath = Paths.get(templateDirectory).resolve("viz-template.html").toString();
      ClassLoader cl = getClass().getClassLoader();
      assert cl != null;
      InputStream resourceAsStream = cl.getResourceAsStream(templatePath);
      assert resourceAsStream != null;
      String htmlTemplate = IOUtils.toString(resourceAsStream, StandardCharsets.UTF_8);

      String htmlFileName = "volcano-viz" + outputSuffix + ".html";
      String dataFileName = "volcano-viz-data" + outputSuffix + ".js";

      String replaceString = "src=\"volcano-viz-data.js\"";
      int replaceIndex = htmlTemplate.indexOf(replaceString);
      String htmlContent = htmlTemplate.substring(0, replaceIndex)
          + "src=\"" + dataFileName + "\""
          + htmlTemplate.substring(replaceIndex + replaceString.length());

      String dataJsContent = "var data = " + getJsonStringResult() + ";\n";

      Path outputDirPath = Paths.get(outputDirectory);
      Path htmlOutput = outputDirPath.resolve(htmlFileName);
      Path dataOutput = outputDirPath.resolve(dataFileName);

      if (!Files.exists(outputDirPath)) {
        Files.createDirectories(outputDirPath);
      }

      Files.write(htmlOutput, htmlContent.getBytes(Charsets.UTF_8), StandardOpenOption.CREATE,
          StandardOpenOption.TRUNCATE_EXISTING);
      Files.write(dataOutput, dataJsContent.getBytes(Charsets.UTF_8), StandardOpenOption.CREATE,
          StandardOpenOption.TRUNCATE_EXISTING);
    } catch (IOException e) {
      throw new UncheckedIOException(e);
    }
  }


  private static String formatCost(Double rowCount, @Nullable RelOptCost cost) {
    if (cost == null) {
      return "null";
    }
    String originalStr = cost.toString();
    if (originalStr.contains("inf") || originalStr.contains("huge")
        || originalStr.contains("tiny")) {
      return originalStr;
    }
    return new MessageFormat("\nrowCount: {0}\nrows: {1}\ncpu:  {2}\nio:   {3}",
        Locale.ROOT).format(new String[]{
            formatCostScientific(rowCount),
            formatCostScientific(cost.getRows()),
            formatCostScientific(cost.getCpu()),
            formatCostScientific(cost.getIo())
        }
    );
  }

  private static String formatCostScientific(double costNumber) {
    long costRounded = Math.round(costNumber);
    DecimalFormat formatter = (DecimalFormat) DecimalFormat.getInstance(Locale.ROOT);
    formatter.applyPattern("#.#############################################E0");
    return formatter.format(costRounded);
  }

}
