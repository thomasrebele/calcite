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
package org.apache.calcite.plan.volcano;

import org.apache.calcite.plan.RelOptCost;
import org.apache.calcite.plan.RelOptListener;
import org.apache.calcite.plan.RelOptPlanner;
import org.apache.calcite.plan.RelOptRuleCall;
import org.apache.calcite.rel.RelNode;
import org.apache.calcite.rel.metadata.RelMetadataQuery;
import org.apache.calcite.tools.visualizer.InputExcludedRelWriter;
import org.apache.calcite.tools.visualizer.VisualizerNodeInfo;
import org.apache.calcite.tools.visualizer.VisualizerRuleMatchInfo;

import org.apache.commons.io.IOUtils;

import com.fasterxml.jackson.core.JsonProcessingException;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.google.common.base.Charsets;

import java.io.IOException;
import java.io.InputStream;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.function.Consumer;
import java.util.stream.Collectors;

import static java.util.stream.Collectors.joining;

/**
 * This is tool to visualize the rule match process of the VolcanoPlanner.
 *
 *
 * <p>To use the visualizer, add a listener before the VolcanoPlanner optimization phase.
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
public class VolcanoRuleMatchVisualizer implements RelOptListener {

  private String latestRuleID = "";
  private int latestRuleTransformCount = 1;

  // default HTML template is under "resources"
  private String templateDirectory = "volcano-viz";
  private String outputDirectory;
  private String outputSuffix;

  private VolcanoPlanner volcanoPlanner;

  // a sequence of ruleMatch ID to represent the order of rule match
  private List<String> ruleMatchSequence = new ArrayList<>();
  // map of ruleMatch ID and the info, including the state snapshot at the time of ruleMatch
  private Map<String, VisualizerRuleMatchInfo> ruleInfoMap = new LinkedHashMap<>();
  // map of nodeID to the ruleID it's first added
  private Map<String, String> nodeAddedInRule = new LinkedHashMap<>();

  // a map of relNode ID to the actual RelNode object
  // contains all the relNodes appear during the optimization
  // all RelNode are immutable in Calcite, therefore only new nodes will be added
  private Map<String, RelNode> allNodes = new LinkedHashMap<>();

  public VolcanoRuleMatchVisualizer(
      String outputDirectory,
      String outputSuffix) {
    this.outputDirectory = outputDirectory;
    this.outputSuffix = outputSuffix;
  }

  public void attachTo(VolcanoPlanner planner) {
    assert this.volcanoPlanner == null;
    planner.addListener(this);
    this.volcanoPlanner = planner;
  }

  /**
   * After a rule is matched, record the rule and the state after matching.
   */
  @Override public void ruleAttempted(RuleAttemptedEvent event) {
  }

  @Override public void relChosen(RelChosenEvent event) {
    if(event.getRel() == null)
      this.addFinalPlan();
    this.writeToFile();
  }

  @Override public void ruleProductionSucceeded(RuleProductionEvent event) {
    RelOptPlanner planner = event.getRuleCall().getPlanner();
    if (!(planner instanceof VolcanoPlanner)) {
      return;
    }

    // ruleAttempted is called once before ruleMatch, and once after ruleMatch
    if (event.isBefore()) {
      // add the initialState
      if (latestRuleID.isEmpty()) {
        this.addRuleMatch("INITIAL", new ArrayList<>());
        this.latestRuleID = "INITIAL";
      }
      return;
    }

    // we add the state after the rule is applied
    RelOptRuleCall ruleCall = event.getRuleCall();
    String ruleID = Integer.toString(ruleCall.id);

    String displayRuleName = ruleCall.id + "-" + ruleCall.getRule().toString();

    // a rule might call transform to multiple times, handle it by modifying the rule name
    if (ruleID.equals(this.latestRuleID)) {
      latestRuleTransformCount++;
      displayRuleName += "-" + latestRuleTransformCount;
    } else {
      latestRuleTransformCount = 1;
    }
    this.latestRuleID = ruleID;

    this.addRuleMatch(displayRuleName, Arrays.stream(ruleCall.rels)
        .collect(Collectors.toList()));
  }

  @Override public void relDiscarded(RelDiscardedEvent event) {
  }

  @Override public void relEquivalenceFound(RelEquivalenceEvent event) {
  }

  public void addRuleMatch(String ruleCallID, Collection<? extends RelNode> matchedRels) {
    assert volcanoPlanner != null;

    // store the current state snapshot
    // nodes contained in the sets
    // and inputs of relNodes (and relSubsets)
    Map<String, String> setLabels = new TreeMap<>();
    Map<String, String> setOriginalRel = new TreeMap<>();
    Map<String, Set<String>> nodesInSet = new TreeMap<>();
    Map<String, Set<String>> nodeInputs = new TreeMap<>();

    // newNodes appeared after this ruleCall
    Set<String> newNodes = new TreeSet<>();

    // populate current snapshot, and fill in the allNodes map
    volcanoPlanner.allSets.forEach(set -> {
      String setID = "set-" + set.id;
      String setLabel = getSetLabel(set);
      setLabels.put(setID, setLabel);
      setOriginalRel.put(setID, set.rel == null ? "" : String.valueOf(set.rel.getId()));

      nodesInSet.put(setID, nodesInSet.getOrDefault(setID, new TreeSet<>()));

      Consumer<RelNode> addNode = rel -> {
        String nodeID = String.valueOf(rel.getId());
        nodesInSet.get(setID).add(nodeID);

        if (!allNodes.containsKey(nodeID)) {
          newNodes.add(nodeID);
          allNodes.put(nodeID, rel);
        }
      };

      Consumer<RelNode> addLink = rel -> {
        String nodeID = String.valueOf(rel.getId());
        Set<String> relInputs = nodeInputs.computeIfAbsent(nodeID, k -> new TreeSet<>());
        if (rel instanceof RelSubset) {
          RelSubset relSubset = (RelSubset) rel;
          relSubset.getRels().forEach(input -> relInputs.add(String.valueOf(input.getId())));
          relSubset.getSubsetsSatisfyingThis()
              .filter(other -> !other.equals(relSubset))
              .forEach(input -> relInputs.add(String.valueOf(input.getId())));
        } else {
          rel.getInputs().forEach(input -> relInputs.add(String.valueOf(input.getId())));
        }
      };

      set.rels.forEach(addNode);
      set.subsets.forEach(addNode);
      set.rels.forEach(addLink);
      set.subsets.forEach(addLink);
    });

    // get the matched nodes of this rule
    Set<String> matchedNodeIDs = matchedRels.stream()
        .map(rel -> String.valueOf(rel.getId()))
        .collect(Collectors.toCollection(() -> new TreeSet<>()));

    // get importance 0 rels as of right now
    Set<String> importanceZeroNodes = new TreeSet<>();
    volcanoPlanner.prunedNodes
        .forEach(rel -> importanceZeroNodes.add(Integer.toString(rel.getId())));

    VisualizerRuleMatchInfo ruleMatchInfo =
        new VisualizerRuleMatchInfo(setLabels, setOriginalRel, nodesInSet,
            nodeInputs, matchedNodeIDs, newNodes, importanceZeroNodes);

    ruleMatchSequence.add(ruleCallID);
    ruleInfoMap.put(ruleCallID, ruleMatchInfo);

    newNodes.forEach(newNode -> nodeAddedInRule.put(newNode, ruleCallID));
  }

  /**
   * Add a final plan to the variable.
   */
  private void addFinalPlan() {
    if (ruleMatchSequence.contains("FINAL")) {
      return;
    }

    Set<RelNode> finalPlanNodes = new LinkedHashSet<>();
    Deque<RelSubset> subsetsToVisit = new ArrayDeque<>();
    RelSubset root = (RelSubset) volcanoPlanner.getRoot();
    assert root != null;
    subsetsToVisit.add(root);

    RelSubset subset;
    while ((subset = subsetsToVisit.poll()) != null) {
      // add subset itself to the highlight list
      finalPlanNodes.add(subset);
      // highlight its best node if it exists
      RelNode best = subset.getBest();
      if (best == null) {
        continue;
      }
      finalPlanNodes.add(best);
      // recursively visit the input relSubsets of the best node
      best.getInputs().stream().map(rel -> (RelSubset) rel).forEach(subsetsToVisit::add);
    }

    this.addRuleMatch("FINAL", new ArrayList<>(finalPlanNodes));
  }

  private String getSetLabel(RelSet set) {
    return "set-" + set.id + "    ";
  }

  private String getJsonStringResult() {
    try {
      RelNode root = volcanoPlanner.getRoot();
      if (root == null) {
        throw new RuntimeException("volcano planner root is null");
      }
      RelMetadataQuery mq = root.getCluster().getMetadataQuery();

      Map<String, VisualizerNodeInfo> nodeInfoMap = new TreeMap<>();
      for (Map.Entry<String, RelNode> entry : allNodes.entrySet()) {
        RelNode relNode = entry.getValue();
        RelOptCost cost = volcanoPlanner.getCost(relNode, mq);
        Double rowCount = mq.getRowCount(relNode);

        VisualizerNodeInfo nodeInfo;
        if (relNode instanceof RelSubset) {
          RelSubset relSubset = (RelSubset) relNode;
          String nodeLabel = "subset#" + relSubset.getId() + "-set#" + relSubset.set.id + "-\n"
              + relSubset.getTraitSet().toString();
          String relIDs = relSubset.getRelList().stream()
              .map(i -> "#" + i.getId()).collect(joining(", "));
          String explanation = "rels: [" + relIDs + "]";
          nodeInfo =
              new VisualizerNodeInfo(nodeLabel, true, explanation, cost, rowCount);
        } else {
          InputExcludedRelWriter relWriter = new InputExcludedRelWriter();
          relNode.explain(relWriter);
          String inputIDs = relNode.getInputs().stream()
              .map(i -> "#" + i.getId()).collect(joining(", "));
          String explanation = relWriter.toString() + ", inputs: [" + inputIDs + "]";

          String nodeLabel = "#" + relNode.getId() + "-" + relNode.getRelTypeName();
          nodeInfo = new VisualizerNodeInfo(nodeLabel, false, explanation, cost,
              rowCount);
        }

        nodeInfoMap.put(entry.getKey(), nodeInfo);
      }

      LinkedHashMap<String, Object> data = new LinkedHashMap<>();
      data.put("allNodes", nodeInfoMap);
      data.put("ruleMatchSequence", ruleMatchSequence);
      data.put("ruleMatchInfoMap", ruleInfoMap);
      data.put("nodeAddedInRule", nodeAddedInRule);

      ObjectMapper objectMapper = new ObjectMapper();
      return objectMapper.writerWithDefaultPrettyPrinter().writeValueAsString(data);
    } catch (JsonProcessingException e) {
      throw new RuntimeException(e);
    }
  }

  /**
   * Writes the HTML and JS files of the rule match visualization.
   * <p>
   * The old files with the same name will be replaced.
   */
  private void writeToFile() {
    addFinalPlan();
    try {
      String templatePath = Paths.get(templateDirectory).resolve("viz-template.html").toString();
      assert templatePath != null;
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

}
