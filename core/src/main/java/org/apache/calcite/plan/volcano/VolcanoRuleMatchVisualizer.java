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
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Objects;
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

  private static final String INITIAL = "INITIAL";
  private static final String FINAL = "FINAL";

  private String latestRuleID = "";
  private int latestRuleTransformCount = 1;

  // default HTML template is under "resources"
  private String templateDirectory = "volcano-viz";
  private String outputDirectory;
  private String outputSuffix;

  private VolcanoPlanner volcanoPlanner;

  // TODO: delete old code
  // a sequence of ruleMatch ID to represent the order of rule match
  private List<String> ruleMatchSequence = new ArrayList<>();
  // map of ruleMatch ID and the info, including the state snapshot at the time of ruleMatch
  private Map<String, VisualizerRuleMatchInfo> ruleInfoMap = new LinkedHashMap<>();
  // map of nodeID to the ruleID it's first added
  private Map<String, String> nodeAddedInRule = new LinkedHashMap<>();

  // a map of relNode ID to the actual RelNode object
  // contains all the relNodes appear during the optimization
  // all RelNode are immutable in Calcite, therefore only new nodes will be added
  private Map<String, RelNode> allNodesOld = new LinkedHashMap<>();

  private boolean includeNonFinalCost = false;
  private List<NewRuleMatchInfo> steps = new ArrayList<>();
  // TODO: combine to one hashmap?
  private Map<String, RelNode> allNodes = new LinkedHashMap<>();
  private Map<String, NodeUpdateInfo> currentState = new LinkedHashMap<>();
  private Map<String, NodeUpdateInfo> nextNodeUpdates = new LinkedHashMap<>();
  private List<String> finalPlan = new ArrayList<>();

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
    if(event.getRel() != null) {
      finalPlan.add(key(event.getRel()));
    }
    if (event.getRel() == null) {
      System.out.println("\ndone");
      this.addFinalPlan();
      this.writeToFile();
    }
  }

  @Override public void ruleProductionSucceeded(RuleProductionEvent event) {
    RelOptPlanner planner = event.getRuleCall().getPlanner();
    if (!(planner instanceof VolcanoPlanner)) {
      return;
    }

    System.out.println("\napplied rule (before: " + event.isBefore() + ")");
    // ruleAttempted is called once before ruleMatch, and once after ruleMatch
    if (event.isBefore()) {
      // add the initialState
      if (latestRuleID.isEmpty()) {
        this.addRuleMatch(INITIAL, null);
        this.latestRuleID = INITIAL;
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

    this.addRuleMatch(displayRuleName, ruleCall);
  }

  @Override public void relDiscarded(RelDiscardedEvent event) {
  }

  @Override public void relEquivalenceFound(RelEquivalenceEvent event) {
    Object eqClass = event.getEquivalenceClass();
    System.out.println("eq rel " + event.getRel() + " class " + eqClass
        + " " + eqClass.getClass());

    if (eqClass instanceof String) {
      String eqClassStr = (String) eqClass;
      eqClassStr = eqClassStr.replace("equivalence class ", "");
      String setId = "set-" + eqClassStr;
      registerSet(setId);

      getNodeUpdateHelper(event.getRel()).updateNodeInfo("set", setId);
    }
    registerNode(event.getRel());
  }


  private void registerNode(final RelNode rel) {
    String key = key(rel);
    allNodes.put(key, rel);
  }

  private void registerSet(final String setID) {
    NodeUpdateHelper helper = new NodeUpdateHelper(setID);
    if(helper.init()) {
       helper.updateNodeInfo("label", setID);
       helper.updateNodeInfo("kind", "set");
    }

    this.currentState.computeIfAbsent(setID, k -> {
      // attributes that only need to be set once
      NodeUpdateInfo newState = new NodeUpdateInfo(), update = null;
      return newState;
    });
  }

  private NodeUpdateHelper getNodeUpdateHelper(final RelNode rel) {
    NodeUpdateHelper h = new NodeUpdateHelper(key(rel));
    if(h.init()) {
      // attributes that need to be set only once
      h.updateNodeInfo("label", getNodeLabel(rel));
      h.updateNodeInfo("explanation", getNodeExplanation(rel));

      if (rel instanceof RelSubset) {
        h.updateNodeInfo("kind", "subset");
      }
    };

    return h;
  }

  private void updateNodeInfo(final RelNode rel, final boolean finalPlan) {
    NodeUpdateHelper helper = getNodeUpdateHelper(rel);
    if (this.includeNonFinalCost || finalPlan) {
      RelMetadataQuery mq = rel.getCluster().getMetadataQuery();
      RelOptCost cost = volcanoPlanner.getCost(rel, mq);
      Double rowCount = mq.getRowCount(rel);
      helper.updateNodeInfo("cost", formatCost(rowCount, cost));
    }

    List<String> inputs = new ArrayList<>();
    if(rel instanceof RelSubset) {
      RelSubset relSubset = (RelSubset) rel;
      // TODO: remove transitive edges?
      relSubset.getRels().forEach(input -> inputs.add(key(input)));
      relSubset.getSubsetsSatisfyingThis()
          .filter(other -> !other.equals(relSubset))
          .forEach(input -> inputs.add(key(input)));
    }
    else {
      rel.getInputs().forEach(input -> inputs.add(key(input)));
    }

    helper.updateNodeInfo("inputs", inputs);
    if(helper.isEmptyUpdate())
      this.nextNodeUpdates.remove(helper.key);
  }


  private String key(final RelNode rel) {
    return "" + rel.getId();
  }

  public void addRuleMatch(String ruleCallID, RelOptRuleCall ruleCall) {
    assert volcanoPlanner != null;

    //Collection<? extends RelNode> matchedRels;

    for (RelNode n : allNodes.values()) {
      updateNodeInfo(n, FINAL.equals(ruleCallID));
    }

    NewRuleMatchInfo mi = new NewRuleMatchInfo();
    this.steps.add(mi);
    mi.id = ruleCallID;
    if (ruleCall != null) {
      mi.matchedRels = Arrays.stream(ruleCall.rels).map(this::key).collect(Collectors.toList());
    } else {
      mi.matchedRels = this.finalPlan;
    }
    mi.updates = nextNodeUpdates;

    nextNodeUpdates = new LinkedHashMap<>();

    // --------------------------------------------------------------------------------
    // old code
    List<RelNode> matchedRels = ruleCall == null
        ? Collections.emptyList()
        : Arrays.stream(ruleCall.rels).collect(Collectors.toList());

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

        if (!allNodesOld.containsKey(nodeID)) {
          newNodes.add(nodeID);
          allNodesOld.put(nodeID, rel);
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
    if (ruleMatchSequence.contains(FINAL)) {
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

    this.addRuleMatch(FINAL, null);
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
      for (Map.Entry<String, RelNode> entry : allNodesOld.entrySet()) {
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

          String nodeLabel = getNodeLabel(relNode);
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

      data.put("steps", steps);

      ObjectMapper objectMapper = new ObjectMapper();
      return objectMapper.writerWithDefaultPrettyPrinter().writeValueAsString(data);
    } catch (JsonProcessingException e) {
      throw new RuntimeException(e);
    }
  }

  private String getNodeLabel(final RelNode relNode) {
    if(relNode instanceof RelSubset) {
      final RelSubset relSubset = (RelSubset) relNode;
      return "subset#" + relSubset.getId() + "-set#" + relSubset.set.id + "-\n"
          + relSubset.getTraitSet().toString();
    }

    return "#" + relNode.getId() + "-" + relNode.getRelTypeName();
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

  private static class NewRuleMatchInfo {
    public String id;
    public Map<String, NodeUpdateInfo> updates = new LinkedHashMap<>();
    public List<String> matchedRels;
  }

  private static class NodeUpdateInfo extends LinkedHashMap<String, Object> {
    public NodeUpdateInfo(final NodeUpdateInfo update) {
      super(update);
    }

    public NodeUpdateInfo() {}
  }

  private class NodeUpdateHelper {
    String key;
    NodeUpdateInfo state;
    NodeUpdateInfo update;

    NodeUpdateHelper(String key) {
      this.key = key;
    }

    public boolean init() {
      this.state = VolcanoRuleMatchVisualizer.this.currentState.get(key);
      if (this.state == null) {
        this.state = new NodeUpdateInfo();
        VolcanoRuleMatchVisualizer.this.currentState.put(key, this.state);
        return true;
      }
      return false;
    }

    private void updateNodeInfo(final String attr, final Object newValue) {
      if (Objects.equals(newValue, state.get(attr))) {
        return;
      }

      state.put(attr, newValue);

      if (update == null) {
        update = VolcanoRuleMatchVisualizer.this.nextNodeUpdates.computeIfAbsent(key, k -> new NodeUpdateInfo());
      }

      if(newValue instanceof List
          && ((List<?>) newValue).size() == 0
          && !update.containsKey(attr)) {
        return;
      }

      update.put(attr, newValue);
      return;
    }

    public boolean isEmptyUpdate() {
      return this.update != null && update.isEmpty();
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
    return new MessageFormat("\nrowCount: {0}\nrows: {1}\ncpu:  {2}\nio:   {3}'}'",
        Locale.ROOT).format(new String[] { formatCostScientific(rowCount),
        formatCostScientific(cost.getRows()),
        formatCostScientific(cost.getCpu()),
        formatCostScientific(cost.getIo()) }
    );
  }

  private static String formatCostScientific(double costNumber) {
    long costRounded = Math.round(costNumber);
    DecimalFormat formatter = (DecimalFormat) DecimalFormat.getInstance(Locale.ROOT);
    formatter.applyPattern("#.#############################################E0");
    return formatter.format(costRounded);
  }
}
