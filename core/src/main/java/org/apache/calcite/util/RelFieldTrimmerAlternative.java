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
package org.apache.calcite.util;

import org.apache.calcite.linq4j.Ord;
import org.apache.calcite.plan.Convention;
import org.apache.calcite.plan.RelOptUtil;
import org.apache.calcite.plan.RelTrait;
import org.apache.calcite.plan.RelTraitSet;
import org.apache.calcite.rel.RelCollation;
import org.apache.calcite.rel.RelFieldCollation;
import org.apache.calcite.rel.RelNode;
import org.apache.calcite.rel.core.Aggregate;
import org.apache.calcite.rel.core.AggregateCall;
import org.apache.calcite.rel.core.Correlate;
import org.apache.calcite.rel.core.Filter;
import org.apache.calcite.rel.core.Join;
import org.apache.calcite.rel.core.Project;
import org.apache.calcite.rel.core.SetOp;
import org.apache.calcite.rel.core.Sort;
import org.apache.calcite.rel.core.TableScan;
import org.apache.calcite.rel.logical.LogicalSort;
import org.apache.calcite.rel.logical.LogicalValues;
import org.apache.calcite.rel.type.RelDataType;
import org.apache.calcite.rel.type.RelDataTypeField;
import org.apache.calcite.rex.RexBuilder;
import org.apache.calcite.rex.RexDynamicParam;
import org.apache.calcite.rex.RexLiteral;
import org.apache.calcite.rex.RexNode;
import org.apache.calcite.rex.RexPermuteInputsShuttle;
import org.apache.calcite.rex.RexShuttle;
import org.apache.calcite.rex.RexUtil;
import org.apache.calcite.rex.RexVisitor;
import org.apache.calcite.sql.SqlExplainFormat;
import org.apache.calcite.sql.SqlExplainLevel;
import org.apache.calcite.sql.SqlKind;
import org.apache.calcite.sql.type.ArraySqlType;
import org.apache.calcite.tools.RelBuilder;
import org.apache.calcite.util.mapping.Mapping;
import org.apache.calcite.util.mapping.MappingType;
import org.apache.calcite.util.mapping.Mappings;

import com.google.common.collect.ImmutableList;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Objects;
import java.util.Set;
import java.util.function.BiFunction;

import jdk.vm.ci.meta.JavaType;

/**
 * Transformer that walks over a tree of relational expressions, replacing each
 * {@link RelNode} with a 'slimmed down' relational expression that projects
 * only the columns required by its consumer.
 *
 * Warning: this trimmer does not yet support Calcite extra fields.
 */
public class RelFieldTrimmerAlternative extends RelFieldUsageVisitor {

  /**
   * Uses multi-methods to fire the right rule for each type of relational
   * expression. This allows the transformer to be extended without having to
   * add a new method to RelNode, and without requiring a collection of rule
   * classes scattered to the four winds.
   */
  protected final ReflectUtil.MethodDispatcher<Void> trimDispatcher;

  public RelFieldTrimmerAlternative() {
    ReflectUtil.MethodDispatcher<Void> dispatcher = ReflectUtil
        .createMethodDispatcher(
            void.class,
            this,
            "trimNode",
            RelNode.class,
            TrimWorker.class);
    this.trimDispatcher = dispatcher;
  }

  /**
   * Trims the rel node.
   * This is the main method.
   */
  public RelNode trim(RelNode relNode, RelBuilder builder) {
    Context ctx = this.createContext(relNode, builder);
    RelNode sameType;
    try {
      TrimWorker helper = (TrimWorker) this.analyze(relNode, ctx);
      sameType = helper.getSameTypeRel();
    } catch (TrimmerException e) {
      String plan = RelOptUtil.dumpPlan("", relNode, SqlExplainFormat.TEXT,
          SqlExplainLevel.NON_COST_ATTRIBUTES);
      throw new TrimmerException("Exception while trimming plan\n"
          + plan, e);
    }

    return sameType;
  }

  protected TrimContext createContext(RelNode relNode, RelBuilder builder) {
    return new TrimContext(relNode, builder, this.trimDispatcher);
  }

  @Override protected TrimWorker createWorker(RelNode rel, Context data) {
    return new TrimWorker(rel, data, this::createWorker);
  }

  private static Mapping createMapping(int sourceCount, int targetCount) {
    return Mappings.create(MappingType.INVERSE_SURJECTION, sourceCount, targetCount);
  }

  /**
   * Create a mapping where the output consists of only the used fields.
   */
  protected static Mapping createMapping(ImmutableBitSet fieldsUsed, RelNode originalRel) {
    int originalFieldCount = getFieldCount(originalRel);
    final Mapping mapping = createMapping(originalFieldCount, fieldsUsed.cardinality());
    int i = 0;
    for (int field : fieldsUsed) {
      mapping.set(field, i++);
    }
    return mapping;
  }

  /**
   * Visit method, per {@link org.apache.calcite.util.ReflectiveVisitor}.
   *
   * See {@link TrimWorker#calculateSameColumnsFallback()} for the default trimming algorithm.
   *
   * <p>
   * This method is invoked reflectively, so there may not be any apparent
   * calls to it. The class (or derived classes) may contain overloads of
   * this method with more specific types for the {@code rel} parameter.
   *
   * @param node   Node that should be trimmed
   * @param worker Provides the necessary information for trimming,
   *               and stores the result (in and out).
   *               The node param is the same as worker.original.
   *
   * @see org.apache.calcite.sql2rel.RelFieldTrimmer#trimFields(RelNode, ImmutableBitSet, Set)
   */
  public void trimNode(RelNode node, TrimWorker worker) {
    //
  }

  /**
   * Variant of {@link #trimNode(RelNode, TrimWorker)}.
   */
  public void trimNode(LogicalValues values, TrimWorker worker) {
    assert worker.getChildren().isEmpty();

    final RelDataType rowType = values.getRowType();
    final int fieldCount = rowType.getFieldCount();
    ImmutableBitSet neededFields = worker.getNeededByParent();

    // If they are asking for no fields, we can't give them what they want,
    // because zero-column records are illegal. Give them the last field,
    // which is unlikely to be a system field.
    if (neededFields.isEmpty()) {
      neededFields = ImmutableBitSet.range(fieldCount - 1, fieldCount);
    }

    // If all fields are used, we cannot do better
    if (neededFields.equals(ImmutableBitSet.range(fieldCount))) {
      return;
    }

    final ImmutableList.Builder<ImmutableList<RexLiteral>> newTuples = ImmutableList.builder();
    for (ImmutableList<RexLiteral> tuple : values.getTuples()) {
      ImmutableList.Builder<RexLiteral> newTuple = ImmutableList.builder();
      for (int field : neededFields) {
        newTuple.add(tuple.get(field));
      }
      newTuples.add(newTuple.build());
    }

    final Mapping mapping = createMapping(neededFields, values);
    final RelDataType newRowType = RelOptUtil.permute(values.getCluster().getTypeFactory(), rowType,
        mapping);
    final LogicalValues newValues = LogicalValues.create(values.getCluster(), newRowType,
        newTuples.build());

    worker.updateBest(newValues, mapping);
  }

  /**
   * Variant of {@link #trimNode(RelNode, TrimWorker)}.
   */
  public void trimNode(Project project, TrimWorker worker) {
    assert worker.getChildren().size() == 1;
    ImmutableBitSet neededFields = worker.getNeededByParent();
    TrimResult best = worker.getChildren().get(0).getBest();
    RelNode newInput = best.rel;
    final Mapping inputMapping = best.mapping;

    RelDataType rowType = project.getRowType();
    int fieldCount = rowType.getFieldCount();
    RelNode input = project.getInput();

    // If the input is unchanged, and we need to project all columns,
    // there's nothing we can do.
    if (newInput == input
        && neededFields.cardinality() == fieldCount) {
      return;
    }

    // Build new project expressions, and populate the mapping.
    final List<RexNode> newProjects = new ArrayList<>();
    final RexVisitor<RexNode> shuttle = new RexPermuteInputsShuttle(
        inputMapping, newInput);

    final Mapping mapping = worker.createMapping(neededFields.cardinality());
    for (Ord<RexNode> ord : Ord.zip(project.getProjects())) {
      if (neededFields.get(ord.i)) {
        mapping.set(ord.i, newProjects.size());
        RexNode newProjectExpr = ord.e.accept(shuttle);
        newProjects.add(newProjectExpr);
      }
    }

    final RelDataType newRowType = RelOptUtil.permute(project.getCluster().getTypeFactory(),
        rowType,
        mapping);

    RelBuilder relBuilder = worker.getRelBuilder();
    relBuilder.push(newInput);
    relBuilder.project(newProjects, newRowType.getFieldNames());
    final RelNode newProject = RelOptUtil.propagateRelHints(project, relBuilder.build());
    worker.updateBest(newProject, mapping);
  }

  /**
   * Variant of {@link #trimNode(RelNode, TrimWorker)}.
   */
  public void trimNode(Filter filter, TrimWorker worker) {
    TrimResult child = worker.getChildren().get(0).getBest();
    Mapping inputMapping = child.mapping;
    RelNode input = child.rel;

    // Build new project expressions, and populate the mapping.
    final RexVisitor<RexNode> shuttle = new RexPermuteInputsShuttle(inputMapping, input);
    RexNode newConditionExpr = filter.getCondition().accept(shuttle);

    // Build new filter with trimmed input and condition.
    RelBuilder relBuilder = worker.getRelBuilder();
    relBuilder
        .push(input)
        .filter(filter.getVariablesSet(), newConditionExpr);

    // The result has the same mapping as the input gave us.
    // The worker might remove fields that the parent didn't ask for.
    worker.updateBest(relBuilder.build(), inputMapping);
  }

  /**
   * Variant of {@link #trimNode(RelNode, TrimWorker)}.
   */
  public void trimNode(Sort rel, TrimWorker worker) {
    TrimResult bestInput = worker.getChildren().get(0).getBest();
    RelNode input = bestInput.rel;
    Mapping inputMapping = bestInput.mapping;
    RelBuilder relBuilder = worker.getRelBuilder();
    RelNode newSort = this.createSort(rel, input, inputMapping, relBuilder);
    worker.updateBest(newSort, inputMapping);
  }

  /**
   * Create a sort with the new input and the mapping.
   */
  private RelNode createSort(Sort rel, RelNode input, Mapping inputMapping, RelBuilder relBuilder) {
    if (rel.getInput() == input && inputMapping.isIdentity()) {
      return rel;
    }

    // handle LIMIT 0
    if (this.isFetchZero(rel)) {
      relBuilder.push(input);
      relBuilder.empty();
      return relBuilder.build();
    }

    // sort columns stay the same,
    if (!this.isChangedSortCols(rel, inputMapping)) {
      return rel.copy(rel.getTraitSet(), Collections.singletonList(input));
    }

    RelCollation newCollation = RexUtil.apply(inputMapping, rel.collation);

    if (rel.offset instanceof RexDynamicParam
        || rel.fetch instanceof RexDynamicParam) {
      if (input instanceof Sort) {
        Sort sort2 = (Sort) input;
        if (sort2.fetch == null && sort2.offset == null) {
          input = sort2.getInput();
        }
      }
      return LogicalSort.create(input, newCollation, rel.offset, rel.fetch);
    }

    relBuilder.push(input);
    final int offset = rel.offset == null ? 0 : RexLiteral.intValue(rel.offset);
    final int fetch = rel.fetch == null ? -1 : RexLiteral.intValue(rel.fetch);
    final ImmutableList<RexNode> fields = relBuilder.fields(newCollation);
    relBuilder.sortLimit(offset, fetch, fields);
    return relBuilder.build();
  }

  private boolean isFetchZero(Sort rel) {
    if (!(rel.fetch instanceof RexLiteral)) {
      return false;
    }

    Object value = ((RexLiteral) rel.fetch).getValue();
    if (!(value instanceof BigDecimal)) {
      return false;
    }

    return ((BigDecimal) value).intValue() == 0;
  }

  /**
   * Check if the mapping affects the sort columns.
   */
  private boolean isChangedSortCols(Sort rel, Mapping inputMapping) {
    final RelCollation collation = rel.getCollation();
    for (RelFieldCollation field : collation.getFieldCollations()) {
      int sortCol = field.getFieldIndex();
      if (sortCol >= inputMapping.getTargetCount()) {
        return true;
      }
      int idx = inputMapping.getSource(sortCol);
      if (idx != sortCol) {
        return true;
      }
    }
    return false;
  }

  /**
   * Variant of {@link #trimNode(RelNode, TrimWorker)}.
   */
  public void trimNode(TableScan rel, TrimWorker worker) {
    ImmutableBitSet fieldsUsed = worker.getNeededByParent();

    Set<RelDataTypeField> extraFields = Collections.emptySet();
    final RelNode newRel = rel.project(fieldsUsed, extraFields, worker.getRelBuilder());

    final Mapping mapping = createMapping(fieldsUsed, rel);
    worker.updateBest(newRel, mapping);
  }

  /**
   * Variant of {@link #trimNode(RelNode, TrimWorker)}.
   */
  public void trimNode(Join rel, TrimWorker worker) {
    // limited implementation: Calcite extra/system fields not yet supported
    @SuppressWarnings("unchecked")
    List<TrimWorker> children = (List<TrimWorker>) worker.getChildren();
    assert children.size() == 2;
    TrimResult bestLeft = children.get(0).getBest();
    TrimResult bestRight = children.get(1).getBest();

    Mapping inputMapping = (Mapping) Mappings.append(bestLeft.mapping, bestRight.mapping);
    Mapping newMapping = rel.getJoinType().projectsRight()
        ? inputMapping
        : bestLeft.mapping;

    final RexShuttle shuttle = RexPermuteInputsShuttle.of(inputMapping);
    RelNode rewritten = rel.accept(shuttle);
    RelTraitSet newTraits = this.adaptTraitSet(rewritten.getTraitSet(), newMapping);
    rewritten = rewritten.copy(newTraits, Arrays.asList(bestLeft.rel, bestRight.rel));
    worker.updateBest(rewritten, newMapping);
  }

  /**
   * Variant of {@link #trimNode(RelNode, TrimWorker)}.
   */
  public void trimNode(Correlate rel, TrimWorker worker) {
    // limited implementation: Calcite extra/system fields not yet supported

    ImmutableBitSet.Builder req = ImmutableBitSet.builder();
    @SuppressWarnings("unchecked")
    List<TrimWorker> children = (List<TrimWorker>) worker.getChildren();
    assert children.size() == 2;
    TrimResult bestLeft = children.get(0).getSameType();
    TrimResult bestRight = children.get(1).getBest();

    for (int i : rel.getRequiredColumns()) {
      req.set(bestLeft.mapping.getTarget(i));
    }

    Mapping inputMapping = (Mapping) Mappings.append(bestLeft.mapping, bestRight.mapping);
    Mapping newMapping = rel.getJoinType().projectsRight()
        ? inputMapping
        : bestLeft.mapping;

    ImmutableBitSet newRequired = req.build(rel.getRequiredColumns());
    RelTraitSet newTraits = this.adaptTraitSet(rel.getTraitSet(), newMapping);
    RelNode newRelNode = rel.copy(newTraits,
        bestLeft.rel, bestRight.rel,
        rel.getCorrelationId(), newRequired, rel.getJoinType());
    assert newRelNode.getClass() == rel.getClass();
    worker.updateBest(newRelNode, newMapping);
  }

  /**
   * Variant of {@link #trimNode(RelNode, TrimWorker)}.
   */
  public void trimNode(SetOp rel, TrimWorker worker) {
    // UNION | INTERSECT | INTERSECT ALL | EXCEPT | EXCEPT ALL
    // all have comparison between branches.
    // They can not be trimmed because the comparison needs
    // complete fields.
    if (!(rel.kind == SqlKind.UNION && rel.all)) {
      return;
    }

    ImmutableBitSet neededFields = worker.getNeededByParent();
    // Compute the desired field mapping. Give the consumer the fields they
    // want, in the order that they appear in the bitset.
    Mapping mapping = createMapping(neededFields, rel);

    // Create input with trimmed columns.
    RelBuilder relBuilder = worker.getRelBuilder();
    for (TrimWorker child : worker.getChildren()) {
      TrimResult trimResult = child.getBest();

      //@formatter:off
      // We want "mapping", the input gave us "inputMapping", compute
      // "remaining" mapping.
      //    |                   |                |
      //    |---------------- mapping ---------->|
      //    |-- inputMapping -->|                |
      //    |                   |-- remaining -->|
      //
      // For instance, suppose we have columns [a, b, c, d],
      // the consumer asked for mapping = [b, d],
      // and the transformed input has columns inputMapping = [d, a, b].
      // remaining will permute [b, d] to [d, a, b].
      //@formatter:on
      Mapping remaining = Mappings.divide(mapping, trimResult.mapping);

      // Create a projection; does nothing if remaining is identity.
      relBuilder.push(trimResult.rel);
      relBuilder.permute(remaining);
    }

    assert rel.kind == SqlKind.UNION;
    relBuilder.union(rel.all, rel.getInputs().size());

    worker.updateBest(relBuilder.build(), mapping);
  }

  /**
   * Variant of {@link #trimNode(RelNode, TrimWorker)}.
   */
  public void trimNode(Aggregate aggregate, TrimWorker worker) {
    // limited implementation: Calcite extra/system fields not yet supported

    TrimResult best = worker.getChildren().get(0).getBest();
    final RelNode newInput = best.rel;
    final Mapping inputMapping = best.mapping;

    // A subclass (such as CteFieldTrimmerExtended) might remove some unnecessary grouping fields
    // so calculate which of those remain
    final ImmutableBitSet newInputGroupSet = TrimWorker.applyOpt(inputMapping,
        aggregate.getGroupSet());
    // We have to return group keys and (if present) indicators.
    // So, pretend that the consumer asked for them.
    final int oldGroupCount = aggregate.getGroupCount();
    final int newGroupCount = newInputGroupSet.cardinality();
    ImmutableBitSet fieldsUsed = worker.getNeededByParent();

    // Which agg calls are used by our consumer?
    ImmutableBitSet oldOutputGroupSet = ImmutableBitSet.range(oldGroupCount);
    int usedAggCallCount = fieldsUsed.except(oldOutputGroupSet).cardinality();

    // Offset due to the number of system fields having changed.
    Mapping mapping = worker.createMapping(newGroupCount + usedAggCallCount);

    final ImmutableList<ImmutableBitSet> newGroupSets = ImmutableList.copyOf(
        Util.transform(aggregate.getGroupSets(),
            input1 -> TrimWorker.applyOpt(inputMapping, input1)));

    // Populate mapping of where to find the fields. System, group key and
    // indicator fields first.
    this.calculateGroupMapping(aggregate.getGroupSet(), inputMapping, newInputGroupSet, mapping);

    // Now create new agg calls, and populate mapping for them.
    RelBuilder relBuilder = worker.getRelBuilder();
    relBuilder.push(newInput);
    final List<RelBuilder.AggCall> newAggCallList = new ArrayList<>();
    int j = newGroupCount;
    for (AggregateCall aggCall : aggregate.getAggCallList()) {
      if (fieldsUsed.get(j)) {
        mapping.set(j, newGroupCount + newAggCallList.size());
        newAggCallList.add(relBuilder.aggregateCall(aggCall, inputMapping));
      }
      ++j;
    }

    if (newAggCallList.isEmpty() && newGroupCount == 0) {
      // Add a dummy call if all the column fields have been trimmed
      mapping = createMapping(mapping.getSourceCount(), 1);
      newAggCallList.add(relBuilder.count(false, "DUMMY"));
    }

    final RelBuilder.GroupKey groupKey = relBuilder
        .groupKey(
            newInputGroupSet,
            newGroupSets);
    relBuilder.aggregate(groupKey, newAggCallList);

    final RelNode newAggregate = RelOptUtil.propagateRelHints(aggregate, relBuilder.build());
    worker.updateBest(newAggregate, mapping);
  }

  //@formatter:off

  /**
   * Calculates a mapping from the old grouping key to the new one.
   * The fields that have no mapping in the input will be not be part of the output.
   *
   * Example:
   * Assume The old aggregate would project (or "squeeze") [1, 4, 5] to [0, 1, 2].
   * The input mapping is {4 &rarr; 3, 5 &rarr; 2}. The column 1 has been "removed"
   * (e.g. by a subclass).
   * So the new aggregate projects [4, 5] to [1, 0], because of a crossing in the inputMapping.
   * The output mapping would therefore be
   * <pre>
   * { 1 &rarr; 1,    // column 4 was output field 1, and afterwards it's 1
   *   2 &rarr; 0 }   // column 5 was output field 2, and afterwards it's 0
   * </pre>
   */
  //@formatter:on
  private void calculateGroupMapping(
      ImmutableBitSet oldInputGroupSet,
      Mapping inputMapping,
      ImmutableBitSet newInputGroupSet,
      Mapping outputMapping) {
    //@formatter:off
    // The following commutative diagram holds:
    //
    //                             squeeze_old
    //  old input group fields  --------------------X  old output group fields
    //      |                                                |
    //      |                                                | groupMapping
    //      | inputMapping                                   | (that's what we want to calculate)
    //      |                                                |
    //      X                                                X
    //  new input group fields  --------------------X  new output group fields
    //                             squeeze_new
    //
    //@formatter:on

    int target = 0;
    for (int i : newInputGroupSet) {
      // invert squeeze_new
      int src = i;

      // invert inputMapping
      src = inputMapping.getSource(src);

      // follow squeeze_old
      src = oldInputGroupSet.indexOf(src);

      // to get old group fields to new group fields
      outputMapping.set(src, target++);
    }
  }

  protected RelTraitSet adaptTraitSet(RelTraitSet traitSet, Mappings.TargetMapping mapping) {
    for (@SuppressWarnings("unused")
        RelTrait trait : traitSet) {
      if (trait instanceof Convention) {
        continue;
      }

      if (trait instanceof RelCollation) {
        if (((RelCollation) trait).getFieldCollations().isEmpty()) {
          continue;
        }
      }

      throw new UnsupportedOperationException(
          "Trimming of trait sets not yet supported, trait was "
              + trait
              + ", class "
              + trait.getClass());
    }
    return traitSet;
  }

  // ~ Inner Classes ----------------------------------------------------------

  /**
   * Collects the results for {@link RelFieldTrimmerAlternative}.
   *
   * <p>
   * There are several possibilities for the trim result of the current node
   * depending on the node and the caller (i.e., the parent of the node):
   * <ol>
   * <li>trimmed
   * <li>trimmed, but with same row type
   * <li>not trimmed, but children replaced with a trimmed version (same row type)
   * <li>original
   * </ol>
   *
   * Another possibility (not implemented): not trimmed, but children replaced
   * with a trimmed version (changing row type) and using a RexShuttle to rewrite references.
   */
  public static class TrimWorker extends FieldUsageWorker {
    // Possible trimming results for current node (from "most optimal" to "least optional"):

    /**
     * Optimal trimmed option: current node trimmed + additional projection
     * to project only the fields required by the node's parent.
     */
    private TrimResult best;

    /**
     * Sub-optimal trimmed option: current node trimmed, but no additional projection
     * to project only the fields required by the node's parent.
     */
    private TrimResult bestWithoutExtraProject;

    /**
     * Current node trimmed (as much as possible), under the condition of keeping
     * the same fields (with potentially different names).
     */
    private RelNode sameColumns;

    /**
     * True, iff the trimming has already done for this node.
     * It avoids calculating the best trim result twice.
     */
    private boolean trimmerCalled = false;

    public TrimWorker(
        RelNode original,
        Context data,
        BiFunction<RelNode, Context, FieldUsageWorker> workerCreator) {
      super(original, data, workerCreator);
    }

    protected RelBuilder getRelBuilder() {
      return ((TrimContext) this.context).relBuilder;
    }

    /**
     * Checks if a dispatch is always needed.
     * Some RelNodes will get simplified by the builder,
     * so force the dispatch:
     *
     * <ul>
     * <li>sort with fetch=0
     * <li>filter with condition=false
     * <li>project(project(...))
     * </ul>
     */
    boolean alwaysNeedsDispatch() {
      return this.original instanceof Sort
          || this.original instanceof Filter
          || this.original instanceof Project;
    }

    /**
     * Calling the trim on the parent can be avoided, if trimming does not "change" its children.
     * In that case the trim falls back on a general method that just copies the parent node
     * with the new children (if necessary). See {@link #calculateSameColumnsFallback()}.
     * However, if the mapping of a child changes, the trim must be called for the parent,
     * so that the result of the trimming is actually used.
     */
    boolean parentNeedsDispatch() {
      // if the child has no improvement
      if (this.best == null || this.best.rel == this.sameColumns) {
        return false;
      }

      // if the parent uses all fields and the child keeps the same columns
      Mapping map = this.best.mapping;
      int fc = getFieldCount(this.original);
      if (map.getSourceCount() == fc && map.getTargetCount() == fc && map.isIdentity()) {
        return false;
      }

      return true;
    }

    @Override @SuppressWarnings("unchecked")
    protected List<? extends TrimWorker> getChildren() {
      return (List<TrimWorker>) super.getChildren();
    }

    @Override public String toString() {
      if (this.best != null) {
        return "best: " + this.best;
      }
      return "original: " + this.original;
    }

    @Override public void toString(StringBuilder sb, String prefix) {
      super.toString(sb, prefix);
      if (this.best != null) {
        String cp = prefix;
        sb.append(cp).append("best: ").append(this.best).append("\n");
        sb.append(cp).append("type: ").append(this.best.rel.getRowType()).append("\n");
      }
    }

    /**
     * Updates the best trimmed version of this node.
     * May only be called once.
     */
    public void updateBest(RelNode rel, Mapping mapping) {
      assert this.best == null;
      assert this.bestWithoutExtraProject == null;
      assert this.sameColumns == null;
      if (rel == this.original) {
        return;
      }

      this.bestWithoutExtraProject = new TrimResult(rel, mapping);
      // TODO tre: what to do here?
      // do not add project to join to prevent rule explosion
      // in the planning phase (to be fixed by CP-23138)
      if (rel instanceof Join) {
        this.best = this.bestWithoutExtraProject;
      } else {
        this.best = this.projectFieldsNeededByParent(this.bestWithoutExtraProject);
      }
    }

    /**
     * Gets a possibly trimmed version of this node.
     * It should trim the whole subtree as much as possible.
     * If this node cannot be trimmed, it should at least
     * return a RelNode where the children have been trimmed
     * using {@link #getSameColumns()}.
     */
    public TrimResult getBest() {
      this.ensureRecursion();
      if (this.best != null) {
        return this.best;
      }
      // fall-back: trim children recursively and add a project
      return this.best = this.projectFieldsNeededByParent(this.getSameColumns());
    }

    public TrimResult getBestWithoutExtraProject() {
      this.ensureRecursion();
      if (this.bestWithoutExtraProject != null) {
        return this.bestWithoutExtraProject;
      }
      return this.getSameColumns();
    }

    /**
     * Similar to {@link #getBest()}, but ensuring that the row type
     * of the result stays compatible. I.e., the field names may change,
     * but the types of the field must stay the same.
     */
    public RelNode getSameColumnsRel() {
      if (this.sameColumns != null) {
        return this.sameColumns;
      }

      this.sameColumns = this.calculateBestRelWithSameColumnsOrNull();
      if (this.sameColumns != null) {
        return this.sameColumns;
      }

      return this.sameColumns = this.calculateSameColumnsFallback();
    }

    public TrimResult getSameColumns() {
      return TrimResult.identity(this.getSameColumnsRel());
    }

    /**
     * Like {@link #getSameColumns()}, where not just the field types,
     * but also the field names are the same.
     */
    public RelNode getSameTypeRel() {
      RelNode rel = this.getSameColumnsRel();
      RelDataType origType = this.original.getRowType();
      if (Objects.equals(rel.getRowType(), origType)) {
        return rel;
      }
      assert getFieldCount(rel) == origType.getFieldCount();

      List<String> fieldNames = origType.getFieldNames();
      RelBuilder relBuilder = this.getRelBuilder();
      relBuilder.push(rel).rename(fieldNames);
      return relBuilder.build();
    }

    public TrimResult getSameType() {
      return TrimResult.identity(this.getSameTypeRel());
    }

    /**
     * Adds a project so that only the fields needed by the parent remain.
     * The result from the methods that do the trimming for the individual RelNode types
     * might still have more fields than the parent requested. Add a project to remove them.
     */
    private TrimResult projectFieldsNeededByParent(TrimResult v) {
      ImmutableBitSet neededFields = this.getNeededByParent();
      return this.projectFields(v, neededFields);
    }

    /**
     * Adds a project so that only the specified fields remain.
     */
    protected TrimResult projectFields(TrimResult v, ImmutableBitSet neededFields) {
      RelBuilder relBuilder = this.getRelBuilder();
      int fieldCount = getFieldCount(v.rel);

      // Some parts of the system can't handle rows with zero fields,
      // so add a dummy project
      if (fieldCount == 0 || neededFields.cardinality() == 0) {
        assert neededFields.cardinality() == 0;
        RexLiteral dummyField = relBuilder.literal(Integer.valueOf(0));
        relBuilder.push(v.rel);
        relBuilder.projectNamed(Arrays.asList(dummyField), Arrays.asList("dummy"), false);

        final Mapping mapping = this.createMapping(1);
        return new TrimResult(relBuilder.build(), mapping);
      }

      // add projection if we got too many fields
      if (fieldCount > neededFields.cardinality()) {
        relBuilder.push(v.rel);
        List<RexNode> expr = new ArrayList<>();
        List<String> oldNames = this.original.getRowType().getFieldNames();
        List<String> newNames = new ArrayList<>();
        int field = -1;
        final Mapping mapping = this.createMapping(neededFields.cardinality());
        for (int i = 0; i < neededFields.cardinality(); i++) {
          field = neededFields.nextSetBit(field + 1);
          newNames.add(oldNames.get(field));
          int target = v.mapping.getTarget(field);
          expr.add(relBuilder.field(target));
          mapping.set(field, i);
        }

        // Some parts of the system can't handle rows with zero fields,
        // so pretend that one field is used.
        if (expr.isEmpty()) {
          expr.add(relBuilder.literal(Integer.valueOf(0)));
          newNames.add("dummy");
        }

        relBuilder.projectNamed(expr, newNames, false);

        return new TrimResult(relBuilder.build(), mapping);
      }

      return v;
    }

    /**
     * Makes the trimming recursive.
     * This method takes care that the trimming for this node is done at most once.
     */
    private void ensureRecursion() {
      if (this.trimmerCalled) {
        return;
      }

      this.trimmerCalled = true;
      try {
        // short circuit
        if (!this.alwaysNeedsDispatch() && this.allFieldsRequired()) {
          boolean needDispatch = false;
          for (TrimWorker child : this.getChildren()) {
            child.ensureRecursion();
            needDispatch |= child.parentNeedsDispatch();
          }
          // parent needs all fields, and no child provides a really trimmed plan
          // so we can avoid the dispatch
          if (!needDispatch) {
            return;
          }
        }

        ((TrimContext) this.context).trimDispatcher.invoke(this.original, this);
      } catch (TrimmerException e) {
        throw e;
      } catch (Exception | AssertionError e) {
        String msg = "Exception while trimming " + this.original;
        throw new TrimmerException(msg, e);
      }
    }

    private boolean allFieldsRequired() {
      int fc = getFieldCount(this.original);
      return this.getNeededByParent().cardinality() == fc;
    }

    /**
     * Create a mapping from the original fields (source)
     * to some trimmed fields (target).
     *
     * @param trimmedFieldCount Number of fields for a trimmed relation.
     */
    private Mapping createMapping(int trimmedFieldCount) {
      return RelFieldTrimmerAlternative.createMapping(getFieldCount(this.original),
          trimmedFieldCount);
    }

    /**
     * Calculate best rel with the same columns.
     * @return a trimmed rel node with the same columns,
     *         or null if trimming has not changed the node.
     */
    private RelNode calculateBestRelWithSameColumnsOrNull() {
      this.ensureRecursion();
      if (this.best == null) {
        return null;
      }

      if (this.best.mapping.isIdentity()) {
        if (Objects.equals(this.best.rel.getRowType(), this.original.getRowType())) {
          return this.best.rel;
        }

        // best with projection to get same row type and identity mapping
        if (this.original.getRowType().equalsSansFieldNames(this.best.rel.getRowType())) {
          return this.best.rel;
        }
      }

      return this.restoreTypeOrNull(this.best);
    }

    /**
     * Calculates a trimmed sub-tree, if {@link #bestWithoutExtraProject} has not been updated.
     */
    private RelNode calculateSameColumnsFallback() {
      this.ensureRecursion();
      if (this.getChildren().isEmpty()) {
        return this.original;
      }

      // trim the children as good as possible
      List<RelNode> inputs = new ArrayList<>();
      for (TrimWorker c : this.getChildren()) {
        inputs.add(c.getSameColumnsRel());
      }

      // the result has the same columns, so we do not need to adapt the trait set
      return this.original.copy(this.original.getTraitSet(), inputs);
    }

    /**
     * Adds a projection with dummy fields, so that the resulting row type
     * is the same as the one from the original node.
     *
     * @return null, if the type could not be restored
     */
    private RelNode restoreTypeOrNull(TrimResult v) {
      final RelDataType targetRowType = this.original.getRowType();
      List<RelDataTypeField> fieldList = targetRowType.getFieldList();
      final List<RexNode> exprList = new ArrayList<>();
      final List<String> nameList = targetRowType.getFieldNames();
      RexBuilder rexBuilder = this.original.getCluster().getRexBuilder();
      assert v.mapping.getSourceCount() == fieldList.size();
      for (int i = 0; i < fieldList.size(); i++) {
        int source = v.mapping.getTargetOpt(i);
        RelDataTypeField field = fieldList.get(i);
        RexNode e = source < 0
            ? makeZeroLiteral(rexBuilder, field.getType())
            : rexBuilder.makeInputRef(field.getType(), source);
        if (e == null) {
          return null;
        }
        exprList.add(e);
      }
      RelBuilder relBuilder = this.getRelBuilder();
      relBuilder
          .push(v.rel)
          .project(exprList, nameList);
      return relBuilder.build();
    }

    // ~ Helper methods ------------------------------------------------------

    /**
     * Applies a mapping to an {@code ImmutableBitSet}.
     *
     * <p>
     * If the mapping does not affect the bit set, returns the original.
     * Never changes the original.
     *
     * @param mapping Mapping
     * @param bitSet  Bit set
     * @return Bit set with mapping applied
     */
    public static ImmutableBitSet applyOpt(Mapping mapping, ImmutableBitSet bitSet) {
      final ImmutableBitSet.Builder builder = ImmutableBitSet.builder();
      for (int source : bitSet) {
        final int target = mapping.getTargetOpt(source);
        if (target < 0) {
          continue;
        }
        builder.set(target);
      }
      return builder.build(bitSet);
    }

    /**
     * Make a literal representing the default value.
     *
     * @return null if not possible;
     * @see RexBuilder#makeZeroLiteral(RelDataType)
     */
    // could be integrated into RexBuilder?
    private static RexLiteral makeZeroLiteral(RexBuilder rexBuilder, RelDataType type) {
      if (type.isNullable()) {
        return rexBuilder.makeNullLiteral(type);
      }

      if (type instanceof ArraySqlType || type instanceof JavaType) {
        return rexBuilder.makeNullLiteral(type);
      }

      RexLiteral zero;
      try {
        zero = rexBuilder.makeZeroLiteral(type);
      } catch (AssertionError e) {
        // TODO tre: logging
        return null;
      }
      return zero;
    }
  }

  /**
   * Result of an attempt to trim columns from a relational expression.
   *
   * <p>
   * The mapping describes where to find the columns wanted by the parent
   * of the current relational expression.
   *
   * <p>
   * The mapping is a
   * {@link org.apache.calcite.util.mapping.Mappings.SourceMapping}, which means
   * that no column can be used more than once, and some columns are not used.
   * {@code columnsUsed.getSource(i)} returns the source of the i'th output
   * field.
   *
   * <p>
   * For example, consider the mapping for a relational expression that
   * has 4 output columns but only two are being used. The mapping
   * {2 &rarr; 1, 3 &rarr; 0} would give the following behavior:
   *
   * <ul>
   * <li>columnsUsed.getSourceCount() returns 4
   * <li>columnsUsed.getTargetCount() returns 2
   * <li>columnsUsed.getSource(0) returns 3
   * <li>columnsUsed.getSource(1) returns 2
   * <li>columnsUsed.getSource(2) throws IndexOutOfBounds
   * <li>columnsUsed.getTargetOpt(3) returns 0
   * <li>columnsUsed.getTargetOpt(0) returns -1
   * </ul>
   */
  static class TrimResult {
    final RelNode rel;
    final Mapping mapping;

    private static Mapping identityMapping(RelNode rel) {
      int fieldCount = getFieldCount(rel);
      return Mappings.createIdentity(fieldCount);
    }

    private static TrimResult identity(RelNode rel) {
      return new TrimResult(rel, identityMapping(rel));
    }

    TrimResult(RelNode rel, Mapping mapping) {
      this.rel = rel;
      this.mapping = mapping;
      if (mapping.getTargetCount() != getFieldCount(rel)) {
        throw new IllegalStateException(
            "Illegal mapping: "
                + mapping
                + "\nfor row type "
                + rel.getRowType()
                + "\nof rel "
                + rel);
      }
    }
  }

  /**
   * Allows to attach the input plan when an exception happens while trimming.
   */
  protected static class TrimmerException extends RuntimeException {
    public TrimmerException(String message) {
      super(message);
    }

    public TrimmerException(String message, Throwable cause) {
      super(message, cause);
    }
  }

  /**
   * Trim context.
   */
  protected static class TrimContext extends Context {
    final ReflectUtil.MethodDispatcher<Void> trimDispatcher;
    final RelBuilder relBuilder;

    TrimContext(RelNode root, RelBuilder builder,
        ReflectUtil.MethodDispatcher<Void> trimDispatcher) {
      super(root);
      this.relBuilder = builder;
      this.trimDispatcher = trimDispatcher;
    }

  }
}
