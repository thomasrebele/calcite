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
import org.apache.calcite.plan.RelOptUtil;
import org.apache.calcite.rel.RelCollation;
import org.apache.calcite.rel.RelCollations;
import org.apache.calcite.rel.RelFieldCollation;
import org.apache.calcite.rel.RelNode;
import org.apache.calcite.rel.core.Aggregate;
import org.apache.calcite.rel.core.AggregateCall;
import org.apache.calcite.rel.core.Calc;
import org.apache.calcite.rel.core.Correlate;
import org.apache.calcite.rel.core.Filter;
import org.apache.calcite.rel.core.Join;
import org.apache.calcite.rel.core.Project;
import org.apache.calcite.rel.core.SetOp;
import org.apache.calcite.rel.core.Sort;
import org.apache.calcite.rel.core.TableScan;
import org.apache.calcite.rel.core.Uncollect;
import org.apache.calcite.rel.core.Values;
import org.apache.calcite.rel.metadata.RelMetadataQuery;
import org.apache.calcite.rel.type.RelDataTypeField;
import org.apache.calcite.rex.RexNode;
import org.apache.calcite.rex.RexProgram;
import org.apache.calcite.sql.SqlKind;

import com.google.common.collect.ImmutableList;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.function.BiFunction;

/**
 * Calculates for every node the fields that are required by its parent for evaluating the query.
 * All other fields may be removed by the field trimmer.
 *
 *
 *
 * <p>Algorithm: start at the root node and mark all fields as required.
 * Start visiting the tree at the root. To determine the fields that should
 * be calculated by a RelNode n, we take the fields requested by the parent
 * plus the fields that are required to evaluate n. These fields need
 * to be provided by the children, so call the algorithm recursively on them.
 *
 *
 *
 * <p>For a possible later optimization of the dispatcher, the attributes of the visitor
 * must be independent of the trimming of a {@link RelNode}. They must be stored
 * in a {@link Context} object instead.
 */
public class RelFieldUsageVisitor implements ReflectiveVisitor {

  // TODO tre: implement:
  // Exchange, SortExchange, LogicalTableModify, LogicalTableFunctionScan

  /**
   * Uses multi-methods to fire the right rule for each type of relational
   * expression. This allows the visitor to be extended without having to
   * add a new method to RelNode, and without requiring a collection of rule
   * classes scattered to the four winds.
   */
  @SuppressWarnings("rawtypes")
  protected final ReflectUtil.MethodDispatcher<List> analyzeDispatcher;

  public RelFieldUsageVisitor() {
    this.analyzeDispatcher = ReflectUtil
        .createMethodDispatcher(
            List.class,
            this,
            "calculateUsedFields",
            RelNode.class,
            FieldUsageWorker.class);
  }

  /**
   * Analyze the RelNode tree.
   * This is the main method.
   */
  public FieldUsageWorker analyze(RelNode rel) {
    Context ctx = new Context(rel);
    return this.analyze(rel, ctx);
  }

  protected FieldUsageWorker analyze(RelNode rel, Context ctx) {
    FieldUsageWorker worker = this.createWorker(rel, ctx);
    worker.setFieldsNeededByParent(this.useEveryField(rel));
    this.analyzeNode(rel, worker);
    return worker;
  }

  /**
   * Create a new worker. To be overridden by a subclass, if it wants to use a different worker.
   *
   * You probably want to call {@link #getChildWorker(FieldUsageWorker, int)}.
   */
  protected FieldUsageWorker createWorker(RelNode rel, Context data) {
    return new FieldUsageWorker(rel, data, this::createWorker);
  }

  protected FieldUsageWorker getChildWorker(
      FieldUsageWorker parent,
      int childIndex) {
    return parent.getOrCreateChild(childIndex);
  }

  /**
   * A field set indicating that all fields from the rel are required by the parent.
   */
  protected ImmutableBitSet useEveryField(RelNode rel) {
    final int fieldCount = getFieldCount(rel);
    final ImmutableBitSet fieldsUsed = ImmutableBitSet.range(fieldCount);
    return fieldsUsed;
  }

  @SuppressWarnings("unchecked")
  protected void analyzeNode(RelNode rel, FieldUsageWorker worker) {
    List<ImmutableBitSet> fieldsUsed = this.analyzeDispatcher.invoke(rel, worker);

    if (fieldsUsed == null) {
      // the specialized method could not calculate the used fields,
      // so use the general algorithm
      fieldsUsed = this.calculateUsedFields(rel, worker);
    }

    // recursively call children
    List<RelNode> inputs = rel.getInputs();
    for (int i = 0; i < inputs.size(); i++) {
      RelNode childRel = inputs.get(i);
      FieldUsageWorker child = this.getChildWorker(worker, i);
      child.setFieldsNeededByParent(fieldsUsed.get(i));
      this.analyzeNode(childRel, child);
    }
  }

  /**
   * Visit method, per {@link org.apache.calcite.util.ReflectiveVisitor}.
   *
   * <p>
   * This method is invoked reflectively, so there may not be any apparent
   * calls to it. The class (or derived classes) may contain overloads of
   * this method with more specific types for the {@code rel} parameter.
   *
   * <p>
   * The general implementation assumes that the node requires all fields from its children.
   *
   * @return a list where the i-th entry indicates the required fields for the i-th child.
   */
  public List<ImmutableBitSet> calculateUsedFields(RelNode node, FieldUsageWorker worker) {
    List<ImmutableBitSet> childFieldsUsed = new ArrayList<>();
    for (RelNode input : node.getInputs()) {
      childFieldsUsed.add(this.useEveryField(input));
    }
    return childFieldsUsed;
  }

  /**
   * Variant of {@link #calculateUsedFields(RelNode, FieldUsageWorker)}.
   */
  public List<ImmutableBitSet> calculateUsedFields(Calc calc, FieldUsageWorker worker) {
    RexProgram prog = calc.getProgram();
    final List<RexNode> projs = Util.transform(prog.getProjectList(), prog::expandLocalRef);
    RexNode condition = prog.getCondition() == null
        ? null
        : prog.expandLocalRef(prog.getCondition());
    return this.calculateUsedFieldsForCalc(worker, projs, condition);
  }

  /**
   * Variant of {@link #calculateUsedFields(RelNode, FieldUsageWorker)}.
   */
  public List<ImmutableBitSet> calculateUsedFields(Project project, FieldUsageWorker worker) {
    return this.calculateUsedFieldsForCalc(worker, project.getProjects(), null);
  }

  /**
   * Variant of {@link #calculateUsedFields(RelNode, FieldUsageWorker)}.
   */
  public List<ImmutableBitSet> calculateUsedFields(Filter filter, FieldUsageWorker worker) {
    return this.calculateUsedFieldsForCalc(worker, null, filter.getCondition());
  }

  private List<ImmutableBitSet> calculateUsedFieldsForCalc(
      FieldUsageWorker worker,
      final List<RexNode> projs,
      RexNode condition) {
    // limited implementation: extra/system fields not yet supported
    Set<RelDataTypeField> inputExtraFields = Collections.emptySet();
    ImmutableBitSet init = projs == null ? worker.getNeededByParent() : ImmutableBitSet.of();
    RelOptUtil.InputFinder inputFinder = new RelOptUtil.InputFinder(inputExtraFields, init);
    if (projs != null) {
      for (Ord<RexNode> ord : Ord.zip(projs)) {
        if (worker.getNeededByParent().get(ord.i)) {
          ord.e.accept(inputFinder);
        }
      }
    }
    // condition
    if (condition != null) {
      condition.accept(inputFinder);
    }

    ImmutableBitSet inputFieldsUsed = inputFinder.build();
    return Collections.singletonList(inputFieldsUsed);
  }

  /**
   * Variant of {@link #calculateUsedFields(RelNode, FieldUsageWorker)}.
   */
  public List<ImmutableBitSet> calculateUsedFields(Sort sort, FieldUsageWorker worker) {
    RelCollation collation = sort.getCollation();

    // We use the fields used by the consumer, plus any fields used as sort keys.
    final ImmutableBitSet.Builder inputFieldsUsed = worker.getNeededByParent().rebuild();
    for (RelFieldCollation field : collation.getFieldCollations()) {
      inputFieldsUsed.set(field.getFieldIndex());
    }

    return Collections.singletonList(inputFieldsUsed.build());
  }

  /**
   * Variant of {@link #calculateUsedFields(RelNode, FieldUsageWorker)}.
   */
  public List<ImmutableBitSet> calculateUsedFields(Join join, FieldUsageWorker worker) {
    // limited implementation: extra/system fields not yet supported

    final Set<RelDataTypeField> combinedInputExtraFields = Collections.emptySet();
    RelOptUtil.InputFinder inputFinder = new RelOptUtil.InputFinder(combinedInputExtraFields,
        worker.getNeededByParent());
    join.getCondition().accept(inputFinder);
    ImmutableBitSet fieldsUsed = inputFinder.build();

    List<RelNode> inputs = join.getInputs();
    return this.fieldsUsedForJoin(inputs, fieldsUsed);
  }

  /**
   * Variant of {@link #calculateUsedFields(RelNode, FieldUsageWorker)}.
   */
  public List<ImmutableBitSet> calculateUsedFields(Correlate rel, FieldUsageWorker worker) {
    List<RelNode> inputs = rel.getInputs();
    assert inputs.size() == 2;
    ImmutableBitSet fieldsUsed = worker.getNeededByParent();
    fieldsUsed = fieldsUsed.union(rel.getRequiredColumns());
    return this.fieldsUsedForJoin(inputs, fieldsUsed);
  }

  /**
   * Variant of {@link #calculateUsedFields(RelNode, FieldUsageWorker)}.
   */
  private List<ImmutableBitSet> fieldsUsedForJoin(List<RelNode> inputs,
      ImmutableBitSet fieldsUsed) {
    List<ImmutableBitSet> result = new ArrayList<>(2);
    int shiftIn = 0;
    for (int i = 0; i < inputs.size(); i++) {
      RelNode input = inputs.get(i);

      final int inputFieldCount = getFieldCount(input);
      ImmutableBitSet inputRange = ImmutableBitSet.range(shiftIn, shiftIn + inputFieldCount);
      ImmutableBitSet inputFieldsUsed = fieldsUsed.intersect(inputRange);
      if (i > 0) {
        inputFieldsUsed = inputFieldsUsed.shift(-shiftIn);
      }

      result.add(inputFieldsUsed);
      shiftIn += inputFieldCount;
    }
    return result;
  }

  /**
   * Variant of {@link #calculateUsedFields(RelNode, FieldUsageWorker)}.
   *
   * Only UNION ALL supported atm.
   */
  public List<ImmutableBitSet> calculateUsedFields(SetOp setOp, FieldUsageWorker worker) {
    // UNION | INTERSECT | INTERSECT ALL | EXCEPT | EXCEPT ALL
    // all have comparison between branches.
    // They can not be trimmed because the comparison needs
    // complete fields.
    if (!(setOp.kind == SqlKind.UNION && setOp.all)) {
      // the caller provides a fall-back
      return null;
    }

    List<ImmutableBitSet> result = new ArrayList<>(setOp.getInputs().size());
    for (int i = 0; i < setOp.getInputs().size(); i++) {
      result.add(worker.getNeededByParent());
    }
    return result;
  }

  /**
   * Variant of {@link #calculateUsedFields(RelNode, FieldUsageWorker)}.
   */
  public List<ImmutableBitSet> calculateUsedFields(Aggregate rel, FieldUsageWorker worker) {
    return this.calculateUsedField(rel, worker, rel.getGroupSet());
  }

  /**
   * Calculates the fields used by an aggregate.
   *
   * @param usedGroupFields the group fields that need to be retained so that
   *                        the result of the aggregation is correct
   */
  protected List<ImmutableBitSet> calculateUsedField(
      Aggregate rel,
      FieldUsageWorker worker,
      ImmutableBitSet usedGroupFields) {
    // Compute which input fields are used.
    // 1. group fields are always used
    final ImmutableBitSet.Builder inputFieldsUsed = usedGroupFields.rebuild();

    // 2. agg functions
    int offset = rel.getGroupCount();
    for (int i = 0; i < rel.getAggCallList().size(); i++) {
      // we only need the inputs fields for those agg calls that are actually used
      if (!worker.getNeededByParent().get(offset + i)) {
        continue;
      }

      AggregateCall aggCall = rel.getAggCallList().get(i);

      inputFieldsUsed.addAll(aggCall.getArgList());
      if (aggCall.filterArg >= 0) {
        inputFieldsUsed.set(aggCall.filterArg);
      }
      if (aggCall.distinctKeys != null) {
        inputFieldsUsed.addAll(aggCall.distinctKeys);
      }
      inputFieldsUsed.addAll(RelCollations.ordinals(aggCall.collation));
    }

    return Collections.singletonList(inputFieldsUsed.build());
  }

  /**
   * Variant of {@link #calculateUsedFields(RelNode, FieldUsageWorker)}.
   */
  public List<ImmutableBitSet> calculateUsedFields(Values rel, FieldUsageWorker worker) {
    assert rel.getInputs().size() == 0;
    return Collections.emptyList();
  }

  /**
   * Variant of {@link #calculateUsedFields(RelNode, FieldUsageWorker)}.
   */
  public List<ImmutableBitSet> calculateUsedFields(TableScan rel, FieldUsageWorker worker) {
    assert rel.getInputs().size() == 0;
    return Collections.emptyList();
  }

  /**
   * Variant of {@link #calculateUsedFields(RelNode, FieldUsageWorker)}.
   */
  public List<ImmutableBitSet> calculateUsedFields(Uncollect rel, FieldUsageWorker worker) {
    // Uncollect behaves like a cross product, so even if a field is not requested by the parent,
    // it might influence the number of rows for the remaining fields.
    // Improvements could be possible if the parent tree throws away that information.
    // (e.g., doing a MAX(...))

    int fieldCount = getFieldCount(rel);
    if (rel.withOrdinality) {
      fieldCount--;
    }
    return Collections.singletonList(ImmutableBitSet.range(fieldCount));
  }

  public static int getFieldCount(RelNode r) {
    return r.getRowType().getFieldCount();
  }

  /**
   * Collects the result of {@link RelFieldUsageVisitor}.
   */
  static class FieldUsageWorker {
    final RelNode original;
    final Context context;

    /**
     * Represents the fields needed by the parent.
     * This does not include the fields needed by the node!
     */
    private ImmutableBitSet neededByParent;

    private List<FieldUsageWorker> children;

    /** Used to create child workers. */
    private final BiFunction<RelNode, Context, FieldUsageWorker> workerCreator;

    FieldUsageWorker(
        RelNode original,
        Context context,
        BiFunction<RelNode, Context, FieldUsageWorker> workerCreator) {
      this.original = original;
      this.context = context;
      this.workerCreator = workerCreator;
    }

    public FieldUsageWorker getOrCreateChild(int childIndex) {
      int size = this.original.getInputs().size();
      RelNode rel = this.original.getInput(childIndex);
      if (childIndex >= size) {
        throw new IllegalArgumentException(
            "RelNode has no child with index " + childIndex + ", just " + size + ": " + rel);
      }
      if (this.children == null) {
        this.children = new ArrayList<>(size);
        for (int i = 0; i < size; i++) {
          this.children.add(null);
        }
      }
      FieldUsageWorker result = this.children.get(childIndex);
      if (result != null) {
        return result;
      }

      FieldUsageWorker childWorker = this.workerCreator.apply(rel, this.context);
      this.children.set(childIndex, childWorker);
      return childWorker;
    }

    public ImmutableBitSet getNeededByParent() {
      return this.neededByParent;
    }

    protected List<? extends FieldUsageWorker> getChildren() {
      int s = (int) (this.children == null
          ? 0
          : this.children.stream().filter(w -> w != null).count());
      if (s != this.original.getInputs().size()) {
        // normally it should not happen, but just in case, enforce children creation
        for (int i = 0; i < this.original.getInputs().size(); i++) {
          this.getOrCreateChild(i);
        }
      }
      return this.children == null
          ? Collections.emptyList()
          : Collections.unmodifiableList(this.children);
    }

    /**
     * Sets the fields needed by the parent.
     * It also ensures that the fields required for the collation
     * are included in the {@link FieldUsageWorker#neededByParent} set.
     */
    public void setFieldsNeededByParent(ImmutableBitSet neededByParent) {
      if (this.getNeededByParent() != null) {
        throw new IllegalStateException();
      }
      this.setFieldsNeededByParentCore(neededByParent);
    }

    public void setFieldsNeededByParentCore(ImmutableBitSet neededByParent) {
      // Fields that define the collation cannot be discarded.
      final RelMetadataQuery mq = this.original.getCluster().getMetadataQuery();
      final ImmutableList<RelCollation> collations = mq.collations(this.original);
      if (collations == null) {
        this.neededByParent = neededByParent;
        return;
      }

      // limited implementation: sometimes it might be better to throw away the collation.
      // To keep the algorithm simple, we just keep the fields as they are.
      final ImmutableBitSet.Builder fieldsUsedBuilder = neededByParent.rebuild();
      for (RelCollation collation : collations) {
        for (RelFieldCollation fieldCollation : collation.getFieldCollations()) {
          fieldsUsedBuilder.set(fieldCollation.getFieldIndex());
        }
      }
      this.neededByParent = fieldsUsedBuilder.build();
    }

    /**
     * String representation of the worker tree.
     */
    public String toStringRec() {
      StringBuilder sb = new StringBuilder();
      this.toStringRec(sb, "");
      return sb.toString();
    }

    private void toStringRec(StringBuilder sb, String prefix) {
      this.toString(sb, prefix);
      for (FieldUsageWorker c : this.getChildren()) {
        String cp = prefix + "   ";
        if (c == null) {
          sb.append(cp).append("<missing>\n");
        } else {
          c.toStringRec(sb, cp);
        }
      }
    }

    /**
     * Override in subclasses, if you want to change the result of {@link #toStringRec()}.
     */
    public void toString(StringBuilder sb, String prefix) {
      // TODO tre: check format or delete toString methods
      String p = prefix;
      if (p.length() > 2) {
        p = prefix.substring(0, prefix.length() - 2) + "- ";
      }
      String orig = this.original.explain();
      sb.append(p).append("original: ").append(orig).append("\n");
      sb.append(prefix).append("type:     ").append(this.original.getRowType()).append("\n");
      sb.append(prefix).append("needed: ").append(this.getNeededByParent()).append("\n");
    }
  }

  /**
   * "Global" variables for the trimming of a RelNode tree.
   */
  static class Context {
    final RelNode root;

    Context(RelNode root) {
      this.root = root;
    }

  }

}
