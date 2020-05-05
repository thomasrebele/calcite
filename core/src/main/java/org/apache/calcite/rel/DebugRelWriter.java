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

package org.apache.calcite.rel;

import org.apache.calcite.rel.externalize.RelWriterImpl;
import org.apache.calcite.rel.metadata.RelMetadataQuery;
import org.apache.calcite.sql.SqlExplainLevel;
import org.apache.calcite.util.Pair;

import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.List;

public class DebugRelWriter extends RelWriterImpl
{
  //~ Constructors -----------------------------------------------------------

  public DebugRelWriter(PrintWriter pw, SqlExplainLevel sqlExplainLevel)
  {
    super(pw, sqlExplainLevel, true);
  }

  //~ Methods ----------------------------------------------------------------

  @Override
  protected void explain_(RelNode rel, List<Pair<String, Object>> values)
  {
    SqlExplainLevel detailLevel = this.getDetailLevel();

    List<RelNode> inputs = rel.getInputs();
    final RelMetadataQuery mq = rel.getCluster().getMetadataQuery();
    if (!mq.isVisibleInExplain(rel, detailLevel))
    {
      // render children in place of this, at same level
      this.explainInputs(inputs);
      return;
    }

    StringBuilder s = new StringBuilder();
    this.spacer.spaces(s);
    s.append(rel.getRelTypeName());
    if (detailLevel != SqlExplainLevel.NO_ATTRIBUTES)
    {
      int j = 0;
      for (Pair<String, Object> value : values)
      {
        if (value.right instanceof RelNode)
        {
          continue;
        }
        if (j++ == 0)
        {
          s.append("(");
        }
        else
        {
          s.append(", ");
        }
        s.append(value.left).append("=[").append(value.right).append("]");
      }
      if (j > 0)
      {
        s.append(")");
      }
    }
    s.append(", len=" + rel.getRowType().getFieldCount());
    switch (detailLevel)
    {
    case ALL_ATTRIBUTES:
      s.append(": rowcount = ")
          .append(mq.getRowCount(rel))
          .append(", cumulative cost = ")
          .append(mq.getCumulativeCost(rel));
    }
    switch (detailLevel)
    {
    case NON_COST_ATTRIBUTES:
    case ALL_ATTRIBUTES:
      s.append(", id = ").append(rel.getId());
      break;
    }
    this.pw.println(s);
    this.spacer.add(2);
    this.explainInputs(inputs);
    this.spacer.subtract(2);
  }

  private void explainInputs(List<RelNode> inputs)
  {
    for (RelNode input : inputs)
    {
      input.explain(this);
    }
  }

  public static void printToStdout(RelNode query)
  {
    System.out.println(explain(query, SqlExplainLevel.EXPPLAN_ATTRIBUTES));
  }

  public static void printSimpleToStdout(RelNode query)
  {
    System.out.println(explain(query, SqlExplainLevel.EXPPLAN_ATTRIBUTES));
  }

  public static String explain(RelNode query, SqlExplainLevel sqlExplainLevel)
  {
    StringWriter sw = new StringWriter();
    PrintWriter pw = new PrintWriter(sw);
    RelWriter planWriter = new DebugRelWriter(pw, sqlExplainLevel);
    query.explain(planWriter);
    pw.flush();
    return sw.toString();
  }

}
