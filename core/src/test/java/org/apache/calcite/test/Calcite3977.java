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

package org.apache.calcite.test;

import org.apache.calcite.plan.RelOptUtil;
import org.apache.calcite.rel.RelNode;
import org.apache.calcite.rel.core.JoinRelType;
import org.apache.calcite.rex.RexCorrelVariable;
import org.apache.calcite.schema.SchemaPlus;
import org.apache.calcite.sql.fun.SqlStdOperatorTable;
import org.apache.calcite.sql2rel.RelDecorrelator;
import org.apache.calcite.tools.FrameworkConfig;
import org.apache.calcite.tools.RelBuilder;
import org.apache.calcite.util.Holder;

import static org.apache.calcite.tools.Frameworks.createRootSchema;
import static org.apache.calcite.tools.Frameworks.newConfigBuilder;

public class Calcite3977 {

  public static void main(String[] args) {
    SchemaPlus rootSchema = createRootSchema(true);
    CalciteAssert.addSchema(rootSchema, CalciteAssert.SchemaSpec.BOOKSTORE);
    FrameworkConfig fwkCfg = newConfigBuilder().defaultSchema(rootSchema).build();
    RelBuilder b = RelBuilder.create(fwkCfg);
    final Holder<RexCorrelVariable> cor0 = Holder.of(null);

    b.scan("bookstore", "authors");
    b.variable(cor0);

    b.scan("bookstore", "authors");
    b.filter(
        b.call(SqlStdOperatorTable.EQUALS,
            b.literal("Munich"),
            b.field(
                b.field(cor0.get(), "birthPlace"),
                "city"))
    );

    b.correlate(
        JoinRelType.LEFT,
        cor0.get().id,
        b.field("birthPlace")
    );


    RelNode q = b.build();

    System.out.println("before decorrelate");
    System.out.println(RelOptUtil.toString((q)));
    q = RelDecorrelator.decorrelateQuery(q, b);

    System.out.println("after decorrelate");
    String output = RelOptUtil.toString((q));
    System.out.println(output);

    if (output.contains("$cor") && !output.contains("LogicalCorrelate")) {
      System.out.println("ERROR");
    }
  }

}
