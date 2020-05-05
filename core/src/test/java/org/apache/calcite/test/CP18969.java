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

import org.apache.calcite.plan.RelOptCluster;
import org.apache.calcite.plan.RelOptUtil;
import org.apache.calcite.prepare.PlannerImpl;
import org.apache.calcite.rel.DebugRelWriter;
import org.apache.calcite.rel.RelNode;
import org.apache.calcite.rel.RelRoot;
import org.apache.calcite.rel.core.JoinRelType;
import org.apache.calcite.rel.type.RelDataType;
import org.apache.calcite.rel.type.RelDataTypeFactory;
import org.apache.calcite.rel.type.RelDataTypeSystemImpl;
import org.apache.calcite.rex.RexBuilder;
import org.apache.calcite.rex.RexCorrelVariable;
import org.apache.calcite.rex.RexDynamicParam;
import org.apache.calcite.schema.SchemaPlus;
import org.apache.calcite.schema.impl.AbstractTable;
import org.apache.calcite.sql.SqlNode;
import org.apache.calcite.sql.fun.SqlStdOperatorTable;
import org.apache.calcite.sql.type.BasicSqlType;
import org.apache.calcite.sql.type.SqlTypeName;
import org.apache.calcite.sql2rel.RelDecorrelator;
import org.apache.calcite.sql2rel.SqlToRelConverter;
import org.apache.calcite.tools.FrameworkConfig;
import org.apache.calcite.tools.Planner;
import org.apache.calcite.tools.RelBuilder;
import org.apache.calcite.util.Holder;

import java.util.Arrays;
import java.util.function.BiConsumer;

import static org.apache.calcite.sql.type.SqlTypeName.VARCHAR;
import static org.apache.calcite.tools.Frameworks.*;

public class CP18969 {

  public static void main(String[] args) throws Exception {
    cpTest();
  }

  static RelDataType varchar() {
    return new BasicSqlType(new RelDataTypeSystemImpl() { }, VARCHAR);
  }

  static RelDataType row_varchar(String name, RelDataTypeFactory tf) {
    RelDataTypeFactory.FieldInfoBuilder builder = tf.builder();
    builder.add(name, varchar());
    return builder.build();
  }

  static AbstractTable table(BiConsumer<RelDataTypeFactory, RelDataTypeFactory.Builder> build) {
    return new AbstractTable() {
      @Override
      public RelDataType getRowType(RelDataTypeFactory typeFactory) {
        RelDataTypeFactory.Builder builder = typeFactory.builder();
        build.accept(typeFactory, builder);
        return builder.build();
      }
    };
  }

  static void cpTest() throws Exception{
    SchemaPlus rootSchema = createRootSchema(true);
    rootSchema.add("TABLE1", table((tf, b) -> {
      b.add("F_1", varchar());
    }));

    rootSchema.add("TABLE2", table((tf,b) -> {
      b.add("F_2A", varchar());
      b.add("F_2B", row_varchar("F_2B_SUB", tf));
    }));

    rootSchema.add("TABLE3", table((tf,b) -> {
      b.add("F_3", row_varchar("F_3_SUB", tf));
    }));


    FrameworkConfig fwkCfg = newConfigBuilder().defaultSchema(rootSchema).build();
    RelBuilder b = RelBuilder.create(fwkCfg);
    RexBuilder r = b.getRexBuilder();

    final Holder<RexCorrelVariable> cor0 = Holder.of(null);

    b.scan("TABLE1");
    b.variable(cor0);

    b.scan("TABLE2");

    b.filter(
        b.call(SqlStdOperatorTable.EQUALS,
            b.field(cor0.get(), "F_1"),
            b.field(
                b.field("F_2B"),
                "F_2B_SUB"))
    );

    b.scan("TABLE3");

    b.join(JoinRelType.INNER, b.call(SqlStdOperatorTable.EQUALS,
        b.field(2, 0, "F_2A"),
        b.field(
            b.field(2, 1, "F_3"),
            "F_3_SUB"))
    );

    b.project(
        b.literal(Boolean.TRUE)
    );

    b.aggregate(b.groupKey(
        b.field(0)
    ));

    b.correlate(
        JoinRelType.INNER,
        cor0.get().id,
        b.field(2, 0, "F_1")
    );



    RelNode q = b.build();

    System.out.println("before decorrelate");
    DebugRelWriter.printSimpleToStdout(q);

    q = RelDecorrelator.decorrelateQuery(q, b);

    System.out.println("after decorrelate");
    DebugRelWriter.printSimpleToStdout(q);

  }

  static void cteTest() throws Exception {
    SchemaPlus rootSchema = createRootSchema(true);

    rootSchema.add("LIKES", new AbstractTable() {
      public RelDataType getRowType(final RelDataTypeFactory typeFactory) {
        RelDataTypeFactory.Builder builder = typeFactory.builder();
        builder.add("DRINKER", new BasicSqlType(new RelDataTypeSystemImpl() {
        }, VARCHAR));
        builder.add("BEER", new BasicSqlType(new RelDataTypeSystemImpl() {
        }, VARCHAR));
        return builder.build();
      }
    });

    rootSchema.add("SERVES", new AbstractTable() {
      public RelDataType getRowType(final RelDataTypeFactory typeFactory) {
        RelDataTypeFactory.Builder builder = typeFactory.builder();
        builder.add("BAR", new BasicSqlType(new RelDataTypeSystemImpl() {
        }, VARCHAR));
        builder.add("BEER", new BasicSqlType(new RelDataTypeSystemImpl() {
        }, VARCHAR));
        builder.add("PRICE", new BasicSqlType(new RelDataTypeSystemImpl() {
        }, SqlTypeName.DECIMAL));
        return builder.build();
      }
    });

    rootSchema.add("DRINKER", new AbstractTable() {
      public RelDataType getRowType(final RelDataTypeFactory typeFactory) {
        RelDataTypeFactory.Builder builder = typeFactory.builder();
        builder.add("NAME", new BasicSqlType(new RelDataTypeSystemImpl() {
        }, VARCHAR));
        builder.add("ADDRESS", new BasicSqlType(new RelDataTypeSystemImpl() {
        }, VARCHAR));
        return builder.build();
      }
    });

    rootSchema.add("FREQUENTS", new AbstractTable() {
      public RelDataType getRowType(final RelDataTypeFactory typeFactory) {
        RelDataTypeFactory.Builder builder = typeFactory.builder();
        builder.add("DRINKER", new BasicSqlType(new RelDataTypeSystemImpl() {
        }, VARCHAR));
        builder.add("BAR", new BasicSqlType(new RelDataTypeSystemImpl() {
        }, VARCHAR));
        builder.add("TIMES_A_WEEK", new BasicSqlType(new RelDataTypeSystemImpl() {
        }, SqlTypeName.SMALLINT));
        return builder.build();
      }
    });

    String SAMPLE_QUERY = "SELECT Frequents.drinker, Frequents.bar\n" +
        "FROM Frequents\n" +
        "WHERE NOT EXISTS(SELECT * FROM Likes, Serves\n" +
        "WHERE Likes.drinker = Frequents.drinker\n" +
        "AND Serves.bar = Frequents.bar\n" +
        "AND Likes.beer = Serves.beer)";

    Planner planner = getPlanner(newConfigBuilder().defaultSchema(rootSchema).build());
    SqlNode parsed = planner.parse(SAMPLE_QUERY);
    SqlNode validated = planner.validate(parsed);
    RelRoot relRoot = planner.rel(validated);
    System.out.println(RelOptUtil.toString(relRoot.rel));
  }
}
