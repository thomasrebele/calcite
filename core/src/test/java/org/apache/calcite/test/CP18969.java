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

import org.apache.calcite.adapter.java.ReflectiveSchema;
import org.apache.calcite.rel.DebugRelWriter;
import org.apache.calcite.rel.RelNode;
import org.apache.calcite.rel.core.JoinRelType;
import org.apache.calcite.rel.type.RelDataType;
import org.apache.calcite.rel.type.RelDataTypeFactory;
import org.apache.calcite.rel.type.RelDataTypeSystemImpl;
import org.apache.calcite.rex.RexBuilder;
import org.apache.calcite.rex.RexCorrelVariable;
import org.apache.calcite.rex.RexDynamicParam;
import org.apache.calcite.schema.SchemaPlus;
import org.apache.calcite.schema.impl.AbstractTable;
import org.apache.calcite.sql.SqlExplainLevel;
import org.apache.calcite.sql.fun.SqlStdOperatorTable;
import org.apache.calcite.sql.type.BasicSqlType;
import org.apache.calcite.sql.type.SqlTypeName;
import org.apache.calcite.sql2rel.RelDecorrelator;
import org.apache.calcite.tools.FrameworkConfig;
import org.apache.calcite.tools.RelBuilder;
import org.apache.calcite.util.Holder;

import java.util.Arrays;
import java.util.function.BiConsumer;
import java.util.function.BiFunction;
import java.util.function.Consumer;
import java.util.function.Function;

import static org.apache.calcite.sql.type.SqlTypeName.VARCHAR;
import static org.apache.calcite.tools.Frameworks.createRootSchema;
import static org.apache.calcite.tools.Frameworks.newConfigBuilder;

public class CP18969 {

  static interface FieldT extends BiConsumer<RelDataTypeFactory, RelDataTypeFactory.Builder> {
  }

  static interface RowT extends Function<RelDataTypeFactory, RelDataType> {
  }

  static FieldT field(String name, SqlTypeName type) {
    return (tf, b) -> b.add(name, type);
  }

  static FieldT field(String name, RowT type) {
    return (tf, b) -> b.add(name, type.apply(tf));
  }

  static RowT row(FieldT... fields) {
    return (tf) -> {
      RelDataTypeFactory.Builder builder = tf.builder();
      for (FieldT f : fields) {
        f.accept(tf, builder);
      }
      return builder.build();
    };
  }

  static AbstractTable table(FieldT... fields) {
    return new AbstractTable() {
      @Override
      public RelDataType getRowType(RelDataTypeFactory typeFactory) {
        return row(fields).apply(typeFactory);
      }
    };
  }

  public static void main(String[] args) throws Exception {
    test1();
  }

  public static void test2() throws Exception {
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
        cor0.get().id
    );


    RelNode q = b.build();

    System.out.println("before decorrelate");
    DebugRelWriter.printSimpleToStdout(q);

    q = RelDecorrelator.decorrelateQuery(q, b);

    System.out.println("after decorrelate");
    DebugRelWriter.printSimpleToStdout(q);

    String s = DebugRelWriter.explain(q, SqlExplainLevel.ALL_ATTRIBUTES);
    if (s.contains("$cor") && !s.contains("LogicalCorrelate")) {
      System.out.println("ERROR");
    }
  }


  public static void test1() throws Exception {
    SchemaPlus rootSchema = createRootSchema(true);
    rootSchema.add("TABLE3", table(field("F_3", row(field("F_3_SUB", VARCHAR)))));



    CalciteAssert.addSchema(rootSchema, CalciteAssert.SchemaSpec.BOOKSTORE);
    FrameworkConfig fwkCfg = newConfigBuilder().defaultSchema(rootSchema).build();
    RelBuilder b = RelBuilder.create(fwkCfg);
    final Holder<RexCorrelVariable> cor0 = Holder.of(null);

    b.scan("bookstore", "authors").as("a1");
    b.variable(cor0);

    b.scan("bookstore", "authors").as("a2");
    b.filter(
        b.call(SqlStdOperatorTable.EQUALS,
            b.field(cor0.get(), "name"),
            b.field(
                b.field("birthPlace"),
                "city"))
    );

    b.scan("TABLE3");

    b.join(JoinRelType.INNER, b.call(SqlStdOperatorTable.EQUALS,
        b.field(b.field(2, "a2", "birthPlace"), "city"),
        b.field(b.field(2, "TABLE3", "F_3"), "F_3_SUB"))
    );

    b.correlate(
        JoinRelType.INNER,
        cor0.get().id
    );


    RelNode q = b.build();

    System.out.println("before decorrelate");
    DebugRelWriter.printSimpleToStdout(q);

    q = RelDecorrelator.decorrelateQuery(q, b);

    System.out.println("after decorrelate");
    DebugRelWriter.printSimpleToStdout(q);

  }
}
