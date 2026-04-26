# Prioritized Table API Implementation List

This document provides a complete, prioritized implementation roadmap for the APIs listed in `TableAPI.md`.

Priority is ordered from foundational operations to advanced transformations.

## Prioritization Principles

1. Build the smallest useful table core first.
2. Prioritize ingestion + select/filter workflows.
3. Implement `Raw`-friendly operations before proof-heavy abstractions.
4. Defer high-complexity joins/reshaping APIs until core semantics stabilize.

## Phase 0 - Core Foundations

- `emptyTable :: t:Table`
- `nrows :: t:Table -> n:Number`
- `ncols :: t:Table -> n:Number`
- `header :: t:Table -> cs:Seq<ColName>`
- `values :: rs:Seq<Row> -> t:Table`

## Phase 1 - Basic Access (Read Path)

- `getRow :: t:Table * n:Number -> r:Row`
- `getValue :: r:Row * c:ColName -> v:Value`
- `(overloading 1/2) getColumn :: t:Table * n:Number -> vs:Seq<Value>`
- `(overloading 2/2) getColumn :: t:Table * c:ColName -> vs:Seq<Value>`
- `head :: t1:Table * n:Number -> t2:Table`

## Phase 2 - Basic Construction (Write Path)

- `addRows :: t1:Table * rs:Seq<Row> -> t2:Table`
- `addColumn :: t1:Table * c:ColName * vs:Seq<Value> -> t2:Table`
- `buildColumn :: t1:Table * c:ColName * f:(r:Row -> v:Value) -> t2:Table`

## Phase 3 - Subtable Selection (MVP Focus)

- `(overload 1/2) selectRows :: t1:Table * ns:Seq<Number> -> t2:Table`
- `(overload 2/2) selectRows :: t1:Table * bs:Seq<Boolean> -> t2:Table`
- `(overload 1/3) selectColumns :: t1:Table * bs:Seq<Boolean> -> t2:Table`
- `(overload 2/3) selectColumns :: t1:Table * ns:Seq<Number> -> t2:Table`
- `(overload 3/3) selectColumns :: t1:Table * cs:Seq<ColName> -> t2:Table`
- `tfilter :: t1:Table * f:(r:Row -> b:Boolean) -> t2:Table`
- `dropColumn :: t1:Table * c:ColName -> t2:Table`
- `dropColumns :: t1:Table * cs:Seq<ColName> -> t2:Table`
- `vcat :: t1:Table * t2:Table -> t3:Table`
- `hcat :: t1:Table * t2:Table -> t3:Table`

## Phase 4 - Table Combination (Intro Joins)

- `distinct :: t1:Table -> t2:Table`
- `crossJoin :: t1:Table * t2:Table -> t3:Table`
- `leftJoin :: t1:Table * t2:Table * cs:Seq<ColName> -> t3:Table`

## Phase 5 - Light Utilities

- `renameColumns :: t1:Table * ccs:Seq<ColName * ColName> -> t2:Table`
- `transformColumn :: t1:Table * c:ColName * f:(v1:Value -> v2:Value) -> t2:Table`
- `select :: t1:Table * f:(r1:Row * n:Number -> r2:Row) -> t2:Table`

## Phase 5.5 - Missing values

- `completeCases :: t:Table * c:ColName -> bs:Seq<Boolean>`
- `dropna :: t1:Table -> t2:Table`
- `fillna :: t1:Table * c:ColName * v:Value -> t2:Table`

## Phase 6 - Ordering + Aggregation

- `tsort :: t1:Table * c:ColName * b:Boolean -> t2:Table`
- `sortByColumns :: t1:Table * cs:Seq<ColName> -> t2:Table`
- `count :: t1:Table * c:ColName -> t2:Table`

## Phase 7 - Advanced Reshaping + Generalized Joins

- `pivotLonger :: t1:Table * cs:Seq<ColName> * c1:ColName * c2:ColName -> t2:Table`
- `pivotWider :: t1:Table * c1:ColName * c2:ColName -> t2:Table`
- `flatten :: t1:Table * cs:Seq<ColName> -> t2:Table`
- `find :: t:Table * r:Row -> n:Error<Number>`
- `groupByRetentive :: t1:Table * c:ColName -> t2:Table`
- `groupBySubtractive :: t1:Table * c:ColName -> t2:Table`
- `selectMany :: t1:Table * project:(r1:Row * n:Number -> t2:Table) * result:(r2:Row * r3:Row -> r4:Row) -> t3:Table`
- `orderBy :: t1:Table * Seq<Exists K . getKey:(r:Row -> k:K) * compare:(k1:K * k2:K -> Boolean)> -> t2:Table`
- `groupJoin<K> :: t1:Table * t2:Table * getKey1:(r1:Row -> k1:K) * getKey2:(r2:Row -> k2:K) * aggregate:(r3:Row * t3:Table -> r4:Row) -> t4:Table`
- `join<K> :: t1:Table * t2:Table * getKey1:(r1:Row -> k1:K) * getKey2:(r2:Row -> k2:K) * combine:(r3:Row * r4:Row -> r5:Row) -> t3:Table`

## Phase 8 - Think later

- `update :: t1:Table * f:(r1:Row -> r2:Row) -> t2:Table`
  - Maybe a column-based operation is more useful. Let's see what Pandas provides
- `bin :: t1:Table * c:ColName * n:Number -> t2:Table`
- `pivotTable :: t1:Table * cs:Seq<ColName> * aggs:Seq<ColName * ColName * Function> -> t2:Table`
- `groupBy<K,V> :: t1:Table * key:(r1:Row -> k1:K) * project:(r2:Row -> v:V) * aggregate:(k2:K * vs:Seq<V> -> r3:Row) -> t2:Table`
  - Similarly to `update`, we need to ensure that each produced Row has the same shape.

## Complete Coverage Check

- Total items listed (counting overloaded signatures separately): **49**
- Scope covered: **all functions/properties from `TableAPI.md`**

