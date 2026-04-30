## Reference

> Q. Where can we learn about the programming medium covered by this datasheet?
> (Feel free to link to multiple kinds of artifacts: repositories, papers, videos, etc.
> Please also include version information where applicable.)

- Repository: https://github.com/pandaman64/Tables
- Version: https://github.com/pandaman64/Tables/tree/8ad85e17f306e6ed784baba9c8bf2c9fa704025a

> Q. What is the URL of the version of the benchmark being used?

https://github.com/brownplt/B2T2/tree/8636f6328cb01d5a17f959ade56c6d929e21d2bd

> Q. On what date was this version of the datasheet last updated?

2026-04-30


> Q. If you are not using the latest benchmark available on that date, please explain why not.


## Example Tables

> Q. Do tables express heterogeneous data, or must data be homogenized?

A table consists of columns that may each have different data types (heterogeneous columns). Each individual column, however, contains an array of values that are all of the same type (homogeneous values).


> Q. Do tables capture missing data and, if so, how? Do missing values affect the output constraints of any operations, for example `groupBy`?

Every cell is nullable: cell values are represented as `Option _`. A present value is `some v`, and a missing value is `none` (printed as `"null"`).

Many operations therefore work over arrays of optional values. For example, grouping/aggregation consumes values of type `Array (Option α)`, so missingness is explicit and can be observed and handled by the aggregation function. Certain operators also reject missing values at runtime (in their `... ?`/`Except` variants) when an argument must be present.

> Q. Are mutable tables supported? Are there any limitations?

Tables are immutable (persistent). All operations that “change” a table return a fresh `Table` value.

Some operations are exposed in two styles:

- Total style: requires proofs of preconditions (e.g. schema equality, column freshness, bounds, no-duplicates), and cannot fail at runtime.
- Partial style: the `... ?` variants return `Except Error _` and perform dynamic checks.


> You may reference, instead of duplicating, the responses to the above questions in answering those below:

> Q. Which tables are inexpressible? Why?

Nested tables are not supported at the moment. All benchmark tables that do not require nested tables can be represented.


> Q. Which tables are only partially expressible? Why, and what’s missing?

None known.


> Q. Which tables’ expressibility is unknown? Why?

None known.


> Q. Which tables can be expressed more precisely than in the benchmark? How?

None known.


> Q. How direct is the mapping from the tables in the benchmark to representations in your system? How complex is the encoding?

The encoding is straightforward, while we use a columnar representation instead of a row-oriented representation.

- A table is represented as an `Array Column`.
- A column is a record containing a `name : String`, a `dataType : DataType`, and `values : Array (Option dataType.toType)`.
- Missing cells are encoded as `none` (printed as `"null"`).

The public `Table` wrapper additionally carries proofs that the underlying raw table is well-formed (column lengths match; column names are unique).

## TableAPI

> Q. Are there consistent changes made to the way the operations are represented?

- Operations are dynamically typed: `Table`, `Column`, and `Row` do not carry the schema as a type parameter. Instead, each cell/column carries a runtime `DataType` tag, and values are stored behind this tag.
- Many operations are provided in two forms:
  - a proof-carrying version (cannot fail, but requires explicit precondition proofs),
  - and an `Except Error _` version whose name ends with `?` (does dynamic checks).
- Every cell is nullable: values are represented as `Option _`, and callbacks typically receive `Option α` (rather than a distinguished `null` value).

> Q. Which operations are entirely inexpressible? Why?

Operations that require nested tables (e.g., `groupByRetentive`,  `groupBySubtractive`) are skipped for now.

> Q. Which operations are only partially expressible? Why, and what’s missing?

User callbacks receive dynamically-typed `Row`s. In particular, a callback does not carry a proof that the row originates from the source table, so cell access must go through runtime-checked lookup functions (e.g. by column name and `DataType`).

> Q. Which operations’ expressibility is unknown? Why?

None known.


> Q. Which operations can be expressed more precisely than in the benchmark? How?

Many operations can be made total by requiring proofs of their preconditions (e.g. schema equality for joins/unions; column freshness for `addColumn`; no-duplicates for column selections), which prevents constructing ill-formed programs in the first place.


## Example Programs

> Q. Which examples are inexpressible? Why?

None known. The repository includes Lean implementations of many B2T2-style examples (e.g. joins, pivots, flattening nested columns, sorting, group-based aggregation).


> Q. Which examples’ expressibility is unknown? Why?

None known.


> Q. Which examples, or aspects thereof, can be expressed especially precisely? How?

None known.

> Q. How direct is the mapping from the pseudocode in the benchmark to representations in your system? How complex is the encoding?

Overall, the translation is direct, but many “side conditions” become either:

- explicit proof parameters (for total versions), or
  - Currently, many proofs rely on `native_decide`, which increases the size of trusted computing base a lot (because it needs to trust the Lean compiler)
- dynamic checks producing `Except Error _` (for `... ?` versions).


## Errors

> There are (at least) two parts to errors: representing the source program that causes the error, and generating output that explains it. The term “error situation” refers to a representation of the cause of the error in the program source.
> 
> For each error situation it may be that the language:
> 
> - isn’t expressive enough to capture it
> - can at least partially express the situation
> - prevents the program from being constructed
> 
> Expressiveness, in turn, can be for multiple artifacts:
> 
> - the buggy versions of the programs
> - the correct variants of the programs
> - the type system’s representation of the constraints
> - the type system’s reporting of the violation

> Q. Which error situations are known to be inexpressible? Why?

Unknown. (This datasheet does not yet map each B2T2 error situation to the corresponding Lean encoding.)


> Q. Which error situations are only partially expressible? Why, and what’s missing?

Unknown. (This datasheet does not yet map each B2T2 error situation to the corresponding Lean encoding.)


> Q. Which error situations’ expressibility is unknown? Why?

Unknown. (This datasheet does not yet map each B2T2 error situation to the corresponding Lean encoding.)


> Q. Which error situations can be expressed more precisely than in the benchmark? How?

Unknown. (This datasheet does not yet map each B2T2 error situation to the corresponding Lean encoding.)

Theoretically, some error situations are prevented from being constructed when using proof-carrying operator variants, because the program cannot be built without supplying the required precondition proofs.


> Q. Which error situations are prevented from being constructed? How?

Unknown. (This datasheet does not yet map each B2T2 error situation to the corresponding Lean encoding.)


> Q. For each error situation that is at least partially expressible, what is the quality of feedback to the programmer?

For `... ?` variants, feedback is an `Error` value (e.g. `columnNotFound`, `duplicateColumnName`, `mismatchedSchema`, `mismatchedRowCount`, `invalidArgument`, etc.).

For proof-carrying variants, feedback is whatever Lean reports when a proof obligation cannot be satisfied; this can range from readable (simple `simp`/`native_decide`) to verbose (dependent proof goals).


> Q. For each error situation that is prevented from being constructed, what is the quality of feedback to the programmer?

Lean's type errors / unsatisfied proof obligations serve as the feedback. The quality depends on how automated the proof is.
