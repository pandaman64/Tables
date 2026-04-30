module

public import Tables.Table.Basic
import Tables.Table.BasicLemmas
public import Std.Data.HashMap

open Std (HashMap)

public section

namespace Tables.Table

/--
A partial version of `groupBy` with a proof the rows come from `self`.
-/
def pgroupBy {α β} [BEq α] [Hashable α] (self : Table)
    (key : (i : Nat) → (isLt : i < self.nrows) → (row : Row) → row = self.getRow i isLt → α)
    (project : (i : Nat) → (isLt : i < self.nrows) → (row : Row) → row = self.getRow i isLt → β) :
    HashMap α (Array β) :=
  Nat.fold (init := ∅) self.nrows fun i isLt groups =>
    let row := self.getRow i isLt
    let key := key i isLt row rfl
    let project := project i isLt row rfl
    groups.alter key fun
      | some vs => some (vs.push project)
      | none => some #[project]

/--
TableAPI: groupBy

Note: we return a HashMap instead of a Table because it's more generic and useful for other operations.
A table can be constructed via `ofRows?` afterwards.
-/
def groupBy {α β} [BEq α] [Hashable α] (self : Table)
    (key : Row → α)
    (project : Row → β) :
    HashMap α (Array β) :=
  self.pgroupBy (fun _ _ row _ => key row) (fun _ _ row _ => project row)

-- TODO: `groupByRetentive` and `groupBySubtractive` are not implemented because we don't handle nested tables yet.

structure Aggregation where
  outColumn : String
  inColumn : String
  aggregate : (dt : DataType) → Array (Option dt.toType) → Except Error ((dt' : DataType) × Option (dt'.toType))

namespace Aggregation

/--
An aggregation specification with a function to aggregate values of a certain data type.

If the input table has a column with a different data type, the aggregation will throw an error.
-/
def ofFn {α β} [DataType.OfType α] [DataType.OfType β] (outColumn inColumn : String) (aggregate : Array (Option α) → Option β) : Aggregation :=
  let aggregate (dt : DataType) (values : Array (Option dt.toType)) : Except Error ((dt' : DataType) × Option (dt'.toType)) := do
    if h : dt = DataType.OfType.dataType α then
      have eqType : dt.toType = α := by simp [h, DataType.OfType.eq α]
      let outValue := aggregate (eqType ▸ values)
      .ok ⟨DataType.OfType.dataType β, DataType.OfType.eq β ▸ outValue⟩
    else
      .error (Error.dataTypeNotSupported dt)
  { outColumn, inColumn, aggregate }

end Aggregation

def pivotTable? (self : Table) (names : Array String) (aggs : Array Aggregation) : Except Error Table := do
  let groups:= self.groupBy (fun row => row.filter (fun cell => cell.name ∈ names)) id

  let rows ← groups.foldM (init := #[]) fun result keyRow rows => do
    let row ← aggs.foldlM (init := keyRow) fun row agg => do
      let some dt := self.schema.getDataTypeByName agg.inColumn
        | throw (Error.columnNotFound agg.inColumn)
      let values : Array (Option dt.toType) ← rows.mapM fun row => do
        if h : row.hasNameAndDataType agg.inColumn dt then
          return row.getValueByNameAndDataType agg.inColumn dt h
        else
          throw (Error.columnNotFound agg.inColumn)
      let ⟨dt', outValue⟩ ← agg.aggregate dt values
      return row.pushCell { name := agg.outColumn, dataType := dt', value := outValue }
    return result.push row

  ofRows? rows

end Tables.Table
