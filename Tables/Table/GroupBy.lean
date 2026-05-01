module

public import Tables.Table.Basic
import Tables.Table.BasicLemmas
public import Std.Data.HashMap
import Std.Data.HashSet

open Std (HashMap HashSet Iter)

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

def pivotLonger? (self : Table) (names : Array String) (c₁ c₂ : String) : Except Error Table := do
  if hsize : names.size = 0 then
    throw (.invalidArgument "pivotLonger: `names` must be non-empty")
  else
    -- Check `names` has no duplicates.
    let mut seen : HashSet String := ∅
    for name in names do
      if seen.contains name then
        throw (.duplicateColumnName name)
      else
        seen := seen.insert name

    -- Check columns exist and have a single common data type.
    let some dt₀ := self.schema.getDataTypeByName names[0]
      | throw (.columnNotFound names[0])
    for name in names do
      let some dt := self.schema.getDataTypeByName name
        | throw (.columnNotFound name)
      if dt ≠ dt₀ then
        throw <| .invalidArgument s!"pivotLonger: all `names` columns must have the same datatype (mismatch at {name})"

    -- Check new columns don't overlap remaining columns.
    let remainingHeader := self.header.filter (fun h => h ∉ names)
    if c₁ = c₂ then
      throw <| .duplicateColumnName c₁
    if remainingHeader.any (· = c₁) then
      throw <| .overlappingColumnName c₁
    if remainingHeader.any (· = c₂) then
      throw <| .overlappingColumnName c₂

    self.selectMany?
      (fun row _ _ =>
        names.map fun name =>
          (name, row.getValueByNameAndDataType! name dt₀))
      (fun row (name, value) =>
        row.selectNotByNames names
          |>.pushCell { name := c₁, dataType := .string, value := some name }
          |>.pushCell { name := c₂, dataType := dt₀, value := value })

def pivotWider? (self : Table) (c₁ c₂ : String) : Except Error Table := do
  if h₁ : self.hasColumn c₁ then
    if h₂ : self.hasColumn c₂ then
      let col₁ := self[c₁]
      if hdt₁ : col₁.dataType = .string then
        have h : col₁.dataType.toType = String := by
          simp [hdt₁]
        let newColumnNames := collectNewColumnNames (h ▸ col₁.values)

        let dt₂ := self[c₂].dataType
        let groups : HashMap Row (Array (Option String × Option dt₂.toType)) := self.groupBy
          (fun row => row.filter (fun cell => cell.name ≠ c₁ ∧ cell.name ≠ c₂))
          -- Ideally, we should propagate the schema so this can be provably safe.
          (fun row => (row.getValueByNameAndDataType! c₁ .string, row.getValueByNameAndDataType! c₂ dt₂))
        let groups' : HashMap Row (HashMap String (Option dt₂.toType)) :=
          groups.map fun _ values => values.foldl (init := ∅) fun map (k, v) =>
            match k with
            | some k => map.insertIfNew k v -- Select the first occurrence of each key.
            | none => map

        let rows : Array Row := Iter.toArray <| groups'.iter.map fun (row, kv) =>
          newColumnNames.foldl (init := row) fun row k =>
            row.pushCell { name := k, dataType := dt₂, value := kv[k]?.getD none }

        ofRows? rows
      else
        throw (Error.dataTypeNotSupported col₁.dataType)
    else
      throw (Error.columnNotFound c₂)
  else
    throw (Error.columnNotFound c₁)
where
  collectNewColumnNames (names : Array (Option String)) : Array String := Id.run do
    let mut result : Array String := #[]
    let mut seen : HashSet String := ∅
    for name in names do
      match name with
      | some name =>
        if !seen.contains name then
          result := result.push name
          seen := seen.insert name
      | none => continue
    result

end Tables.Table
