module
/-
We specify the corresponding TableAPI definitions when we use a different name.
-/

public import Tables.Error
public import Tables.Column
public import Tables.Row
public import Tables.Data.Array.Pairwise
import Std.Data.HashMap

open Std (HashMap)

public section

namespace Tables.Table

/--
Internal, dynamically-typed representation of a table.

The raw table doesn't maintain cross-column invariants.
In other words, it's possible to have two columns with the same name, or columns with mismatching row counts.

On the other hand, within each column, the values are guaranteed to be of the same data type.
When manipulating a raw table, we take the minimal amount of proofs needed to maintain the within-column invariants.
-/
@[ext]
structure Raw where
  columns : Array Column
  nrows : Nat
deriving DecidableEq, Hashable

namespace Raw

def WfColumnSize (self : Raw) : Prop :=
  ∀ column ∈ self.columns, column.size = self.nrows

instance {self : Raw} : Decidable (WfColumnSize self) :=
  inferInstanceAs (Decidable (∀ column ∈ self.columns, column.size = self.nrows))

def ncols (self : Raw) : Nat :=
  self.columns.size

def header (self : Raw) : Array String :=
  self.columns.map (·.name)

def schema (self : Raw) : Schema :=
  { specs := self.columns.map fun column => (column.name, column.dataType) }

@[simp, grind =]
theorem schema_size_eq {self : Raw} : self.schema.size = self.ncols := by
  simp [Raw.schema, Schema.size, Raw.ncols]

/--
TableAPI: emptyTable

Note: we require the schema to be provided explicitly.
-/
def empty (schema : Schema) : Raw :=
  {
    columns := schema.specs.map fun (name, dataType) => { name, dataType, values := #[] },
    nrows := 0,
  }

instance : Inhabited Raw := ⟨.empty default⟩

@[simp, grind =]
theorem empty_schema {schema : Schema} : (empty schema).schema = schema := by
  simp [Raw.schema, Raw.empty, Array.map_map, Function.comp_def]

def ofColumns (columns : Array Column) : Raw :=
  if h : columns.size > 0 then
    { columns, nrows := columns[0].size }
  else
    default

def getRow (self : Raw) (i : Nat) (h₁ : i < self.nrows) (h₂ : self.WfColumnSize) : Row :=
  let cells := self.columns.attach.map fun column =>
    {
      name := column.val.name,
      dataType := column.val.dataType,
      value := column.val.get i ((h₂ column.val column.property) ▸ h₁),
    }
  { cells }

def getRow? (self : Raw) (i : Nat) : Option Row := do
  let cells ← self.columns.mapM fun column => do
    pure { name := column.name, dataType := column.dataType, value := ←column.values[i]? }
  pure { cells }

@[simp, grind =]
theorem getRow_schema {self : Raw} (i : Nat) (h₁ : i < self.nrows) (h₂ : self.WfColumnSize) :
    (self.getRow i h₁ h₂).schema = self.schema := by
  simp [Raw.getRow, Raw.schema, Row.schema]

@[simp, grind =]
theorem getRow_size {self : Raw} (i : Nat) (h₁ : i < self.nrows) (h₂ : self.WfColumnSize) :
    (self.getRow i h₁ h₂).size = self.ncols := by
  simp [Raw.getRow, Raw.ncols, Row.size]

def getColumn (self : Raw) (i : Nat) (h : i < self.ncols := by get_elem_tactic) : Column :=
  self.columns[i]

def getColumn? (self : Raw) (i : Nat) : Option Column :=
  self.columns[i]?

@[simp, grind =]
theorem schema_getName_eq_getColumn_name {self : Raw} (i : Nat) (h : i < self.ncols) :
    self.schema.getName i (self.schema_size_eq ▸ h) = (self.getColumn i h).name := by
  grind [Raw.schema, Raw.getColumn, Schema.getName]

@[simp, grind =]
theorem schema_getDataType_eq_getColumn_dataType {self : Raw} (i : Nat) (h : i < self.ncols) :
    self.schema.getDataType i (self.schema_size_eq ▸ h) = (self.getColumn i h).dataType := by
  grind [Raw.schema, Raw.getColumn, Schema.getDataType]

def hasColumn (self : Raw) (name : String) : Bool :=
  self.columns.any (·.name = name)

theorem hasColumn_iff_mem_schema_specs (self : Raw) (name : String) :
    self.hasColumn name ↔ ∃ dataType, (name, dataType) ∈ self.schema.specs := by
  simp only [hasColumn, Array.any_eq_true, decide_eq_true_eq, schema, Array.mem_iff_getElem,
    Array.getElem_map, Prod.mk.injEq, Array.size_map]
  grind

def findColumnIdx? (self : Raw) (name : String) : Option Nat :=
  self.columns.findIdx? (·.name = name)

def findColumnIdx (self : Raw) (name : String) (h : self.hasColumn name) : Nat :=
  have isSome : (self.findColumnIdx? name).isSome := by
    rw [findColumnIdx?, Array.findIdx?_isSome]
    exact h
  (self.findColumnIdx? name).get isSome

theorem findColumnIdx_lt {self : Raw} (name : String) (h : self.hasColumn name) :
    self.findColumnIdx name h < self.ncols := by
  show self.findColumnIdx name h < self.columns.size
  simp only [findColumnIdx, findColumnIdx?]
  match h' : self.columns.findIdx? (·.name = name) with
  | some i => simpa [h'] using (Array.findIdx?_eq_some_iff_findIdx_eq.mp h').1
  | none => grind

/--
TableAPI: getColumn (overloading 2/2)
-/
def getColumnByName? (self : Raw) (name : String) : Option Column :=
  self.columns.find? (·.name = name)

/--
TableAPI: getColumn (overloading 2/2)
-/
def getColumnByName (self : Raw) (name : String) (h : self.hasColumn name) : Column :=
  have isSome : (self.columns.find? (·.name = name)).isSome := by
    grind [hasColumn]
  (self.getColumnByName? name).get isSome

/--
TableAPI: selectColumns (overloading 2/3)
-/
def selectColumns (self : Raw) (ns : Array (Fin self.ncols)) : Raw :=
  let columns := ns.map fun i => self.getColumn i.val i.isLt
  { columns, nrows := self.nrows }

/--
TableAPI: selectColumns (overloading 1/3)
-/
def selectColumnsByMask (self : Raw) (mask : Vector Bool self.ncols) : Raw :=
  let ns := (Array.finRange self.ncols).filter fun i => mask[i.val]
  self.selectColumns ns

/--
TableAPI: selectColumns (overloading 3/3)
-/
def selectColumnsByName (self : Raw) (names : Array String) (h : ∀ name ∈ names, self.hasColumn name) : Raw :=
  let columns := names.attach.map fun name => self.getColumnByName name.val (h name.val name.property)
  { columns, nrows := self.nrows }

/--
TableAPI: head

Note: we don't support negative `n` for now. We can consider taking a range instead.
-/
def take (self : Raw) (n : Nat) : Raw :=
  {
    columns := self.columns.map (·.take n),
    nrows := n,
  }

def addRow (self : Raw) (row : Row) (h : row.schema = self.schema) : Raw :=
  let nrows := self.nrows + 1
  let columns := Array.ofFn fun (i : Fin self.ncols) =>
    let column := self.getColumn i
    have isLt : i < row.size := by simp [←row.schema_size_eq_size, h, schema_size_eq]
    have eqDataType : row.getDataType i = column.dataType := by
      rw [←row.schema_getDataType_eq_getDataType]
      simp [h, schema_getDataType_eq_getColumn_dataType, column]
    column.push (eqDataType ▸ row.getValue i isLt)
  { columns, nrows }

def addRows (self : Raw) (rows : Array Row) (h : ∀ row ∈ rows, row.schema = self.schema) : Raw :=
  let nrows := self.nrows + rows.size
  let columns := Array.ofFn fun (i : Fin self.ncols) =>
    let column := self.getColumn i
    let newValues : Array (Option column.dataType.toType) := Array.ofFn fun (j : Fin rows.size) =>
      let row := rows[j]
      have h : row.schema = self.schema := h row (by grind)
      have isLt : i < row.size := by simp [←row.schema_size_eq_size, h, schema_size_eq]
      have eqDataType : row.getDataType i = column.dataType := by
        rw [←row.schema_getDataType_eq_getDataType]
        simp [h, schema_getDataType_eq_getColumn_dataType, column]
      eqDataType ▸ row.getValue i
    { name := column.name, dataType := column.dataType, values := column.values ++ newValues }
  { columns, nrows }

/--
TableAPI: values
-/
def ofRows (schema : Schema) (rows : Array Row) (h : ∀ row ∈ rows, row.schema = schema) : Raw :=
  (empty schema).addRows rows (by simpa using h)

def addColumn (self : Raw) (column : Column) : Raw :=
  { columns := self.columns.push column, nrows := self.nrows }

def buildColumn {α} [DataType.OfType α] (self : Raw) (name : String) (f : Row → Option α) (h : self.WfColumnSize) : Raw :=
  let values := Array.ofFn fun (i : Fin self.nrows) =>
    let row := self.getRow i i.isLt h
    f row
  self.addColumn (Column.ofRawValues name values)

def replaceColumn (self : Raw) (column : Column) : Raw :=
  let columns := self.columns.map fun col =>
    if col.name = column.name then
      column
    else
      col
  { columns, nrows := self.nrows }

def transformColumn {α} [DataType.OfType α] (self : Raw) (name : String) (h : self.hasColumn name)
    (f : Option ((self.getColumnByName name h).dataType.toType) → Option α) : Raw :=
  let newColumn := (self.getColumnByName name h).mapValues f
  self.replaceColumn newColumn

/--
TableAPI: selectRows (overloading 1/2)
-/
def selectRows (self : Raw) (ns : Array (Fin self.nrows)) (h : self.WfColumnSize) : Raw :=
  let rows := ns.map fun i => self.getRow i.val i.isLt h
  have h (row : Row) (mem : row ∈ rows) : row.schema = self.schema := by
    simp only [Array.mem_map, rows] at mem
    obtain ⟨i, _, eq⟩ := mem
    exact eq ▸ getRow_schema i i.isLt h
  ofRows self.schema rows h

/--
TableAPI: selectRows (overloading 2/2)
-/
def selectRowsByMask (self : Raw) (mask : Vector Bool self.nrows) (h : self.WfColumnSize) : Raw :=
  let ns := (Array.range self.nrows).attach.filterMap fun i =>
    have isLt : Subtype.val i < self.nrows := by grind
    if mask[i.val] then
      some ⟨i.val, isLt⟩
    else
      none
  self.selectRows ns h

def tfilter (self : Raw) (p : Row → Bool) (h : self.WfColumnSize) : Raw :=
  let rows : Array { row : Row // row.schema = self.schema } := Nat.fold (init := #[]) self.nrows fun i isLt rows =>
    let row := self.getRow i isLt h
    if p row then
      rows.push ⟨row, by simp [row, getRow_schema]⟩
    else
      rows
  have h : rows.Pairwise (fun x y => x.val.schema = y.val.schema) := by
    grind [Array.pairwise_iff_getElem]
  ofRows self.schema rows.unattach (by grind [Array.mem_unattach])

def dropColumn (self : Raw) (name : String) : Raw :=
  let columns := self.columns.filter fun column => column.name ≠ name
  { columns, nrows := self.nrows }

def dropColumns (self : Raw) (names : Array String) : Raw :=
  let columns := self.columns.filter fun column => column.name ∉ names
  { columns, nrows := self.nrows }

def vcat (self : Raw) (other : Raw) (h : self.schema = other.schema) : Raw :=
  let nrows := self.nrows + other.nrows
  let columns := Array.ofFn fun (i : Fin self.ncols) =>
    have eqNcols : self.ncols = other.ncols := by
      rw [←schema_size_eq, ←schema_size_eq, h]
    have otherIsLt : i < other.ncols := eqNcols ▸ i.isLt

    let column := self.getColumn i
    let otherColumn := other.getColumn i
    have eqName : column.name = otherColumn.name := by
      unfold column otherColumn
      rw [←schema_getName_eq_getColumn_name, ←schema_getName_eq_getColumn_name]
      simp [h]
    have eqDataType : column.dataType = otherColumn.dataType := by
      unfold column otherColumn
      rw [←schema_getDataType_eq_getColumn_dataType, ←schema_getDataType_eq_getColumn_dataType]
      simp [h]
    column.concat otherColumn eqName eqDataType
  { columns, nrows }

def hcat (self : Raw) (other : Raw) : Raw :=
  { columns := self.columns ++ other.columns, nrows := self.nrows }

def renameColumn (self : Raw) (oldName newName : String) : Raw :=
  let nrows := self.nrows
  let columns := self.columns.map fun column =>
    if column.name = oldName then
      { column with name := newName }
    else
      column
  { columns, nrows }

def renameColumns (self : Raw) (renames : Array (String × String)) : Raw :=
  renames.foldl (init := self) fun table (oldName, newName) => table.renameColumn oldName newName

/--
TableAPI: select

Note: it requires an explicit schema, but the API feels too verbose. Maybe we need a typed Row type.
-/
def select (self : Raw) (schema : Schema) (f : Row → (n : Nat) → n < self.nrows → Row)
    (h₁ : ∀ row n h, (f row n h).schema = schema) (h₂ : self.WfColumnSize) : Raw :=
  let rows : Array { row : Row // row.schema = schema } := Array.ofFn fun (i : Fin self.nrows) =>
    let row := self.getRow i.val i.isLt h₂
    ⟨f row i.val i.isLt, h₁ row i.val i.isLt⟩
  ofRows schema rows.unattach (by grind [Array.mem_unattach])

def completeCases (self : Raw) (column : String) (h : self.hasColumn column) : Array Bool :=
  let column := self.getColumnByName column h
  column.values.map fun
    | some _ => true
    | none => false

def dropna (self : Raw) (h : self.WfColumnSize) : Raw :=
  self.tfilter (fun row => row.cells.all (·.value.isSome)) h

def fillna (self : Raw) (column : String) (h₁ : self.hasColumn column) (replacement : (self.getColumnByName column h₁).dataType.toType) : Raw :=
  let column := self.getColumnByName column h₁
  let newColumn := column.fillna replacement
  self.replaceColumn newColumn

def count (self : Raw) (column : String) (h : self.hasColumn column) : Raw :=
  let column := self.getColumnByName column h
  let countMap : HashMap (Option column.dataType.toType) Nat := column.values.foldl (init := ∅) fun map value =>
    map.alter value fun
      | some count => some (count + 1)
      | none => some 1
  let values := countMap.keysArray
  let counts := countMap.valuesArray
  Raw.ofColumns #[
    { name := "value", dataType := column.dataType, values := values },
    { name := "count", dataType := DataType.nat, values := counts.map some },
  ]

def find (self : Raw) (r : Row) (h : self.WfColumnSize) : Option Nat := Id.run do
  for hi : i in 0 ...< self.nrows do
    let row := self.getRow i (Std.Rco.lt_upper_of_mem hi) h
    if row = r then
      return some i
  none

def bin? (self : Raw) (column : String) (n : Nat) : Except Error Raw := do
  if n = 0 then
    throw (.invalidArgument "n must be positive")
  else
    let some column := self.getColumnByName? column
      | throw (.columnNotFound column)
    match h : column.dataType with
    | .nat =>
      have eqType : column.dataType.toType = Nat := by simp [h]
      let values : Array Nat := column.values.filterMap fun v => eqType ▸ v
      if h : values.isEmpty then
        throw (.emptyColumn column.name)
      else
        let min := values.min (by grind)
        let max := values.max (by grind)
        let start := min / n * n
        let numGroups := (max - start) / n + 1
        let map : HashMap Nat Nat := values.foldl (init := ∅) fun map value =>
          let key := (value - start) / n
          map.alter key fun
            | some count => some (count + 1)
            | none => some 1
        let values := map.keysArray
        let counts := map.valuesArray
        pure (Raw.ofColumns #[
          { name := "group", dataType := DataType.string, values := values.map fun i => s!"{start + i * n} <= {column.name} < {start + (i + 1) * n}" },
          { name := "count", dataType := DataType.nat, values := counts.map some },
        ])
    | _ => throw (.dataTypeNotSupported column.dataType)

def toString (self : Raw) : String := Id.run do
  let columns := self.columns.map fun column =>
    #[column.name] ++ column.values.map fun
      | some value => DataType.toString column.dataType value
      | none => "null"
  let widths := columns.map fun strs => strs.map (·.length) |>.max? |>.getD 0

  let mut result := printRow columns widths 0 ++ "\n" ++ printSeparatorRow widths ++ "\n"

  for i in [1:self.nrows + 1] do
    result := result ++ printRow columns widths i ++ "\n"
  result
where
  printRow (columns : Array (Array String)) (widths : Array Nat) (i : Nat) : String := Id.run do
    let mut line := "|"
    for j in [0:columns.size] do
      let value := columns[j]![i]!
      let width := widths[j]!
      line := line ++ rightPad value " " width ++ "|"
    line
  printSeparatorRow (widths : Array Nat) : String := Id.run do
    let mut line := "|"
    for j in [0:widths.size] do
      let width := widths[j]!
      line := line ++ repeatStr "-" width ++ "|"
    line
  repeatStr (str : String) (n : Nat) : String :=
    String.join (List.replicate n str)
  rightPad (str : String) (pad : String) (n : Nat) : String :=
    str ++ repeatStr pad (n - str.length)

def toFormat (self : Raw) : Std.Format := self.toString.toFormat

def WfColumnNames (self : Raw) : Prop :=
  ∀ (i j : Fin self.ncols), i < j → (self.getColumn i).name ≠ (self.getColumn j).name

end Raw

end Tables.Table

end
