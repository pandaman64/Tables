module
/-
We specify the corresponding TableAPI definitions when we use a different name.
-/

public import Tables.Column
public import Tables.Row

@[expose]
public section

namespace Tables.Table

/--
Internal, dynamically-typed representation of a table.

The raw table doesn't maintain cross-column invariants.
In other words, it's possible to have two columns with the same name, or columns with mismatching row counts.

On the other hand, within each column, the values are guaranteed to be of the same data type.
When manipulating a raw table, we take the minimal amount of proofs needed to maintain the within-column invariants.
-/
structure Raw where
  columns : Array Column
  nrows : Nat

namespace Raw

instance : Inhabited Raw :=
  ⟨{ columns := #[], nrows := 0 }⟩

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

@[simp, grind =]
theorem empty_schema {schema : Schema} : (empty schema).schema = schema := by
  simp [Raw.schema, Raw.empty, Array.map_map, Function.comp_def]

def getRow (self : Raw) (i : Nat) (h₁ : i < self.nrows) (h₂ : ∀ column ∈ self.columns, column.size = self.nrows) : Row :=
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
theorem getRow_schema {self : Raw} (i : Nat) (h₁ : i < self.nrows) (h₂ : ∀ column ∈ self.columns, column.size = self.nrows) :
    (self.getRow i h₁ h₂).schema = self.schema := by
  simp [Raw.getRow, Raw.schema, Row.schema]

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
    let newValues := Array.ofFn fun (j : Fin rows.size) =>
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

Note: we require the schema to be provided explicitly.
-/
def ofRows (schema : Schema) (rows : Array Row) (h : ∀ row ∈ rows, row.schema = schema) : Raw :=
  (empty schema).addRows rows (by simpa using h)

def addColumn (self : Raw) (column : Column) : Raw :=
  { columns := self.columns.push column, nrows := self.nrows }

/--
TableAPI: buildColumn

Note: we require the data type in addition to the column name.
-/
def buildColumn (self : Raw) (name : String) (dataType : DataType) (f : Row → dataType.toType) (h : ∀ column ∈ self.columns, column.size = self.nrows) : Raw :=
  let values := Array.ofFn fun (i : Fin self.nrows) =>
    let row := self.getRow i i.isLt h
    f row
  self.addColumn { name, dataType, values }

/--
TableAPI: selectRows (overloading 1/2)
-/
def selectRows (self : Raw) (ns : Array (Fin self.nrows)) (h : ∀ column ∈ self.columns, column.size = self.nrows) : Raw :=
  let rows := ns.map fun i => self.getRow i.val i.isLt h
  have h (row : Row) (mem : row ∈ rows) : row.schema = self.schema := by
    simp only [Array.mem_map, rows] at mem
    obtain ⟨i, _, eq⟩ := mem
    exact eq ▸ getRow_schema i i.isLt h
  ofRows self.schema rows h

/--
TableAPI: selectRows (overloading 2/2)
-/
def selectRowsByMask (self : Raw) (mask : Vector Bool self.nrows) (h : ∀ column ∈ self.columns, column.size = self.nrows) : Raw :=
  let ns := (Array.range self.nrows).attach.filterMap fun i =>
    have isLt : Subtype.val i < self.nrows := by grind
    if mask[i.val] then
      some ⟨i.val, isLt⟩
    else
      none
  self.selectRows ns h

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
  let columns := (Array.range self.ncols).attach.filterMap fun i =>
    have isLt : Subtype.val i < self.ncols := by grind
    if mask[i.val] then
      some (self.getColumn i.val isLt)
    else
      none
  { columns, nrows := self.nrows }

/--
TableAPI: selectColumns (overloading 3/3)
-/
def selectColumnsByName (self : Raw) (names : Array String) (h : ∀ name ∈ names, self.hasColumn name) : Raw :=
  let columns := names.attach.map fun name => self.getColumnByName name.val (h name.val name.property)
  { columns, nrows := self.nrows }

def tfilter (self : Raw) (p : Row → Bool) (h : ∀ column ∈ self.columns, column.size = self.nrows) : Raw :=
  let rows := (Array.range self.nrows).attach.filterMap fun i =>
    have isLt : Subtype.val i < self.nrows := by grind
    let row := self.getRow i isLt h
    if p row then
      some row
    else
      none
  have h (row : Row) (mem : row ∈ rows) : row.schema = self.schema := by
    unfold rows at mem
    rw [Array.mem_filterMap] at mem
    simp only [Array.mem_attach, Option.ite_none_right_eq_some, Option.some.injEq, true_and,
      Subtype.exists, Array.mem_range] at mem
    obtain ⟨i, hi, _, eq⟩ := mem
    exact eq ▸ getRow_schema i hi h
  ofRows self.schema rows h

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

end Raw

end Tables.Table

end
