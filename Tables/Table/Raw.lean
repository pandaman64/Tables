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

/-
TableAPI: emptyTable
-/
instance : Inhabited Raw :=
  ⟨{ columns := #[], nrows := 0 }⟩

def ncols (self : Raw) : Nat :=
  self.columns.size

def header (self : Raw) : Array String :=
  self.columns.map (·.name)

/--
TableAPI: values
-/
def ofRows (schema : Schema) (rows : Array Row) (h : ∀ i, (_ : i < rows.size) → rows[i].schema = schema) : Raw :=
  let nrows := rows.size
  let columns := Array.ofFn fun (i : Fin schema.size) =>
    let name := schema.getName i
    let dataType := schema.getDataType i
    let values := Array.ofFn fun (j : Fin rows.size) =>
      let row := rows[j]
      have h : row.schema = schema := h j j.isLt
      have isLt : i < row.size := by simpa [←h] using i.isLt
      have eqDataType : row.getDataType i = dataType := by
        rw [←row.schema_getDataType_eq_getDataType]
        simp [h, dataType]
      eqDataType ▸ row.getValue i
    { name, dataType, values }
  { columns, nrows }

def getRow (self : Raw) (i : Nat) (h : ∀ column ∈ self.columns, i < column.size) : Row :=
  let cells := self.columns.attach.map fun column =>
    { name := column.val.name, dataType := column.val.dataType, value := column.val.values[i]'(h column.val column.property) }
  { cells }

def getRow? (self : Raw) (i : Nat) : Option Row := do
  let cells ← self.columns.mapM fun column => do
    pure { name := column.name, dataType := column.dataType, value := ←column.values[i]? }
  pure { cells }

def getColumn (self : Raw) (i : Nat) (h : i < self.ncols) : Column :=
  self.columns[i]

def getColumn? (self : Raw) (i : Nat) : Option Column :=
  self.columns[i]?

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

end Raw

end Tables.Table

end
