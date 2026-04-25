module

public import Tables.Column
public import Tables.Schema
public import Tables.Error

public section

namespace Tables

-- THIS WILL BE ABANDONED SOON. WE'LL START WITH Table.Raw. NEVER LOOK AT THIS.
structure Table where
  columns : Array Column
  nrows : Nat
  wfNoDup : ∀ (i j : Fin columns.size), i ≠ j → columns[i].name ≠ columns[j].name
  wfSize : ∀ col ∈ columns, col.size = nrows

namespace Table

instance : Inhabited Table :=
  ⟨{ columns := #[], nrows := 0, wfNoDup := nofun, wfSize := nofun }⟩

@[reducible]
def ncols (self : Table) : Nat :=
  self.columns.size

def header (self : Table) : Array String :=
  self.columns.map (·.name)

def schema (self : Table) : Schema :=
  { columns := self.columns.map (fun col => (col.name, col.dataType)) }

def addColumn (self : Table) (column : Column)
    (h₁ : column.name ∉ self.header) (h₂ : column.size = self.nrows) : Table :=
  {
    columns := self.columns.push column,
    nrows := self.nrows,
    wfNoDup := by
      intro i j ne eq
      have hi : i ≤ self.ncols := by grind [i.isLt]
      have hj : j ≤ self.ncols := by grind [j.isLt]
      cases Nat.lt_or_eq_of_le hi with
      | inl hi =>
        cases Nat.lt_or_eq_of_le hj with
        | inl hj => exact self.wfNoDup ⟨i, hi⟩ ⟨j, hj⟩ (by grind) (by grind)
        | inr hj => grind [header]
      | inr hi =>
        cases Nat.lt_or_eq_of_le hj with
        | inl hj => grind [header]
        | inr hj => grind,
    wfSize := by grind [self.wfSize]
  }

def addColumn? (self : Table) (column : Column) : Except Error Table :=
  if h₁ : column.name ∉ self.header then
    if h₂ : column.size = self.nrows then
      .ok (self.addColumn column h₁ h₂)
    else
      .error (.mismatchedRowCount self.nrows column.size)
  else
    .error (.duplicateColumnName column.name)

private def vcatAux (columns₁ columns₂ : Array Column)
    (h₁ : columns₁.size = columns₂.size)
    (h₂ : ∀ i, (_ : i < columns₁.size) → columns₁[i].name = columns₂[i].name)
    (h₃ : ∀ i, (_ : i < columns₁.size) → columns₁[i].dataType = columns₂[i].dataType) : Array Column :=
  Array.ofFn fun (i : Fin columns₁.size) =>
    columns₁[i].concat columns₂[i] (h₂ i i.isLt) (h₃ i i.isLt)

section vcatAux

variable {columns₁ columns₂ : Array Column}
  {h₁ : columns₁.size = columns₂.size}
  {h₂ : ∀ i, (_ : i < columns₁.size) → columns₁[i].name = columns₂[i].name}
  {h₃ : ∀ i, (_ : i < columns₁.size) → columns₁[i].dataType = columns₂[i].dataType}

private theorem vcatAux_size : (vcatAux columns₁ columns₂ h₁ h₂ h₃).size = columns₁.size :=
  by simp [vcatAux]

-- TODO: necessary theorems

end vcatAux

def vcat (self : Table) (other : Table)
    (h : self.schema = other.schema) : Table :=
  {
    columns := vcatAux self.columns other.columns sorry sorry sorry,
    nrows := self.nrows + other.nrows,
    wfNoDup := by sorry,
    wfSize := by sorry,
  }

def vcat? (self : Table) (other : Table) : Except Error Table :=
  if h : self.schema = other.schema then
    .ok (self.vcat other h)
  else
    .error (.mismatchedSchema self.schema other.schema)

end Table

end Tables

end
