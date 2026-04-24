module

public import Tables.Column
public import Tables.Error

@[expose]
public section

namespace Tables

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

end Table

end Tables

end
