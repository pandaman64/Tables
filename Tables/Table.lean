module

public import Tables.Column

@[expose]
public section

namespace Tables

structure Table where
  columns : Array Column
  nrows : Nat
  wf : ∀ col ∈ columns, col.size = nrows

namespace Table

instance : Inhabited Table :=
  ⟨{ columns := #[], nrows := 0, wf := nofun }⟩

def ncols (self : Table) : Nat :=
  self.columns.size

end Table

end Tables

end
