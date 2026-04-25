module

public import Tables.Column

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

end Raw

end Tables.Table

end
