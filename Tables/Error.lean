module

@[expose]
public section

namespace Tables

inductive Error where
  | duplicateColumnName (name : String)
  | mismatchedRowCount (expected : Nat) (actual : Nat)
deriving Repr, DecidableEq

end Tables

end
