module

public import Tables.Schema

@[expose]
public section

namespace Tables

inductive Error where
  | duplicateColumnName (name : String)
  | mismatchedRowCount (expected : Nat) (actual : Nat)
  | mismatchedSchema (expected : Schema) (actual : Schema)
deriving Repr, DecidableEq

end Tables

end
