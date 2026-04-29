module

public import Tables.Schema

@[expose]
public section

namespace Tables

inductive Error where
  | columnNotFound (name : String)
  | duplicateColumnName (name : String)
  | mismatchedRowCount (expected : Nat) (actual : Nat)
  | mismatchedSchema (expected : Schema) (actual : Schema)
  | overlappingColumnName (name : String)
  | schemaNotWellFormed
deriving Repr, DecidableEq

end Tables

end
