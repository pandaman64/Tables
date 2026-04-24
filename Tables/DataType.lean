module

namespace Tables

public inductive DataType where
  | bool
  | nat
  | string
  | option (s : DataType)
  | array (s : DataType)
deriving Repr, Ord, DecidableEq

@[expose, reducible]
public def DataType.toType (s : DataType) : Type :=
  match s with
  | bool => Bool
  | nat => Nat
  | string => String
  | option s => Option (DataType.toType s)
  | array s => Array (DataType.toType s)

end Tables
