module

namespace String

public def joinSep (sep : String) (xs : Array String) : String :=
  xs.foldl (fun acc x => if acc.isEmpty then x else acc ++ sep ++ x) ""

end String

namespace Tables

public inductive DataType where
  | bool
  | nat
  | string
  | option (dt : DataType)
  | array (dt : DataType)
deriving Repr, Ord, DecidableEq

namespace DataType

@[expose, reducible]
public def toType (dt : DataType) : Type :=
  match dt with
  | bool => Bool
  | nat => Nat
  | string => String
  | option dt => Option (toType dt)
  | array dt => Array (toType dt)

public def toString (dt : DataType) (x : dt.toType) : String :=
  match dt with
  | bool => ToString.toString x
  | nat => ToString.toString x
  | string => x
  | option dt =>
    match x with
    | some x => s!"some {toString dt x}"
    | none => "none"
  | array dt => s!"#[{x.map (toString dt) |> String.joinSep ", "}]"

end DataType

end Tables
