module

import Std.Data.HashMap

public section

namespace Tables

inductive DataType where
  | bool
  | nat
  | string
  | array (dt : DataType)
deriving Repr, DecidableEq, Hashable

namespace DataType

@[expose, reducible]
def toType (dt : DataType) : Type :=
  match dt with
  | bool => Bool
  | nat => Nat
  | string => String
  | array dt => Array (toType dt)

def toString (dt : DataType) (x : dt.toType) : String :=
  match dt with
  | bool => ToString.toString x
  | nat => ToString.toString x
  | string => x
  | array dt => s!"#[{x.map (toString dt) |>.toList |> ", ".intercalate}]"

instance {dt : DataType} : ToString dt.toType where
  toString := toString dt

def beq (dt : DataType) (x y : dt.toType) : Bool :=
  match dt with
  | bool => x == y
  | nat => x == y
  | string => x == y
  | array dt =>
    if h : x.size = y.size then
      Nat.all x.size fun i isLt => beq dt x[i] y[i]
    else
      false

theorem beq_refl {dt : DataType} {x : dt.toType} : beq dt x x := by
  induction dt with
  | bool => grind [beq]
  | nat => grind [beq]
  | string => grind [beq]
  | array dt ih => grind [beq]

theorem eq_of_beq {dt : DataType} {x y : dt.toType} (h : beq dt x y) : x = y := by
  induction dt with
  | bool => grind [beq]
  | nat => grind [beq]
  | string => grind [beq]
  | array dt ih =>
    simp only [beq] at h
    split at h
    next h' =>
      simp only [Nat.all_eq_finRange_all, List.all_eq_true, List.mem_finRange, forall_const] at h
      refine Array.ext h' fun i hi₁ hi₂ => ?_
      exact ih (h ⟨i, hi₁⟩)
    next => contradiction

instance {dt : DataType} : BEq dt.toType where
  beq := beq dt

instance {dt : DataType} : LawfulBEq dt.toType where
  rfl := beq_refl
  eq_of_beq := eq_of_beq

instance {dt : DataType} : DecidableEq dt.toType :=
  instDecidableEqOfLawfulBEq

def hash (dt : DataType) (x : dt.toType) : UInt64 :=
  match dt with
  | bool => Hashable.hash x
  | nat => Hashable.hash x
  | string => Hashable.hash x
  | array dt =>
    -- Taken from Init.Data
    x.foldl (fun r a => mixHash r (hash dt a)) 7

instance {dt : DataType} : Hashable dt.toType where
  hash := hash dt

class OfType (α : Type) where
  dataType (α) : DataType
  eq (α) : α = dataType.toType

instance : OfType Bool where
  dataType := DataType.bool
  eq := rfl

instance : OfType Nat where
  dataType := DataType.nat
  eq := rfl

instance : OfType String where
  dataType := DataType.string
  eq := rfl

instance {α} [OfType α] : OfType (Array α) where
  dataType := DataType.array (OfType.dataType α)
  eq := by simp [OfType.eq α]

end DataType

end Tables

end
