module

public import Tables.DataType

@[expose]
public section

namespace Tables

@[ext]
structure Schema where
  specs : Array (String × DataType)
deriving Repr, DecidableEq, Inhabited

namespace Schema

def size (self : Schema) : Nat :=
  self.specs.size

instance : GetElem Schema Nat (String × DataType) (fun s i => i < s.size) where
  getElem s i h := s.specs[i]

def getName (self : Schema) (i : Nat) (h : i < self.size := by get_elem_tactic) : String :=
  self.specs[i].1

def getDataType (self : Schema) (i : Nat) (h : i < self.size := by get_elem_tactic) : DataType :=
  self.specs[i].2

end Schema

end Tables

end
