module

public import Tables.DataType

import Init.Data.Array.Lemmas

@[expose]
public section

namespace Tables

@[ext]
structure Schema where
  specs : Array (String × DataType)
deriving Repr, DecidableEq, Inhabited

namespace Schema

def ofSpecs (specs : Array (String × DataType)) : Schema :=
  { specs }

def size (self : Schema) : Nat :=
  self.specs.size

instance : GetElem Schema Nat (String × DataType) (fun s i => i < s.size) where
  getElem s i h := s.specs[i]

def getName (self : Schema) (i : Nat) (h : i < self.size := by get_elem_tactic) : String :=
  self.specs[i].1

def getDataType (self : Schema) (i : Nat) (h : i < self.size := by get_elem_tactic) : DataType :=
  self.specs[i].2

def getDataTypeByName (self : Schema) (name : String) : Option DataType :=
  self.specs.findSome? fun (n, d) => if n = name then some d else none

def header (self : Schema) : Array String :=
  self.specs.map (·.1)

def hasName (self : Schema) (name : String) : Bool :=
  self.specs.any (·.1 = name)

def Wf (self : Schema) : Prop :=
  ∀ (i j : Fin self.size), i < j → self.getName i ≠ self.getName j

instance {schema : Schema} : Decidable (Wf schema) :=
  inferInstanceAs (Decidable (∀ (i j : Fin schema.size), i < j → schema.getName i ≠ schema.getName j))

def push (self : Schema) (spec : String × DataType) : Schema :=
  ofSpecs (self.specs.push spec)

def concat (self other : Schema) : Schema :=
  ofSpecs (self.specs ++ other.specs)

instance : Append Schema where
  append := concat

def replace (self : Schema) (name : String) (dataType : DataType) : Schema :=
  ofSpecs (self.specs.map fun (n, d) => if n = name then (name, dataType) else (n, d))

def rename (self : Schema) (oldName newName : String) : Schema :=
  ofSpecs (self.specs.map fun (n, d) => if n = oldName then (newName, d) else (n, d))

def filterByName (self : Schema) (p : String → Bool) : Schema :=
  ofSpecs (self.specs.filter fun (name, _) => p name)

def selectNotByNames (self : Schema) (names : Array String) : Schema :=
  self.filterByName fun name => name ∉ names

end Schema

end Tables

end
