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

def push (self : Schema) (spec : String × DataType) : Schema :=
  { specs := self.specs.push spec }

def concat (self other : Schema) : Schema :=
  { specs := self.specs ++ other.specs }

instance : Append Schema where
  append := concat

theorem append_def (self other : Schema) : self ++ other = { specs := self.specs ++ other.specs } := (rfl)

def replace (self : Schema) (name : String) (dataType : DataType) : Schema :=
  { specs := self.specs.map fun (n, d) => if n = name then (name, dataType) else (n, d) }

@[simp, grind =]
theorem replace_size (self : Schema) (name : String) (dataType : DataType) : (self.replace name dataType).size = self.size := by
  simp [replace, size]

def rename (self : Schema) (oldName newName : String) : Schema :=
  { specs := self.specs.map fun (n, d) => if n = oldName then (newName, d) else (n, d) }

@[simp, grind =]
theorem rename_size (self : Schema) (oldName newName : String) : (self.rename oldName newName).size = self.size := by
  simp [rename, size]

def filter (self : Schema) (p : String × DataType → Bool) : Schema :=
  { specs := self.specs.filter p }

def selectNotByNames (self : Schema) (names : Array String) : Schema :=
  { specs := self.specs.filter fun (name, _) => name ∉ names }

end Schema

end Tables

end
