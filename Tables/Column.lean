module

public import Tables.DataType

@[expose]
public section

namespace Tables

/-
Explore later. Maybe something like this is better

```lean4
inductive Column' where
  | bool (name : String) (values : Array Bool)
  | nat (name : String) (values : Array Nat)
  | string (name : String) (values : Array String)
  -- Think about what to do with option/array
  | table (name : String) (values : Array (Array Column'))

-- then give dataType/values post-hoc
def Column'.dataType (self : Column') : DataType :=
  match self with
  | bool _ _ => DataType.bool
  | nat _ _ => DataType.nat
  | string _ _ => DataType.string
  | table _ _ => sorry

def Column'.values (self : Column') : Array self.dataType.toType :=
  match self with
  | bool _ values => values
  | nat _ values => values
  | string _ values => values
  | table _ values => sorry
```
-/

/--
A column is a named collection of values of a given data type.
-/
structure Column where
  name : String
  dataType : DataType
  values : Array (Option dataType.toType)
deriving DecidableEq, Hashable

namespace Column

def toString (self : Column) : String :=
  let values := self.values.map fun
    | some value => self.dataType.toString value
    | none => "null"
  s!"{self.name}: #[{", ".intercalate values.toList}]"

def spec (self : Column) : String × DataType :=
  (self.name, self.dataType)

def size (self : Column) : Nat :=
  self.values.size

def get (self : Column) (i : Nat) (h : i < self.size) : Option self.dataType.toType :=
  self.values[i]

def push (self : Column) (value : Option self.dataType.toType) : Column :=
  {
    name := self.name,
    dataType := self.dataType,
    values := self.values.push value,
  }

def pushValue (self : Column) (value : self.dataType.toType) : Column :=
  self.push (some value)

def pushNull (self : Column) : Column :=
  self.push none

def concat (self : Column) (other : Column)
    (_h₁ : self.name = other.name) (h₂ : self.dataType = other.dataType) : Column :=
  {
    name := self.name,
    dataType := self.dataType,
    values := self.values ++ h₂ ▸ other.values,
  }

def take (self : Column) (n : Nat) : Column :=
  {
    name := self.name,
    dataType := self.dataType,
    values := self.values.take n,
  }

@[simp, grind =]
theorem take_name (self : Column) (n : Nat) : (self.take n).name = self.name := by
  simp [take]

@[simp, grind =]
theorem take_dataType (self : Column) (n : Nat) : (self.take n).dataType = self.dataType := by
  simp [take]

@[simp, grind =]
theorem take_spec (self : Column) (n : Nat) : (self.take n).spec = self.spec := by
  simp [spec]

@[simp, grind =]
theorem push_name (self : Column) (v : Option self.dataType.toType) : (self.push v).name = self.name := by
  simp [push]

@[simp, grind =]
theorem push_dataType (self : Column) (v : Option self.dataType.toType) : (self.push v).dataType = self.dataType := by
  simp [push]

@[simp, grind =]
theorem push_spec (self : Column) (v : Option self.dataType.toType) : (self.push v).spec = self.spec := by
  simp [spec]

@[simp, grind =]
theorem push_size (self : Column) (v : Option self.dataType.toType) : (self.push v).size = self.size + 1 := by
  simp [push, size]

@[simp, grind =]
theorem concat_name (self other : Column) (h₁ : self.name = other.name) (h₂ : self.dataType = other.dataType) :
    (self.concat other h₁ h₂).name = self.name := by
  simp [concat]

@[simp, grind =]
theorem concat_dataType (self other : Column) (h₁ : self.name = other.name) (h₂ : self.dataType = other.dataType) :
    (self.concat other h₁ h₂).dataType = self.dataType := by
  simp [concat]

@[simp, grind =]
theorem concat_spec (self other : Column) (h₁ : self.name = other.name) (h₂ : self.dataType = other.dataType) :
    (self.concat other h₁ h₂).spec = self.spec := by
  simp [spec]

def ofRawValues {α} [DataType.OfType α] (name : String) (values : Array (Option α)) : Column :=
  {
    name := name,
    dataType := DataType.OfType.dataType α,
    values := DataType.OfType.eq α ▸ values,
  }

@[simp, grind =]
theorem ofRawValues_size {α} [DataType.OfType α] (name : String) (values : Array (Option α)) :
    (ofRawValues name values).size = values.size := by
  grind only [ofRawValues, size]

def ofValues {α} [DataType.OfType α] (name : String) (values : Array α) : Column :=
  ofRawValues name (values.map some)

@[simp, grind =]
theorem ofValues_size {α} [DataType.OfType α] (name : String) (values : Array α) :
    (ofValues name values).size = values.size := by
  simp [ofValues]

def mapValues {α} [DataType.OfType α] (self : Column) (f : Option self.dataType.toType → Option α) : Column :=
  {
    name := self.name,
    dataType := DataType.OfType.dataType α,
    values := DataType.OfType.eq α ▸ self.values.map f,
  }

@[simp, grind =]
theorem mapValues_name {α} [DataType.OfType α] (self : Column) (f : Option self.dataType.toType → Option α) :
    (self.mapValues f).name = self.name := by
  simp [mapValues]

@[simp, grind =]
theorem mapValues_dataType {α} [DataType.OfType α] (self : Column) (f : Option self.dataType.toType → Option α) :
    (self.mapValues f).dataType = DataType.OfType.dataType α := by
  simp [mapValues]

@[simp, grind =]
theorem mapValues_spec {α} [DataType.OfType α] (self : Column) (f : Option self.dataType.toType → Option α) :
    (self.mapValues f).spec = (self.name, DataType.OfType.dataType α) := by
  simp [spec]

def fillna (self : Column) (replacement : self.dataType.toType) : Column :=
  {
    name := self.name,
    dataType := self.dataType,
    values := self.values.map fun
      | some value => some value
      | none => some replacement,
  }

@[simp, grind =]
theorem fillna_name (self : Column) (r : self.dataType.toType) : (self.fillna r).name = self.name := by
  simp [fillna]

@[simp, grind =]
theorem fillna_dataType (self : Column) (r : self.dataType.toType) : (self.fillna r).dataType = self.dataType := by
  simp [fillna]

@[simp, grind =]
theorem fillna_spec (self : Column) (r : self.dataType.toType) : (self.fillna r).spec = self.spec := by
  simp [fillna, spec]

end Column

end Tables

end
