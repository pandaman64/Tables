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

def fillna (self : Column) (replacement : self.dataType.toType) : Column :=
  {
    name := self.name,
    dataType := self.dataType,
    values := self.values.map fun
      | some value => some value
      | none => some replacement,
  }

end Column

end Tables

end
