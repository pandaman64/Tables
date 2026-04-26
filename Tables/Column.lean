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
  values : Array dataType.toType
deriving DecidableEq, Hashable

namespace Column

def toString (self : Column) : String :=
  s!"{self.name}: #[{self.values.map (DataType.toString self.dataType) |>.toList |> ", ".intercalate}]"

def size (self : Column) : Nat :=
  self.values.size

def get (self : Column) (i : Nat) (h : i < self.size) : self.dataType.toType :=
  self.values[i]

def push (self : Column) (value : self.dataType.toType) : Column :=
  {
    name := self.name,
    dataType := self.dataType,
    values := self.values.push value,
  }

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

def ofValues {α} [DataType.OfType α] (name : String) (values : Array α) : Column :=
  {
    name := name,
    dataType := DataType.OfType.dataType α,
    values := DataType.OfType.eq α ▸ values,
  }

def mapValues {α} [DataType.OfType α] (self : Column) (f : self.dataType.toType → α) : Column :=
  {
    name := self.name,
    dataType := DataType.OfType.dataType α,
    values := DataType.OfType.eq α ▸ self.values.map f,
  }

end Column

end Tables

end
