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

namespace Column

def toString (self : Column) : String :=
  s!"{self.name}: #[{self.values.map (DataType.toString self.dataType) |> String.joinSep ", "}]"

def size (self : Column) : Nat :=
  self.values.size

def concat (self : Column) (other : Column)
    (_h₁ : self.name = other.name) (h₂ : self.dataType = other.dataType) : Column :=
  {
    name := self.name,
    dataType := self.dataType,
    values := self.values ++ h₂ ▸ other.values,
  }

end Column

end Tables

end
