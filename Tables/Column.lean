module

public import Tables.DataType

@[expose]
public section

namespace Tables

structure Column where
  name : String
  dataType : DataType
  values : Array dataType.toType

namespace Column

def toString (self : Column) : String :=
  s!"{self.name}: #[{self.values.map (DataType.toString self.dataType) |> String.joinSep ", "}]"

def size (self : Column) : Nat :=
  self.values.size

end Column

end Tables

end
