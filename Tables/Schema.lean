module

public import Tables.DataType

@[expose]
public section

namespace Tables

def Schema.WF (names : Array String) (types : Array DataType) : Prop :=
  names.size = types.size

structure Schema where
  names : Array String
  types : Array DataType
  wf : Schema.WF names types
deriving Repr, Ord, DecidableEq

namespace Schema

instance : Inhabited Schema := ⟨{ names := #[], types := #[], wf := rfl }⟩

def size (self : Schema) : Nat :=
  self.names.size

def getName (self : Schema) (i : Nat) (h : i < self.size) : String :=
  self.names[i]

def getType (self : Schema) (i : Nat) (h : i < self.size) : DataType :=
  self.types[i]'(self.wf ▸ h)

end Schema

end Tables

end
