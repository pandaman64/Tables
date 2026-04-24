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

instance : Inhabited Schema := ⟨{ names := #[], types := #[], wf := rfl }⟩

end Tables

end
