module

public import Tables.Schema
public import Std.Data.DHashMap

@[expose]
public section

namespace Tables

structure Table where
  schema : Schema
  -- TODO: how to use Array?
  rows : Std.DHashMap (Fin schema.size) (fun i => (schema.getType i.val i.isLt).toType)

namespace Table

instance : Inhabited Table := ⟨{ schema := default, rows := default }⟩

end Table

end Tables
