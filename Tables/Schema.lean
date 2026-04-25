module

public import Tables.DataType

@[expose]
public section

namespace Tables

structure Schema where
  columns : Array (String × DataType)
deriving Repr, DecidableEq, Inhabited

end Tables

end
