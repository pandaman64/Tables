module

public section

namespace Tables

inductive Order where
  | ascending
  | descending
deriving Repr, DecidableEq

end Tables

end
