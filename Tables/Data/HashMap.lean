module

public import Std.Data.HashMap

public section

namespace Std.HashMap

/--
Upstreams to `Std.Data.HashMap.Lemmas`: `valuesArray` parallels `keysArray` — same length as `size`.
-/
theorem size_valuesArray.{u, v}
    {α : Type u} {β : Type v} {_ : BEq α} {_ : Hashable α}
    [EquivBEq α] [LawfulHashable α] (m : HashMap α β) :
    m.valuesArray.size = m.size := by
  sorry

end Std.HashMap

end
