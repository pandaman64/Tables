module

public import Batteries.Data.Array.Pairwise

public section

namespace Array

theorem Pairwise.filter {α} {R : α → α → Prop} {a : Array α} (p : α → Bool) (h : Pairwise R a) :
    Pairwise R (a.filter p) := by
  rw [Pairwise, Array.toList_filter]
  exact List.Pairwise.filter p h

end Array

end
