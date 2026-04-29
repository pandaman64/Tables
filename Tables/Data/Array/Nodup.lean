module

public import Batteries.Data.Array.Pairwise

public section

namespace List

variable {α} {l : List α}

-- From Mathlib
theorem Nodup.filter (p : α → Bool) (h : Nodup l) : Nodup (l.filter p) := by
  simpa using Pairwise.filter p h

end List

namespace Array

@[expose]
def Nodup {α} (a : Array α) : Prop := Pairwise (fun x y => x ≠ y) a

namespace Nodup

instance {α} [DecidableEq α] {a : Array α}: Decidable (Nodup a) :=
  inferInstanceAs (Decidable (Pairwise (fun x y => x ≠ y) a))

theorem toList_iff {α} (a : Array α) : a.Nodup ↔ a.toList.Nodup := by
  rfl

theorem empty {α} : Nodup (@empty α) := by
  exact pairwise_empty

theorem range (n : Nat) : Nodup (Array.range n) := by
  rw [toList_iff, Array.toList_range]
  exact List.nodup_range

theorem finRange (n : Nat) : Nodup (Array.finRange n) := by
  rw [toList_iff, List.nodup_iff_pairwise_ne, List.pairwise_iff_getElem]
  intro i j hi hj lt
  simpa [Array.getElem_finRange] using Nat.ne_of_lt lt

theorem push {α} {a : Array α} {x : α} (h : Nodup a) (hfresh : x ∉ a) : Nodup (a.push x) := by
  unfold Nodup
  rw [Array.pairwise_push]
  exact ⟨h, by grind only⟩

theorem filter {α} {a : Array α} (p : α → Bool) (h : Nodup a) : Nodup (a.filter p) := by
  rw [toList_iff, toList_filter]
  apply List.Nodup.filter p
  rw [← toList_iff]
  exact h

end Nodup

end Array

end
