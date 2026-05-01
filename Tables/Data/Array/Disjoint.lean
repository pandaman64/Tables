module

public import Batteries.Data.List.Basic
public import Tables.Data.Array.Pairwise

public section

namespace Array

@[expose]
def Disjoint {α} (a b : Array α) : Prop :=
  a.toList.Disjoint b.toList

namespace Disjoint

variable {α} {a b : Array α}

theorem iff_getElem_ne : a.Disjoint b ↔ ∀ i j, (_ : i < a.size) → (_ : j < b.size) → a[i] ≠ b[j] := by
  unfold Disjoint List.Disjoint
  simp only [List.mem_iff_getElem, Array.getElem_toList]
  grind

theorem iff_getElem_ne' : a.Disjoint b ↔ ∀ (i : Fin a.size) (j : Fin b.size), a[i.val] ≠ b[j.val] := by
  rw [iff_getElem_ne]
  apply Iff.intro
  . intro h i j
    exact h i.val j.val i.isLt j.isLt
  . intro h i j hi hj
    exact h ⟨i, hi⟩ ⟨j, hj⟩

instance [DecidableEq α] : Decidable (Disjoint a b) :=
  decidable_of_iff' _ iff_getElem_ne'

end Disjoint

end Array

end
