module

public section

namespace List

variable {α} {l : List α}

-- From Mathlib
theorem Nodup.filter (p : α → Bool) (h : Nodup l) : Nodup (l.filter p) := by
  simpa using Pairwise.filter p h

end List

namespace Array

@[expose]
def Nodup {α} (a : Array α) : Prop :=
  ∀ i j : Nat, (_ : i < a.size) → (_ : j < a.size) → i ≠ j → a[i] ≠ a[j]

namespace Nodup

abbrev Nodup' {α} (a : Array α) : Prop :=
  ∀ i j : Fin a.size, i ≠ j → a[i] ≠ a[j]

theorem iff_nodup' {α} (a : Array α) : Nodup a ↔ Nodup' a := by
  apply Iff.intro
  . grind [Nodup]
  . intro h i j hi hj ne
    exact h ⟨i, hi⟩ ⟨j, hj⟩ (by grind)

instance {α} [DecidableEq α] {a : Array α}: Decidable (Nodup a) :=
  decidable_of_iff' (Nodup' a) (iff_nodup' a)

theorem empty {α} : Nodup (@empty α) := by
  intro i j hi hj ne
  exact (Nat.not_lt_zero i hi).elim

theorem range (n : Nat) : Nodup (Array.range n) := by
  intro i j
  simp [Array.getElem_range]

theorem finRange (n : Nat) : Nodup (Array.finRange n) := by
  intro i j
  simp [Array.getElem_finRange]

theorem push {α} {a : Array α} {x : α} (h : Nodup a) (hfresh : x ∉ a) : Nodup (a.push x) := by
  intro i j hi hj ne
  simp only [getElem_push]
  split
  next hi =>
    split
    next hj => exact h i j hi hj ne
    next hj => grind
  next hi => grind

theorem toList_iff {α} (a : Array α) : a.Nodup ↔ a.toList.Nodup := by
  constructor
  . intro h
    simp only [List.nodup_iff_pairwise_ne, ne_eq, List.pairwise_iff_getElem, length_toList,
      getElem_toList]
    intro i j hi hj lt
    exact h i j hi hj (Nat.ne_of_lt lt)
  . intro h
    simp only [List.nodup_iff_pairwise_ne, ne_eq, List.pairwise_iff_getElem, length_toList,
      getElem_toList] at h
    intro i j hi hj ne
    cases Nat.lt_or_gt_of_ne ne with
    | inl lt => exact h i j hi hj lt
    | inr gt => exact Ne.symm (h j i hj hi gt)

theorem filter {α} {a : Array α} (p : α → Bool) (h : Nodup a) : Nodup (a.filter p) := by
  rw [toList_iff, toList_filter]
  apply List.Nodup.filter p
  rw [← toList_iff]
  exact h

end Nodup

end Array

end
