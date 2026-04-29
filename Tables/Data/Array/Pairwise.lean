module

public import Batteries.Data.Array.Pairwise

public section

namespace Array

theorem Pairwise.filter {α} {R : α → α → Prop} {a : Array α} (p : α → Bool) (h : Pairwise R a) :
    Pairwise R (a.filter p) := by
  rw [Pairwise, Array.toList_filter]
  exact List.Pairwise.filter p h

theorem pairwise_map {α β} {R : β → β → Prop} {f : α → β} {a : Array α} :
    (a.map f).Pairwise R ↔ a.Pairwise (fun a b => R (f a) (f b)) := by
  rw [Pairwise, Array.toList_map]
  exact List.pairwise_map

theorem pairwise_attach {α} {R : α → α → Prop} {a : Array α}  :
    a.attach.Pairwise (fun a b => R a.val b.val) ↔ a.Pairwise R := by
  simp only [Pairwise, attach, attachWith, List.attachWith, List.pairwise_pmap]
  rw [List.pairwise_iff_getElem, List.pairwise_iff_getElem]
  simp

theorem pairwise_unattach {α} {R : α → α → Prop} {p : α → Prop} {a : Array { a : α // p a }} :
    a.unattach.Pairwise R ↔ a.Pairwise (fun a b => R a.val b.val) := by
  simp [Pairwise, Array.toList_unattach]
  rw [List.unattach, List.pairwise_map]

end Array

end
