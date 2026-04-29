module

public import Tables.DataType

import Init.Data.Array.Lemmas
import Init.Data.List.Nat.Pairwise

@[expose]
public section

namespace Tables

@[ext]
structure Schema where
  specs : Array (String × DataType)
deriving Repr, DecidableEq, Inhabited

namespace Schema

def ofSpecs (specs : Array (String × DataType)) : Schema :=
  { specs }

def size (self : Schema) : Nat :=
  self.specs.size

instance : GetElem Schema Nat (String × DataType) (fun s i => i < s.size) where
  getElem s i h := s.specs[i]

def getName (self : Schema) (i : Nat) (h : i < self.size := by get_elem_tactic) : String :=
  self.specs[i].1

def getDataType (self : Schema) (i : Nat) (h : i < self.size := by get_elem_tactic) : DataType :=
  self.specs[i].2

def Wf (self : Schema) : Prop :=
  ∀ (i j : Fin self.size), i ≠ j → self.getName i ≠ self.getName j

instance {schema : Schema} : Decidable (Wf schema) := inferInstanceAs (Decidable (∀ (i j : Fin schema.size), i ≠ j → schema.getName i ≠ schema.getName j))

def push (self : Schema) (spec : String × DataType) : Schema :=
  { specs := self.specs.push spec }

def concat (self other : Schema) : Schema :=
  { specs := self.specs ++ other.specs }

instance : Append Schema where
  append := concat

theorem append_def (self other : Schema) : self ++ other = { specs := self.specs ++ other.specs } := (rfl)

def replace (self : Schema) (name : String) (dataType : DataType) : Schema :=
  { specs := self.specs.map fun (n, d) => if n = name then (name, dataType) else (n, d) }

@[simp, grind =]
theorem replace_size (self : Schema) (name : String) (dataType : DataType) : (self.replace name dataType).size = self.size := by
  simp [replace, size]

def rename (self : Schema) (oldName newName : String) : Schema :=
  { specs := self.specs.map fun (n, d) => if n = oldName then (newName, d) else (n, d) }

@[simp, grind =]
theorem rename_size (self : Schema) (oldName newName : String) : (self.rename oldName newName).size = self.size := by
  simp [rename, size]

@[simp, grind =]
theorem rename_getName (self : Schema) (oldName newName : String) (i : Nat) (hi : i < self.size) :
    (self.rename oldName newName).getName i (self.rename_size oldName newName ▸ hi) =
      if self.getName i hi = oldName then newName else self.getName i hi := by
  simp only [getName, rename, Array.getElem_map]
  grind

def filter (self : Schema) (p : String × DataType → Bool) : Schema :=
  { specs := self.specs.filter p }

def selectNotByNames (self : Schema) (names : Array String) : Schema :=
  { specs := self.specs.filter fun (name, _) => name ∉ names }

@[simp, grind =]
theorem ofSpecs_size (specs : Array (String × DataType)) : (ofSpecs specs).size = specs.size := by
  simp [ofSpecs, size]

@[simp, grind =]
theorem ofSpecs_getElem (specs : Array (String × DataType)) (i : Nat) (h : i < (ofSpecs specs).size) :
    (ofSpecs specs)[i] = specs[i] := by
  rfl

@[simp, grind =]
theorem ofSpecs_getName (specs : Array (String × DataType)) (i : Nat) (h : i < (ofSpecs specs).size) :
  (ofSpecs specs).getName i h = specs[i].1 := by
  rfl

@[simp, grind =]
theorem ofSpecs_getDataType (specs : Array (String × DataType)) (i : Nat) (h : i < (ofSpecs specs).size) :
  (ofSpecs specs).getDataType i h = specs[i].2 := by
  rfl

theorem wf_replace {schema : Schema} {name : String} {dataType : DataType}
    (hwf : schema.Wf) : (schema.replace name dataType).Wf := by
  intro i j hij
  grind [Schema.Wf, Schema.replace, Schema.getName]

private theorem wf_implies_pairwise_toList {schema : Schema} (hwf : schema.Wf) :
    schema.specs.toList.Pairwise (fun x y => x.1 ≠ y.1) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij_lt
  have hi' : i < schema.specs.size := by simpa using hi
  have hj' : j < schema.specs.size := by simpa using hj
  have hij_ne : (⟨i, hi'⟩ : Fin schema.specs.size) ≠ ⟨j, hj'⟩ :=
    Fin.ne_of_val_ne (Nat.ne_of_lt hij_lt)
  have hneq := hwf ⟨i, hi'⟩ ⟨j, hj'⟩ hij_ne
  simpa only [Schema.getName, ← Array.getElem_toList] using hneq

private theorem pairwise_toList_implies_Wf {specs : Array (String × DataType)}
    (hp : specs.toList.Pairwise fun x y => x.1 ≠ y.1) :
    ({ specs := specs } : Schema).Wf := by
  intro i j hij
  rw [List.pairwise_iff_getElem] at hp
  rcases Nat.lt_trichotomy i.val j.val with hlt | heq | hgt
  · have hi₁ := i.isLt
    have hj₁ := j.isLt
    simpa only [Schema.getName, ← Array.getElem_toList] using hp i.val j.val hi₁ hj₁ hlt
  · exact absurd (Fin.ext heq) hij
  · have hi₁ := i.isLt
    have hj₁ := j.isLt
    simpa only [Schema.getName, ← Array.getElem_toList] using Ne.symm (hp j.val i.val hj₁ hi₁ hgt)

theorem wf_filter {schema : Schema} {p : String × DataType → Bool}
    (hwf : schema.Wf) : (schema.filter p).Wf := by
  dsimp only [Schema.filter]
  have hp := List.Pairwise.filter p (wf_implies_pairwise_toList hwf)
  have hp' : (schema.specs.filter p).toList.Pairwise fun x y => x.1 ≠ y.1 := by
    rw [Array.toList_filter]
    exact hp
  exact pairwise_toList_implies_Wf hp'

theorem wf_push {schema : Schema} {spec : String × DataType}
    (hwf : schema.Wf)
    (hfresh : ∀ i : Fin schema.size, schema.getName i ≠ spec.1) :
    (schema.push spec).Wf := by
  dsimp only [Schema.push]
  refine pairwise_toList_implies_Wf ?_
  have hp := wf_implies_pairwise_toList hwf
  rw [Array.toList_push]
  rw [List.pairwise_append]
  refine ⟨hp, List.pairwise_singleton _ spec, ?_⟩
  intro a ha b hb
  simp only [List.mem_singleton] at hb
  subst hb
  rcases List.mem_iff_getElem.mp ha with ⟨i, hi, rfl⟩
  simpa only [Schema.getName, ← Array.getElem_toList] using hfresh ⟨i, hi⟩

theorem wf_rename {schema : Schema} {oldName newName : String}
    (hwf : schema.Wf)
    (hfresh : ∀ i : Fin schema.size, schema.getName i ≠ newName ∨ schema.getName i = oldName) :
    (schema.rename oldName newName).Wf := by
  intro i j ne
  have hi : i < schema.size := by grind
  have hj : j < schema.size := by grind
  rw [rename_getName schema oldName newName i hi, rename_getName schema oldName newName j hj]
  grind [Wf]

theorem wf_concat {schema₁ schema₂ : Schema}
    (hwf₁ : schema₁.Wf) (hwf₂ : schema₂.Wf)
    (hdisjoint :
      ∀ (i : Fin schema₁.size) (j : Fin schema₂.size),
        schema₁.getName i ≠ schema₂.getName j) :
    (schema₁ ++ schema₂).Wf := by
  refine pairwise_toList_implies_Wf ?_
  have hp1 := wf_implies_pairwise_toList hwf₁
  have hp2 := wf_implies_pairwise_toList hwf₂
  rw [Array.toList_append]
  rw [List.pairwise_append]
  refine ⟨hp1, hp2, ?_⟩
  intro a ha b hb
  rcases List.mem_iff_getElem.mp ha with ⟨i, hi, rfl⟩
  rcases List.mem_iff_getElem.mp hb with ⟨j, hj, rfl⟩
  simpa only [Schema.getName, ← Array.getElem_toList] using hdisjoint ⟨i, hi⟩ ⟨j, hj⟩

end Schema

end Tables

end
