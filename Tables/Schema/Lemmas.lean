module

public import Tables.Schema.Basic

import Tables.Data.Array.Nodup
public import Tables.Data.Array.Pairwise

import Init.Data.Array.Lemmas
import Init.Data.List.Nat.Pairwise

public section

namespace Tables

namespace Schema

theorem append_def (self other : Schema) :
    self ++ other = { specs := self.specs ++ other.specs } := (rfl)

@[simp, grind =]
theorem size_eq (self : Schema) : self.specs.size = self.size := (rfl)

@[simp, grind =]
theorem ofSpecs_specs (specs : Array (String × DataType)) : (ofSpecs specs).specs = specs := (rfl)

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

@[simp, grind =]
theorem replace_size (self : Schema) (name : String) (dataType : DataType) :
    (self.replace name dataType).size = self.size := by
  simp [replace]

@[simp, grind =]
theorem rename_size (self : Schema) (oldName newName : String) :
    (self.rename oldName newName).size = self.size := by
  simp [rename]

@[simp, grind =]
theorem rename_getName (self : Schema) (oldName newName : String) (i : Nat) (hi : i < self.size) :
    (self.rename oldName newName).getName i (self.rename_size oldName newName ▸ hi) =
      if self.getName i hi = oldName then newName else self.getName i hi := by
  grind only [getName, rename, = ofSpecs_specs, = Array.getElem_map]

@[simp, grind =]
theorem ofSpecs_hasName_iff {specs : Array (String × DataType)} {name : String} :
    (ofSpecs specs).hasName name ↔ specs.any (·.1 = name) := by
  simp [ofSpecs, hasName]

@[simp, grind =]
theorem push_hasName_iff {schema : Schema} {spec : String × DataType} {name : String} :
    (schema.push spec).hasName name ↔ schema.hasName name ∨ spec.1 = name := by
  simp [push, hasName]

@[simp, grind =]
theorem concat_hasName_iff {schema₁ schema₂ : Schema} {name : String} :
    (schema₁ ++ schema₂).hasName name ↔ schema₁.hasName name ∨ schema₂.hasName name := by
  simp [append_def, hasName]

@[simp, grind =]
theorem replace_hasName_iff {schema : Schema} {name name' : String} {dataType : DataType} :
    (schema.replace name dataType).hasName name' ↔ schema.hasName name' := by
  simp only [replace, ofSpecs_hasName_iff, Array.any_map, Function.comp_apply]
  unfold hasName
  apply Iff.of_eq
  congr
  funext x
  split <;> simp_all

theorem rename_not_hasName_oldName_iff {schema : Schema} {oldName newName : String} :
    (schema.rename oldName newName).hasName oldName ↔ oldName = newName ∧ schema.hasName oldName := by
  grind [rename, hasName]

theorem rename_hasName_newName_iff {schema : Schema} {oldName newName : String} :
    (schema.rename oldName newName).hasName newName ↔ schema.hasName newName ∨ schema.hasName oldName := by
  grind [rename, hasName]

theorem rename_hasName_iff_of_ne {schema : Schema} {oldName newName name : String}
    (h₁ : name ≠ oldName) (h₂ : name ≠ newName) :
    (schema.rename oldName newName).hasName name ↔ schema.hasName name := by
  grind [rename, hasName]

theorem wf_default : (default : Schema).Wf := by decide

theorem wf_replace {schema : Schema} {name : String} {dataType : DataType}
    (hwf : schema.Wf) : (schema.replace name dataType).Wf := by
  intro i j hij
  grind [Schema.Wf, Schema.replace, Schema.getName]

private theorem pairwise_of_wf {schema : Schema} (hwf : schema.Wf) :
    schema.specs.Pairwise fun x y => x.1 ≠ y.1 := by
  rw [Array.pairwise_iff_getElem]
  intro i j hi hj lt
  have hi' : i < schema.specs.size := by simpa using hi
  have hj' : j < schema.specs.size := by simpa using hj
  have hneq := hwf ⟨i, hi'⟩ ⟨j, hj'⟩ lt
  simpa using hneq

private theorem wf_of_pairwise {specs : Array (String × DataType)}
    (hp : specs.Pairwise fun x y => x.1 ≠ y.1) :
    (ofSpecs specs).Wf := by
  intro i j lt
  rw [Array.pairwise_iff_getElem] at hp
  simpa [getName] using hp i j i.isLt j.isLt lt

theorem wf_iff_pairwise {schema : Schema} :
    schema.Wf ↔ schema.specs.Pairwise fun x y => x.1 ≠ y.1 :=
  ⟨pairwise_of_wf, wf_of_pairwise⟩

theorem wf_filter {schema : Schema} {p : String × DataType → Bool}
    (hwf : schema.Wf) : (schema.filter p).Wf := by
  dsimp only [Schema.filter]
  exact wf_of_pairwise (Array.Pairwise.filter p (pairwise_of_wf hwf))

theorem wf_push {schema : Schema} {spec : String × DataType}
    (hwf : schema.Wf)
    (hfresh : ∀ i : Fin schema.size, schema.getName i ≠ spec.1) :
    (schema.push spec).Wf := by
  dsimp only [Schema.push]
  refine wf_of_pairwise (Array.pairwise_push.mpr ⟨pairwise_of_wf hwf, ?_⟩)
  intro s h
  obtain ⟨n, lt, eq⟩ := Array.getElem_of_mem h
  simpa [←eq] using hfresh ⟨n, by grind only [= size_eq]⟩

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
    (hdisjoint : ∀ (i : Fin schema₁.size) (j : Fin schema₂.size),
      schema₁.getName i ≠ schema₂.getName j) :
    (schema₁ ++ schema₂).Wf := by
  refine wf_of_pairwise (Array.pairwise_append.mpr ⟨pairwise_of_wf hwf₁, pairwise_of_wf hwf₂, ?_⟩)
  intro s₁ h₁ s₂ h₂
  obtain ⟨n₁, lt₁, eq₁⟩ := Array.getElem_of_mem h₁
  obtain ⟨n₂, lt₂, eq₂⟩ := Array.getElem_of_mem h₂
  simpa [←eq₁, ←eq₂] using hdisjoint ⟨n₁, lt₁⟩ ⟨n₂, lt₂⟩

end Schema

end Tables

end
