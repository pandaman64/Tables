module

public import Tables.Order
public import Tables.Table.Raw.Basic
import all Tables.Table.Raw.Basic
import Tables.Table.Raw.BasicLemmas

import Std.Data.TreeMap

open Std (TreeMap)

public section

namespace Tables

structure Comparator.{u} where
  T : Type u
  getKey : Row → T
  compare : T → T → Ordering

namespace Comparator

def ofOrd {α} [Ord α] (getKey : Row → α) : Comparator :=
  {
    T := α
    getKey := getKey
    compare := Ord.compare
  }

end Comparator

end Tables

namespace Tables.Table.Raw

-- We should have Array.sortBy
def tsort (self : Raw) (key : String) (order : Order) (h₁ : self.hasColumn key) (h₂ : self.WfColumnSize) : Raw :=
  let dataType := (self.getColumnByName key h₁).dataType
  let compare : Option dataType.toType → Option dataType.toType → Ordering :=
    match order with
    | .ascending => Ord.compare
    | .descending => fun a b => Ord.compare b a
  let init : TreeMap (Option dataType.toType) (Array (Fin self.nrows)) compare := ∅
  let map := Nat.fold (init := init) self.nrows fun i isLt map =>
    let row := self.getRow i isLt h₂
    -- `dataType` comes from an existing column, so it must appear in the schema specs.
    have h : row.hasNameAndDataType key dataType := by
      rw [Row.hasNameAndDataType_iff_mem_schema]
      simp only [getRow_schema, schema, Array.mem_map, Prod.mk.injEq, row, dataType]
      exact ⟨
        self.getColumnByName key h₁,
        mem_getColumnByName self key h₁,
        by simp [getColumnByName_name],
        rfl
      ⟩
    let value := row.getValueByNameAndDataType key dataType h
    map.alter value fun
      | some indices => some (indices.push ⟨i, isLt⟩)
      | none => some #[⟨i, isLt⟩]

  let table : { table : Raw // table.schema = self.schema } := map.foldl (init := ⟨Raw.empty self.schema, empty_schema⟩)
    fun table _ indices =>
      let rows := indices.map fun i => self.getRow i.val i.isLt h₂
      ⟨table.val.addRows rows (by simp [rows, table.property]), by simp [addRows_schema, table.property]⟩
  table.val

theorem wfColumnSize_tsort (self : Raw) (key : String) (order : Order) (h₁ : self.hasColumn key) (h₂ : self.WfColumnSize) :
    (self.tsort key order h₁ h₂).WfColumnSize := by
  dsimp [tsort]
  rw [TreeMap.foldl_eq_foldl_toArray]
  apply Array.foldl_induction (fun _ (table : { table : Raw // table.schema = self.schema }) => table.val.WfColumnSize)
  . exact wfColumnSize_empty self.schema
  . intro _ table ht
    exact wfColumnSize_addRows _ _ (by simp [table.property]) ht

theorem tsort_schema (self : Raw) (key : String) (order : Order) (h₁ : self.hasColumn key) (h₂ : self.WfColumnSize) :
    (self.tsort key order h₁ h₂).schema = self.schema := by
  unfold tsort
  grind only

theorem wfColumnNames_tsort (self : Raw) (key : String) (order : Order)
    (h₁ : self.hasColumn key) (h₂ : self.WfColumnSize) (h₃ : self.WfColumnNames) :
    (self.tsort key order h₁ h₂).WfColumnNames := by
  simpa [wfColumnNames_iff_schema_wf, tsort_schema] using h₃

def sortByColumns (self : Raw) (keys : Array (String × Order))
    (h₁ : ∀ key ∈ keys, self.hasColumn key.1) (h₂ : self.WfColumnSize) : Raw :=
  let table : { table : Raw // table.schema = self.schema ∧ table.WfColumnSize } :=
    keys.attach.foldr (init := ⟨self, rfl, h₂⟩) fun ⟨(key, order), hkey⟩ table =>
      have h : table.val.hasColumn key := by
        have h' : self.hasColumn key := h₁ (key, order) hkey
        simpa [hasColumn_iff_mem_schema_specs, table.property.1] using h'
      ⟨
        table.val.tsort key order h table.property.2,
        by simp [tsort_schema, table.property.1],
        wfColumnSize_tsort table key order h table.property.2
      ⟩
  table.val

theorem wfColumnSize_sortByColumns (self : Raw) (keys : Array (String × Order))
    (h₁ : ∀ key ∈ keys, self.hasColumn key.1) (h₂ : self.WfColumnSize) :
    (self.sortByColumns keys h₁ h₂).WfColumnSize := by
  dsimp [sortByColumns]
  apply Array.foldr_induction (fun _ (table : { table : Raw // table.schema = self.schema ∧ table.WfColumnSize }) => table.val.WfColumnSize) h₂
  intro _ table ht
  apply wfColumnSize_tsort table

theorem sortByColumns_schema (self : Raw) (keys : Array (String × Order))
    (h₁ : ∀ key ∈ keys, self.hasColumn key.1) (h₂ : self.WfColumnSize) :
    (self.sortByColumns keys h₁ h₂).schema = self.schema := by
  unfold sortByColumns
  grind only

theorem wfColumnNames_sortByColumns (self : Raw) (keys : Array (String × Order))
    (h₁ : ∀ key ∈ keys, self.hasColumn key.1) (h₂ : self.WfColumnSize) (h₃ : self.WfColumnNames) :
    (self.sortByColumns keys h₁ h₂).WfColumnNames := by
  simpa [wfColumnNames_iff_schema_wf, sortByColumns_schema] using h₃

def orderBy (self : Raw) (comparators : Array Comparator) (h : self.WfColumnSize) : Raw :=
  let compare (r₁ r₂ : Row) : Ordering := Id.run do
    for comparator in comparators do
      let ordering := comparator.compare (comparator.getKey r₁) (comparator.getKey r₂)
      if ordering ≠ .eq then
        return ordering
    return .eq

  let init : TreeMap Row (Array (Fin self.nrows)) compare := ∅
  let map := Nat.fold (init := init) self.nrows fun i isLt map =>
    let row := self.getRow i isLt h
    map.alter row fun
      | some indices => some (indices.push ⟨i, isLt⟩)
      | none => some #[⟨i, isLt⟩]

  let table : { table : Raw // table.schema = self.schema } := map.foldl (init := ⟨Raw.empty self.schema, empty_schema⟩)
    fun table _ indices =>
      let rows := indices.map fun i => self.getRow i.val i.isLt h
      ⟨table.val.addRows rows (by simp [rows, table.property]), by simp [addRows_schema, table.property]⟩
  table.val

theorem wfColumnSize_orderBy (self : Raw) (comparators : Array Comparator) (h : self.WfColumnSize) :
    (self.orderBy comparators h).WfColumnSize := by
  dsimp [orderBy]
  rw [TreeMap.foldl_eq_foldl_toArray]
  apply Array.foldl_induction (fun _ (table : { table : Raw // table.schema = self.schema }) => table.val.WfColumnSize) (wfColumnSize_empty self.schema)
  intro _ table ht
  apply wfColumnSize_addRows _ _ (by simp [table.property]) ht

theorem orderBy_schema (self : Raw) (comparators : Array Comparator) (h : self.WfColumnSize) :
    (self.orderBy comparators h).schema = self.schema := by
  unfold orderBy
  grind only

theorem wfColumnNames_orderBy (self : Raw) (comparators : Array Comparator) (h₁ : self.WfColumnSize) (h₂ : self.WfColumnNames) :
    (self.orderBy comparators h₁).WfColumnNames := by
  simpa [wfColumnNames_iff_schema_wf, orderBy_schema] using h₂

end Tables.Table.Raw

end
