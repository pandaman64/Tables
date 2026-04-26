module

public import Tables.Table.Raw.Basic
import all Tables.Table.Raw.Basic
import Init.Data.Array.Lemmas
import Std.Data.HashMap.Lemmas

open Std (HashMap)
open Array

public section

namespace Tables.Table.Raw

section wfColumnSize

theorem Column_size_eq_values (c : Column) : c.size = c.values.size := rfl

theorem Column_size_push (c : Column) (v : Option c.dataType.toType) : (c.push v).size = c.size + 1 := by
  show (c.values.push v).size = c.values.size + 1
  simp [Array.size_push]

private theorem list_foldl_push_pair_size_eq
    {α β} (l : List (α × β)) (v0 : Array α) (c0 : Array β) (hv0 : v0.size = c0.size) :
    (l.foldl (fun p x => (p.1.push x.1, p.2.push x.2)) (v0, c0)).1.size =
      (l.foldl (fun p x => (p.1.push x.1, p.2.push x.2)) (v0, c0)).2.size := by
  induction l generalizing v0 c0 hv0 with
  | nil => exact hv0
  | cons a l ih =>
    simp only [List.foldl]
    refine ih (v0 := v0.push a.1) (c0 := c0.push a.2) ?_
    simp [Array.size_push, hv0]

theorem mapValues_size_eq {α} [DataType.OfType α] (c : Column) (f : Option c.dataType.toType → Option α) :
    (c.mapValues f).size = c.size := by
  grind [Column.mapValues, Column.size, DataType.OfType.eq, Array.size_map]

theorem fillna_size_eq (c : Column) (r : c.dataType.toType) : (c.fillna r).size = c.size := by
  simp [Column.fillna, Column.size, Array.size_map]

theorem wfColumnSize_empty (schema : Schema) : (empty schema).WfColumnSize := by
  intro c hc
  rw [empty, Array.mem_map] at hc
  obtain ⟨x, _, rfl⟩ := hc
  simp [empty, Column.size]

theorem wfColumnSize_ofColumns
    (columns : Array Column) (nrows : Nat) (h : ∀ column ∈ columns, column.size = nrows) :
    (ofColumns columns nrows).WfColumnSize :=
  h

theorem mem_getColumn (self : Raw) (i : Nat) (h : i < self.ncols) : self.getColumn i h ∈ self.columns := by
  simp [getColumn]

theorem mem_getColumnByName (self : Raw) (name : String) (h : self.hasColumn name) : self.getColumnByName name h ∈ self.columns := by
  unfold getColumnByName getColumnByName?
  grind

theorem wfColumnSize_selectColumns
    (self : Raw) (ns : Array (Fin self.ncols)) (hwf : self.WfColumnSize) :
    (selectColumns self ns).WfColumnSize := by
  intro c hc
  rw [selectColumns, WfColumnSize] at *
  rw [Array.mem_map] at hc
  obtain ⟨i, _, rfl⟩ := hc
  exact hwf _ (mem_getColumn self i.val i.isLt)

theorem wfColumnSize_selectColumnsByMask
    (self : Raw) (mask : Vector Bool self.ncols) (hwf : self.WfColumnSize) :
    (selectColumnsByMask self mask).WfColumnSize := by
  intro c hc
  rw [selectColumnsByMask, WfColumnSize] at *
  rw [Array.mem_filterMap] at hc
  obtain ⟨i, hmem, hsome⟩ := hc
  have hlt : i.val < self.ncols :=
    (Array.mem_range (m := i.val) (n := self.ncols)).1 (Subtype.property i)
  have heq : c = self.getColumn i.val hlt := by
    grind
  exact heq ▸ (hwf _ (mem_getColumn self i.val hlt))

theorem wfColumnSize_selectColumnsByName
    (self : Raw) (names : Array String) (h : ∀ name ∈ names, self.hasColumn name) (hwf : self.WfColumnSize) :
    (selectColumnsByName self names h).WfColumnSize := by
  intro c hc
  rw [selectColumnsByName, WfColumnSize] at *
  rw [Array.mem_map] at hc
  obtain ⟨s, hmem, rfl⟩ := hc
  have hcol : self.hasColumn s.1 := h s.1 s.property
  exact hwf (self.getColumnByName s.1 hcol) (mem_getColumnByName self s.1 hcol)

theorem wfColumnSize_take
    (self : Raw) (n : Nat) (hwf : self.WfColumnSize) (hle : n ≤ self.nrows) : (take self n).WfColumnSize := by
  intro c hc
  rw [take, WfColumnSize] at *
  rw [Array.mem_map] at hc
  obtain ⟨a, hma, rfl⟩ := hc
  have hvs : a.values.size = self.nrows := by simpa [Column.size] using (hwf a hma)
  simp [Column.size, Column.take, take_eq_extract, size_extract, hvs, Nat.sub_zero, Nat.min_eq_left hle]

theorem addRow_columns_size_eq_ncols (self : Raw) (row : Row) (h : row.schema = self.schema) :
    (addRow self row h).columns.size = self.ncols := by
  simp [addRow, ncols, Array.size_ofFn]

theorem wfColumnSize_addRow
    (self : Raw) (row : Row) (h : row.schema = self.schema) (hwf : self.WfColumnSize) :
    (addRow self row h).WfColumnSize := by
  intro c hc
  obtain ⟨j, hlt, e⟩ := getElem_of_mem hc
  have hs := addRow_columns_size_eq_ncols self row h
  have hjn : j < self.ncols := hs ▸ hlt
  have h1 : (self.getColumn j hjn).size = self.nrows := hwf (self.getColumn j hjn) (getElem_mem hjn)
  have eqsz : c.size = (addRow self row h).columns[j].size := (congrArg Column.size (Eq.symm e))
  rw [eqsz]
  have hsz : (addRow self row h).columns[j].size = self.nrows + 1 := by
    grind [addRow, ncols, getColumn, Array.getElem_ofFn, Array.size_ofFn, Column, Column_size_push,
      Fin, Fin.eta, Fin.is_lt, Fin.ext_iff, schema_size_eq, Row.schema, Row.size, Row.schema_size_eq_size]
  have hn : (addRow self row h).nrows = self.nrows + 1 := by simp [addRow]
  rw [hsz, hn]

theorem wfColumnSize_addRows
    (self : Raw) (rows : Array Row) (h : ∀ row ∈ rows, row.schema = self.schema) (hwf : self.WfColumnSize) :
    (addRows self rows h).WfColumnSize := by
  intro c hc
  obtain ⟨j, hlt, e⟩ := getElem_of_mem hc
  have hs : (addRows self rows h).columns.size = self.ncols := by simp [addRows, ncols, Array.size_ofFn]
  have hjn : j < self.ncols := by rw [hs] at hlt; exact hlt
  have h1 : (self.getColumn j hjn).size = self.nrows := hwf (self.getColumn j hjn) (getElem_mem (i := j) hjn)
  have eqsz : c.size = (addRows self rows h).columns[j].size := (congrArg Column.size (Eq.symm e))
  rw [eqsz]
  have hsz : (addRows self rows h).columns[j].size = self.nrows + rows.size := by
    grind [addRows, ncols, getColumn, Array.getElem_ofFn, Column, Column.size, Array.size_append,
      Array.size_ofFn, Fin, Fin.eta, Fin.is_lt, Fin.ext_iff, schema_size_eq, Row.schema, Row.size, Row.schema_size_eq_size,
      getRow, getRow_schema, Row.getDataType, Row.getValue]
  have hn : (addRows self rows h).nrows = self.nrows + rows.size := by simp [addRows]
  rw [hsz, hn]

theorem wfColumnSize_ofRows
    (schema : Schema) (rows : Array Row) (h : ∀ row ∈ rows, row.schema = schema) : (ofRows schema rows h).WfColumnSize := by
  simp [ofRows]
  exact wfColumnSize_addRows (empty schema) rows (by simpa using h) (wfColumnSize_empty schema)

theorem wfColumnSize_addColumn
    (self : Raw) (column : Column) (hsize : column.size = self.nrows) (hwf : self.WfColumnSize) : (addColumn self column).WfColumnSize := by
  intro c hc
  rw [WfColumnSize, addColumn] at *
  rw [Array.mem_push] at hc
  cases hc with
  | inl h' => exact hwf c h'
  | inr h' => simpa [h'] using hsize

theorem wfColumnSize_buildColumn
    {α} [DataType.OfType α] (self : Raw) (name : String) (f : Row → Option α) (h : self.WfColumnSize) :
    (buildColumn self name f h).WfColumnSize := by
  apply wfColumnSize_addColumn
  · rw [Column.ofRawValues_size, Array.size_ofFn]
  · exact h

theorem wfColumnSize_replaceColumn
    (self : Raw) (column : Column) (hsize : column.size = self.nrows) (hwf : self.WfColumnSize) : (replaceColumn self column).WfColumnSize := by
  intro c hc
  rw [WfColumnSize, replaceColumn] at *
  rw [Array.mem_map] at hc
  obtain ⟨c0, h0, rfl⟩ := hc
  by_cases hnm : c0.name = column.name
  · simpa [hnm, replaceColumn, Column] using hsize
  · simpa [hnm, replaceColumn, Column] using (hwf c0 h0)

theorem wfColumnSize_transformColumn
    {α} [DataType.OfType α] (self : Raw) (name : String) (hcol : self.hasColumn name)
    (f : Option ((getColumnByName self name hcol).dataType.toType) → Option α) (hwf : self.WfColumnSize) :
    (transformColumn self name hcol f).WfColumnSize := by
  have hmem : self.getColumnByName name hcol ∈ self.columns := by
    have hs' : (self.columns.find? fun col => col.name = name).isSome := by grind [hasColumn]
    simpa [getColumnByName, getColumnByName?] using (get_find?_mem (h := hs'))
  have hs : ((self.getColumnByName name hcol).mapValues f).size = self.nrows := by
    simp [mapValues_size_eq, hwf _ hmem]
  apply wfColumnSize_replaceColumn
  · exact hs
  · exact hwf

theorem wfColumnSize_selectRows
    (self : Raw) (ns : Array (Fin self.nrows)) (h : self.WfColumnSize) : (selectRows self ns h).WfColumnSize := by
  unfold selectRows
  apply wfColumnSize_ofRows

theorem wfColumnSize_selectRowsByMask
    (self : Raw) (mask : Vector Bool self.nrows) (h : self.WfColumnSize) : (selectRowsByMask self mask h).WfColumnSize := by
  unfold selectRowsByMask
  apply wfColumnSize_selectRows

theorem wfColumnSize_tfilter
    (self : Raw) (p : Row → Bool) (h : self.WfColumnSize) : (tfilter self p h).WfColumnSize := by
  unfold tfilter
  apply wfColumnSize_ofRows

theorem wfColumnSize_dropColumn (self : Raw) (name : String) (hwf : self.WfColumnSize) : (dropColumn self name).WfColumnSize := by
  intro c hc
  rw [dropColumn, WfColumnSize] at *
  rw [Array.mem_filter] at hc
  obtain ⟨hmem, _⟩ := hc
  exact hwf c hmem

theorem wfColumnSize_dropColumns
    (self : Raw) (names : Array String) (hwf : self.WfColumnSize) : (dropColumns self names).WfColumnSize := by
  intro c hc
  rw [dropColumns, WfColumnSize] at *
  rw [Array.mem_filter] at hc
  obtain ⟨hmem, _⟩ := hc
  exact hwf c hmem

theorem wfColumnSize_vcat
    (self other : Raw) (hschema : self.schema = other.schema) (hwf₁ : self.WfColumnSize) (hwf₂ : other.WfColumnSize) :
    (vcat self other hschema).WfColumnSize := by
  intro c hc
  obtain ⟨j, hlt, e⟩ := getElem_of_mem hc
  have hs : (vcat self other hschema).columns.size = self.ncols := by
    simp [vcat, ncols, Array.size_ofFn]
  have hjn : j < self.ncols := hs ▸ hlt
  have eqNcols : self.ncols = other.ncols := by rw [← schema_size_eq, ← schema_size_eq, hschema]
  have olt : j < other.ncols := eqNcols.symm ▸ hjn
  have h1 : (self.getColumn j hjn).size = self.nrows := hwf₁ (self.getColumn j hjn) (getElem_mem hjn)
  have h2 : (other.getColumn j olt).size = other.nrows := hwf₂ (other.getColumn j olt) (getElem_mem olt)
  have eqsz : c.size = (vcat self other hschema).columns[j].size := (congrArg Column.size (Eq.symm e))
  rw [eqsz]
  have hsz : (vcat self other hschema).columns[j].size = self.nrows + other.nrows := by
    grind [vcat, ncols, getColumn, Array.getElem_ofFn, Array.size_ofFn, Column, Column.concat, Column.size,
      Array.size_append, Fin, Fin.eta, Fin.is_lt, Fin.ext_iff, schema_size_eq, schema, Raw.schema]
  have hn : (vcat self other hschema).nrows = self.nrows + other.nrows := by simp [vcat]
  rw [hsz, hn]

theorem wfColumnSize_hcat
    (self other : Raw) (hwf₁ : self.WfColumnSize) (hwf₂ : other.WfColumnSize) (hrows : self.nrows = other.nrows) : (hcat self other).WfColumnSize := by
  intro c hc
  rw [hcat, WfColumnSize] at *
  rw [Array.mem_append] at hc
  cases hc with
  | inl h' => exact hwf₁ c h'
  | inr h' => simpa [hrows] using (hwf₂ c h')

theorem wfColumnSize_renameColumn
    (self : Raw) (oldName newName : String) (hwf : self.WfColumnSize) : (renameColumn self oldName newName).WfColumnSize := by
  intro c hc
  rw [renameColumn, WfColumnSize] at *
  rw [Array.mem_map] at hc
  obtain ⟨c0, h0, heq⟩ := hc
  have hsze : c.size = c0.size := by
    rw [← heq]
    grind [Column, Column.size, Row]
  exact (hsze.trans (hwf c0 h0))

theorem wfColumnSize_renameColumns
    (self : Raw) (renames : Array (String × String)) (hwf : self.WfColumnSize) : (renameColumns self renames).WfColumnSize := by
  simp [renameColumns]
  refine renames.foldl_induction
    (motive := fun _ (t : Raw) => t.WfColumnSize) (h0 := hwf) (fun i t ht => ?_)
  obtain ⟨o, n⟩ := renames[i]
  exact wfColumnSize_renameColumn t o n ht

theorem wfColumnSize_select
    (self : Raw) (schema' : Schema) (f : Row → (n : Nat) → n < self.nrows → Row) (h₁ : ∀ row n h, (f row n h).schema = schema') (h₂ : self.WfColumnSize) :
    (self.select schema' f h₁ h₂).WfColumnSize := by
  apply wfColumnSize_ofRows
  intro row hrow
  grind [Array.mem_unattach, Fin, Fin.eta, Fin.is_lt, getRow, getRow_schema, Row, Row.schema, schema]

theorem wfColumnSize_dropna (self : Raw) (h : self.WfColumnSize) : (dropna self h).WfColumnSize := by
  unfold dropna; exact wfColumnSize_tfilter self _ h

theorem wfColumnSize_fillna
    (self : Raw) (column : String) (h₁ : self.hasColumn column) (replacement : (getColumnByName self column h₁).dataType.toType) (hwf : self.WfColumnSize) :
    (self.fillna column h₁ replacement).WfColumnSize := by
  have hcol : (self.getColumnByName column h₁) ∈ self.columns := mem_getColumnByName self column h₁
  have hsz : ((self.getColumnByName column h₁).fillna replacement).size = self.nrows := by
    rw [fillna_size_eq]
    exact hwf (self.getColumnByName column h₁) hcol
  simp [fillna, WfColumnSize]
  apply wfColumnSize_replaceColumn
  · exact hsz
  · exact hwf

-- Not in Std
private theorem HashMap.size_valuesArray.{u, v}
    {α : Type u} {β : Type v} {_ : BEq α} {_ : Hashable α}
    [EquivBEq α] [LawfulHashable α] (m : Std.HashMap α β) :
  m.valuesArray.size = m.size := by
  sorry

theorem wfColumnSize_count
    (self : Raw) (column : String) (h : self.hasColumn column) : (count self column h).WfColumnSize := by
  unfold count
  apply wfColumnSize_ofColumns
  intro c hc
  simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hc
  cases hc with
  | inl hc =>
    rw [hc]
    simp [Column.size]
  | inr hc =>
    rw [hc]
    simp [Column.size, HashMap.size_valuesArray]

end wfColumnSize

end Tables.Table.Raw

end
