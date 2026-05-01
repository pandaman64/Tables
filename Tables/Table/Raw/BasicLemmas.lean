module

public import Tables.Table.Raw.Basic
import all Tables.Table.Raw.Basic
public import Tables.Data.Array.Disjoint
public import Tables.Data.Array.Nodup

import Std.Data.HashMap.Lemmas
import Tables.Data.HashMap

open Std (HashMap)
open Array

public section

namespace Tables.Table.Raw

@[grind =]
theorem header_eq_schema_header (self : Raw) : self.header = self.schema.header := by
  simp [header, schema, Schema.header]

section wfColumnSize

theorem Column_size_eq_values (c : Column) : c.size = c.values.size := rfl

theorem Column_size_push (c : Column) (v : Option c.dataType.toType) : (c.push v).size = c.size + 1 := by
  show (c.values.push v).size = c.values.size + 1
  simp [Array.size_push]

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

theorem wfColumnSize_default : (default : Raw).WfColumnSize :=
  wfColumnSize_empty default

theorem wfColumnSize_ofColumns
    (columns : Array Column) (h : columns.Pairwise (fun x y => x.size = y.size)) :
    (ofColumns columns).WfColumnSize := by
  unfold ofColumns
  split
  next lt =>
    rw [Array.pairwise_iff_getElem] at h
    dsimp [WfColumnSize]
    intro c hc
    obtain ⟨n, lt', eq⟩ := Array.getElem_of_mem hc
    grind
  next => exact wfColumnSize_default

theorem mem_getColumn (self : Raw) (i : Nat) (h : i < self.ncols) : self.getColumn i h ∈ self.columns := by
  simp [getColumn]

theorem mem_getColumnByName (self : Raw) (name : String) (h : self.hasColumn name) : self.getColumnByName name h ∈ self.columns := by
  unfold getColumnByName getColumnByName?
  grind

theorem getColumnByName?_name_of_some (self : Raw) (nm : String) (c : Column) (h : self.getColumnByName? nm = some c) :
    c.name = nm := by
  grind only [getColumnByName?, → find?_some]

@[simp]
theorem getColumnByName_name (self : Raw) (nm : String) (h : self.hasColumn nm) :
    (self.getColumnByName nm h).name = nm := by
  apply getColumnByName?_name_of_some self nm _
  unfold getColumnByName
  grind only [= Option.some_get]

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
  unfold selectColumnsByMask
  exact wfColumnSize_selectColumns self _ hwf

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
  grind only [mem_unattach]

theorem wfColumnSize_selectMany {α} (self : Raw) (schema : Schema)
    (project : Row → (n : Nat) → n < self.nrows → Array α)
    (result : Row → α → Row)
    (h₁ : ∀ row a, (result row a).schema = schema)
    (h₂ : self.WfColumnSize) :
    (self.selectMany schema project result h₁ h₂).WfColumnSize := by
  apply wfColumnSize_ofRows
  intro row hrow
  grind only [= mem_map]

theorem wfColumnSize_dropna (self : Raw) (h : self.WfColumnSize) : (dropna self h).WfColumnSize := by
  unfold dropna
  exact wfColumnSize_tfilter self _ h

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

theorem wfColumnSize_count
    (self : Raw) (column : String) (h : self.hasColumn column) : (count self column h).WfColumnSize := by
  unfold count
  apply wfColumnSize_ofColumns
  simp [Array.Pairwise, Column.size, HashMap.size_valuesArray]

theorem wfColumnSize_bin? (self result : Raw) (column : String) (n : Nat)
    (h : bin? self column n = .ok result) :
    result.WfColumnSize := by
  unfold bin? at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  dsimp at h
  split at h <;> try contradiction
  simp only [pure, Except.pure, Except.ok.injEq] at h
  rw [←h]
  apply wfColumnSize_ofColumns
  simp [Array.Pairwise, Column.size, HashMap.size_valuesArray]

end wfColumnSize

@[grind =]
theorem renameColumn_eq_of_not_hasColumn (self : Raw) (oldName newName : String) (h : ¬self.hasColumn oldName) :
    renameColumn self oldName newName = self := by
  unfold renameColumn
  simp only [Raw.ext_iff, and_true]
  grind [hasColumn]

section schema

theorem default_schema : (default : Raw).schema = (default : Schema) := by
  simp [default]

theorem ofColumns_schema (columns : Array Column) :
    (ofColumns columns).schema = Schema.ofSpecs (columns.map Column.spec) := by
  unfold ofColumns
  split
  next => simp [Raw.schema, Schema.ofSpecs, Column.spec]
  next h =>
    have eq : columns = #[] := by grind
    simp only [default_schema, Schema.ofSpecs, eq, List.map_toArray, List.map_nil, Schema.ext_iff]
    rfl

theorem selectColumns_schema (self : Raw) (ns : Array (Fin self.ncols)) :
    (selectColumns self ns).schema = Schema.ofSpecs (ns.map fun i => (self.getColumn i.val i.isLt).spec) := by
  simp [Raw.selectColumns, Raw.schema, Schema.ofSpecs, Schema.ext_iff, Column.spec]

theorem selectColumnsByMask_schema (self : Raw) (mask : Vector Bool self.ncols) :
    letI ns := (Array.finRange self.ncols).filter fun i => mask[i.val]
    (selectColumnsByMask self mask).schema = (selectColumns self ns).schema := by
  rfl

theorem selectColumnsByName_schema (self : Raw) (names : Array String)
    (h : ∀ name ∈ names, self.hasColumn name) :
    (selectColumnsByName self names h).schema =
      Schema.ofSpecs (names.attach.map fun nm => (self.getColumnByName nm.val (h nm.val nm.property)).spec) := by
  simp [Raw.selectColumnsByName, Raw.schema, Schema.ofSpecs, Schema.ext_iff, Column.spec]

theorem take_schema (self : Raw) (n : Nat) :
    (take self n).schema = self.schema := by
  simp [Raw.take, Raw.schema, Schema.ext_iff]

theorem addRow_schema (self : Raw) (row : Row) (h : row.schema = self.schema) :
    (addRow self row h).schema = self.schema := by
  simp only [schema, addRow, ncols, getColumn, map_ofFn, Schema.mk.injEq, Array.ext_iff, size_ofFn,
    size_map, getElem_ofFn, Function.comp_apply, Column.push_name, Column.push_dataType,
    getElem_map, Prod.mk.injEq, true_and]
  grind only

theorem addRows_schema (self : Raw) (rows : Array Row) (h : ∀ row ∈ rows, row.schema = self.schema) :
    (addRows self rows h).schema = self.schema := by
  simp only [schema, addRows, ncols, getColumn, Fin.getElem_fin, map_ofFn, Schema.mk.injEq,
    Array.ext_iff, size_ofFn, size_map, getElem_ofFn, Function.comp_apply, getElem_map,
    Prod.mk.injEq, true_and]
  grind only

theorem ofRows_schema (schema : Schema) (rows : Array Row) (h : ∀ row ∈ rows, row.schema = schema) :
    (ofRows schema rows h).schema = schema := by
  simp [ofRows, empty_schema, addRows_schema]

theorem addColumn_schema (self : Raw) (column : Column) :
    (addColumn self column).schema = self.schema.push column.spec := by
  simp [Raw.addColumn, Raw.schema, Schema.push, Schema.ofSpecs, Column.spec]

theorem buildColumn_schema {α} [DataType.OfType α] (self : Raw) (name : String) (f : Row → Option α)
    (h : self.WfColumnSize) :
    (buildColumn self name f h).schema = self.schema.push (name, DataType.OfType.dataType α) := by
  simp [Raw.buildColumn, Raw.addColumn, Raw.schema, Column.ofRawValues, Schema.push, Schema.ofSpecs]

theorem replaceColumn_schema (self : Raw) (column : Column) :
    (replaceColumn self column).schema = self.schema.replace column.name column.dataType :=
  Schema.ext (by
    dsimp only [Raw.replaceColumn, Raw.schema, Schema.replace]
    refine Array.ext ?_ ?_
    · simp [Array.size_map]
    · grind only [= getElem_map, = Schema.ofSpecs_specs])

theorem transformColumn_schema {α} [DataType.OfType α] (self : Raw) (colName : String) (hcol : self.hasColumn colName)
    (f : Option ((getColumnByName self colName hcol).dataType.toType) → Option α) :
    (transformColumn self colName hcol f).schema = self.schema.replace colName (DataType.OfType.dataType α) :=
  Schema.ext (by
    dsimp only [Raw.transformColumn, Raw.replaceColumn, Raw.schema, Schema.replace]
    refine Array.ext ?_ ?_
    · simp [Array.size_map]
    · intro i hi₁ hi₂
      have hi₁' : i < self.columns.size := by simpa [Array.size_map] using hi₁
      simp only [Array.getElem_map, Column.mapValues_name, getColumnByName_name]
      by_cases h : (self.columns[i]'hi₁').name = colName <;> simp [h, Column.mapValues])

theorem selectRows_schema (self : Raw) (ns : Array (Fin self.nrows)) (h : self.WfColumnSize) :
    (selectRows self ns h).schema = self.schema := by
  simp [Raw.selectRows, ofRows_schema]

theorem selectRowsByMask_schema (self : Raw) (mask : Vector Bool self.nrows) (h : self.WfColumnSize) :
    (selectRowsByMask self mask h).schema = self.schema := by
  simp [Raw.selectRowsByMask]
  rw [selectRows_schema]

theorem tfilter_schema (self : Raw) (p : Row → Bool) (h : self.WfColumnSize) :
    (tfilter self p h).schema = self.schema := by
  simp [Raw.tfilter, ofRows_schema]

theorem dropColumn_schema (self : Raw) (name : String) :
    (dropColumn self name).schema = self.schema.filterByName (· ≠ name) :=
  Schema.ext (by
    dsimp only [Raw.dropColumn, Raw.schema, Schema.filterByName]
    rw [Array.filter_map, Schema.ofSpecs_specs]
    congr)

theorem dropColumns_schema (self : Raw) (names : Array String) :
    (dropColumns self names).schema = self.schema.filterByName (· ∉ names) :=
  Schema.ext (by
    dsimp only [Raw.dropColumns, Raw.schema, Schema.filterByName]
    rw [Array.filter_map, Schema.ofSpecs_specs]
    congr)

theorem hcat_schema (self other : Raw) :
    (hcat self other).schema = self.schema ++ other.schema := by
  simp [Raw.hcat, Raw.schema, Schema.append_def]

theorem vcat_schema (self other : Raw) (h : self.schema = other.schema) :
    (vcat self other h).schema = self.schema := by
  simp only [schema, vcat, ncols, getColumn, map_ofFn, Schema.mk.injEq, Array.ext_iff, size_ofFn,
    size_map, getElem_ofFn, Function.comp_apply, Column.concat_name, Column.concat_dataType,
    getElem_map, Prod.mk.injEq, true_and]
  grind only

theorem renameColumn_schema_eq_rename (self : Raw) (oldName newName : String) :
    (renameColumn self oldName newName).schema = self.schema.rename oldName newName :=
  Schema.ext (by
    dsimp only [Raw.renameColumn, Raw.schema, Schema.rename]
    refine Array.ext ?_ ?_
    · simp [Array.size_map]
    · intro i hi₁ hi₂
      have hi₁' : i < self.columns.size := by simpa [Array.size_map] using hi₁
      simp only [Array.getElem_map]
      by_cases h : (self.columns[i]'hi₁').name = oldName <;> simp [h])

theorem renameColumn_schema_of_hasColumn (self : Raw) (oldName newName : String) (_h : self.hasColumn oldName) :
    (renameColumn self oldName newName).schema = self.schema.rename oldName newName :=
  renameColumn_schema_eq_rename self oldName newName

theorem renameColumn_schema_of_not_hasColumn (self : Raw) (oldName newName : String) (h : ¬self.hasColumn oldName) :
    (renameColumn self oldName newName).schema = self.schema := by
  rw [renameColumn_eq_of_not_hasColumn self oldName newName h]

theorem renameColumn_schema (self : Raw) (oldName newName : String) :
    (renameColumn self oldName newName).schema = self.schema.rename oldName newName :=
  renameColumn_schema_eq_rename self oldName newName

theorem select_schema (self : Raw) (schema' : Schema) (f : Row → (n : Nat) → n < self.nrows → Row)
    (h₁ : ∀ row n h, (f row n h).schema = schema') (h₂ : self.WfColumnSize) :
    (self.select schema' f h₁ h₂).schema = schema' := by
  simp [Raw.select, ofRows_schema]

theorem selectMany_schema {α} (self : Raw) (schema : Schema)
    (project : Row → (n : Nat) → n < self.nrows → Array α)
    (result : Row → α → Row)
    (h₁ : ∀ row a, (result row a).schema = schema)
    (h₂ : self.WfColumnSize) :
    (self.selectMany schema project result h₁ h₂).schema = schema := by
  simp [Raw.selectMany, ofRows_schema]

theorem dropna_schema (self : Raw) (h : self.WfColumnSize) :
    (dropna self h).schema = self.schema := by
  simp [Raw.dropna, tfilter_schema]

-- `fillna_schema` can replace multiple columns with the same name but different data types
-- if the table is not well-formed.
-- theorem fillna_schema (self : Raw) (column : String) (h₁ : self.hasColumn column)
--     (replacement : (getColumnByName self column h₁).dataType.toType) :
--     (self.fillna column h₁ replacement).schema = self.schema := by
--   sorry

theorem count_schema (self : Raw) (column : String) (h : self.hasColumn column) :
    (count self column h).schema = Schema.ofSpecs #[("value", (self.getColumnByName column h).dataType), ("count", DataType.nat)] := by
  unfold Raw.count Raw.ofColumns
  simp [Raw.schema, Schema.ofSpecs]

theorem bin?_schema (self result : Raw) (column : String) (n : Nat)
    (h : bin? self column n = .ok result) :
    result.schema = Schema.ofSpecs #[("group", DataType.string), ("count", DataType.nat)] := by
  unfold bin? at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  dsimp at h
  split at h <;> try contradiction
  simp only [pure, Except.pure, Except.ok.injEq] at h
  rw [←h]
  simp [Raw.schema, Raw.ofColumns, Schema.ofSpecs]

end schema

section wfColumnNames

theorem wfColumnNames_iff_schema_wf (self : Raw) : self.WfColumnNames ↔ self.schema.Wf := by
  apply Iff.intro
  . intro h i j ne
    have := h ⟨i, by simpa using i.isLt⟩ ⟨j, by simpa using j.isLt⟩ (by grind)
    grind only [usr Fin.isLt, = schema_getName_eq_getColumn_name]
  . intro h i j ne
    have := h ⟨i, by simp⟩ ⟨j, by simp⟩ (by grind)
    grind only [= schema_getName_eq_getColumn_name]

theorem wfColumnNames_empty (schema : Schema) (hwf : schema.Wf) : (empty schema).WfColumnNames := by
  simpa [wfColumnNames_iff_schema_wf, empty_schema] using hwf

theorem wfColumnNames_default : (default : Raw).WfColumnNames :=
  wfColumnNames_empty default (Schema.wf_default)

theorem wfColumnNames_ofColumns (columns : Array Column)
    (hnames : columns.Pairwise (fun x y => x.name ≠ y.name)) :
    (ofColumns columns).WfColumnNames := by
  rw [wfColumnNames_iff_schema_wf, ofColumns_schema, Schema.wf_iff_pairwise, Schema.ofSpecs_specs]
  simpa [Array.size_map, Array.pairwise_iff_getElem, Column.spec] using hnames

@[simp, grind =]
theorem selectColumns_ncols (self : Raw) (ns : Array (Fin self.ncols)) :
    (selectColumns self ns).ncols = ns.size := by
  simp [Raw.selectColumns, Raw.ncols]

@[simp, grind =]
theorem selectColumns_getColumn (self : Raw) (ns : Array (Fin self.ncols)) (i : Nat) (h : i < ns.size) :
    (selectColumns self ns).getColumn i (selectColumns_ncols self ns ▸ h) = self.getColumn ns[i].val ns[i].isLt := by
  simp [selectColumns, getColumn]

theorem wfColumnNames_selectColumns (self : Raw) (ns : Array (Fin self.ncols))
    (hwf : self.WfColumnNames)
    (hinj : ns.Nodup) :
    (selectColumns self ns).WfColumnNames := by
  intro i j lt
  have hi : i < ns.size := by grind
  have hj : j < ns.size := by grind
  rw [selectColumns_getColumn self ns i hi, selectColumns_getColumn self ns j hj]
  rw [Array.Nodup, Array.pairwise_iff_getElem] at hinj
  cases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne (hinj i j hi hj lt)) with
  | inl lt => exact hwf ns[i] ns[j] lt
  | inr gt => exact (hwf ns[j] ns[i] gt).symm

theorem wfColumnNames_selectColumnsByMask (self : Raw) (mask : Vector Bool self.ncols)
    (hwf : self.WfColumnNames) :
    (selectColumnsByMask self mask).WfColumnNames := by
  unfold selectColumnsByMask
  exact wfColumnNames_selectColumns self _ hwf (Array.Nodup.filter _ (Array.Nodup.finRange _))

@[simp, grind =]
theorem selectColumnsByName_ncols (self : Raw) (names : Array String) (h : ∀ name ∈ names, self.hasColumn name) :
    (selectColumnsByName self names h).ncols = names.size := by
  simp [Raw.selectColumnsByName, Raw.ncols]

@[simp, grind =]
theorem selectColumnsByName_getColumn_name (self : Raw) (names : Array String) (h : ∀ name ∈ names, self.hasColumn name)
    (i : Nat) (hi : i < names.size) :
    ((selectColumnsByName self names h).getColumn i (selectColumnsByName_ncols self names h ▸ hi)).name = names[i] := by
  simp [selectColumnsByName, getColumn]

theorem wfColumnNames_selectColumnsByName (self : Raw) (names : Array String)
    (h : ∀ name ∈ names, self.hasColumn name)
    (hdupfree : names.Nodup) :
    (selectColumnsByName self names h).WfColumnNames := by
  intro i j lt
  have hi : i < names.size := by grind
  have hj : j < names.size := by grind
  rw [selectColumnsByName_getColumn_name self names h i.val hi, selectColumnsByName_getColumn_name self names h j.val hj]
  rw [Array.Nodup, Array.pairwise_iff_getElem] at hdupfree
  exact hdupfree i j hi hj lt

theorem wfColumnNames_take (self : Raw) (n : Nat) (hwf : self.WfColumnNames) :
    (take self n).WfColumnNames := by
  simpa [wfColumnNames_iff_schema_wf, take_schema] using (wfColumnNames_iff_schema_wf self).mp hwf

theorem wfColumnNames_addRow (self : Raw) (row : Row) (h : row.schema = self.schema)
    (hwf : self.WfColumnNames) :
    (addRow self row h).WfColumnNames := by
  simpa [wfColumnNames_iff_schema_wf, addRow_schema] using (wfColumnNames_iff_schema_wf self).mp hwf

theorem wfColumnNames_addRows (self : Raw) (rows : Array Row) (h : ∀ row ∈ rows, row.schema = self.schema)
    (hwf : self.WfColumnNames) :
    (addRows self rows h).WfColumnNames := by
  simpa [wfColumnNames_iff_schema_wf, addRows_schema] using (wfColumnNames_iff_schema_wf self).mp hwf

theorem wfColumnNames_ofRows (schema : Schema) (rows : Array Row) (h : ∀ row ∈ rows, row.schema = schema)
    (hwf : schema.Wf) :
    (ofRows schema rows h).WfColumnNames := by
  simpa [wfColumnNames_iff_schema_wf, ofRows_schema] using hwf

theorem wfColumnNames_addColumn (self : Raw) (column : Column)
    (hwf : self.WfColumnNames)
    (hfresh : ∀ (i : Fin self.ncols), (self.getColumn i.val i.isLt).name ≠ column.name) :
    (addColumn self column).WfColumnNames := by
  rw [wfColumnNames_iff_schema_wf (addColumn self column), addColumn_schema]
  exact Schema.wf_push ((wfColumnNames_iff_schema_wf self).mp hwf) fun i => by
    have isLt : i.val < self.ncols := by simpa [schema_size_eq] using i.isLt
    have eqName : self.schema.getName i.val i.isLt = (self.getColumn i.val isLt).name := by
      rw [schema_getName_eq_getColumn_name]
    simpa [eqName, Column.spec] using hfresh ⟨i, isLt⟩

theorem wfColumnNames_buildColumn {α} [DataType.OfType α] (self : Raw) (name : String) (f : Row → Option α)
    (h : self.WfColumnSize)
    (hwf : self.WfColumnNames)
    (hfresh : ∀ (i : Fin self.ncols), (self.getColumn i.val i.isLt).name ≠ name) :
    (buildColumn self name f h).WfColumnNames := by
  simpa [buildColumn_schema] using wfColumnNames_addColumn self _ hwf hfresh

theorem wfColumnNames_replaceColumn (self : Raw) (column : Column)
    (hwf : self.WfColumnNames)
    (_hsize : column.size = self.nrows) :
    (replaceColumn self column).WfColumnNames := by
  rw [wfColumnNames_iff_schema_wf (replaceColumn self column)]
  rw [replaceColumn_schema]
  exact Schema.wf_replace ((wfColumnNames_iff_schema_wf self).mp hwf)

theorem wfColumnNames_transformColumn {α} [DataType.OfType α] (self : Raw) (name : String)
    (hcol : self.hasColumn name)
    (f : Option ((getColumnByName self name hcol).dataType.toType) → Option α)
    (hwf : self.WfColumnNames) :
    (transformColumn self name hcol f).WfColumnNames := by
  rw [wfColumnNames_iff_schema_wf (transformColumn self name hcol f)]
  rw [transformColumn_schema]
  exact Schema.wf_replace ((wfColumnNames_iff_schema_wf self).mp hwf)

theorem wfColumnNames_selectRows (self : Raw) (ns : Array (Fin self.nrows)) (h : self.WfColumnSize)
    (hwf : self.WfColumnNames) :
    (selectRows self ns h).WfColumnNames := by
  simpa [wfColumnNames_iff_schema_wf, selectRows_schema] using (wfColumnNames_iff_schema_wf self).mp hwf

theorem wfColumnNames_selectRowsByMask (self : Raw) (mask : Vector Bool self.nrows) (h : self.WfColumnSize)
    (hwf : self.WfColumnNames) :
    (selectRowsByMask self mask h).WfColumnNames := by
  simpa [wfColumnNames_iff_schema_wf, selectRowsByMask_schema] using (wfColumnNames_iff_schema_wf self).mp hwf

theorem wfColumnNames_tfilter (self : Raw) (p : Row → Bool) (h : self.WfColumnSize)
    (hwf : self.WfColumnNames) :
    (tfilter self p h).WfColumnNames := by
  simpa [wfColumnNames_iff_schema_wf, tfilter_schema] using (wfColumnNames_iff_schema_wf self).mp hwf

theorem wfColumnNames_dropColumn (self : Raw) (name : String) (hwf : self.WfColumnNames) :
    (dropColumn self name).WfColumnNames := by
  rw [wfColumnNames_iff_schema_wf (dropColumn self name), dropColumn_schema]
  exact Schema.wf_filterByName ((wfColumnNames_iff_schema_wf self).mp hwf)

theorem wfColumnNames_dropColumns (self : Raw) (names : Array String) (hwf : self.WfColumnNames) :
    (dropColumns self names).WfColumnNames := by
  rw [wfColumnNames_iff_schema_wf (dropColumns self names), dropColumns_schema]
  exact Schema.wf_filterByName ((wfColumnNames_iff_schema_wf self).mp hwf)

theorem wfColumnNames_vcat (self other : Raw) (hschema : self.schema = other.schema)
    (hwf : self.WfColumnNames) :
    (vcat self other hschema).WfColumnNames := by
  simpa [wfColumnNames_iff_schema_wf, vcat_schema] using (wfColumnNames_iff_schema_wf self).mp hwf

theorem wfColumnNames_hcat (self other : Raw)
    (hwf₁ : self.WfColumnNames) (hwf₂ : other.WfColumnNames)
    (hdisjoint : self.header.Disjoint other.header) :
    (hcat self other).WfColumnNames := by
  rw [wfColumnNames_iff_schema_wf (hcat self other)]
  rw [hcat_schema]
  have hs₁ : self.columns.size = self.schema.size := by simp [Raw.schema, Schema.size]
  have hs₂ : other.columns.size = other.schema.size := by simp [Raw.schema, Schema.size]
  exact Schema.wf_concat
    ((wfColumnNames_iff_schema_wf self).mp hwf₁)
    ((wfColumnNames_iff_schema_wf other).mp hwf₂)
    (by simpa [header_eq_schema_header] using hdisjoint)

theorem wfColumnNames_renameColumn (self : Raw) (oldName newName : String)
    (hwf : self.WfColumnNames)
    (hfresh :
      ∀ (i : Fin self.ncols),
        (self.getColumn i.val i.isLt).name ≠ newName ∨ (self.getColumn i.val i.isLt).name = oldName) :
    (renameColumn self oldName newName).WfColumnNames := by
  rw [wfColumnNames_iff_schema_wf (renameColumn self oldName newName)]
  rw [renameColumn_schema_eq_rename]
  have hs : self.columns.size = self.schema.size := by simp [Raw.schema, Schema.size]
  exact Schema.wf_rename ((wfColumnNames_iff_schema_wf self).mp hwf) fun i => by
    have isLt : i.val < self.ncols := by simpa [schema_size_eq] using i.isLt
    have eqName : self.schema.getName i.val i.isLt = (self.getColumn i.val isLt).name := by
      rw [schema_getName_eq_getColumn_name]
    simpa [eqName, Column.spec] using hfresh ⟨i, isLt⟩

theorem wfColumnNames_select (self : Raw) (schema' : Schema) (f : Row → (n : Nat) → n < self.nrows → Row)
    (h₁ : ∀ row n h, (f row n h).schema = schema')
    (h₂ : self.WfColumnSize)
    (hwf_schema : schema'.Wf) :
    (self.select schema' f h₁ h₂).WfColumnNames := by
  simpa [wfColumnNames_iff_schema_wf, select_schema] using hwf_schema

theorem wfColumnNames_selectMany {α} (self : Raw) (schema : Schema)
    (project : Row → (n : Nat) → n < self.nrows → Array α)
    (result : Row → α → Row)
    (h₁ : ∀ row a, (result row a).schema = schema)
    (h₂ : self.WfColumnSize)
    (hwf_schema : schema.Wf) :
    (self.selectMany schema project result h₁ h₂).WfColumnNames := by
  simpa [wfColumnNames_iff_schema_wf, selectMany_schema] using hwf_schema

theorem wfColumnNames_dropna (self : Raw) (h : self.WfColumnSize)
    (hwf : self.WfColumnNames) :
    (dropna self h).WfColumnNames := by
  simpa [wfColumnNames_iff_schema_wf, dropna_schema] using (wfColumnNames_iff_schema_wf self).mp hwf

theorem wfColumnNames_fillna (self : Raw) (column : String) (h₁ : self.hasColumn column)
    (replacement : (getColumnByName self column h₁).dataType.toType)
    (hwf : self.WfColumnNames) :
    (fillna self column h₁ replacement).WfColumnNames := by
  rw [wfColumnNames_iff_schema_wf (fillna self column h₁ replacement)]
  simp only [fillna, replaceColumn_schema]
  exact Schema.wf_replace ((wfColumnNames_iff_schema_wf self).mp hwf)

theorem wfColumnNames_count (self : Raw) (column : String) (h : self.hasColumn column) :
    (count self column h).WfColumnNames := by
  rw [wfColumnNames_iff_schema_wf (count self column h)]
  rw [count_schema]
  intro i j ne
  grind

theorem wfColumnNames_bin? (self result : Raw) (column : String) (n : Nat)
    (h : bin? self column n = .ok result) :
    result.WfColumnNames := by
  rw [wfColumnNames_iff_schema_wf result, bin?_schema self result column n h]
  intro i j ne
  grind

end wfColumnNames

section hasColumn

theorem hasColumn_selectColumns_iff (self : Raw) (ns : Array (Fin self.ncols)) (name : String) :
    (self.selectColumns ns).hasColumn name ↔
      ∃ (i : Fin self.ncols), i ∈ ns ∧ (self.getColumn i.val i.isLt).name = name := by
  grind [hasColumn, selectColumns, Array.mem_iff_getElem]

theorem hasColumn_selectColumnsByMask_iff (self : Raw) (mask : Vector Bool self.ncols) (name : String) :
    (self.selectColumnsByMask mask).hasColumn name ↔ ∃ (i : Nat) (h : i < self.ncols), mask[i] = true ∧ (self.getColumn i h).name = name := by
  dsimp [selectColumnsByMask]
  simp only [hasColumn_selectColumns_iff, mem_filter]
  simp only [mem_iff_getElem, getElem_finRange, Fin.cast_mk, size_finRange]
  grind

theorem hasColumn_selectColumnsByName_iff (self : Raw) (names : Array String)
    (h : ∀ name ∈ names, self.hasColumn name) (name : String) :
    (self.selectColumnsByName names h).hasColumn name ↔ name ∈ names := by
  rw [hasColumn_iff_schema_hasName, selectColumnsByName_schema, Schema.ofSpecs_hasName_iff]
  grind [Column.spec, getColumnByName_name, mem_iff_getElem]

theorem hasColumn_take_iff (self : Raw) (n : Nat) (name : String) :
    (self.take n).hasColumn name ↔ self.hasColumn name := by
  simp [Raw.hasColumn_iff_schema_hasName, take_schema]

theorem hasColumn_addRow_iff (self : Raw) (row : Row) (h : row.schema = self.schema) (name : String) :
    (self.addRow row h).hasColumn name ↔ self.hasColumn name := by
  simp [Raw.hasColumn_iff_schema_hasName, addRow_schema]

theorem hasColumn_addRows_iff (self : Raw) (rows : Array Row)
    (h : ∀ row ∈ rows, row.schema = self.schema) (name : String) :
    (self.addRows rows h).hasColumn name ↔ self.hasColumn name := by
  simp [Raw.hasColumn_iff_schema_hasName, addRows_schema]

theorem hasColumn_ofRows_iff (schema : Schema) (rows : Array Row)
    (h : ∀ row ∈ rows, row.schema = schema) (name : String) :
    (Raw.ofRows schema rows h).hasColumn name ↔ schema.hasName name := by
  simp [Raw.hasColumn_iff_schema_hasName, ofRows_schema]

theorem hasColumn_addColumn_iff (self : Raw) (column : Column) (name : String) :
    (self.addColumn column).hasColumn name ↔ self.hasColumn name ∨ column.name = name := by
  simp [Raw.hasColumn_iff_schema_hasName, addColumn_schema, Column.spec]

theorem hasColumn_buildColumn_iff {α} [DataType.OfType α] (self : Raw) (colName : String)
    (f : Row → Option α) (h : self.WfColumnSize) (name : String) :
    (self.buildColumn colName f h).hasColumn name ↔ self.hasColumn name ∨ colName = name := by
  simp [Raw.hasColumn_iff_schema_hasName, buildColumn_schema, Schema.push_hasName_iff]

theorem hasColumn_replaceColumn_iff (self : Raw) (column : Column) (name : String) :
    (self.replaceColumn column).hasColumn name ↔ self.hasColumn name := by
  simp [Raw.hasColumn_iff_schema_hasName, replaceColumn_schema]

theorem hasColumn_transformColumn_iff {α} [DataType.OfType α] (self : Raw) (colName : String) (hcol : self.hasColumn colName)
    (f : Option ((self.getColumnByName colName hcol).dataType.toType) → Option α) (name : String) :
    (self.transformColumn colName hcol f).hasColumn name ↔ self.hasColumn name := by
  simp [Raw.hasColumn_iff_schema_hasName, transformColumn_schema]

theorem hasColumn_selectRows_iff (self : Raw) (ns : Array (Fin self.nrows)) (h : self.WfColumnSize) (name : String) :
    (self.selectRows ns h).hasColumn name ↔ self.hasColumn name := by
  simp [Raw.hasColumn_iff_schema_hasName, selectRows_schema]

theorem hasColumn_selectRowsByMask_iff (self : Raw) (mask : Vector Bool self.nrows) (h : self.WfColumnSize) (name : String) :
    (self.selectRowsByMask mask h).hasColumn name ↔ self.hasColumn name := by
  simp [Raw.hasColumn_iff_schema_hasName, selectRowsByMask_schema]

theorem hasColumn_tfilter_iff (self : Raw) (p : Row → Bool) (h : self.WfColumnSize) (name : String) :
    (self.tfilter p h).hasColumn name ↔ self.hasColumn name := by
  simp [Raw.hasColumn_iff_schema_hasName, tfilter_schema]

theorem hasColumn_dropColumn_iff (self : Raw) (colName : String) (name : String) :
    (self.dropColumn colName).hasColumn name ↔ self.hasColumn name ∧ name ≠ colName := by
  simp [Raw.hasColumn_iff_schema_hasName, dropColumn_schema, Schema.filterByName_hasName_iff]

theorem hasColumn_dropColumns_iff (self : Raw) (names : Array String) (name : String) :
    (self.dropColumns names).hasColumn name ↔ self.hasColumn name ∧ name ∉ names := by
  simp [Raw.hasColumn_iff_schema_hasName, dropColumns_schema, Schema.filterByName_hasName_iff]

theorem hasColumn_vcat_iff (self other : Raw) (h : self.schema = other.schema) (name : String) :
    (self.vcat other h).hasColumn name ↔ self.hasColumn name := by
  simp [Raw.hasColumn_iff_schema_hasName, vcat_schema]

theorem hasColumn_hcat_iff (self other : Raw) (name : String) :
    (self.hcat other).hasColumn name ↔ self.hasColumn name ∨ other.hasColumn name := by
  simp [Raw.hasColumn_iff_schema_hasName, hcat_schema, Schema.concat_hasName_iff]

theorem hasColumn_renameColumn_oldName_iff (self : Raw) {oldName newName : String} :
    (self.renameColumn oldName newName).hasColumn oldName ↔ oldName = newName ∧ self.hasColumn oldName := by
  simp [Raw.hasColumn_iff_schema_hasName, renameColumn_schema, Schema.rename_not_hasName_oldName_iff]

theorem hasColumn_renameColumn_newName_iff (self : Raw) (oldName newName : String) :
    (self.renameColumn oldName newName).hasColumn newName ↔ self.hasColumn newName ∨ self.hasColumn oldName := by
  simp [Raw.hasColumn_iff_schema_hasName, renameColumn_schema, Schema.rename_hasName_newName_iff]

theorem hasColumn_renameColumn_of_ne_iff (self : Raw) {oldName newName name : String}
    (h₁ : name ≠ oldName) (h₂ : name ≠ newName) :
    (self.renameColumn oldName newName).hasColumn name ↔ self.hasColumn name := by
  simp [Raw.hasColumn_iff_schema_hasName, renameColumn_schema, Schema.rename_hasName_iff_of_ne, h₁, h₂]

theorem hasColumn_renameColumns_iff (self : Raw) (renames : Array (String × String)) (name : String) :
    (self.renameColumns renames).hasColumn name ↔ (renames.foldl (init := self) fun t r => t.renameColumn r.1 r.2).hasColumn name := by
  rfl

theorem hasColumn_select_iff (self : Raw) (schema' : Schema)
    (f : Row → (n : Nat) → n < self.nrows → Row)
    (h₁ : ∀ row n h, (f row n h).schema = schema') (h₂ : self.WfColumnSize) (name : String) :
    (self.select schema' f h₁ h₂).hasColumn name ↔ schema'.hasName name := by
  simp [Raw.hasColumn_iff_schema_hasName, select_schema]

theorem hasColumn_selectMany_iff {α} (self : Raw) (schema' : Schema)
    (project : Row → (n : Nat) → n < self.nrows → Array α)
    (result : Row → α → Row)
    (h₁ : ∀ row a, (result row a).schema = schema')
    (h₂ : self.WfColumnSize) (name : String) :
    (self.selectMany schema' project result h₁ h₂).hasColumn name ↔ schema'.hasName name := by
  simp [Raw.hasColumn_iff_schema_hasName, selectMany_schema]

theorem hasColumn_dropna_iff (self : Raw) (h : self.WfColumnSize) (name : String) :
    (dropna self h).hasColumn name ↔ self.hasColumn name := by
  simp [Raw.hasColumn_iff_schema_hasName, dropna_schema]

theorem hasColumn_fillna_iff (self : Raw) (column : String) (h₁ : self.hasColumn column)
    (replacement : (self.getColumnByName column h₁).dataType.toType) (name : String) :
    (self.fillna column h₁ replacement).hasColumn name ↔ self.hasColumn name := by
  apply hasColumn_replaceColumn_iff

theorem hasColumn_count_iff (self : Raw) (column : String) (h : self.hasColumn column) (name : String) :
    (self.count column h).hasColumn name ↔ name = "value" ∨ name = "count" := by
  rw [Raw.hasColumn_iff_schema_hasName, count_schema, Schema.ofSpecs_hasName_iff]
  grind

theorem hasColumn_bin?_iff (self result : Raw) (column : String) (n : Nat) (name : String)
    (h : bin? self column n = .ok result) :
    result.hasColumn name ↔ name = "group" ∨ name = "count" := by
  rw [Raw.hasColumn_iff_schema_hasName, bin?_schema self result column n h, Schema.ofSpecs_hasName_iff]
  grind

end hasColumn

end Tables.Table.Raw

end
