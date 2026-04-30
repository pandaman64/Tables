module

public import Tables.Table.Basic
import all Tables.Table.Basic
import Tables.Table.Raw.BasicLemmas
import Tables.Table.Raw.JoinLemmas
import Tables.Table.Raw.Sort

public section

namespace Tables.Table

section schema

theorem getRow_schema (self : Table) (i : Nat) (h : i < self.nrows) :
    (self.getRow i h).schema = self.schema := by
  simp [getRow, schema, Raw.getRow_schema]

theorem take_schema (self : Table) (n : Nat) (hle : n ≤ self.nrows) :
    (self.take n hle).schema = self.schema := by
  simp [Table.take, Table.schema, Raw.take_schema]

theorem selectColumns_schema (self : Table) (ns : Array (Fin self.ncols)) (hinj : ns.Nodup) :
    (self.selectColumns ns hinj).schema =
      Schema.ofSpecs (ns.map fun i => (self.getColumn i.val i.isLt).spec) := by
  simp only [schema, selectColumns, Raw.selectColumns_schema, getColumn]
  rfl

theorem selectColumns_ncols (self : Table) (ns : Array (Fin self.ncols)) (hinj : ns.Nodup) :
    (self.selectColumns ns hinj).ncols = ns.size := by
  simp [Table.selectColumns, Table.ncols, Raw.selectColumns_ncols]

theorem selectColumnsByMask_schema (self : Table) (mask : Vector Bool self.ncols) :
    letI ns := (Array.finRange self.ncols).filter fun i => mask[i.val]
    (self.selectColumnsByMask mask).schema = (self.selectColumns ns (Array.Nodup.filter _ (Array.Nodup.finRange _))).schema := by
  simp only [schema, selectColumnsByMask, Raw.selectColumnsByMask_schema, Array.size_finRange,
    selectColumns, ncols]
  rfl

theorem selectColumnsByName_schema (self : Table) (names : Array String)
    (h : ∀ name ∈ names, self.hasColumn name) (hdupfree : names.Nodup) :
    (self.selectColumnsByName names h hdupfree).schema =
      Schema.ofSpecs (names.attach.map fun nm => (self.getColumnByName nm.val (h nm.val nm.property)).spec) := by
  simp [Table.selectColumnsByName, Table.schema, Table.getColumnByName, Raw.selectColumnsByName_schema]

theorem selectColumnsByName_ncols (self : Table) (names : Array String)
    (h : ∀ name ∈ names, self.hasColumn name) (hdupfree : names.Nodup) :
    (self.selectColumnsByName names h hdupfree).ncols = names.size := by
  simp [Table.selectColumnsByName, Table.ncols, Raw.selectColumnsByName_ncols]

theorem addRow_schema (self : Table) (row : Row) (h : row.schema = self.schema) :
    (self.addRow row h).schema = self.schema := by
  simp [Table.addRow, Table.schema, Raw.addRow_schema]

theorem addRows_schema (self : Table) (rows : Array Row) (h : ∀ row ∈ rows, row.schema = self.schema) :
    (self.addRows rows h).schema = self.schema := by
  simp [Table.addRows, Table.schema, Raw.addRows_schema]

theorem ofRows_schema (schema : Schema) (rows : Array Row) (h : ∀ row ∈ rows, row.schema = schema) (hwf : schema.Wf) :
    (Table.ofRows schema rows h hwf).schema = schema := by
  simp [Table.ofRows, Table.schema, Raw.ofRows_schema]

theorem addColumn_schema (self : Table) (column : Column)
    (hsize : column.size = self.nrows)
    (hfresh : ∀ (i : Fin self.ncols), (self.getColumn i.val i.isLt).name ≠ column.name) :
    (self.addColumn column hsize hfresh).schema = self.schema.push column.spec := by
  simp [Table.addColumn, Table.schema, Raw.addColumn_schema]

theorem buildColumn_schema {α} [DataType.OfType α] (self : Table) (name : String) (f : Row → Option α)
    (hfresh : ∀ (i : Fin self.ncols), (self.getColumn i.val i.isLt).name ≠ name) :
    (self.buildColumn name f hfresh).schema = self.schema.push (name, DataType.OfType.dataType α) := by
  simp [Table.buildColumn, Table.schema, Raw.buildColumn_schema]

theorem replaceColumn_schema (self : Table) (column : Column) (hsize : column.size = self.nrows) :
    (self.replaceColumn column hsize).schema = self.schema.replace column.name column.dataType := by
  simp [Table.replaceColumn, Table.schema, Raw.replaceColumn_schema]

theorem transformColumn_schema {α} [DataType.OfType α] (self : Table) (colName : String) (hcol : self.hasColumn colName)
    (f : Option ((self.getColumnByName colName hcol).dataType.toType) → Option α) :
    (self.transformColumn colName hcol f).schema = self.schema.replace colName (DataType.OfType.dataType α) := by
  simp [Table.transformColumn, Table.schema, Raw.transformColumn_schema]

theorem selectRows_schema (self : Table) (ns : Array (Fin self.nrows)) :
    (self.selectRows ns).schema = self.schema := by
  simp [Table.selectRows, Table.schema, Raw.selectRows_schema]

theorem selectRowsByMask_schema (self : Table) (mask : Vector Bool self.nrows) :
    (self.selectRowsByMask mask).schema = self.schema := by
  simp [Table.selectRowsByMask, Table.schema, Raw.selectRowsByMask_schema]

theorem tfilter_schema (self : Table) (p : Row → Bool) :
    (self.tfilter p).schema = self.schema := by
  simp [Table.tfilter, Table.schema, Raw.tfilter_schema]

theorem dropColumn_schema (self : Table) (name : String) :
    (self.dropColumn name).schema = self.schema.filterByName (· ≠ name) := by
  simp [Table.dropColumn, Table.schema, Raw.dropColumn_schema]

theorem dropColumns_schema (self : Table) (names : Array String) :
    (self.dropColumns names).schema = self.schema.filterByName (· ∉ names) := by
  simp [Table.dropColumns, Table.schema, Raw.dropColumns_schema]

theorem vcat_schema (self other : Table) (h : self.schema = other.schema) :
    (self.vcat other h).schema = self.schema := by
  simp [Table.vcat, Table.schema, Raw.vcat_schema]

theorem hcat_schema (self other : Table)
    (hrows : self.nrows = other.nrows)
    (hdisjoint :
      ∀ (i : Fin self.ncols) (j : Fin other.ncols),
        (self.getColumn i.val i.isLt).name ≠ (other.getColumn j.val j.isLt).name) :
    (self.hcat other hrows hdisjoint).schema = self.schema ++ other.schema := by
  simp [Table.hcat, Table.schema, Raw.hcat_schema]

theorem renameColumn_schema (self : Table) (oldName newName : String)
    (hfresh :
      ∀ (i : Fin self.ncols),
        (self.getColumn i.val i.isLt).name ≠ newName ∨ (self.getColumn i.val i.isLt).name = oldName) :
    (self.renameColumn oldName newName hfresh).schema = self.schema.rename oldName newName := by
  simp [Table.renameColumn, Table.schema, Raw.renameColumn_schema]

theorem select_schema (self : Table) (schema : Schema) (f : Row → (n : Nat) → n < self.nrows → Row)
    (h₁ : ∀ row n h, (f row n h).schema = schema) (hwf_schema : schema.Wf) :
    (self.select schema f h₁ hwf_schema).schema = schema := by
  simp [Table.select, Table.schema, Raw.select_schema]

theorem selectMany_schema {α} (self : Table) (schema : Schema)
    (project : Row → (n : Nat) → n < self.nrows → Array α)
    (result : Row → α → Row)
    (h₁ : ∀ row a, (result row a).schema = schema)
    (hwf_schema : schema.Wf) :
    (self.selectMany schema project result h₁ hwf_schema).schema = schema := by
  simp [Table.selectMany, Table.schema, Raw.selectMany_schema]

theorem dropna_schema (self : Table) :
    self.dropna.schema = self.schema := by
  simp [Table.dropna, Table.schema, Raw.dropna_schema]

theorem count_schema (self : Table) (column : String) (h : self.hasColumn column) :
    (self.count column h).schema =
      Schema.ofSpecs #[("value", (self.getColumnByName column h).dataType), ("count", DataType.nat)] := by
  simp [Table.count, Table.schema, Table.getColumnByName, Raw.count_schema]

theorem bin?_schema (self result : Table) (column : String) (n : Nat) (h : self.bin? column n = .ok result) :
    result.schema = Schema.ofSpecs #[("group", DataType.string), ("count", DataType.nat)] := by
  unfold bin? at h
  split at h <;> try contradiction
  next eq =>
    simp only [Except.ok.injEq] at h
    simp [←h, schema, Raw.bin?_schema self.raw _ column n eq]

theorem distinct_schema (self : Table) :
    self.distinct.schema = self.schema := by
  simp [Table.distinct, Table.schema, Raw.distinct_schema]

theorem crossJoin_schema (self other : Table)
    (hdisjoint :
      ∀ (i : Fin self.ncols) (j : Fin other.ncols),
        (self.getColumn i.val i.isLt).name ≠ (other.getColumn j.val j.isLt).name) :
    (crossJoin self other hdisjoint).schema = self.schema ++ other.schema := by
  simp [Table.crossJoin, Table.schema, Raw.crossJoin_schema]

theorem leftJoin_schema (self other : Table) (keys : Array String)
    (hdisjoint :
      ∀ (i : Fin self.schema.size) (j : Fin (other.schema.selectNotByNames keys).size),
        self.schema.getName i.val i.isLt ≠ (other.schema.selectNotByNames keys).getName j.val j.isLt) :
    (leftJoin self other keys hdisjoint).schema = self.schema ++ other.schema.selectNotByNames keys := by
  simp [Table.leftJoin, Table.schema, Raw.leftJoin_schema]

theorem join_schema {α} [BEq α] [Hashable α] (self other : Table) (schema : Schema)
    (getKey₁ : Row → α) (getKey₂ : Row → α)
    (combine : Row → Row → Row)
    (h : ∀ r₁ r₂, (combine r₁ r₂).schema = schema) (hwf_schema : schema.Wf) :
    (join self other schema getKey₁ getKey₂ combine h hwf_schema).schema = schema := by
  simp [Table.join, Table.schema, Raw.join_schema]

theorem groupJoin_schema {α} [BEq α] [Hashable α] (self other : Table) (schema : Schema)
    (getKey₁ : Row → α) (getKey₂ : Row → α)
    (combine : Row → Raw → Row)
    (h : ∀ r₁ r₂, (combine r₁ r₂).schema = schema) (hwf_schema : schema.Wf) :
    (groupJoin self other schema getKey₁ getKey₂ combine h hwf_schema).schema = schema := by
  simp [Table.groupJoin, Table.schema, Raw.groupJoin_schema]

theorem tsort_schema (self : Table) (key : String) (order : Order) (h : self.hasColumn key) :
    (self.tsort key order h).schema = self.schema := by
  simp [Table.tsort, Table.schema, Raw.tsort_schema]

theorem sortByColumns_schema (self : Table) (keys : Array (String × Order))
    (h : ∀ key ∈ keys, self.hasColumn key.1) :
    (self.sortByColumns keys h).schema = self.schema := by
  simp [Table.sortByColumns, Table.schema, Raw.sortByColumns_schema]

theorem orderBy_schema (self : Table) (comparators : Array Comparator) :
    (self.orderBy comparators).schema = self.schema := by
  simp [Table.orderBy, Table.schema, Raw.orderBy_schema]

end schema

section hasColumn

theorem hasColumn_iff_schema_hasName (self : Table) (name : String) :
    self.hasColumn name ↔ self.schema.hasName name := by
  simp [Table.hasColumn, Table.schema, Raw.hasColumn_iff_schema_hasName]

theorem hasColumn_selectColumns_iff (self : Table) (ns : Array (Fin self.ncols)) (hinj : ns.Nodup) (name : String) :
    (self.selectColumns ns hinj).hasColumn name ↔ ∃ i ∈ ns, (self.getColumn i.val i.isLt).name = name := by
  simpa [Table.hasColumn, Table.selectColumns, getColumn] using Raw.hasColumn_selectColumns_iff self.raw ns name

theorem hasColumn_selectColumnsByMask_iff (self : Table) (mask : Vector Bool self.ncols) (name : String) :
    (self.selectColumnsByMask mask).hasColumn name ↔
      ∃ (i : Nat) (h : i < self.ncols), mask[i] = true ∧ (self.getColumn i h).name = name := by
  simpa [Table.hasColumn, Table.selectColumnsByMask, getColumn] using Raw.hasColumn_selectColumnsByMask_iff self.raw mask name

theorem hasColumn_selectColumnsByName_iff (self : Table) (names : Array String)
    (h : ∀ name ∈ names, self.hasColumn name) (hdupfree : names.Nodup) (name : String) :
    (self.selectColumnsByName names h hdupfree).hasColumn name ↔ name ∈ names := by
  simp [Table.hasColumn, Table.selectColumnsByName, Raw.hasColumn_selectColumnsByName_iff]

theorem hasColumn_take_iff (self : Table) (n : Nat) (hle : n ≤ self.nrows) (name : String) :
    (self.take n hle).hasColumn name ↔ self.hasColumn name := by
  simp [Table.hasColumn, Table.take, Raw.hasColumn_take_iff]

theorem hasColumn_addRow_iff (self : Table) (row : Row) (h : row.schema = self.schema) (name : String) :
    (self.addRow row h).hasColumn name ↔ self.hasColumn name := by
  simp [Table.hasColumn, Table.addRow, Raw.hasColumn_addRow_iff]

theorem hasColumn_addRows_iff (self : Table) (rows : Array Row)
    (h : ∀ row ∈ rows, row.schema = self.schema) (name : String) :
    (self.addRows rows h).hasColumn name ↔ self.hasColumn name := by
  simp [Table.hasColumn, Table.addRows, Raw.hasColumn_addRows_iff]

theorem hasColumn_ofRows_iff (schema : Schema) (rows : Array Row)
    (h : ∀ row ∈ rows, row.schema = schema) (hwf : schema.Wf) (name : String) :
    (Table.ofRows schema rows h hwf).hasColumn name ↔ schema.hasName name := by
  simp [Table.hasColumn, Table.ofRows, Raw.hasColumn_ofRows_iff]

theorem hasColumn_addColumn_iff (self : Table) (column : Column)
    (hsize : column.size = self.nrows)
    (hfresh : ∀ (i : Fin self.ncols), (self.getColumn i.val i.isLt).name ≠ column.name) (name : String) :
    (self.addColumn column hsize hfresh).hasColumn name ↔ self.hasColumn name ∨ column.name = name := by
  simp [Table.hasColumn, Table.addColumn, Raw.hasColumn_addColumn_iff]

theorem hasColumn_buildColumn_iff {α} [DataType.OfType α] (self : Table) (colName : String)
    (f : Row → Option α)
    (hfresh : ∀ (i : Fin self.ncols), (self.getColumn i.val i.isLt).name ≠ colName) (name : String) :
    (self.buildColumn colName f hfresh).hasColumn name ↔ self.hasColumn name ∨ colName = name := by
  simp [Table.hasColumn, Table.buildColumn, Raw.hasColumn_buildColumn_iff]

theorem hasColumn_replaceColumn_iff (self : Table) (column : Column) (hsize : column.size = self.nrows) (name : String) :
    (self.replaceColumn column hsize).hasColumn name ↔ self.hasColumn name := by
  simp [Table.hasColumn, Table.replaceColumn, Raw.hasColumn_replaceColumn_iff]

theorem hasColumn_transformColumn_iff {α} [DataType.OfType α] (self : Table) (colName : String) (hcol : self.hasColumn colName)
    (f : Option ((self.getColumnByName colName hcol).dataType.toType) → Option α) (name : String) :
    (self.transformColumn colName hcol f).hasColumn name ↔ self.hasColumn name := by
  simp [Table.hasColumn, Table.transformColumn, Raw.hasColumn_transformColumn_iff]

theorem hasColumn_selectRows_iff (self : Table) (ns : Array (Fin self.nrows)) (name : String) :
    (self.selectRows ns).hasColumn name ↔ self.hasColumn name := by
  simp [Table.hasColumn, Table.selectRows, Raw.hasColumn_selectRows_iff self.raw ns self.wfColumnSize]

theorem hasColumn_selectRowsByMask_iff (self : Table) (mask : Vector Bool self.nrows) (name : String) :
    (self.selectRowsByMask mask).hasColumn name ↔ self.hasColumn name := by
  simp [Table.hasColumn, Table.selectRowsByMask, Raw.hasColumn_selectRowsByMask_iff self.raw mask self.wfColumnSize]

theorem hasColumn_tfilter_iff (self : Table) (p : Row → Bool) (name : String) :
    (self.tfilter p).hasColumn name ↔ self.hasColumn name := by
  simp [Table.hasColumn, Table.tfilter, Raw.hasColumn_tfilter_iff self.raw p self.wfColumnSize]

theorem hasColumn_dropColumn_iff (self : Table) (colName : String) (name : String) :
    (self.dropColumn colName).hasColumn name ↔ self.hasColumn name ∧ name ≠ colName := by
  simp [Table.hasColumn, Table.dropColumn, Raw.hasColumn_dropColumn_iff]

theorem hasColumn_dropColumns_iff (self : Table) (names : Array String) (name : String) :
    (self.dropColumns names).hasColumn name ↔ self.hasColumn name ∧ name ∉ names := by
  simp [Table.hasColumn, Table.dropColumns, Raw.hasColumn_dropColumns_iff]

theorem hasColumn_vcat_iff (self other : Table) (h : self.schema = other.schema) (name : String) :
    (self.vcat other h).hasColumn name ↔ self.hasColumn name := by
  simp [Table.hasColumn, Table.vcat, Raw.hasColumn_vcat_iff self.raw other.raw h]

theorem hasColumn_hcat_iff (self other : Table)
    (hrows : self.nrows = other.nrows)
    (hdisjoint :
      ∀ (i : Fin self.ncols) (j : Fin other.ncols),
        (self.getColumn i.val i.isLt).name ≠ (other.getColumn j.val j.isLt).name) (name : String) :
    (self.hcat other hrows hdisjoint).hasColumn name ↔ self.hasColumn name ∨ other.hasColumn name := by
  simp [Table.hasColumn, Table.hcat, Raw.hasColumn_hcat_iff]

theorem hasColumn_renameColumn_oldName_iff (self : Table) (oldName newName : String)
    (hfresh :
      ∀ (i : Fin self.ncols),
        (self.getColumn i.val i.isLt).name ≠ newName ∨ (self.getColumn i.val i.isLt).name = oldName) :
    (self.renameColumn oldName newName hfresh).hasColumn oldName ↔ oldName = newName ∧ self.hasColumn oldName := by
  simp [Table.hasColumn, Table.renameColumn, Raw.hasColumn_renameColumn_oldName_iff]

theorem hasColumn_renameColumn_newName_iff (self : Table) (oldName newName : String)
    (hfresh :
      ∀ (i : Fin self.ncols),
        (self.getColumn i.val i.isLt).name ≠ newName ∨ (self.getColumn i.val i.isLt).name = oldName) :
    (self.renameColumn oldName newName hfresh).hasColumn newName ↔ self.hasColumn newName ∨ self.hasColumn oldName := by
  simp [Table.hasColumn, Table.renameColumn, Raw.hasColumn_renameColumn_newName_iff]

theorem hasColumn_renameColumn_of_ne_iff (self : Table) (oldName newName : String)
    (hfresh :
      ∀ (i : Fin self.ncols),
        (self.getColumn i.val i.isLt).name ≠ newName ∨ (self.getColumn i.val i.isLt).name = oldName)
    {name : String} (h₁ : name ≠ oldName) (h₂ : name ≠ newName) :
    (self.renameColumn oldName newName hfresh).hasColumn name ↔ self.hasColumn name := by
  simp [Table.hasColumn, Table.renameColumn, Raw.hasColumn_renameColumn_of_ne_iff, h₁, h₂]

theorem hasColumn_select_iff (self : Table) (schema : Schema)
    (f : Row → (n : Nat) → n < self.nrows → Row)
    (h₁ : ∀ row n h, (f row n h).schema = schema) (hwf_schema : schema.Wf) (name : String) :
    (self.select schema f h₁ hwf_schema).hasColumn name ↔ schema.hasName name := by
  simp [Table.hasColumn, Table.select, Raw.hasColumn_select_iff self.raw schema f h₁ self.wfColumnSize]

theorem hasColumn_selectMany_iff {α} (self : Table) (schema : Schema)
    (project : Row → (n : Nat) → n < self.nrows → Array α)
    (result : Row → α → Row)
    (h₁ : ∀ row a, (result row a).schema = schema)
    (hwf_schema : schema.Wf) (name : String) :
    (self.selectMany schema project result h₁ hwf_schema).hasColumn name ↔ schema.hasName name := by
  simp [Table.hasColumn, Table.selectMany, Raw.hasColumn_selectMany_iff self.raw schema project result h₁ self.wfColumnSize]

theorem hasColumn_dropna_iff (self : Table) (name : String) :
    self.dropna.hasColumn name ↔ self.hasColumn name := by
  simp [Table.hasColumn, Table.dropna, Raw.hasColumn_dropna_iff self.raw self.wfColumnSize]

theorem hasColumn_fillna_iff (self : Table) (column : String) (h₁ : self.hasColumn column)
    (replacement : (self.getColumnByName column h₁).dataType.toType) (name : String) :
    (self.fillna column h₁ replacement).hasColumn name ↔ self.hasColumn name := by
  simp [Table.hasColumn, Table.fillna, Raw.hasColumn_fillna_iff]

theorem hasColumn_count_iff (self : Table) (column : String) (h : self.hasColumn column) (name : String) :
    (self.count column h).hasColumn name ↔ name = "value" ∨ name = "count" := by
  simp [Table.hasColumn, Table.count, Raw.hasColumn_count_iff]

theorem hasColumn_bin?_iff (self result : Table) (column : String) (n : Nat) (name : String)
    (h : self.bin? column n = .ok result) :
    result.hasColumn name ↔ name = "group" ∨ name = "count" := by
  rw [hasColumn_iff_schema_hasName]
  rw [bin?_schema self result column n h]
  rw [Schema.ofSpecs_hasName_iff]
  grind

theorem hasColumn_distinct_iff (self : Table) (name : String) :
    self.distinct.hasColumn name ↔ self.hasColumn name := by
  simp [Table.hasColumn, Table.distinct, Raw.distinct_hasColumn_iff self.raw self.wfColumnSize]

theorem hasColumn_crossJoin_iff (self other : Table)
    (hdisjoint :
      ∀ (i : Fin self.ncols) (j : Fin other.ncols),
        (self.getColumn i.val i.isLt).name ≠ (other.getColumn j.val j.isLt).name) (name : String) :
    (crossJoin self other hdisjoint).hasColumn name ↔ self.hasColumn name ∨ other.hasColumn name := by
  simpa [Table.hasColumn, Table.crossJoin, getColumn] using
    (Raw.crossJoin_hasColumn_iff self.raw other.raw self.wfColumnSize other.wfColumnSize name)

theorem hasColumn_leftJoin_iff (self other : Table) (keys : Array String)
    (hdisjoint :
      ∀ (i : Fin self.schema.size) (j : Fin (other.schema.selectNotByNames keys).size),
        self.schema.getName i.val i.isLt ≠ (other.schema.selectNotByNames keys).getName j.val j.isLt)
    (name : String) :
    (leftJoin self other keys hdisjoint).hasColumn name ↔
      self.hasColumn name ∨ (other.hasColumn name ∧ name ∉ keys) := by
  simp [Table.hasColumn, Table.leftJoin, Raw.leftJoin_hasColumn_iff self.raw other.raw keys self.wfColumnSize other.wfColumnSize]

theorem hasColumn_join_iff {α} [BEq α] [Hashable α] (self other : Table) (schema : Schema)
    (getKey₁ : Row → α) (getKey₂ : Row → α)
    (combine : Row → Row → Row)
    (h : ∀ r₁ r₂, (combine r₁ r₂).schema = schema) (hwf_schema : schema.Wf) (name : String) :
    (join self other schema getKey₁ getKey₂ combine h hwf_schema).hasColumn name ↔ schema.hasName name := by
  simp [Table.hasColumn, Table.join, Raw.join_hasColumn_iff self.raw other.raw schema getKey₁ getKey₂ combine self.wfColumnSize other.wfColumnSize h]

theorem hasColumn_groupJoin_iff {α} [BEq α] [Hashable α] (self other : Table) (schema : Schema)
    (getKey₁ : Row → α) (getKey₂ : Row → α)
    (combine : Row → Raw → Row)
    (h : ∀ r₁ r₂, (combine r₁ r₂).schema = schema) (hwf_schema : schema.Wf) (name : String) :
    (groupJoin self other schema getKey₁ getKey₂ combine h hwf_schema).hasColumn name ↔ schema.hasName name := by
  simp [Table.hasColumn, Table.groupJoin, Raw.groupJoin_hasColumn_iff self.raw other.raw schema getKey₁ getKey₂ combine self.wfColumnSize other.wfColumnSize h]

theorem hasColumn_tsort_iff (self : Table) (key : String) (order : Order) (h : self.hasColumn key) (name : String) :
    (self.tsort key order h).hasColumn name ↔ self.hasColumn name := by
  simp [Table.hasColumn, Table.tsort, Raw.tsort_hasColumn_iff self.raw key order h self.wfColumnSize]

theorem hasColumn_sortByColumns_iff (self : Table) (keys : Array (String × Order))
    (h : ∀ key ∈ keys, self.hasColumn key.1) (name : String) :
    (self.sortByColumns keys h).hasColumn name ↔ self.hasColumn name := by
  simp [Table.hasColumn, Table.sortByColumns, Raw.sortByColumns_hasColumn_iff self.raw keys h self.wfColumnSize]

theorem hasColumn_orderBy_iff (self : Table) (comparators : Array Comparator) (name : String) :
    (self.orderBy comparators).hasColumn name ↔ self.hasColumn name := by
  simp [Table.hasColumn, Table.orderBy, Raw.orderBy_hasColumn_iff self.raw comparators self.wfColumnSize]

end hasColumn

end Tables.Table

end
