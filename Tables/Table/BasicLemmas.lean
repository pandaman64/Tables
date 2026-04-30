module

public import Tables.Table.Basic
import all Tables.Table.Basic
import Tables.Table.Raw.BasicLemmas

public section

namespace Tables.Table

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
    (self.dropColumn name).schema = self.schema.filter fun x => x.fst ≠ name := by
  simp [Table.dropColumn, Table.schema, Raw.dropColumn_schema]

theorem dropColumns_schema (self : Table) (names : Array String) :
    (self.dropColumns names).schema = self.schema.filter fun x => x.fst ∉ names := by
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

end Tables.Table

end
