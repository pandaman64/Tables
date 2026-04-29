module

public import Tables.Table.Raw

open Tables.Table (Raw)
open Tables.Table.Raw
open Array

public section

namespace Tables

structure Table where
  raw : Raw
  wfColumnSize : raw.WfColumnSize
  wfColumnNames : raw.WfColumnNames
deriving DecidableEq, Hashable

namespace Table

instance : Inhabited Table :=
  ⟨{ raw := default, wfColumnSize := wfColumnSize_default, wfColumnNames := wfColumnNames_default }⟩

def ncols (self : Table) : Nat :=
  self.raw.ncols

def nrows (self : Table) : Nat :=
  self.raw.nrows

def header (self : Table) : Array String :=
  self.raw.header

def schema (self : Table) : Schema :=
  self.raw.schema

def columns (self : Table) : Array Column :=
  self.raw.columns

def empty (schema : Schema) (hwf : schema.Wf) : Table where
  raw := Raw.empty schema
  wfColumnSize := wfColumnSize_empty schema
  wfColumnNames := wfColumnNames_empty schema hwf

def ofColumns (columns : Array Column) (nrows : Nat)
    (hsize : ∀ column ∈ columns, column.size = nrows)
    (hnames : ∀ (i j : Fin columns.size), i ≠ j → columns[i].name ≠ columns[j].name) : Table :=
  {
    raw := Raw.ofColumns columns nrows
    wfColumnSize := wfColumnSize_ofColumns columns nrows hsize
    wfColumnNames := wfColumnNames_ofColumns columns nrows hnames
  }

def getRow (self : Table) (i : Nat) (h₁ : i < self.nrows) : Row :=
  self.raw.getRow i h₁ self.wfColumnSize

def getRow? (self : Table) (i : Nat) : Option Row :=
  self.raw.getRow? i

def getColumn (self : Table) (i : Nat) (h : i < self.ncols := by get_elem_tactic) : Column :=
  self.raw.getColumn i h

def getColumn? (self : Table) (i : Nat) : Option Column :=
  self.raw.getColumn? i

def hasColumn (self : Table) (name : String) : Bool :=
  self.raw.hasColumn name

def findColumnIdx? (self : Table) (name : String) : Option Nat :=
  self.raw.findColumnIdx? name

def findColumnIdx (self : Table) (name : String) (h : self.hasColumn name) : Nat :=
  self.raw.findColumnIdx name h

def getColumnByName? (self : Table) (name : String) : Option Column :=
  self.raw.getColumnByName? name

def getColumnByName (self : Table) (name : String) (h : self.hasColumn name) : Column :=
  self.raw.getColumnByName name h

def selectColumns (self : Table) (ns : Array (Fin self.ncols)) (hinj : ns.Nodup) : Table :=
  {
    raw := self.raw.selectColumns ns
    wfColumnSize := wfColumnSize_selectColumns self.raw ns self.wfColumnSize
    wfColumnNames := wfColumnNames_selectColumns self.raw ns self.wfColumnNames hinj
  }

def selectColumnsByMask (self : Table) (mask : Vector Bool self.ncols) : Table :=
  {
    raw := self.raw.selectColumnsByMask mask
    wfColumnSize := wfColumnSize_selectColumnsByMask self.raw mask self.wfColumnSize
    wfColumnNames := wfColumnNames_selectColumnsByMask self.raw mask self.wfColumnNames
  }

def selectColumnsByName (self : Table) (names : Array String) (h : ∀ name ∈ names, self.hasColumn name)
    (hdupfree : names.Nodup) : Table :=
  {
    raw := self.raw.selectColumnsByName names h
    wfColumnSize := wfColumnSize_selectColumnsByName self.raw names h self.wfColumnSize
    wfColumnNames := wfColumnNames_selectColumnsByName self.raw names h hdupfree
  }

def take (self : Table) (n : Nat) (hle : n ≤ self.nrows) : Table :=
  {
    raw := self.raw.take n
    wfColumnSize := wfColumnSize_take self.raw n self.wfColumnSize hle
    wfColumnNames := wfColumnNames_take self.raw n self.wfColumnNames
  }

def addRow (self : Table) (row : Row) (h : row.schema = self.schema) : Table :=
  {
    raw := self.raw.addRow row h
    wfColumnSize := wfColumnSize_addRow self.raw row h self.wfColumnSize
    wfColumnNames := wfColumnNames_addRow self.raw row h self.wfColumnNames
  }

def addRows (self : Table) (rows : Array Row) (h : ∀ row ∈ rows, row.schema = self.schema) : Table :=
  {
    raw := self.raw.addRows rows h
    wfColumnSize := wfColumnSize_addRows self.raw rows h self.wfColumnSize
    wfColumnNames := wfColumnNames_addRows self.raw rows h self.wfColumnNames
  }

def ofRows (schema : Schema) (rows : Array Row) (h : ∀ row ∈ rows, row.schema = schema) (hwf : schema.Wf) :
    Table :=
  {
    raw := Raw.ofRows schema rows h
    wfColumnSize := wfColumnSize_ofRows schema rows h
    wfColumnNames := wfColumnNames_ofRows schema rows h hwf
  }

def addColumn (self : Table) (column : Column)
    (hsize : column.size = self.nrows)
    (hfresh : ∀ (i : Fin self.ncols), (self.getColumn i.val i.isLt).name ≠ column.name) : Table :=
  {
    raw := self.raw.addColumn column
    wfColumnSize := wfColumnSize_addColumn self.raw column hsize self.wfColumnSize
    wfColumnNames := wfColumnNames_addColumn self.raw column self.wfColumnNames hfresh
  }

def buildColumn {α} [DataType.OfType α] (self : Table) (name : String) (f : Row → Option α)
    (hfresh : ∀ (i : Fin self.ncols), (self.getColumn i.val i.isLt).name ≠ name) : Table :=
  {
    raw := self.raw.buildColumn name f self.wfColumnSize
    wfColumnSize := wfColumnSize_buildColumn self.raw name f self.wfColumnSize
    wfColumnNames := wfColumnNames_buildColumn self.raw name f self.wfColumnSize self.wfColumnNames hfresh
  }

def replaceColumn (self : Table) (column : Column) (hsize : column.size = self.nrows) : Table :=
  {
    raw := self.raw.replaceColumn column
    wfColumnSize := wfColumnSize_replaceColumn self.raw column hsize self.wfColumnSize
    wfColumnNames := wfColumnNames_replaceColumn self.raw column self.wfColumnNames hsize
  }

def transformColumn {α} [DataType.OfType α] (self : Table) (name : String) (h : self.hasColumn name)
    (f : Option ((self.getColumnByName name h).dataType.toType) → Option α) : Table :=
  {
    raw := self.raw.transformColumn name h f
    wfColumnSize := wfColumnSize_transformColumn self.raw name h f self.wfColumnSize
    wfColumnNames := wfColumnNames_transformColumn self.raw name h f self.wfColumnNames
  }

def selectRows (self : Table) (ns : Array (Fin self.nrows)) : Table :=
  {
    raw := self.raw.selectRows ns self.wfColumnSize
    wfColumnSize := wfColumnSize_selectRows self.raw ns self.wfColumnSize
    wfColumnNames := wfColumnNames_selectRows self.raw ns self.wfColumnSize self.wfColumnNames
  }

def selectRowsByMask (self : Table) (mask : Vector Bool self.nrows) : Table :=
  {
    raw := self.raw.selectRowsByMask mask self.wfColumnSize
    wfColumnSize := wfColumnSize_selectRowsByMask self.raw mask self.wfColumnSize
    wfColumnNames := wfColumnNames_selectRowsByMask self.raw mask self.wfColumnSize self.wfColumnNames
  }

def tfilter (self : Table) (p : Row → Bool) : Table :=
  {
    raw := self.raw.tfilter p self.wfColumnSize
    wfColumnSize := wfColumnSize_tfilter self.raw p self.wfColumnSize
    wfColumnNames := wfColumnNames_tfilter self.raw p self.wfColumnSize self.wfColumnNames
  }

def dropColumn (self : Table) (name : String) : Table :=
  {
    raw := self.raw.dropColumn name
    wfColumnSize := wfColumnSize_dropColumn self.raw name self.wfColumnSize
    wfColumnNames := wfColumnNames_dropColumn self.raw name self.wfColumnNames
  }

def dropColumns (self : Table) (names : Array String) : Table :=
  {
    raw := self.raw.dropColumns names
    wfColumnSize := wfColumnSize_dropColumns self.raw names self.wfColumnSize
    wfColumnNames := wfColumnNames_dropColumns self.raw names self.wfColumnNames
  }

def vcat (self : Table) (other : Table) (h : self.schema = other.schema) : Table :=
  {
    raw := self.raw.vcat other.raw h
    wfColumnSize := wfColumnSize_vcat self.raw other.raw h self.wfColumnSize other.wfColumnSize
    wfColumnNames := wfColumnNames_vcat self.raw other.raw h self.wfColumnNames
  }

def hcat (self : Table) (other : Table)
    (hrows : self.nrows = other.nrows)
    (hdisjoint :
      ∀ (i : Fin self.ncols) (j : Fin other.ncols),
        (self.getColumn i.val i.isLt).name ≠ (other.getColumn j.val j.isLt).name) : Table :=
  {
    raw := self.raw.hcat other.raw
    wfColumnSize := wfColumnSize_hcat self.raw other.raw self.wfColumnSize other.wfColumnSize hrows
    wfColumnNames := wfColumnNames_hcat self.raw other.raw self.wfColumnNames other.wfColumnNames hdisjoint
  }

def renameColumn (self : Table) (oldName newName : String)
    (hfresh :
      ∀ (i : Fin self.ncols),
        (self.getColumn i.val i.isLt).name ≠ newName ∨ (self.getColumn i.val i.isLt).name = oldName) : Table :=
  {
    raw := self.raw.renameColumn oldName newName
    wfColumnSize := wfColumnSize_renameColumn self.raw oldName newName self.wfColumnSize
    wfColumnNames := wfColumnNames_renameColumn self.raw oldName newName self.wfColumnNames hfresh
  }

/-- Iterative `renameColumns` preserves row heights; unique column names are not proved here. -/
def renameColumns (self : Table) (renames : Array (String × String)) : Table :=
  {
    raw := self.raw.renameColumns renames
    wfColumnSize := wfColumnSize_renameColumns self.raw renames self.wfColumnSize
    wfColumnNames := sorry
  }

def select (self : Table) (schema : Schema) (f : Row → (n : Nat) → n < self.nrows → Row)
    (h₁ : ∀ row n h, (f row n h).schema = schema) (hwf_schema : schema.Wf) : Table :=
  {
    raw := self.raw.select schema f h₁ self.wfColumnSize
    wfColumnSize := wfColumnSize_select self.raw schema f h₁ self.wfColumnSize
    wfColumnNames := wfColumnNames_select self.raw schema f h₁ self.wfColumnSize hwf_schema
  }

def completeCases (self : Table) (column : String) (h : self.hasColumn column) : Array Bool :=
  self.raw.completeCases column h

def dropna (self : Table) : Table :=
  {
    raw := self.raw.dropna self.wfColumnSize
    wfColumnSize := wfColumnSize_dropna self.raw self.wfColumnSize
    wfColumnNames := wfColumnNames_dropna self.raw self.wfColumnSize self.wfColumnNames
  }

def fillna (self : Table) (column : String) (h₁ : self.hasColumn column)
    (replacement : (self.getColumnByName column h₁).dataType.toType) : Table :=
  {
    raw := self.raw.fillna column h₁ replacement
    wfColumnSize := wfColumnSize_fillna self.raw column h₁ replacement self.wfColumnSize
    wfColumnNames := wfColumnNames_fillna self.raw column h₁ replacement self.wfColumnNames
  }

def count (self : Table) (column : String) (h : self.hasColumn column) : Table :=
  {
    raw := self.raw.count column h
    wfColumnSize := wfColumnSize_count self.raw column h
    wfColumnNames := wfColumnNames_count self.raw column h
  }

def toString (self : Table) : String :=
  self.raw.toString

def toFormat (self : Table) : Std.Format :=
  self.raw.toFormat

def distinct (self : Table) : Table :=
  {
    raw := self.raw.distinct self.wfColumnSize
    wfColumnSize := wfColumnSize_distinct self.raw self.wfColumnSize
    wfColumnNames := wfColumnNames_distinct self.raw self.wfColumnSize self.wfColumnNames
  }

def crossJoin (self other : Table)
    (hdisjoint :
      ∀ (i : Fin self.ncols) (j : Fin other.ncols),
        (self.getColumn i.val i.isLt).name ≠ (other.getColumn j.val j.isLt).name) : Table :=
  {
    raw := self.raw.crossJoin other.raw self.wfColumnSize other.wfColumnSize
    wfColumnSize := wfColumnSize_crossJoin self.raw other.raw self.wfColumnSize other.wfColumnSize
    wfColumnNames := wfColumnNames_crossJoin self.raw other.raw self.wfColumnSize other.wfColumnSize
      self.wfColumnNames other.wfColumnNames hdisjoint
  }

def leftJoin (self other : Table) (keys : Array String)
    (hdisjoint :
      ∀ (i : Fin self.schema.size) (j : Fin (other.schema.selectNotByNames keys).size),
        self.schema.getName i.val i.isLt ≠ (other.schema.selectNotByNames keys).getName j.val j.isLt) :
    Table :=
  {
    raw := self.raw.leftJoin other.raw keys self.wfColumnSize other.wfColumnSize
    wfColumnSize := wfColumnSize_leftJoin self.raw other.raw keys self.wfColumnSize other.wfColumnSize
    wfColumnNames := wfColumnNames_leftJoin self.raw other.raw keys self.wfColumnSize other.wfColumnSize
      self.wfColumnNames other.wfColumnNames hdisjoint
  }

end Table

end Tables

end
