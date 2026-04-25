module

public import Tables.DataType
public import Tables.Schema

@[expose]
public section

namespace Tables

structure Cell where
  name : String
  dataType : DataType
  value : dataType.toType
deriving DecidableEq, Hashable

structure Row where
  cells : Array Cell
deriving Inhabited, DecidableEq, Hashable

namespace Row

def header (self : Row) : Array String :=
  self.cells.map (·.name)

def schema (self : Row) : Schema :=
  { specs := self.cells.map fun cell => (cell.name, cell.dataType) }

def size (self : Row) : Nat :=
  self.cells.size

instance : GetElem Row Nat Cell (fun r i => i < r.size) where
  getElem r i h := r.cells[i]

def getName (self : Row) (i : Nat) (h : i < self.size := by get_elem_tactic) : String :=
  self.cells[i].name

def getDataType (self : Row) (i : Nat) (h : i < self.size := by get_elem_tactic) : DataType :=
  self.cells[i].dataType

def getValue (self : Row) (i : Nat) (h : i < self.size := by get_elem_tactic) : (self.getDataType i h).toType :=
  self.cells[i].value

def getCell (self : Row) (i : Nat) (h : i < self.size := by get_elem_tactic) : Cell :=
  self.cells[i]

def getCell? (self : Row) (i : Nat) : Option Cell :=
  self.cells[i]?

def hasCell (self : Row) (name : String) : Bool :=
  self.cells.any (·.name = name)

/--
TableAPI: getValue
-/
def getCellByName? (self : Row) (name : String) : Option Cell :=
  self.cells.find? (·.name = name)

/--
TableAPI: getValue
-/
def getCellByName (self : Row) (name : String) (h : self.hasCell name) : Cell :=
  have isSome : (self.cells.find? (·.name = name)).isSome := by
    grind [hasCell]
  (self.getCellByName? name).get isSome

end Row

end Tables

end
