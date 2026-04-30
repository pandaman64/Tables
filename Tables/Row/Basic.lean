module

public import Tables.DataType
public import Tables.Schema

@[expose]
public section

namespace Tables

structure Cell where
  name : String
  dataType : DataType
  value : Option dataType.toType
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

def getValue (self : Row) (i : Nat) (h : i < self.size := by get_elem_tactic) : Option (self.getDataType i h).toType :=
  self.cells[i].value

def getCell (self : Row) (i : Nat) (h : i < self.size := by get_elem_tactic) : Cell :=
  self.cells[i]

def getCell? (self : Row) (i : Nat) : Option Cell :=
  self.cells[i]?

def hasCell (self : Row) (name : String) : Bool :=
  self.cells.any (·.name = name)

def findCellIdx (self : Row) (name : String) : Nat :=
  self.cells.findIdx (·.name = name)

def pushCell (self : Row) (cell : Cell) : Row :=
  { cells := self.cells.push cell }

def setCell (self : Row) (i : Nat) (cell : Cell) (h : i < self.size := by get_elem_tactic) : Row :=
  { cells := self.cells.set i cell }

def hasNameAndDataType (self : Row) (name : String) (dataType : DataType) : Bool :=
  self.cells.any (fun cell => cell.name = name ∧ cell.dataType = dataType)

def replace (self : Row) (name : String) (dataType : DataType) (value : Option dataType.toType) : Row :=
  { cells := self.cells.map fun cell =>
    if cell.name = name then
      { cell with dataType, value }
    else
      cell
  }

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

def getValueByNameAndDataType (self : Row) (name : String) (dataType : DataType) (h : self.hasNameAndDataType name dataType) : Option dataType.toType :=
  let found := self.cells.find? (fun cell => cell.name = name ∧ cell.dataType = dataType)
  match hf : found with
  | some cell =>
    have : cell.dataType = dataType := by grind
    this ▸ cell.value
  | none =>
    have : False := by grind [hasNameAndDataType]
    this.elim

def concat (self other : Row) : Row :=
  { cells := self.cells ++ other.cells }

instance : Append Row where
  append := concat

def selectByNames (self : Row) (names : Array String) : Row :=
  { cells := self.cells.filter fun cell => cell.name ∈ names }

def selectNotByNames (self : Row) (names : Array String) : Row :=
  { cells := self.cells.filter fun cell => cell.name ∉ names }

def upsertCell (self : Row) (cell : Cell) : Row :=
  let idx := self.findCellIdx cell.name
  if h : idx < self.size then
    self.setCell idx cell h
  else
    self.pushCell cell

def upsert (self other : Row) : Row :=
  other.cells.foldl (init := self) upsertCell

end Row

end Tables

end
