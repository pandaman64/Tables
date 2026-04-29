module

public import Tables.Table.Raw.Basic
import all Tables.Table.Raw.Basic
import Std.Data.HashMap
import Std.Data.HashSet

open Std (HashMap HashSet)

public section

namespace Tables.Table.Raw

def distinct (self : Raw) (h : self.WfColumnSize) : Raw :=
  let schema := self.schema

  -- TODO: Rewrite other loops using similar Nat.fold pattern.
  let rows : Array { row : Row // row.schema = schema } := Prod.snd <| Nat.fold (init := (∅, #[])) self.nrows fun i isLt (seen, rows) =>
    let row := self.getRow i isLt h
    if row ∈ seen then
      (seen, rows)
    else
      have h' : row.schema = self.schema := by
        simp [row, getRow_schema]
      (HashSet.insert seen row, rows.push ⟨row, h'⟩)

  ofRows schema rows.unattach (by grind [Array.mem_unattach])

def crossJoin (self other : Raw) (h₁ : self.WfColumnSize) (h₂ : other.WfColumnSize) : Raw :=
  let schema := self.schema ++ other.schema
  let rows : Array { row : Row // row.schema = schema } :=
    Nat.fold (init := #[]) self.nrows fun i isLt rows =>
      rows ++ Array.ofFn fun (j : Fin other.nrows) =>
        ⟨self.getRow i isLt h₁ ++ other.getRow j j.isLt h₂, by simp⟩

  ofRows schema rows.unattach (by grind [Array.mem_unattach])

def leftJoin (self other : Raw) (keys : Array String)
    (h₁ : self.WfColumnSize) (h₂ : other.WfColumnSize) : Raw :=
  let schema := self.schema ++ other.schema.selectNotByNames keys

  let otherRowsMap : HashMap Row (Array (Fin other.nrows)) := Nat.fold (init := ∅) other.nrows fun i isLt m =>
    let row := other.getRow i isLt h₂
    let keyRow := row.selectByNames keys
    m.alter keyRow fun
      | some xs => some (xs.push ⟨i, isLt⟩)
      | none => some #[⟨i, isLt⟩]

  let rows : Array { row : Row // row.schema = schema } :=
    Nat.fold (init := #[]) self.nrows fun i isLt rows =>
      let row := self.getRow i isLt h₁
      let keyRow := row.selectByNames keys
      match otherRowsMap.get? keyRow with
      | some ns =>
        rows ++ ns.map fun j => ⟨row ++ (other.getRow j.val j.isLt h₂).selectNotByNames keys, by simp [row, schema]⟩
      | none => rows

  ofRows schema rows.unattach (by grind [Array.mem_unattach])

end Tables.Table.Raw

end
