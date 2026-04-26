module

public import Tables.Table.Raw.Basic
import all Tables.Table.Raw.Basic
import Std.Data.HashMap
import Std.Data.HashSet

open Std (HashMap HashSet)

public section

namespace Tables.Table.Raw

def distinct (self : Raw) (h : ∀ column ∈ self.columns, column.size = self.nrows) : Raw :=
  let schema := self.schema

  -- TODO: Rewrite other loops using similar Nat.fold pattern.
  let rows : Array { row : Row // row.schema = schema } := Prod.snd <| Nat.fold (init := (∅, #[])) self.nrows fun i isLt (seen, rows) =>
    let row := self.getRow i isLt h
    if row ∈ seen then
      (seen, rows)
    else
      have h' : row.schema = schema := by
        simp [row, getRow_schema, schema]
      (HashSet.insert seen row, rows.push ⟨row, h'⟩)

  ofRows schema rows.unattach (by grind [Array.mem_unattach])

def crossJoin (self other : Raw)
    (h₁ : ∀ column ∈ self.columns, column.size = self.nrows) (h₂ : ∀ column ∈ other.columns, column.size = other.nrows) : Raw :=
  let schema := self.schema ++ other.schema
  let rows := Array.flatten <| Array.ofFn fun (i : Fin self.nrows) =>
    Array.ofFn fun (j : Fin other.nrows) =>
      self.getRow i i.isLt h₁ ++ other.getRow j j.isLt h₂
  have h (row : Row) (mem : row ∈ rows) : row.schema = schema := by
    rw [Array.mem_flatten] at mem
    obtain ⟨xs, h, mem⟩ := mem
    rw [Array.mem_ofFn] at h
    obtain ⟨i, eq⟩ := h
    rw [←eq, Array.mem_ofFn] at mem
    obtain ⟨j, eq⟩ := mem
    grind only [= Row.append_schema, = getRow_schema]
  ofRows schema rows h

def leftJoin (self other : Raw) (keys : Array String)
    (h₁ : ∀ column ∈ self.columns, column.size = self.nrows) (h₂ : ∀ column ∈ other.columns, column.size = other.nrows) : Raw :=
  let schema := self.schema ++ other.schema.selectNotByNames keys

  let otherRowsMap : HashMap Row (Array (Fin other.nrows)) := Nat.fold (init := ∅) other.nrows fun i isLt m =>
    let row := other.getRow i isLt h₂
    let keyRow := row.selectByNames keys
    m.alter keyRow fun
      | some xs => some (xs.push ⟨i, isLt⟩)
      | none => some #[⟨i, isLt⟩]
  let rows : Array Row := Array.flatten <| (Array.finRange self.nrows).map fun i =>
    let row := self.getRow i.val i.isLt h₁
    let keyRow := row.selectByNames keys
    match otherRowsMap.get? keyRow with
    | some ns =>
      let newRows := ns.map fun j => row ++ (other.getRow j.val j.isLt h₂).selectNotByNames keys
      newRows
    | none => #[]

  have h (row : Row) (mem : row ∈ rows) : row.schema = schema := by
    simp only [HashMap.get?_eq_getElem?, Array.mem_flatten, Array.mem_map, rows] at mem
    obtain ⟨xs, ⟨i, mem, eq⟩, mem'⟩ := mem
    split at eq
    next ns eq' =>
      subst xs
      simp only [Array.mem_map] at mem'
      obtain ⟨n, mem'', eq''⟩ := mem'
      simp only [←eq'', Row.append_schema, getRow_schema, Row.selectNotByNames_schema, schema]
    next => grind
  ofRows schema rows h

end Tables.Table.Raw

end
