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

@[specialize]
def buildJoinMap {α} [BEq α] [Hashable α] (other : Raw) (h : other.WfColumnSize) (getKey : Row → α) : HashMap α (Array (Fin other.nrows)) :=
  Nat.fold (init := ∅) other.nrows fun i isLt m =>
    let key := getKey (other.getRow i isLt h)
    m.alter key fun
      | some ns => some (ns.push ⟨i, isLt⟩)
      | none => some #[⟨i, isLt⟩]

def leftJoin (self other : Raw) (keys : Array String)
    (h₁ : self.WfColumnSize) (h₂ : other.WfColumnSize) : Raw :=
  let schema := self.schema ++ other.schema.selectNotByNames keys
  let joinMap := other.buildJoinMap h₂ fun row => row.selectByNames keys

  let rows : Array { row : Row // row.schema = schema } :=
    Nat.fold (init := #[]) self.nrows fun i isLt rows =>
      let row := self.getRow i isLt h₁
      let keyRow := row.selectByNames keys
      match joinMap.get? keyRow with
      | some ns =>
        rows ++ ns.map fun j => ⟨row ++ (other.getRow j.val j.isLt h₂).selectNotByNames keys, by simp [row, schema]⟩
      | none => rows -- TODO: fill with null values

  ofRows schema rows.unattach (by grind [Array.mem_unattach])

def join {α} [BEq α] [Hashable α] (self other : Raw) (schema : Schema)
    (getKey₁ : Row → α) (getKey₂ : Row → α)
    (combine : Row → Row → Row)
    (h₁ : self.WfColumnSize) (h₂ : other.WfColumnSize)
    (h₃ : ∀ r₁ r₂, (combine r₁ r₂).schema = schema) : Raw :=
  let joinMap := other.buildJoinMap h₂ getKey₂

  let rows : Array { row : Row // row.schema = schema } :=
    Nat.fold (init := #[]) self.nrows fun i isLt rows =>
      let key := getKey₁ (self.getRow i isLt h₁)
      match joinMap.get? key with
      | some ns =>
        rows ++ ns.map fun j => ⟨combine (self.getRow i isLt h₁) (other.getRow j.val j.isLt h₂), by simp [h₃]⟩
      | none => rows

  ofRows schema rows.unattach (by grind [Array.mem_unattach])

def groupJoin {α} [BEq α] [Hashable α] (self other : Raw) (schema : Schema)
    (getKey₁ : Row → α) (getKey₂ : Row → α)
    (combine : Row → Raw → Row)
    (h₁ : self.WfColumnSize) (h₂ : other.WfColumnSize)
    (h₃ : ∀ r₁ r₂, (combine r₁ r₂).schema = schema) : Raw :=
  let joinMap := other.buildJoinMap h₂ getKey₂
  let rows : Array { row : Row // row.schema = schema } :=
    Nat.fold (init := #[]) self.nrows fun i isLt rows =>
      let key := getKey₁ (self.getRow i isLt h₁)
      match joinMap.get? key with
      | some ns => rows.push ⟨combine (self.getRow i isLt h₁) (other.selectRows ns h₂), by simp [h₃]⟩
      | none => rows
  ofRows schema rows.unattach (by grind [Array.mem_unattach])

end Tables.Table.Raw

end
