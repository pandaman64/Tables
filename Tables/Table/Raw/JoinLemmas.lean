module

public import Tables.Table.Raw.Join
import all Tables.Table.Raw.Join
import Tables.Table.Raw.BasicLemmas

public section

namespace Tables.Table.Raw

section wfColumnSize

theorem wfColumnSize_distinct (self : Raw) (h : self.WfColumnSize) : (distinct self h).WfColumnSize := by
  unfold distinct
  apply wfColumnSize_ofRows

theorem wfColumnSize_crossJoin (self other : Raw)
    (h₁ : self.WfColumnSize) (h₂ : other.WfColumnSize) : (crossJoin self other h₁ h₂).WfColumnSize := by
  unfold crossJoin
  apply wfColumnSize_ofRows

theorem wfColumnSize_leftJoin (self other : Raw) (keys : Array String)
    (h₁ : self.WfColumnSize) (h₂ : other.WfColumnSize) : (leftJoin self other keys h₁ h₂).WfColumnSize := by
  unfold leftJoin
  apply wfColumnSize_ofRows

end wfColumnSize

end Tables.Table.Raw
