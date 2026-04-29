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

section schema

theorem distinct_schema (self : Raw) (h : self.WfColumnSize) :
    (distinct self h).schema = self.schema := by
  unfold distinct
  apply ofRows_schema

theorem crossJoin_schema (self other : Raw) (h₁ : self.WfColumnSize) (h₂ : other.WfColumnSize) :
    (crossJoin self other h₁ h₂).schema = self.schema ++ other.schema := by
  unfold crossJoin
  apply ofRows_schema

theorem leftJoin_schema (self other : Raw) (keys : Array String)
    (h₁ : self.WfColumnSize) (h₂ : other.WfColumnSize) :
    (leftJoin self other keys h₁ h₂).schema = self.schema ++ other.schema.selectNotByNames keys := by
  unfold leftJoin
  apply ofRows_schema

end schema

end Tables.Table.Raw

end
