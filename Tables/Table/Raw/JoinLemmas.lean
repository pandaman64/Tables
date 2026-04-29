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

section wfColumnNames

theorem wfColumnNames_distinct (self : Raw) (h : self.WfColumnSize) (hwf : self.WfColumnNames) :
    (distinct self h).WfColumnNames := by
  simpa [wfColumnNames_iff_schema_wf, distinct_schema] using (wfColumnNames_iff_schema_wf self).mp hwf

theorem wfColumnNames_crossJoin (self other : Raw) (h₁ : self.WfColumnSize) (h₂ : other.WfColumnSize)
    (hwf₁ : self.WfColumnNames) (hwf₂ : other.WfColumnNames)
    (hdisjoint :
      ∀ (i : Fin self.ncols) (j : Fin other.ncols),
        (self.getColumn i.val i.isLt).name ≠ (other.getColumn j.val j.isLt).name) :
    (crossJoin self other h₁ h₂).WfColumnNames := by
  rw [wfColumnNames_iff_schema_wf, crossJoin_schema]
  exact Schema.wf_concat ((wfColumnNames_iff_schema_wf self).mp hwf₁) ((wfColumnNames_iff_schema_wf other).mp hwf₂)
    fun i j => by
      have isLt₁ : i.val < self.ncols := by simpa [schema_size_eq] using i.isLt
      have isLt₂ : j.val < other.ncols := by simpa [schema_size_eq] using j.isLt
      simpa [schema_getName_eq_getColumn_name i.val isLt₁, schema_getName_eq_getColumn_name j.val isLt₂]
        using hdisjoint ⟨i, isLt₁⟩ ⟨j, isLt₂⟩

theorem wfColumnNames_leftJoin (self other : Raw) (keys : Array String)
    (h₁ : self.WfColumnSize) (h₂ : other.WfColumnSize)
    (hwf₁ : self.WfColumnNames) (hwf₂ : other.WfColumnNames)
    (hdisjoint :
      ∀ (i : Fin self.schema.size) (j : Fin (other.schema.selectNotByNames keys).size),
        self.schema.getName i.val i.isLt ≠
          (other.schema.selectNotByNames keys).getName j.val j.isLt) :
    (leftJoin self other keys h₁ h₂).WfColumnNames := by
  rw [wfColumnNames_iff_schema_wf, leftJoin_schema]
  have hwfR : (other.schema.selectNotByNames keys).Wf := by
    simpa [Schema.selectNotByNames] using
      Schema.wf_filter ((wfColumnNames_iff_schema_wf other).mp hwf₂) (p := fun x : String × DataType => x.1 ∉ keys)
  exact Schema.wf_concat ((wfColumnNames_iff_schema_wf self).mp hwf₁) hwfR hdisjoint

end wfColumnNames

end Tables.Table.Raw

end
