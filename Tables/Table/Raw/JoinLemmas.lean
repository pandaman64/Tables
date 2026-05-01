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

theorem wfColumnSize_join {α} [BEq α] [Hashable α] (self other : Raw) (schema : Schema)
    (getKey₁ : Row → α) (getKey₂ : Row → α)
    (combine : Row → Row → Row)
    (h₁ : self.WfColumnSize) (h₂ : other.WfColumnSize)
    (h₃ : ∀ r₁ r₂, (combine r₁ r₂).schema = schema) :
    (join self other schema getKey₁ getKey₂ combine h₁ h₂ h₃).WfColumnSize := by
  unfold join
  apply wfColumnSize_ofRows

theorem wfColumnSize_groupJoin {α} [BEq α] [Hashable α] (self other : Raw) (schema : Schema)
    (getKey₁ : Row → α) (getKey₂ : Row → α)
    (combine : Row → Raw → Row)
    (h₁ : self.WfColumnSize) (h₂ : other.WfColumnSize)
    (h₃ : ∀ r₁ r₂, (combine r₁ r₂).schema = schema) :
    (groupJoin self other schema getKey₁ getKey₂ combine h₁ h₂ h₃).WfColumnSize := by
  unfold groupJoin
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

theorem join_schema {α} [BEq α] [Hashable α] (self other : Raw) (schema : Schema)
    (getKey₁ : Row → α) (getKey₂ : Row → α)
    (combine : Row → Row → Row)
    (h₁ : self.WfColumnSize) (h₂ : other.WfColumnSize)
    (h₃ : ∀ r₁ r₂, (combine r₁ r₂).schema = schema) :
    (join self other schema getKey₁ getKey₂ combine h₁ h₂ h₃).schema = schema := by
  unfold join
  apply ofRows_schema

theorem groupJoin_schema {α} [BEq α] [Hashable α] (self other : Raw) (schema : Schema)
    (getKey₁ : Row → α) (getKey₂ : Row → α)
    (combine : Row → Raw → Row)
    (h₁ : self.WfColumnSize) (h₂ : other.WfColumnSize)
    (h₃ : ∀ r₁ r₂, (combine r₁ r₂).schema = schema) :
    (groupJoin self other schema getKey₁ getKey₂ combine h₁ h₂ h₃).schema = schema := by
  unfold groupJoin
  apply ofRows_schema

end schema

section wfColumnNames

theorem wfColumnNames_distinct (self : Raw) (h : self.WfColumnSize) (hwf : self.WfColumnNames) :
    (distinct self h).WfColumnNames := by
  simpa [wfColumnNames_iff_schema_wf, distinct_schema] using (wfColumnNames_iff_schema_wf self).mp hwf

theorem wfColumnNames_crossJoin (self other : Raw) (h₁ : self.WfColumnSize) (h₂ : other.WfColumnSize)
    (hwf₁ : self.WfColumnNames) (hwf₂ : other.WfColumnNames)
    (hdisjoint : self.header.Disjoint other.header) :
    (crossJoin self other h₁ h₂).WfColumnNames := by
  rw [wfColumnNames_iff_schema_wf, crossJoin_schema]
  exact Schema.wf_concat
    ((wfColumnNames_iff_schema_wf self).mp hwf₁)
    ((wfColumnNames_iff_schema_wf other).mp hwf₂)
    (by simpa [header_eq_schema_header] using hdisjoint)

theorem wfColumnNames_leftJoin (self other : Raw) (keys : Array String)
    (h₁ : self.WfColumnSize) (h₂ : other.WfColumnSize)
    (hwf₁ : self.WfColumnNames) (hwf₂ : other.WfColumnNames)
    (hdisjoint : self.header.Disjoint (other.schema.selectNotByNames keys).header) :
    (leftJoin self other keys h₁ h₂).WfColumnNames := by
  rw [wfColumnNames_iff_schema_wf, leftJoin_schema]
  have hwfR : (other.schema.selectNotByNames keys).Wf := by
    simpa [Schema.selectNotByNames] using Schema.wf_filterByName ((wfColumnNames_iff_schema_wf other).mp hwf₂)
  exact Schema.wf_concat ((wfColumnNames_iff_schema_wf self).mp hwf₁) hwfR (by simpa [header_eq_schema_header] using hdisjoint)

theorem wfColumnNames_join {α} [BEq α] [Hashable α] (self other : Raw) (schema : Schema)
    (getKey₁ : Row → α) (getKey₂ : Row → α)
    (combine : Row → Row → Row)
    (h₁ : self.WfColumnSize) (h₂ : other.WfColumnSize)
    (h₃ : ∀ r₁ r₂, (combine r₁ r₂).schema = schema)
    (hwf : schema.Wf) :
    (join self other schema getKey₁ getKey₂ combine h₁ h₂ h₃).WfColumnNames := by
  simpa [wfColumnNames_iff_schema_wf, join_schema] using hwf

theorem wfColumnNames_groupJoin {α} [BEq α] [Hashable α] (self other : Raw) (schema : Schema)
    (getKey₁ : Row → α) (getKey₂ : Row → α)
    (combine : Row → Raw → Row)
    (h₁ : self.WfColumnSize) (h₂ : other.WfColumnSize)
    (h₃ : ∀ r₁ r₂, (combine r₁ r₂).schema = schema)
    (hwf : schema.Wf) :
    (groupJoin self other schema getKey₁ getKey₂ combine h₁ h₂ h₃).WfColumnNames := by
  simpa [wfColumnNames_iff_schema_wf, groupJoin_schema] using hwf

end wfColumnNames

section hasColumn

theorem distinct_hasColumn_iff (self : Raw) (h : self.WfColumnSize) (name : String) :
    (distinct self h).hasColumn name ↔ self.hasColumn name := by
  simp [Raw.hasColumn_iff_schema_hasName, distinct_schema]

theorem crossJoin_hasColumn_iff (self other : Raw) (h₁ : self.WfColumnSize) (h₂ : other.WfColumnSize)
    (name : String) :
    (crossJoin self other h₁ h₂).hasColumn name ↔ self.hasColumn name ∨ other.hasColumn name := by
  simp [Raw.hasColumn_iff_schema_hasName, crossJoin_schema, Schema.concat_hasName_iff]

theorem leftJoin_hasColumn_iff (self other : Raw) (keys : Array String)
    (h₁ : self.WfColumnSize) (h₂ : other.WfColumnSize) (name : String) :
    (leftJoin self other keys h₁ h₂).hasColumn name ↔
      self.hasColumn name ∨ (other.hasColumn name ∧ name ∉ keys) := by
  simp [Raw.hasColumn_iff_schema_hasName, leftJoin_schema, Schema.concat_hasName_iff,
    Schema.selectNotByNames_hasName_iff]

theorem join_hasColumn_iff {α} [BEq α] [Hashable α] (self other : Raw) (schema : Schema)
    (getKey₁ : Row → α) (getKey₂ : Row → α)
    (combine : Row → Row → Row)
    (h₁ : self.WfColumnSize) (h₂ : other.WfColumnSize)
    (h₃ : ∀ r₁ r₂, (combine r₁ r₂).schema = schema) (name : String) :
    (join self other schema getKey₁ getKey₂ combine h₁ h₂ h₃).hasColumn name ↔ schema.hasName name := by
  simp [Raw.hasColumn_iff_schema_hasName, join_schema]

theorem groupJoin_hasColumn_iff {α} [BEq α] [Hashable α] (self other : Raw) (schema : Schema)
    (getKey₁ : Row → α) (getKey₂ : Row → α)
    (combine : Row → Raw → Row)
    (h₁ : self.WfColumnSize) (h₂ : other.WfColumnSize)
    (h₃ : ∀ r₁ r₂, (combine r₁ r₂).schema = schema) (name : String) :
    (groupJoin self other schema getKey₁ getKey₂ combine h₁ h₂ h₃).hasColumn name ↔ schema.hasName name := by
  simp [Raw.hasColumn_iff_schema_hasName, groupJoin_schema]

end hasColumn

end Tables.Table.Raw

end
