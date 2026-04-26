module

public import Tables.Row.Basic
import all Tables.Row.Basic

public section

namespace Tables.Row

@[simp, grind =]
theorem schema_size_eq_size (self : Row) : self.schema.size = self.size := by
  simp [Row.schema, Row.size, Schema.size]

@[simp, grind =]
theorem schema_getName_eq_getName (self : Row) (i : Nat) (h : i < self.size) :
    self.schema.getName i (self.schema_size_eq_size ▸ h) = self.getName i h := by
  grind [Row.schema, Row.getName, Schema.getName]

@[simp, grind =]
theorem schema_getDataType_eq_getDataType (self : Row) (i : Nat) (h : i < self.size) :
    self.schema.getDataType i (self.schema_size_eq_size ▸ h) = self.getDataType i h := by
  grind [Row.schema, Row.getDataType, Schema.getDataType]

@[simp, grind =]
theorem concat_size (self other : Row) : (self.concat other).size = self.size + other.size := by
  simp [Row.concat, Row.size]

@[simp, grind =]
theorem append_def (self other : Row) : self ++ other = { cells := self.cells ++ other.cells } := (rfl)

@[simp, grind =]
theorem append_schema (self other : Row) : (self ++ other).schema = self.schema ++ other.schema := by
  simp [Row.schema, Schema.append_def]

@[simp, grind =]
theorem selectNotByNames_schema (self : Row) (names : Array String) : (self.selectNotByNames names).schema = self.schema.selectNotByNames names := by
  simp only [schema, selectNotByNames, decide_not, Schema.selectNotByNames, Array.filter_map, Function.comp_def]

end Tables.Row

end
