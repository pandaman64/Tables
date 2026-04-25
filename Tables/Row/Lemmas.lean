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

end Tables.Row

end
