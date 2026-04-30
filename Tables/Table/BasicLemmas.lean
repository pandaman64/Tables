module

public import Tables.Table.Basic
import all Tables.Table.Basic
import Tables.Table.Raw.BasicLemmas

public section

namespace Tables.Table

theorem getRow_schema (self : Table) (i : Nat) (h : i < self.nrows) :
    (self.getRow i h).schema = self.schema := by
  simp [getRow, schema, Raw.getRow_schema]

-- TODO: export more lemmas from `Raw.BasicLemmas`

end Tables.Table

end
