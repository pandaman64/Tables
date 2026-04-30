module

meta import Tables.Table.Basic
meta import Tables.Table.GroupBy

meta section

namespace Tables.Examples

open Tables
open Tables.Table

private def unwrapTable (t : Except Error Table) : Table :=
  match t with
  | .ok t => t
  | .error _ => panic! "unwrapTable: expected a table, but got an error"

private def meanNatFn (xs : Array (Option Nat)) : Option Nat :=
  let ys : Array Nat := xs.filterMap id
  if ys.size = 0 then
    none
  else
    let sum : Nat := ys.foldl (· + ·) 0
    some (sum / ys.size)

private def countTrueFn (xs : Array (Option Bool)) : Option Nat :=
  some <| xs.count (some true)

def students : Table :=
  unwrapTable <| Table.ofColumns? #[
    Column.ofValues "name" #["Bob", "Alice", "Eve"],
    Column.ofValues "age" #[12, 17, 13],
    Column.ofValues "favorite color" #["blue", "green", "red"],
  ]

#eval students.toFormat

def studentsAgeAvgByFavoriteColor : Table :=
  unwrapTable <|
    students.pivotTable? #["favorite color"] #[
      .ofFn "age-average" "age" meanNatFn,
    ]

#eval studentsAgeAvgByFavoriteColor.toFormat

def studentsAgeByFavoriteColorWide : Table :=
  unwrapTable <| students.pivotWider? "name" "age"

#eval studentsAgeByFavoriteColorWide.toFormat

def studentsMissing : Table :=
  unwrapTable <| Table.ofColumns? #[
    Column.ofValues "name" #["Bob", "Alice", "Eve"],
    Column.ofRawValues "age" #[none, some 17, some 13],
    Column.ofRawValues "favorite color" #[some "blue", some "green", none],
  ]

#eval studentsMissing.toFormat

def employees : Table :=
  unwrapTable <| Table.ofColumns? #[
    Column.ofValues "Last Name" #[
      "Rafferty", "Jones", "Heisenberg", "Robinson", "Smith", "Williams"
    ],
    Column.ofRawValues "Department ID" #[
      some 31, some 33, some 33, some 34, some 34, none
    ],
  ]

#eval employees.toFormat

def departments : Table :=
  unwrapTable <| Table.ofColumns? #[
    Column.ofValues "Department ID" #[31, 33, 34, 35],
    Column.ofValues "Department Name" #["Sales", "Engineering", "Clerical", "Marketing"],
  ]

#eval departments.toFormat

def jellyAnon : Table :=
  unwrapTable <| Table.ofColumns? #[
    Column.ofValues "get acne" #[true, true, false, false, false, true, false, true, true, false],
    Column.ofValues "red"      #[false, false, false, false, false, false, false, false, false, true],
    Column.ofValues "black"    #[false, true,  false, false, false, true,  true,  false, false, false],
    Column.ofValues "white"    #[false, false, false, false, false, false, false, false, false, false],
    Column.ofValues "green"    #[true,  true,  true,  false, false, false, false, false, false, false],
    Column.ofValues "yellow"   #[false, true,  false, true,  true,  false, false, false, false, true],
    Column.ofValues "brown"    #[false, false, false, false, false, false, false, true,  false, true],
    Column.ofValues "orange"   #[true,  false, false, false, false, true,  false, true,  true,  false],
    Column.ofValues "pink"     #[false, false, true,  false, true,  true,  true,  false, false, true],
    Column.ofValues "purple"   #[false, false, false, false, false, false, false, false, false, false],
  ]

#eval jellyAnon.toFormat

def jellyNamed : Table :=
  unwrapTable <| Table.ofColumns? #[
    Column.ofValues "name" #[
      "Emily", "Jacob", "Emma", "Aidan", "Madison", "Ethan", "Hannah", "Matthew", "Hailey", "Nicholas"
    ],
    Column.ofValues "get acne" #[true, true, false, false, false, true, false, true, true, false],
    Column.ofValues "red"      #[false, false, false, false, false, false, false, false, false, true],
    Column.ofValues "black"    #[false, true,  false, false, false, true,  true,  false, false, false],
    Column.ofValues "white"    #[false, false, false, false, false, false, false, false, false, false],
    Column.ofValues "green"    #[true,  true,  true,  false, false, false, false, false, false, false],
    Column.ofValues "yellow"   #[false, true,  false, true,  true,  false, false, false, false, true],
    Column.ofValues "brown"    #[false, false, false, false, false, false, false, true,  false, true],
    Column.ofValues "orange"   #[true,  false, false, false, false, true,  false, true,  true,  false],
    Column.ofValues "pink"     #[false, false, true,  false, true,  true,  true,  false, false, true],
    Column.ofValues "purple"   #[false, false, false, false, false, false, false, false, false, false],
  ]

#eval jellyNamed.toFormat

def jellyNamedCountsByAcneAndBrown : Table :=
  unwrapTable <|
    jellyNamed.pivotTable? #["get acne", "brown"] #[
      .ofFn "red count" "red" countTrueFn,
      .ofFn "pink count" "pink" countTrueFn,
    ]

#eval jellyNamedCountsByAcneAndBrown.toFormat

def gradebook : Table :=
  unwrapTable <| Table.ofColumns? #[
    Column.ofValues "name" #["Bob", "Alice", "Eve"],
    Column.ofValues "age" #[12, 17, 13],
    Column.ofValues "quiz1" #[8, 6, 7],
    Column.ofValues "quiz2" #[9, 8, 9],
    Column.ofValues "midterm" #[77, 88, 84],
    Column.ofValues "quiz3" #[7, 8, 8],
    Column.ofValues "quiz4" #[9, 7, 8],
    Column.ofValues "final" #[87, 85, 77],
  ]

#eval gradebook.toFormat

def gradebookLonger : Table :=
  unwrapTable <| gradebook.pivotLonger?
    #["quiz1", "quiz2", "midterm", "quiz3", "quiz4", "final"]
    "test"
    "score"

#eval gradebookLonger.toFormat

def gradebookRoundTrip : Table :=
  unwrapTable <| gradebookLonger.pivotWider? "test" "score"

#eval gradebookRoundTrip.toFormat

def gradebookMissing : Table :=
  unwrapTable <| Table.ofColumns? #[
    Column.ofValues "name" #["Bob", "Alice", "Eve"],
    Column.ofValues "age" #[12, 17, 13],
    Column.ofRawValues "quiz1" #[some 8, some 6, none],
    Column.ofValues "quiz2" #[9, 8, 9],
    Column.ofValues "midterm" #[77, 88, 84],
    Column.ofRawValues "quiz3" #[some 7, none, some 8],
    Column.ofValues "quiz4" #[9, 7, 8],
    Column.ofValues "final" #[87, 85, 77],
  ]

#eval gradebookMissing.toFormat

def gradebookSeq : Table :=
  unwrapTable <| Table.ofColumns? #[
    Column.ofValues "name" #["Bob", "Alice", "Eve"],
    Column.ofValues "age" #[12, 17, 13],
    Column.ofValues "quizzes" #[#[8, 9, 7, 9], #[6, 8, 8, 7], #[7, 9, 8, 8]],
    Column.ofValues "midterm" #[77, 88, 84],
    Column.ofValues "final" #[87, 85, 77],
  ]

#eval gradebookSeq.toFormat

def gradebookQuizzesLong : Table :=
  unwrapTable <| gradebookSeq.flatten? #["quizzes"]

#eval gradebookQuizzesLong.toFormat

def weeklyHoursNested : Table :=
  unwrapTable <| Table.ofColumns? #[
    Column.ofValues "employee" #["Ann", "Bob"],
    Column.ofValues "week" #[#[1, 2, 3], #[1, 2]],
    Column.ofValues "hours" #[#[8, 7, 6], #[5, 9]],
  ]

#eval weeklyHoursNested.toFormat

def weeklyHoursLong : Table :=
  unwrapTable <| weeklyHoursNested.flatten? #["week", "hours"]

#eval weeklyHoursLong.toFormat

def studentsGrades : Table :=
  unwrapTable <| students.leftJoin? gradebook #["name", "age"]

#eval studentsGrades.toFormat

def studentsByAgeAsc : Table :=
  students.tsort "age" .ascending (by native_decide)

#eval studentsByAgeAsc.toFormat

def employeesByDeptIdAsc : Table :=
  employees.tsort "Department ID" .ascending (by native_decide)

-- nulls first
#eval employeesByDeptIdAsc.toFormat

def studentsByAgeAscThenNameDesc : Table :=
  let keys : Array (String × Order) := #[("age", .ascending), ("name", .descending)]
  students.sortByColumns keys (by
    intro key hk
    simp [keys] at hk
    rcases hk with rfl | rfl
    · native_decide
    · native_decide)

#eval studentsByAgeAscThenNameDesc.toFormat

def employeesWithDeptName : Table :=
  unwrapTable <|
    Table.join?
      employees
      departments
      (fun e => e.selectByNames #["Department ID"])
      (fun d => d.selectByNames #["Department ID"])
      (fun e d => e ++ d.selectNotByNames #["Department ID"])

#eval employeesWithDeptName.toFormat

def departmentsWithEmployeeCounts : Table :=
  unwrapTable <|
    Table.groupJoin?
      departments
      employees
      (fun d => d.selectByNames #["Department ID"])
      (fun e => e.selectByNames #["Department ID"])
      (fun d emps =>
        d.pushCell { name := "employee count", dataType := DataType.nat, value := some emps.nrows })

#eval departmentsWithEmployeeCounts.toFormat

end Tables.Examples

end
