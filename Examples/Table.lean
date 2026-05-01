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
  Table.ofColumns #[
    Column.ofValues "name" #["Bob", "Alice", "Eve"],
    Column.ofValues "age" #[12, 17, 13],
    Column.ofValues "favorite color" #["blue", "green", "red"],
  ] (by native_decide) (by native_decide)

/--
info: |name |age|favorite color|
|-----|---|--------------|
|Bob  |12 |blue          |
|Alice|17 |green         |
|Eve  |13 |red           |
-/
#guard_msgs in
#eval students.toFormat

def studentAges : Column := students["age"]'(by native_decide)

/--
info: "age: #[12, 17, 13]"
-/
#guard_msgs in
#eval studentAges.toString

def studentsAgeAvgByFavoriteColor : Table :=
  unwrapTable <|
    students.pivotTable? #["favorite color"] #[
      .ofFn "age-average" "age" meanNatFn,
    ]

/--
info: |favorite color|age-average|
|--------------|-----------|
|green         |17         |
|blue          |12         |
|red           |13         |
-/
#guard_msgs in
#eval studentsAgeAvgByFavoriteColor.toFormat

def studentsAgeByFavoriteColorWide : Table :=
  unwrapTable <| students.pivotWider? "name" "age"

/--
info: |favorite color|Bob |Alice|Eve |
|--------------|----|-----|----|
|green         |null|17   |null|
|blue          |12  |null |null|
|red           |null|null |13  |
-/
#guard_msgs in
#eval studentsAgeByFavoriteColorWide.toFormat

def studentsMissing : Table :=
  Table.ofColumns #[
    Column.ofValues "name" #["Bob", "Alice", "Eve"],
    Column.ofRawValues "age" #[none, some 17, some 13],
    Column.ofRawValues "favorite color" #[some "blue", some "green", none],
  ] (by native_decide) (by native_decide)

/--
info: |name |age |favorite color|
|-----|----|--------------|
|Bob  |null|blue          |
|Alice|17  |green         |
|Eve  |13  |null          |
-/
#guard_msgs in
#eval studentsMissing.toFormat

def employees : Table :=
  Table.ofColumns #[
    Column.ofValues "Last Name" #[
      "Rafferty", "Jones", "Heisenberg", "Robinson", "Smith", "Williams"
    ],
    Column.ofRawValues "Department ID" #[
      some 31, some 33, some 33, some 34, some 34, none
    ],
  ] (by native_decide) (by native_decide)

/--
info: |Last Name |Department ID|
|----------|-------------|
|Rafferty  |31           |
|Jones     |33           |
|Heisenberg|33           |
|Robinson  |34           |
|Smith     |34           |
|Williams  |null         |
-/
#guard_msgs in
#eval employees.toFormat

def departments : Table :=
  Table.ofColumns #[
    Column.ofValues "Department ID" #[31, 33, 34, 35],
    Column.ofValues "Department Name" #["Sales", "Engineering", "Clerical", "Marketing"],
  ] (by native_decide) (by native_decide)

/--
info: |Department ID|Department Name|
|-------------|---------------|
|31           |Sales          |
|33           |Engineering    |
|34           |Clerical       |
|35           |Marketing      |
-/
#guard_msgs in
#eval departments.toFormat

def jellyAnon : Table :=
  Table.ofColumns #[
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
  ] (by native_decide) (by native_decide)

/--
info: |get acne|red  |black|white|green|yellow|brown|orange|pink |purple|
|--------|-----|-----|-----|-----|------|-----|------|-----|------|
|true    |false|false|false|true |false |false|true  |false|false |
|true    |false|true |false|true |true  |false|false |false|false |
|false   |false|false|false|true |false |false|false |true |false |
|false   |false|false|false|false|true  |false|false |false|false |
|false   |false|false|false|false|true  |false|false |true |false |
|true    |false|true |false|false|false |false|true  |true |false |
|false   |false|true |false|false|false |false|false |true |false |
|true    |false|false|false|false|false |true |true  |false|false |
|true    |false|false|false|false|false |false|true  |false|false |
|false   |true |false|false|false|true  |true |false |true |false |
-/
#guard_msgs in
#eval jellyAnon.toFormat

def jellyNamed : Table :=
  Table.ofColumns #[
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
  ] (by native_decide) (by native_decide)

/--
info: |name    |get acne|red  |black|white|green|yellow|brown|orange|pink |purple|
|--------|--------|-----|-----|-----|-----|------|-----|------|-----|------|
|Emily   |true    |false|false|false|true |false |false|true  |false|false |
|Jacob   |true    |false|true |false|true |true  |false|false |false|false |
|Emma    |false   |false|false|false|true |false |false|false |true |false |
|Aidan   |false   |false|false|false|false|true  |false|false |false|false |
|Madison |false   |false|false|false|false|true  |false|false |true |false |
|Ethan   |true    |false|true |false|false|false |false|true  |true |false |
|Hannah  |false   |false|true |false|false|false |false|false |true |false |
|Matthew |true    |false|false|false|false|false |true |true  |false|false |
|Hailey  |true    |false|false|false|false|false |false|true  |false|false |
|Nicholas|false   |true |false|false|false|true  |true |false |true |false |
-/
#guard_msgs in
#eval jellyNamed.toFormat

def jellyNamedCountsByAcneAndBrown : Table :=
  unwrapTable <|
    jellyNamed.pivotTable? #["get acne", "brown"] #[
      .ofFn "red count" "red" countTrueFn,
      .ofFn "pink count" "pink" countTrueFn,
    ]

/--
info: |get acne|brown|red count|pink count|
|--------|-----|---------|----------|
|false   |true |1        |1         |
|true    |true |0        |0         |
|true    |false|0        |1         |
|false   |false|0        |3         |
-/
#guard_msgs in
#eval jellyNamedCountsByAcneAndBrown.toFormat

def gradebook : Table :=
  Table.ofColumns #[
    Column.ofValues "name" #["Bob", "Alice", "Eve"],
    Column.ofValues "age" #[12, 17, 13],
    Column.ofValues "quiz1" #[8, 6, 7],
    Column.ofValues "quiz2" #[9, 8, 9],
    Column.ofValues "midterm" #[77, 88, 84],
    Column.ofValues "quiz3" #[7, 8, 8],
    Column.ofValues "quiz4" #[9, 7, 8],
    Column.ofValues "final" #[87, 85, 77],
  ] (by native_decide) (by native_decide)

/--
info: |name |age|quiz1|quiz2|midterm|quiz3|quiz4|final|
|-----|---|-----|-----|-------|-----|-----|-----|
|Bob  |12 |8    |9    |77     |7    |9    |87   |
|Alice|17 |6    |8    |88     |8    |7    |85   |
|Eve  |13 |7    |9    |84     |8    |8    |77   |
-/
#guard_msgs in
#eval gradebook.toFormat

def gradebookLonger : Table :=
  unwrapTable <| gradebook.pivotLonger?
    #["quiz1", "quiz2", "midterm", "quiz3", "quiz4", "final"]
    "test"
    "score"

/--
info: |name |age|test   |score|
|-----|---|-------|-----|
|Bob  |12 |quiz1  |8    |
|Bob  |12 |quiz2  |9    |
|Bob  |12 |midterm|77   |
|Bob  |12 |quiz3  |7    |
|Bob  |12 |quiz4  |9    |
|Bob  |12 |final  |87   |
|Alice|17 |quiz1  |6    |
|Alice|17 |quiz2  |8    |
|Alice|17 |midterm|88   |
|Alice|17 |quiz3  |8    |
|Alice|17 |quiz4  |7    |
|Alice|17 |final  |85   |
|Eve  |13 |quiz1  |7    |
|Eve  |13 |quiz2  |9    |
|Eve  |13 |midterm|84   |
|Eve  |13 |quiz3  |8    |
|Eve  |13 |quiz4  |8    |
|Eve  |13 |final  |77   |
-/
#guard_msgs in
#eval gradebookLonger.toFormat

def gradebookRoundTrip : Table :=
  unwrapTable <| gradebookLonger.pivotWider? "test" "score"

/--
info: |name |age|quiz1|quiz2|midterm|quiz3|quiz4|final|
|-----|---|-----|-----|-------|-----|-----|-----|
|Bob  |12 |8    |9    |77     |7    |9    |87   |
|Alice|17 |6    |8    |88     |8    |7    |85   |
|Eve  |13 |7    |9    |84     |8    |8    |77   |
-/
#guard_msgs in
#eval gradebookRoundTrip.toFormat

def gradebookMissing : Table :=
  Table.ofColumns #[
    Column.ofValues "name" #["Bob", "Alice", "Eve"],
    Column.ofValues "age" #[12, 17, 13],
    Column.ofRawValues "quiz1" #[some 8, some 6, none],
    Column.ofValues "quiz2" #[9, 8, 9],
    Column.ofValues "midterm" #[77, 88, 84],
    Column.ofRawValues "quiz3" #[some 7, none, some 8],
    Column.ofValues "quiz4" #[9, 7, 8],
    Column.ofValues "final" #[87, 85, 77],
  ] (by native_decide) (by native_decide)

/--
info: |name |age|quiz1|quiz2|midterm|quiz3|quiz4|final|
|-----|---|-----|-----|-------|-----|-----|-----|
|Bob  |12 |8    |9    |77     |7    |9    |87   |
|Alice|17 |6    |8    |88     |null |7    |85   |
|Eve  |13 |null |9    |84     |8    |8    |77   |
-/
#guard_msgs in
#eval gradebookMissing.toFormat

def gradebookSeq : Table :=
  Table.ofColumns #[
    Column.ofValues "name" #["Bob", "Alice", "Eve"],
    Column.ofValues "age" #[12, 17, 13],
    Column.ofValues "quizzes" #[#[8, 9, 7, 9], #[6, 8, 8, 7], #[7, 9, 8, 8]],
    Column.ofValues "midterm" #[77, 88, 84],
    Column.ofValues "final" #[87, 85, 77],
  ] (by native_decide) (by native_decide)

/--
info: |name |age|quizzes      |midterm|final|
|-----|---|-------------|-------|-----|
|Bob  |12 |#[8, 9, 7, 9]|77     |87   |
|Alice|17 |#[6, 8, 8, 7]|88     |85   |
|Eve  |13 |#[7, 9, 8, 8]|84     |77   |
-/
#guard_msgs in
#eval gradebookSeq.toFormat

def gradebookQuizzesLong : Table :=
  unwrapTable <| gradebookSeq.flatten? #["quizzes"]

/--
info: |name |age|quizzes|midterm|final|
|-----|---|-------|-------|-----|
|Bob  |12 |8      |77     |87   |
|Bob  |12 |9      |77     |87   |
|Bob  |12 |7      |77     |87   |
|Bob  |12 |9      |77     |87   |
|Alice|17 |6      |88     |85   |
|Alice|17 |8      |88     |85   |
|Alice|17 |8      |88     |85   |
|Alice|17 |7      |88     |85   |
|Eve  |13 |7      |84     |77   |
|Eve  |13 |9      |84     |77   |
|Eve  |13 |8      |84     |77   |
|Eve  |13 |8      |84     |77   |
-/
#guard_msgs in
#eval gradebookQuizzesLong.toFormat

def weeklyHoursNested : Table :=
  Table.ofColumns #[
    Column.ofValues "employee" #["Ann", "Bob"],
    Column.ofValues "week" #[#[1, 2, 3], #[1, 2]],
    Column.ofValues "hours" #[#[8, 7, 6], #[5, 9]],
  ] (by native_decide) (by native_decide)

/--
info: |employee|week      |hours     |
|--------|----------|----------|
|Ann     |#[1, 2, 3]|#[8, 7, 6]|
|Bob     |#[1, 2]   |#[5, 9]   |
-/
#guard_msgs in
#eval weeklyHoursNested.toFormat

def weeklyHoursLong : Table :=
  unwrapTable <| weeklyHoursNested.flatten? #["week", "hours"]

/--
info: |employee|week|hours|
|--------|----|-----|
|Ann     |1   |8    |
|Ann     |2   |7    |
|Ann     |3   |6    |
|Bob     |1   |5    |
|Bob     |2   |9    |
-/
#guard_msgs in
#eval weeklyHoursLong.toFormat

def studentsGrades : Table :=
  students.leftJoin gradebook #["name", "age"] (by native_decide)

/--
info: |name |age|favorite color|quiz1|quiz2|midterm|quiz3|quiz4|final|
|-----|---|--------------|-----|-----|-------|-----|-----|-----|
|Bob  |12 |blue          |8    |9    |77     |7    |9    |87   |
|Alice|17 |green         |6    |8    |88     |8    |7    |85   |
|Eve  |13 |red           |7    |9    |84     |8    |8    |77   |
-/
#guard_msgs in
#eval studentsGrades.toFormat

def studentsByAgeAsc : Table :=
  students.tsort "age" .ascending (by native_decide)

/--
info: |name |age|favorite color|
|-----|---|--------------|
|Bob  |12 |blue          |
|Eve  |13 |red           |
|Alice|17 |green         |
-/
#guard_msgs in
#eval studentsByAgeAsc.toFormat

def employeesByDeptIdAsc : Table :=
  employees.tsort "Department ID" .ascending (by native_decide)

-- nulls first
/--
info: |Last Name |Department ID|
|----------|-------------|
|Williams  |null         |
|Rafferty  |31           |
|Jones     |33           |
|Heisenberg|33           |
|Robinson  |34           |
|Smith     |34           |
-/
#guard_msgs in
#eval employeesByDeptIdAsc.toFormat

def studentsByAgeAscThenNameDesc : Table :=
  let keys : Array (String × Order) := #[("age", .ascending), ("name", .descending)]
  students.sortByColumns keys (by
    intro key hk
    simp [keys] at hk
    rcases hk with rfl | rfl
    · native_decide
    · native_decide)

/--
info: |name |age|favorite color|
|-----|---|--------------|
|Bob  |12 |blue          |
|Eve  |13 |red           |
|Alice|17 |green         |
-/
#guard_msgs in
#eval studentsByAgeAscThenNameDesc.toFormat

-- TODO: Need a typed Row to actually prove that the join is safe.
def employeesWithDeptName : Table :=
  unwrapTable <|
    Table.join?
      employees
      departments
      (fun e => e.selectByNames #["Department ID"])
      (fun d => d.selectByNames #["Department ID"])
      (fun e d => e ++ d.selectNotByNames #["Department ID"])

/--
info: |Last Name |Department ID|Department Name|
|----------|-------------|---------------|
|Rafferty  |31           |Sales          |
|Jones     |33           |Engineering    |
|Heisenberg|33           |Engineering    |
|Robinson  |34           |Clerical       |
|Smith     |34           |Clerical       |
-/
#guard_msgs in
#eval employeesWithDeptName.toFormat

def employeesWithDeptName_leftJoin : Table :=
  employees.leftJoin departments #["Department ID"] (by native_decide)

-- "Williams" has no Department ID, so Department Name becomes missing (none).
/--
info: |Last Name |Department ID|Department Name|
|----------|-------------|---------------|
|Rafferty  |31           |Sales          |
|Jones     |33           |Engineering    |
|Heisenberg|33           |Engineering    |
|Robinson  |34           |Clerical       |
|Smith     |34           |Clerical       |
|Williams  |null         |null           |
-/
#guard_msgs in
#eval employeesWithDeptName_leftJoin.toFormat

-- TODO: Need a typed Row to actually prove that the join is safe.
def departmentsWithEmployeeCounts : Table :=
  unwrapTable <|
    Table.groupJoin?
      departments
      employees
      (fun d => d.selectByNames #["Department ID"])
      (fun e => e.selectByNames #["Department ID"])
      (fun d emps =>
        d.pushCell { name := "employee count", dataType := DataType.nat, value := some emps.nrows })

/--
info: |Department ID|Department Name|employee count|
|-------------|---------------|--------------|
|31           |Sales          |1             |
|33           |Engineering    |2             |
|34           |Clerical       |2             |
-/
#guard_msgs in
#eval departmentsWithEmployeeCounts.toFormat

end Tables.Examples

end
