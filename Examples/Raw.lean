module

meta import Tables.Table.Raw

open Tables.Table (Raw)

meta section

namespace Tables.Examples

-- Unfortunately, we cannot reduce Array.map in Column.ofValues...
def students : Raw :=
  Raw.ofColumns #[
    Column.ofRawValues "name" #[some "Bob", some "Alice", some "Eve"],
    Column.ofRawValues "age" #[some 12, some 17, some 13],
    Column.ofRawValues "favorite color" #[some "blue", some "green", some "red"],
  ]

/--
info: |name |age|favorite color|
|-----|---|--------------|
|Bob  |12 |blue          |
|Alice|17 |green         |
|Eve  |13 |red           |
-/
#guard_msgs in
#eval students.toFormat

def studentsMissing : Raw :=
  Raw.ofColumns #[
    Column.ofRawValues "name" #[some "Bob", some "Alice", some "Eve"],
    Column.ofRawValues "age" #[none, some 17, some 13],
    Column.ofRawValues "favorite color" #[some "blue", some "green", none],
  ]

/--
info: |name |age |favorite color|
|-----|----|--------------|
|Bob  |null|blue          |
|Alice|17  |green         |
|Eve  |13  |null          |
-/
#guard_msgs in
#eval studentsMissing.toFormat

def employees : Raw :=
  Raw.ofColumns #[
    Column.ofRawValues "Last Name" #[
      some "Rafferty", some "Jones", some "Heisenberg", some "Robinson", some "Smith", some "Williams"
    ],
    Column.ofRawValues "Department ID" #[
      some 31, some 33, some 33, some 34, some 34, none
    ],
  ]

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

def departments : Raw :=
  Raw.ofColumns #[
    Column.ofRawValues "Department ID" #[some 31, some 33, some 34, some 35],
    Column.ofRawValues "Department Name" #[some "Sales", some "Engineering", some "Clerical", some "Marketing"],
  ]

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

def jellyAnon : Raw :=
  Raw.ofColumns #[
    Column.ofRawValues "get acne" #[some true, some true, some false, some false, some false, some true, some false, some true, some true, some false],
    Column.ofRawValues "red"      #[some false, some false, some false, some false, some false, some false, some false, some false, some false, some true],
    Column.ofRawValues "black"    #[some false, some true,  some false, some false, some false, some true,  some true,  some false, some false, some false],
    Column.ofRawValues "white"    #[some false, some false, some false, some false, some false, some false, some false, some false, some false, some false],
    Column.ofRawValues "green"    #[some true,  some true,  some true,  some false, some false, some false, some false, some false, some false, some false],
    Column.ofRawValues "yellow"   #[some false, some true,  some false, some true,  some true,  some false, some false, some false, some false, some true],
    Column.ofRawValues "brown"    #[some false, some false, some false, some false, some false, some false, some false, some true,  some false, some true],
    Column.ofRawValues "orange"   #[some true,  some false, some false, some false, some false, some true,  some false, some true,  some true,  some false],
    Column.ofRawValues "pink"     #[some false, some false, some true,  some false, some true,  some true,  some true,  some false, some false, some true],
    Column.ofRawValues "purple"   #[some false, some false, some false, some false, some false, some false, some false, some false, some false, some false],
  ]

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

def jellyNamed : Raw :=
  Raw.ofColumns #[
    Column.ofRawValues "name" #[
      some "Emily", some "Jacob", some "Emma", some "Aidan", some "Madison", some "Ethan", some "Hannah", some "Matthew", some "Hailey", some "Nicholas"
    ],
    Column.ofRawValues "get acne" #[some true, some true, some false, some false, some false, some true, some false, some true, some true, some false],
    Column.ofRawValues "red"      #[some false, some false, some false, some false, some false, some false, some false, some false, some false, some true],
    Column.ofRawValues "black"    #[some false, some true,  some false, some false, some false, some true,  some true,  some false, some false, some false],
    Column.ofRawValues "white"    #[some false, some false, some false, some false, some false, some false, some false, some false, some false, some false],
    Column.ofRawValues "green"    #[some true,  some true,  some true,  some false, some false, some false, some false, some false, some false, some false],
    Column.ofRawValues "yellow"   #[some false, some true,  some false, some true,  some true,  some false, some false, some false, some false, some true],
    Column.ofRawValues "brown"    #[some false, some false, some false, some false, some false, some false, some false, some true,  some false, some true],
    Column.ofRawValues "orange"   #[some true,  some false, some false, some false, some false, some true,  some false, some true,  some true,  some false],
    Column.ofRawValues "pink"     #[some false, some false, some true,  some false, some true,  some true,  some true,  some false, some false, some true],
    Column.ofRawValues "purple"   #[some false, some false, some false, some false, some false, some false, some false, some false, some false, some false],
  ]

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

def gradebook : Raw :=
  Raw.ofColumns #[
    Column.ofRawValues "name" #[some "Bob", some "Alice", some "Eve"],
    Column.ofRawValues "age" #[some 12, some 17, some 13],
    Column.ofRawValues "quiz1" #[some 8, some 6, some 7],
    Column.ofRawValues "quiz2" #[some 9, some 8, some 9],
    Column.ofRawValues "midterm" #[some 77, some 88, some 84],
    Column.ofRawValues "quiz3" #[some 7, some 8, some 8],
    Column.ofRawValues "quiz4" #[some 9, some 7, some 8],
    Column.ofRawValues "final" #[some 87, some 85, some 77],
  ]

/--
info: |name |age|quiz1|quiz2|midterm|quiz3|quiz4|final|
|-----|---|-----|-----|-------|-----|-----|-----|
|Bob  |12 |8    |9    |77     |7    |9    |87   |
|Alice|17 |6    |8    |88     |8    |7    |85   |
|Eve  |13 |7    |9    |84     |8    |8    |77   |
-/
#guard_msgs in
#eval gradebook.toFormat

def gradebookMissing : Raw :=
  Raw.ofColumns #[
    Column.ofRawValues "name" #[some "Bob", some "Alice", some "Eve"],
    Column.ofRawValues "age" #[some 12, some 17, some 13],
    Column.ofRawValues "quiz1" #[some 8, some 6, none],
    Column.ofRawValues "quiz2" #[some 9, some 8, some 9],
    Column.ofRawValues "midterm" #[some 77, some 88, some 84],
    Column.ofRawValues "quiz3" #[some 7, none, some 8],
    Column.ofRawValues "quiz4" #[some 9, some 7, some 8],
    Column.ofRawValues "final" #[some 87, some 85, some 77],
  ]

/--
info: |name |age|quiz1|quiz2|midterm|quiz3|quiz4|final|
|-----|---|-----|-----|-------|-----|-----|-----|
|Bob  |12 |8    |9    |77     |7    |9    |87   |
|Alice|17 |6    |8    |88     |null |7    |85   |
|Eve  |13 |null |9    |84     |8    |8    |77   |
-/
#guard_msgs in
#eval gradebookMissing.toFormat

def gradebookSeq : Raw :=
  Raw.ofColumns #[
    Column.ofRawValues "name" #[some "Bob", some "Alice", some "Eve"],
    Column.ofRawValues "age" #[some 12, some 17, some 13],
    Column.ofRawValues "quizzes" #[some #[8, 9, 7, 9], some #[6, 8, 8, 7], some #[7, 9, 8, 8]],
    Column.ofRawValues "midterm" #[some 77, some 88, some 84],
    Column.ofRawValues "final" #[some 87, some 85, some 77],
  ]

/--
info: |name |age|quizzes      |midterm|final|
|-----|---|-------------|-------|-----|
|Bob  |12 |#[8, 9, 7, 9]|77     |87   |
|Alice|17 |#[6, 8, 8, 7]|88     |85   |
|Eve  |13 |#[7, 9, 8, 8]|84     |77   |
-/
#guard_msgs in
#eval gradebookSeq.toFormat

def studentsGrades := students.leftJoin gradebook #["name", "age"] (by native_decide) (by native_decide)

/--
info: |name |age|favorite color|quiz1|quiz2|midterm|quiz3|quiz4|final|
|-----|---|--------------|-----|-----|-------|-----|-----|-----|
|Bob  |12 |blue          |8    |9    |77     |7    |9    |87   |
|Alice|17 |green         |6    |8    |88     |8    |7    |85   |
|Eve  |13 |red           |7    |9    |84     |8    |8    |77   |
-/
#guard_msgs in
#eval! studentsGrades.toFormat

end Tables.Examples

end
