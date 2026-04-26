module

import Tables.Table.Raw.Basic
import Tables.Table.Raw.Join

open Tables.Table (Raw)

namespace Tables.Examples

def students : Raw :=
  Raw.ofColumns #[
    Column.ofValues "name" #["Bob", "Alice", "Eve"],
    Column.ofValues "age" #[12, 17, 13],
    Column.ofValues "favorite color" #["blue", "green", "red"],
  ] 3

#eval students.toFormat

def studentsMissing : Raw :=
  Raw.ofColumns #[
    Column.ofValues "name" #["Bob", "Alice", "Eve"],
    Column.ofValues "age" #[none, some 17, some 13],
    Column.ofValues "favorite color" #[some "blue", some "green", none],
  ] 3

#eval studentsMissing.toFormat

def employees : Raw :=
  Raw.ofColumns #[
    Column.ofValues "Last Name" #[
      "Rafferty", "Jones", "Heisenberg", "Robinson", "Smith", "Williams"
    ],
    Column.ofValues "Department ID" #[
      some 31, some 33, some 33, some 34, some 34, none
    ],
  ] 6

#eval employees.toFormat

def departments : Raw :=
  Raw.ofColumns #[
    Column.ofValues "Department ID" #[31, 33, 34, 35],
    Column.ofValues "Department Name" #["Sales", "Engineering", "Clerical", "Marketing"],
  ] 4

#eval departments.toFormat

def jellyAnon : Raw :=
  Raw.ofColumns #[
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
  ] 10

#eval jellyAnon.toFormat

def jellyNamed : Raw :=
  Raw.ofColumns #[
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
  ] 10

#eval jellyNamed.toFormat

def gradebook : Raw :=
  Raw.ofColumns #[
    Column.ofValues "name" #["Bob", "Alice", "Eve"],
    Column.ofValues "age" #[12, 17, 13],
    Column.ofValues "quiz1" #[8, 6, 7],
    Column.ofValues "quiz2" #[9, 8, 9],
    Column.ofValues "midterm" #[77, 88, 84],
    Column.ofValues "quiz3" #[7, 8, 8],
    Column.ofValues "quiz4" #[9, 7, 8],
    Column.ofValues "final" #[87, 85, 77],
  ] 3

#eval gradebook.toFormat

def gradebookMissing : Raw :=
  Raw.ofColumns #[
    Column.ofValues "name" #["Bob", "Alice", "Eve"],
    Column.ofValues "age" #[12, 17, 13],
    Column.ofValues "quiz1" #[some 8, some 6, none],
    Column.ofValues "quiz2" #[some 9, some 8, some 9],
    Column.ofValues "midterm" #[some 77, some 88, some 84],
    Column.ofValues "quiz3" #[some 7, none, some 8],
    Column.ofValues "quiz4" #[some 9, some 7, some 8],
    Column.ofValues "final" #[some 87, some 85, some 77],
  ] 3

#eval gradebookMissing.toFormat

def gradebookSeq : Raw :=
  Raw.ofColumns #[
    Column.ofValues "name" #["Bob", "Alice", "Eve"],
    Column.ofValues "age" #[12, 17, 13],
    Column.ofValues "quizzes" #[#[8, 9, 7, 9], #[6, 8, 8, 7], #[7, 9, 8, 8]],
    Column.ofValues "midterm" #[77, 88, 84],
    Column.ofValues "final" #[87, 85, 77],
  ] 3

#eval gradebookSeq.toFormat

def studentsGrades := students.leftJoin gradebook #["name", "age"] (by decide) (by decide)

#eval studentsGrades.toFormat

end Tables.Examples
