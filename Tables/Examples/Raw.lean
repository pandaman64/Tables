module

import Tables.Table.Raw.Basic
import Tables.Table.Raw.Join

open Tables.Table (Raw)

namespace Tables.Examples

-- Unfortunately, we cannot reduce Array.map in Column.ofValues...
def students : Raw :=
  Raw.ofColumns #[
    Column.ofRawValues "name" #[some "Bob", some "Alice", some "Eve"],
    Column.ofRawValues "age" #[some 12, some 17, some 13],
    Column.ofRawValues "favorite color" #[some "blue", some "green", some "red"],
  ]

#eval students.toFormat

def studentsMissing : Raw :=
  Raw.ofColumns #[
    Column.ofRawValues "name" #[some "Bob", some "Alice", some "Eve"],
    Column.ofRawValues "age" #[none, some 17, some 13],
    Column.ofRawValues "favorite color" #[some "blue", some "green", none],
  ]

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

#eval employees.toFormat

def departments : Raw :=
  Raw.ofColumns #[
    Column.ofRawValues "Department ID" #[some 31, some 33, some 34, some 35],
    Column.ofRawValues "Department Name" #[some "Sales", some "Engineering", some "Clerical", some "Marketing"],
  ]

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

#eval gradebookMissing.toFormat

def gradebookSeq : Raw :=
  Raw.ofColumns #[
    Column.ofRawValues "name" #[some "Bob", some "Alice", some "Eve"],
    Column.ofRawValues "age" #[some 12, some 17, some 13],
    Column.ofRawValues "quizzes" #[some #[8, 9, 7, 9], some #[6, 8, 8, 7], some #[7, 9, 8, 8]],
    Column.ofRawValues "midterm" #[some 77, some 88, some 84],
    Column.ofRawValues "final" #[some 87, some 85, some 77],
  ]

#eval gradebookSeq.toFormat

def studentsGrades := students.leftJoin gradebook #["name", "age"] sorry sorry

#eval! studentsGrades.toFormat

end Tables.Examples
