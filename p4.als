abstract sig Module { }

sig Introductory extends Module { }

sig Advanced extends Module {
	prereqs : some Module
} 
fact prereqsAcyclic {
		no a: Advanced | a in a.^prereqs 
}

enum Grade {A, B, C, F}

sig Subject {
	core: set Module,
	options : set Module
}
{
	no core & options
} 

one sig CSC941 extends Introductory { } 
one sig CSC933, CSC9V4, CSC9P5, CSC9P6, CSC9N6, CSC9V7, CSC9Z7
extends Advanced { } 

fact ComputingPrereqs {
CSC933.prereqs = CSC941
CSC9V4.prereqs = CSC933
CSC9P5.prereqs = CSC9V4
CSC9N6.prereqs = CSC9V4
CSC9P6.prereqs = CSC9P5
CSC9V7.prereqs = CSC9V4
CSC9Z7.prereqs = CSC9V4 
} 

one sig Computing extends Subject { }
fact ComputingModules {
Computing.core =
CSC941 + CSC933 + CSC9V4 + CSC9P5 + CSC9P6 + CSC9Z7
Computing.options = CSC9N6 + CSC9V7
}
one sig Sandy, Lewis, James extends Student { } 



sig Student {
degree : one Subject,
taken : set Module,
grade : taken -> one Grade
}
{
	all m:taken | all n:m.prereqs | m.grade != F && n in taken
} 

pred canGraduate [s:Student] {
let passed = { m : s.taken | s.grade[m] in A + B + C } |
# passed >= 6 and
s.degree.core in passed
} 
run canGraduate for 5

pred ICanGraduate{
	canGraduate[James]
}
run ICanGraduate for 4

pred Failed[s:Student] {
 all m:Module| m in s.taken and not canGraduate[s]
}
run Failed for 5

pred firstClass[s:Student] {
	let first = { m : s.taken | s.grade[m] in A } |
	#first >= 6 and
	canGraduate[s]
}
run firstClass for 5

pred secondClass[s:Student] {
	let second = { m : s.taken | s.grade[m] in A + B} |
	#second >= 6 and
	canGraduate[s] and 
	not firstClass[s]
}
run secondClass for 5

pred thirdClass[s:Student] {
	//let third = { m : s.taken | s.grade[m] in A + B +C} |
	//#third >= 6 and
	canGraduate[s] and 
	(not firstClass[s] or not secondClass[s])
}
run thirdClass for 5

fact modulesHaveOneSubject{
	all m:Module | one s: Subject | m in s.options || m in s.core
}
pred show{}
run show for 5
