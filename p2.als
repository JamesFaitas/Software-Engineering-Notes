module List
sig List {
 head: lone Node
}
sig Node {
 nextNode: lone Node,
data : Int
} 

fact aCyclic {
 no n:Node | n in n.^nextNode
} 

fact everyNodeInUniqueList {
 all n:Node | one l:List | n in l.head.*nextNode
} 


pred show {}
run show for 7 but exactly 3 List 
