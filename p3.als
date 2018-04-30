module Family
abstract sig Person
{
hasChild: set Person // relation mapping a Person to their child(ren)

}


sig Man, Woman , Child extends Person { }

fact Acyclic {
	no p: Person | p in p.^hasChild 
}

fact LOneFather {
all p:Person | lone m:Man | p in m. hasChild
}
fact LoneMother {
all p:Person | lone w:Woman | p in w. hasChild
} 
 
pred fatherOf [m: Man, p:Person] { p in m.hasChild }
pred motherOf [w: Woman, p:Person] { p in w.hasChild }
pred parentOf [p, c: Person] { fatherOf [p,c] or motherOf [p,c] }

pred siblingOf [a, b : Person] {
(a != b) and (some p:Person | parentOf [p,a] and parentOf [p,b])
} 

pred ancestorOf [a, b: Person] {
	b in a.^hasChild and ( a != b)
} 

pred brotherOf [m:Man, b:Person] { (m != b) and (some p:Person | parentOf [p,m] and parentOf [p,b] )} 

pred sisterOf [w:Woman, b:Person] { (w != b) and (some p:Person | parentOf[p,w] and parentOf[p,b]) }

pred uncleOf [m:Man, c:Person] {
	(m != c) and (some p:Person | parentOf[p,c] and siblingOf[p,m])
 }  

pred auntOf [w:Woman, c:Person] {
	(w != c) and (some p:Person | parentOf[p,c] and siblingOf[p,w])
 } 

pred haveMutualChild [m:Man, w:Woman] {
	(some p:Person | parentOf[m,p] and parentOf[w,p])
} 

fact noIncestAncestor {
no p,q:Person | ancestorOf[p,q] and haveMutualChild[p,q]
}

fact noIncestSibling {
no p,q:Person | siblingOf[p,q] and haveMutualChild[p,q] 
} 

assert somePersonHasNoParents {
	some p:Person | no hasChild.p 
}
check somePersonHasNoParents 

assert ifSomePersonExistsThenSomePersonHasNoParents {
some Person implies some p:Person | no hasChild.p
} 
check ifSomePersonExistsThenSomePersonHasNoParents 

pred allPersonsHaveSomeAncestor{ 
	all p:Person | some q:Person | ancestorOf[q,p]
}

pred somePersonExistsAndAllPersonsHaveSomeAncestor{
	some Person and allPersonsHaveSomeAncestor
}
run somePersonExistsAndAllPersonsHaveSomeAncestor for 5

pred allPersonsWithSomeSiblingHaveSomeChild {
	all p:Person |( some q:Person | siblingOf[p,q]) implies (some c:Person | c in p.hasChild)
} 
run allPersonsWithSomeSiblingHaveSomeChild for 7
run haveMutualChild for 4 

pred show { }
