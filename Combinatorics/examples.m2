restart
loadPackage"FourTiTwo"
loadPackage ("Graphs", FileName => "/Users/sonja/Documents/M2repository/wakeforest2012/WFU-2012/Combinatorics/Graphs.m2")
loadPackage ("Posets", FileName => "/Users/sonja/Documents/M2repository/wakeforest2012/WFU-2012/Combinatorics/Posets.m2") -- just load
installPackage ("PosetsPlus", FileName => "/Users/sonja/Documents/M2repository/wakeforest2012/WFU-2012/Combinatorics/PosetsPlus.m2")
installPackage ("DiscreteMorse", FileName => "/Users/sonja/Documents/M2repository/wakeforest2012/WFU-2012/Combinatorics/DiscreteMorse.m2")



------------------------
-- Posets package
------------------------

R = QQ[a,b,c,d];
I = ideal (b*c^2*d, a*c^2*d, a^2*c*d, a^3*b*d, a^3*b*c);

L = lcmLattice (I)
displayPoset(L, SuppressLabels=>false)
texPoset(L)



-------------------------------------
-- simplicial maps and fiber theorems
-------------------------------------

P = poset({(1,5),(2,5),(2,6),(3,6),(4,4),(5,7),(6,7)})
displayPoset (P)
Q1 = poset({(x,z),(y,z),(w,w)})
displayPoset(Q)

f = posetMap (P,Q1, {(1,x),(3,y),(4,w),(2,z),(5,z),(6,z),(7,z)})
isSimplicial f

VerticalList apply(Q1.GroundSet, elt-> posetMapFiber(f,z))
-- and now we can check Quillen's Theorem
principalFilters1 = apply(Q1.GroundSet, elt->principalFilter(Q1, elt)) 
apply(principalFilters1, elt-> isFiberContractible(f,elt))


--alternatively
Q2 = poset({(x,z),(y,z),(w,z)}) 
g = posetMap (P,Q2, {(1,x),(3,y),(4,w),(2,z),(5,z),(6,z),(7,z)})
isSimplicial g
principalFilters2 = apply(Q2.GroundSet, elt->principalFilter(Q2, elt)) 
apply(principalFilters2, elt-> isFiberContractible(g,elt))



-------------------------------------
-- discrete Morse theory
-------------------------------------