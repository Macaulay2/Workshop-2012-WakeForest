restart
debug loadPackage("Tensors")
R=QQ[a..z]
S=QQ[x,y]

-----------------
--Making a tensor
-----------------

 -- from a nested list
T=tensor'{
     {{a,b},{c,d}},
     {{e,f},{g,h}},
     {{i,j},{k,l}}}

-- from a list and given dimensions
tensor'({3,2,2},{a,b,c,d,e,f,g,h,i,j,k,l})

-- generic tensors
genericTensor(R,{3,2,2})
U=genericTensor(R,12,{3,2,2})
genericTensor(R,m,{3,2,2})

-- random tensors of numbers
randomTensor(ZZ,{4,2,2})
randomTensor(QQ,{4,2,2})

-- random tensors of homogeneous polynomials
randomTensor(S,1,{4,2,2})

-----------------------
--Operations on tensors
-----------------------
3*T+U
T**U

---------
--Entries
---------
T_5 -- by ordinal
T_(1,0,1) -- by position

------------------------
--Slices
------------------------
-- to get slices of a tensor, use a 
-- list subscript with blank spots (nulls)
-- for unspecified indices:
T
T_{,0,}
T
T_{1,,}
T_{1,,1}
T_{1,1,1}
--------------------
--Modules of tensors
--------------------

-- a tensor is an element
-- of a "tensor module",
M=class t

-- which is a module that remembers
-- it is a tensor product of smaller 
-- modules:
M0=R^3 ** R^2 ** R^2 -- doesn't remember it's a tensor product
M -- remembers
M'=tensorModule(R,{2,2,3}) -- does
(class M0,class M,class M')
new TensorModule from M--doesn't know it's free
M==M0--they are equal as modules, 
M===M0--but not as hashtables,
M==M'--and tensor modules with different factors are different

N=tensorModule(R,{2,2})

--tensor products of tensor modules
P=M**N
P_11
P_(0,0,2,1,1)
--note it's easiest to see slice matrices
--with the column index and the final index

--making tensors that know where they live:
T=tensor'{{a,b},{-b,a}}
U=tensor'{{{b,c},{-c,b}},{{a,c},{-c,a}}}
U=tensor'{{b,c},{-c,b}}
ancestors class T
--Basic operations on tensors:
3*T+T
T**U
ideal toList entries (T**U)
T'=T**U

--aribtrary compositions of tensors:

--A_(i,j,k) := sum_j T_(i,j) * U_(j,k)
tcomp({{T,i,j},{U,j,k}},{j})

--A_(i,j,k) := T_(j,i) * U_(k,i)
tcomp({{T,j,i},{U,k,i}},{})

--higher order transpositions of a single tensor:

--indices in alphabetical order
--yields the same tensor:
tcomp({{T',i,j,k,l}})
tcomp({{T',l,j,k,i}})
--a harder-to-visualize permutation:
tcomp({{T',j,l,i,k}})

--Extracting order diagonal tensors:
tcomp({{T',i,i,i,i}})
tcomp({{T',i,i,j,j}})
tcomp({{T',i,i,j,k}})

--Symbolic composition of tensors
--by summing over indices:
T
U


--Einstein summation:
--repeated indices are
--automatically summed over
esum({{T,i,j},{U,j,k}})

--marginalization
tcomp({{T',i,j,k,l}},{i})

--T_(i,j) * U_(j,k)

(hold symbol T)_(i_1,i_2)


