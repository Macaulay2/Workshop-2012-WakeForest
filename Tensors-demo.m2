restart
debug loadPackage("Tensors")
R=QQ[a..z]
S=QQ[x,y]

-----------------
--Making a tensor
-----------------

 -- from a nested list
T=makeTensor{
     {{a,b},{c,d}},
     {{e,f},{g,h}},
     {{i,j},{k,l}}}
-- from a list and given dimensions
makeTensor({3,2,2},{a,b,c,d,e,f,g,h,i,j,k,l})

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
T
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
t=T
l={,0,}
T
T_{1,,}
T_{1,,1}
T_{1,1,1}

---------------
--Marginals
---------------
marginalize(T,{0})
marginalize(T,{0,2})
marginalize(T,{0,1,2})

--------------------
--Modules of tensors
--------------------

-- a tensor is an element
-- of a "tensor module",
M=class T
-- which is a module that remembers
-- it is a tensor product of smaller 
-- modules.

M0=R^3 ** R^2 ** R^2 -- doesn't remember it's a tensor product
M -- remembers

M'=tensorModule(R,{2,2,3})
new TensorModule from M--doesn't know it's free
M==M0--they are equal as modules, 
M===M0--but not as hashtables,
M==M'--and tensor modules with different factors are different

--tensor products of tensor modules
N=tensorModule(R,{2,2})
P=M**N
P_7
P_(0,0,1,1,1)

-------------------------------
--Manipulation of tensors using
--symbolic index notation
-------------------------------
T=genericTensor(R,{3,3})
U=genericTensor(R,9,{3,3})
i=symbol i;j=symbol j;k=symbol k;l=symbol l

--A_(i,j,k) := T_(j,i) * U_(k,i), or
tman({{T,j,i},{U,k,i}})
--tcomp({{T,i_1,i_0},{U,i_2,i_0}})

--A_(i,j,k) := sum_i T_(j,i) * U_(k,i)
tman({{T,j,i},{U,k,i}},{i})

--A_(i_0,i_1,i_2) := T_(i_1,i_0) * U_(i_2,i_0)

--higher order transpositions of a single tensor:

--indices in alphabetical order
--yields the same tensor:
T'=T**U
tman({{T',i,j,k,l}})
tman({{T',l,j,k,i}})
--a harder-to-visualize permutation:
tman({{T',j,l,i,k}})

--Extracting order diagonal tensors:
tman({{T',i,i,i,i}})
tman({{T',i,i,j,j}})
tman({{T',i,i,j,k}})


--Einstein summation:
--repeated indices are
--automatically summed over
esum({{T,i,j},{U,j,k}})

--marginalization
tman({{T',i,j,k,l}},{i})

(hold symbol T)_(i_1,i_2)


