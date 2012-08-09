restart
debug loadPackage("Tensors")
R=QQ[a,b,c]

--making modules of tensors:
M'=R^3 ** R^3 ** R^4--doesn't remember it's a tensor product
M=tensorModule(R,{3,3,4})
(class M',class M)
M'==M--they are equal as modules, 
not M==tensorModule(R,{4,3,4})--as a tensor module, M remembers its factors
M.factors

--let's make 
N=tensorModule(R,{5,3})

--tensor products of tensor modules
P=M**N
P_11
P_(0,0,0,3,2)
--note it's easiest to see slice matrices
--with the column index and the final index

--making tensors that know where they live:
T=tensor'{{a,b},{-b,a}}
U=tensor'{{{b,c},{-c,b}},{{a,c},{-c,a}}}
U=tensor'{{b,c},{-c,b}}
ancestors class T
--Basic operations on tensors:
3*T
T**U
ideal toList entries (T**U)

T'=T**U
--higher order transpositions of a single tensor:

--indices in alphabetical order
--yields the same tensor:
T'
tcomp({{T',i,j,k,l}})
tcomp({{T',l,j,k,i}})
--a harder-to-visualize permutation:
tcomp({{T**T,j,l,i,k}})

--Extracting order diagonal tensors:
tcomp({{T**T,i,i,i,i}})
tcomp({{T**T,i,i,j,j}})
tcomp({{T**T,i,i,j,k}})

--Symbolic composition of tensors
--by summing over indices:
tcomp({{T,i,j},{U,j,k}},{j})
tcomp({{T,i,j},{U,j,k}},{})

--Einstein summation:
--repeated indices are
--automatically summed over
esum({{T,i,j},{U,j,k}})
tcomp({{T',i,j,k,l}},{i})


