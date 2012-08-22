restart
debug loadPackage("Tensors")
R=QQ[a,b,c]

--making modules of tensors:
M0=R^3 ** R^3 ** R^4--doesn't remember it's a tensor product
M=tensorModule(R,{4,3,3})--as a tensor module, M remembers its factors
M'=tensorModule(R,{3,4,3})
(class M0,class M,class M')
new TensorModule from M
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

