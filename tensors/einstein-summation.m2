restart
--objects to consider making:
--Tensor (alagous to Matrix)
--SparseTensor
--tensor 
--TensorForm (linear form)
--TensorForm (linear form)
--TensorArray (nested list)
--TensorTable (Hash table)

R=QQ[x,y,z,s,t,u,v,w]
M=R^3
N=R^5
f=x*M_0+ y*M_1 + z*M_2
g=s*N_0+ t*N_1 + u*N_2 + v*N_3 + w*N_4

nA = nestedAccess = method()
nA(Thing,Sequence) := (x,l) -> (
     if l === () then return x else error: "too many indices?")
nA(VisibleList,Sequence) := (N,l) -> (
     if l === () then return N;
     if l_0 === null then return apply(N,i->nA(i,take(l,{1,-1+#l})));
     return nA(N#(l#0),take(l,{1,-1+#l})))

--TEST ///
L={{{1,2,3},{4,5,6}},{{5,6,7},{8,9,10}}}
--entry:
nA(L,(1,1,2))

--slices:
nA(L,(1,))
nA(L,(1,,))
nA(L,(,1,))
nA(L,(,,1))
nA(L,(,1,1))
nA(L,(1,,1))
--///

TensorEntryList  = new Type of List
net TensorEntryList  := T -> netList new List from T
tel=tensorEntryList=method()
tel List := L -> new TensorEntryList from L
tel {{1,2},{3,4}}
tel {L,L}
tel Thing := x -> x
TensorEntryList_Sequence:=(N,s) -> (tel nA(N,s)
TensorEntryList_ZZ := (N,n) -> N_(1:n)

TensorEntryList_Sequence:=(N,s) -> (
          
     tel nA(N,s)
     )

f = x -> hold x
g=method()
g Thing := x -> hold x
(g 3)(g sum)(g 4)
sum for i in 1..3 list (g i)

--
T=tel L
--entry:
T_(1,1,2)
--slices:
T_(1,,2)
T_(,1,)
T_(,,1)
T_(,1,1)
T_(1)
oo==T_1
--

dimensions=method()
dimensions TensorEntryList := L -> (d:={};
     while class L === TensorEntryList do (d=d|{#L},L=L_0);
     return d)

--
dimensions T
--
x=symbol x
R=QQ[x_1..x_27]
m0=tel entries genericMatrix(R,3,3)
m1=tel entries genericMatrix(R,x_10,3,3)
m2=tel entries genericMatrix(R,x_19,3,3)

List**List := (L,M) -> flatten for l in L list for m in M list (l,m)
Sequence**Sequence := (L,M) -> toSequence flatten for l in L list for m in M list (l,m)
(1,2,3)**(4,5,6)



cP=cartesianProduct=method()
cP VisibleList := L -> fold((i,j)->(i**j)/splice,L)
L={{1,2},{3,4},{5,6}}
cP L
--Tensor_Sequence := (L,s) -> (
--     while #s > 1 do (L=L_(s_0),s=(1..<#s)/(i->s_i));
--     return L_(s_0))
isRectangular=method()
isRectangular VisibleList := L -> (d:=dimensions tel L;
     inds:=cartesianProduct(d/(i->0..<i));
     for i in inds do try L_i else return false;
     return true)
isRectangular m1
isRectangular {{1,2},{3}}
isRectangular T

ancestors class(f**g)

-------------------------------
--OUTPUT THE FULL TENSOR
-------------------------------
--want to input
--einsteinSummation{{m0,i,j},{m1,j,k},{m2,k,l}}
--check symbols
{i,j,k,l}/class
tensors={m0,m1,m2}
indicesByTensor={(1,2),(2,3),(3,4)}
einsteinSummation = method()

einsteinSummation (List,List) := (tensors,indicesByTensor) -> (
     numberOfTensors:=#tensors;
     allIndices:=sort toList set splice indicesByTensor;
     indexLocations:= i -> indicesByTensor/(j->positions(j,k->k==i));
     repeatedIndices:=select(allIndices,i->1<#flatten indexLocations i);
     singleIndices:=toList((allIndices - (set repeatedIndices)));
     tensorsWithIndex:= i -> positions(indexLocations i,j->not j==={});
     indexRange:= i -> (
     	  t:= first tensorsWithIndex i;
     	  l:= first (indexLocations i)_t;
     	  return (dimensions(tensors_t))_l);
     TemporaryTensorList=tensors;
     TemporaryIndexList=indicesByTensor;
     sumCommand:=concatenate for r in repeatedIndices list "sum for i"|toString(r)|" in 0..<"|toString(indexRange r)|" list ";
     plugInSequence:= seq -> for ind in indicesByTensor list (
	  toSequence for i in ind list if member(i,singleIndices) then seq_0 else getSymbol("i"|toString i)
	       do if member(i,singleIndices) then seq=remove(seq,0));
     summand:=seq->(
	  TemporaryIndexList=plugInSequence(seq);
	  return "(TemporaryTensorList_0)_"|toString(TemporaryIndexList_0)|(
     	       concatenate for tensorNumber in 1..<numberOfTensors list "*(TemporaryTensorList_"|toString(tensorNumber)|")_"|toString(TemporaryIndexList_tensorNumber)));
     listCommand:=concatenate for s in singleIndices list "for i"|toString(s)|" in 0..<"|toString(indexRange s)|" list ";
     return tel value(listCommand|sumCommand|summand ((singleIndices)/(j->getSymbol("i"|toString(j))))))
einsteinSummation List := L -> einsteinSummation(L/first,L/(i->toSequence remove(i,0)))
es=einsteinSummation

printWidth=1000
A=tel{{1,2,3},{4,5,6},{7,8,9}}
B=tel{{11,12,x},{14,15,16},{17,18,19}}
C=tel{{21,22,23},{24,25,26},{27,28,29}}

es({{A,i,j},{B,j,k},{C,j,l}})

sum_{i,j} (A_(i,j) * B_(j,k) * C_(j,l))
(hold symbol A)_(hold (i,j))

sum for i in 0..2 list for j in 0..2 list 
A_(1,2)



tensorComposition

M=R^3
N=R^5
g=map(R^3,R^3,{{0,1,0},{0,0,1},{1,0,0}})
(g**g**id_(R^5))


--maybe better to have to indicate which indices to sum over?
--allow integers, symbols, indices to sum over
tensorComposition = method()
tensorComposition (List,List,List) := (tensors,indicesByTensor,summationIndices) -> (
     numberOfTensors:=#tensors;
     indicesByTensor=indicesByTensor/toSequence;
     allIndices:=sort toList set splice indicesByTensor;
     ZZindices:=(select(allIndices,i->class i === ZZ))-(set summationIndices);
     indexLocations:= i -> indicesByTensor/(j->positions(j,k->k==i));
     outputIndices:=toList(((allIndices - (set summationIndices)))-(set ZZindices));
     tensorsWithIndex:= i -> positions(indexLocations i,j->not j==={});
     indexRange:= i -> (
     	  t:= first tensorsWithIndex i;
     	  l:= first (indexLocations i)_t;
     	  return (dimensions(tensors_t))_l);
     TemporaryTensorList=tensors;
     TemporaryIndexList=indicesByTensor;
     sumCommand:=concatenate for r in summationIndices list "sum for i"|toString(r)|" in 0..<"|toString(indexRange r)|" list ";
     plugInSequence:= seq -> for ind in indicesByTensor list (
	  toSequence for i in ind list if member(i,singleIndices) then seq_0 else getSymbol("i"|toString i)
	       do if member(i,singleIndices) then seq=remove(seq,0));
     summand:=seq->(
	  TemporaryIndexList=plugInSequence(seq);
	  return "(TemporaryTensorList_0)_"|toString(TemporaryIndexList_0)|(
     	       concatenate for tensorNumber in 1..<numberOfTensors list "*(TemporaryTensorList_"|toString(tensorNumber)|")_"|toString(TemporaryIndexList_tensorNumber)));
     listCommand:=concatenate for s in singleIndices list "for i"|toString(s)|" in 0..<"|toString(indexRange s)|" list ";
     return tel value(listCommand|sumCommand|summand ((singleIndices)/(j->getSymbol("i"|toString(j))))))
einsteinSummation List := L -> einsteinSummation(L/first,L/(i->toSequence remove(i,0)))


--faster method to just extract one entry

sumOut=method()
sumOut (List,List) := (tensors,indicesByTensor) -> (
     numberOfTensors:=#tensors;
     summationIndices:= toList set select(splice indicesByTensor,i->not class i === ZZ);
     indexLocations:= i -> indicesByTensor/(j->positions(j,k->k===i));
     tensorsWithIndex:= i -> positions(indexLocations i,j->not j==={});
     indexRange:= i -> (
     	  t:= first tensorsWithIndex i;
     	  l:= first (indexLocations i)_t;
     	  return (dimensions(tensors_t))_l);
     TemporaryTensorList=tensors;
     TemporaryIndexList=indicesByTensor;
     sumCommand:= concatenate for r in summationIndices list "sum for "|toString(r)|" in 0..<"|toString(indexRange r)|" list ";
     summand:= "(TemporaryTensorList_0)_"|toString(indicesByTensor_0)|(
     concatenate for tensorNumber in 1..<numberOfTensors list "*(TemporaryTensorList_"|toString(tensorNumber)|")_"|toString(TemporaryIndexList_tensorNumber));
     return value(sumCommand|summand))
sumOut List := L -> sumOut(L/first,L/(i->toSequence remove(i,0)))
sumOut({m0,m1,m2},{(2,i),(i,1),(i,0)})
sumOut{{m0,2,i},{m1,i,1},{m2,i,0}}
sumOut({m0,m0,m0},{(0,i),(i,1),(j,0)})

--SUCCESS!!!



