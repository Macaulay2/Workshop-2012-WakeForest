makeDets  = (a,mu) -> (
    -- mu is a list of a filled tableau
    Ind :=  apply(mu, m -> apply(#m, i-> apply(#m,j -> (m_i, j))) );
    R := QQ[(flatten flatten Ind)/(v -> a_v)];
    Ma := apply(Ind, k ->  applyTable(k, j -> value a_j));
    product apply(Ma, ma -> det matrix ma)
    )

makeUnsymmetric = L ->(
    Dets := apply(#L, i -> makeDets(vars i, L_i));
    rings := apply(Dets, i -> ring i);
    uberring := QQ[flatten apply(rings, r->gens r)];
    maps :=apply(rings, r -> map(uberring,r));
    product apply(#Dets, i -> maps_i(Dets_i))
    )

unfactor = F->(
     
     )

end
restart
load"m2make_poly.m2"
mu1 = {{1,2,3},{4}}
mu2 = {{1,2,3},{4}}

F=makeUnsymmetric( {mu1,mu2})
Ra=ring(makeDets(symbol a,mu1))
Rb=ring(makeDets(symbol b,mu2))

X= apply(#mu1_0, j-> apply(#mu2_0,i->x_(i,j) ) )
Rx = QQ[flatten X ]
R = Ra**Rb**Rx
use R
F
F=sub(F,R)

Ra1=sub(basis(1,Ra),R)
Rb1=sub(basis(1,Rb),R)


tmp=F;
for p from 1 to # mu1_0 do(
tmp=sum flatten apply(#mu1_0,   j-> apply(#mu2_0,i->x_(i,j)*contract(a_(p,i)*b_(p,j), tmp) ) )
)
tmp
for p from #mu1_0+1 to #mu1_0+#mu1_1 do(
tmp=sum flatten apply(#mu1_1,   j-> apply(#mu2_1,i->x_(i,j)*contract(a_(p,i)*b_(p,j), tmp) ) )
)
tmp
factor tmp

ABp= apply(#(mu1_0),
     p->apply(#mu1_0, 
	  j-> apply(#mu2_0,
	       i->a_(p+1,i)*b_(p+1,j) ) ))
apply(#(mu1_1),
     p->apply(#mu1_1, 
	  j-> apply(#mu2_1,
	       i->a_(p+1+#mu1_0,i)*b_(p+1+#mu1_0,j) ) ))
FA_0=contract(matrix(ABp_0), F);
X_0_0*((FA_0)_(0,0))
FAx = product(apply(#mu1_0, j-> apply(#mu2_0, i -> x_(i,j)*((FA_0)_(i,j))_0)))

#(flatten mu1)
options R
a_(1,0)
)
Ra1=sub(basis(1,Ra), R)

toString oo
matrix {{a_(1,0), a_(1,1), a_(1,2), 
	  a_(2,0), a_(2,1), a_(2,2), 
	  a_(3,0), a_(3,1), a_(3,2), 
	  a_(4,0), a_(4,1), 
	  a_(5,0), a_(5,1)}}

Rb1=sub(basis(1,Rb), R);

Ra1**Rb1


{makeDets("a", {{x,y,s},{z,w}}),makeDets("b", {{x,z,s},{y,w}})}

makeDets (String, List) := method()
ring(Ma_0_0_0)


mu = {{x,y,s},{z,w}}
mu = {{1,2,3},{4,5}}

restart
partition(3)

makeDets:=proc(a,LL::list,mu::list)
        local L:
        description "this procedure makes a product of
	 determinants of sizes determined by a partition LL.
	  The first index of each column is twisted by a permutation mu.";
        
		L:=myconjpart(LL):
return `*`(seq(Determinant(
Matrix([seq([seq(

a[op(j+( `+`(seq( op(p,L) ,p=1..k-1))),mu),i]

,j=1 .. op(k,L))], 
i = 1 .. op(k,L))])) ,
k=1..nops(L)))
end proc:


makeUnsymmetric:=proc(J::list,K::list)
	description "this procedure takes in a list of partitions J and a list of permutations K and produces the unsymmetrized (and factored!) tensor";
	
	local alpha;
	if(nops(J)<> nops(K)) then return "uneven";
	else
			alpha:= [a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z]:
			return `*`(seq(makeDets(alpha[i],J[i],K[i]),i=1..nops(J)))
	fi:
end proc:


unfactor:= proc(X,degree,L::list)
	description "X is the tensor, d is the degree, L is the list of dimensions of the vector spaces":

	local temp,temp2,p,i;

	if nops(L) >8 then return "too many factors"; fi:

	if nops(L) = 2 then
		temp2 := X; 

		for p to degree do 
			temp := 0; 
				for i[1] from 0 to op(1,L)-1 do for i[2] from 0 to op(2,L)-1 do
					temp := coeff(coeff(temp2, a[p, i[1]+1]), b[p, i[2]+1])*Z[[ seq(i[p],p=1..nops(L) )]]+temp 
				end do end do; 
			temp2 := temp; #print(nops(temp2)) 
		end do; 

		return temp;
	fi:

	if nops(L) = 3 then
		temp2 := X; 
		for p to degree do 
			temp := 0; 
			for i[1] from 0 to op(1,L) do for i[2] from 0 to op(2,L) do for i[3] from 0 to op(3,L) do 
				temp := coeff(coeff(coeff(temp2, a[p, i[1]+1]), b[p, i[2]+1]), c[p, i[3]+1])*Z[[ seq(i[p],p=1..nops(L) )]]+temp 
			end do end do end do; 

			temp2 := temp; #print(nops(temp2)) 
		end do; 

		return temp;
	fi:
end proc:

