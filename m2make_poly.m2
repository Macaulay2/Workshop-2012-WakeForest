makeDets  = (a,mu) -> (
    -- mu is a list of a filled tableau
    Ind:=new MutableHashTable;
    scan (mu, m-> scan (#m,i-> Ind#(m_i) =#m   ));
    Ind = new HashTable from Ind;
    R := QQ[flatten apply( #(flatten mu)  ,p->apply(Ind#(p+1) , i->  a_(p+1,i) )) ];
    Ma :=apply( mu, m->apply(m,  p->apply(Ind#(p) , i-> value  a_(p,i) )));
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

mu = {{1,2,4},{3,5}}
Ind=new MutableHashTable;
scan (mu, m-> scan (#m,i-> Ind#(m_i) =#m   ));
Ind = new HashTable from Ind
R = QQ[flatten apply( #(flatten mu)  ,p->apply(Ind#(p+1) , i->  a_(p+1,i) )) ]
R_*

apply( mu, m->apply(m,  p->apply(Ind#(p) , i->  a_(p,i) )))
    Ma =apply( mu, m->apply(m,  p->apply(Ind#(p) , i->  a_(p,i) )))
    product apply(Ma, ma -> det matrix ma)

restart
load"m2make_poly.m2"
mu1 = {{1,2,3},{4,5}}
mu2 = {{1,2,4},{3,5}}


F=makeUnsymmetric( {mu1,mu2});
Ra=ring(makeDets(a,mu1))
Rb=ring(makeDets(b,mu2))
X= apply(#mu1_0, j-> apply(#mu2_0,i->x_(i,j) ) )
Rx = QQ[flatten X ]
R = Ra**Rb**Rx
use R
F=sub(F,R);

--make a hash table that tells the number of elements in each letter
-- note hashtable #key = what it gets
plist=new MutableHashTable
scan (mu1, m-> scan (#m,i-> plist#(m_i) ={#m,0}   ))
scan (mu2, m-> scan (#m,i-> plist#(m_i) ={(plist#(m_i))_0,#m}))
plist = new HashTable from plist


tmp=F;
scan(1 .. #(flatten mu1), p-> tmp=sum flatten apply(plist#p#1,j-> apply(plist#p#0,i-> x_(i,j)*contract( a_(p,i)*b_(p,j),tmp )  )))
tmp
factor tmp

--- here's a 3-factor example

restart
load"m2make_poly.m2"
mu1 = {{1,2,3},{4,5}}
mu2 = {{1,2,4},{3,5}}
mu3 = {{1,3,5},{2,4}}

plist=new MutableHashTable
scan (mu1, m-> scan (#m,i-> plist#(m_i) ={#m,0,0}   ))
scan (mu2, m-> scan (#m,i-> plist#(m_i) ={plist#(m_i)#0,#m,0}))
scan (mu3, m-> scan (#m,i-> plist#(m_i) ={plist#(m_i)#0,plist#(m_i)#1, #m}))
plist = new HashTable from plist

F=makeUnsymmetric( {mu1,mu2, mu3});
Ra=ring(makeDets(a,mu1))
Rb=ring(makeDets(b,mu2))
Rc=ring(makeDets(c,mu3))
X= apply(#mu3_0,k->apply(#mu2_0, j-> apply(#mu1_0,i-> x_(i,j,k) ) ))
Rx = QQ[flatten flatten X ]
R = Ra**Rb**Rc**Rx
use R
F=sub(F,R);


tmp=F;
scan(1 .. #(flatten mu1), p-> tmp=sum flatten flatten apply(plist#p#2,k->  apply(plist#p#1,j-> apply(plist#p#0,i-> 
		    x_(i,j,k)*contract( a_(p,i)*b_(p,j)*c_(p,k),tmp )
		      ))) )
tmp 
factor tmp
viewHelp drop

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

