restart
debug needsPackage"SchurRings"

S1 = schurRing(s1,2)
S2 = schurRing(S1,s2,2)

k = 4
rep = s1_k * s2_1

m = 7
M = {1_S2} | for r from 1 to m list
(
     sum for i from 0 to r list
         sum for j from 0 to r//2 list
     	     if i+j >= 2*max((i+k-1)//k,j) and i+j <= r then
	        (if i == 0 then s1_{k*r} else s1_(k*r-i,i))*(if j == 0 then s2_{r} else s2_(r-j,j)) else 0
		);

schurResolution(rep,M,SyzygyLimit => 1,DegreeLimit => m)

dim(M#3)

restart
debug needsPackage"SchurRings"

S1 = schurRing(s1,2)
S2 = schurRing(S1,s2,2)

k = 8
rep = s1_k * s2_2

m = 10
M = {1_S2} | for r from 1 to m list
(
     sum for i from 0 to k*r//2 list
         sum for j from 0 to r list
     	     if i+j >= 2*max((i+k-1)//k,(j+1)//2) and i+j <= r then
	        (if i == 0 then s1_{k*r} else s1_(k*r-i,i))*(if j == 0 then s2_{2*r} else s2_(2*r-j,j)) else 0
		);
schurResolution(rep,M,SyzygyLimit => 1,DegreeLimit => m)

--2-factor Segre-Veronese
restart
debug needsPackage"SchurRings"

S1 = schurRing(s1,2)
S2 = schurRing(S1,s2,2)

k = 3
l = 1
rep = s1_k * s2_l

m = 4
M = {1_S2} | for r from 1 to m list
(
     sum for i from 0 to k*r//2 list
         sum for j from 0 to l*r//2 list
     	     if i+j >= 2*max((i+k-1)//k,(j+l-1)//l) and i+j <= r then
	        (if i == 0 then s1_{k*r} else s1_(k*r-i,i))*(if j == 0 then s2_{l*r} else s2_(l*r-j,j)) else 0
		);
schurResolution(rep,M,SyzygyLimit => 1,DegreeLimit => m)

--3-factor Segre-Veronese
restart
debug needsPackage"SchurRings"

S1 = schurRing(s1,2)
S2 = schurRing(S1,s2,2)
S3 = schurRing(S2,s3,2)

k = 5
l = 1
o = 1
rep = s1_k * s2_l * s3_o

m = 6
M = {1_S3} | for r from 1 to m list
(
     sum for i from 0 to k*r//2 list
         sum for j from 0 to l*r//2 list
             sum for t from 0 to o*r//2 list
     	     if i+j+t >= 2*max((i+k-1)//k,(j+l-1)//l,(t+o-1)//o) and i+j+t <= r then
	        (if i == 0 then s1_{k*r} else s1_(k*r-i,i))*(if j == 0 then s2_{l*r} else s2_(l*r-j,j))*(if t == 0 then s3_{o*r} else s3_(o*r-t,t)) 
	     else 0
		);
schurResolution(rep,M,SyzygyLimit => 1,DegreeLimit => m)

