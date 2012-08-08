--a function to find the x-intercept of a line passing through two points
xInt = (x1, y1, x2, y2) ->  x1-(y1/((y1-y2)/(x1-x2)))
 
 
     
--- 
--- Input:
---	t - some positive rational number
---	b - the f-signature of (R,f^{t/p^e})
---     e - some positive integer
---     t1- another rational number > t
---	f - some HOMOGENEOUS polynomial in two or three variables in a ring of PRIME characteristic
---
--- Output:
---	fSig applied to (e,t1,f)
---	x-intercept of the line passing through (t,b) and (t1,fSig(e,t1,f))

threshInt = (e,t,b,t1,f)-> (
{b1=fSig(e,t1,f),xInt(t,b,t1/p^e,b1)}
)



---f-pure threshold estimation
---e is the max depth to search in
---finalCheck is whether the last isFRegularPoly is run (it is possibly very slow) 
threshEst=(f,e, finalCheck)->(
     --error "help";
     p:=char ring f;
     n:=nu(f,e);
     --error "help more";
     if (isFRegularPoly(f,(n/(p^e-1)))==false) then n/(p^e-1)
     else (
	  --error "help most";
	  ak:=threshInt(e,(n-1)/p^e,fSig(e,n-1,f),n,f); 
	  --if (DEBUG == true) then error "help mostest";
	  if ( (n+1)/p^e == (ak#1) ) then (ak#1)
	  else if (finalCheck == true) then ( 
	       if (isFRegularPoly(f,(ak#1) )==false) then (ak#1)
	       else {(ak#1),(n+1)/p^e} 
	  )
	  else {(ak#1),(n+1)/p^e}
     )
)










