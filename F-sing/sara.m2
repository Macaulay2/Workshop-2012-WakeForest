--a function to find the x-intercept of a line passing through two points
xInt = (x1, y1, x2, y2) ->  x1-(y1/((y1-y2)/(x1-x2)))
 
 
--- Computes the F-signature for a specific value a/p^e
--- Input:
---	e - some positive integer
---	a - some positive integer between 0 and p^e
---	f - some HOMOGENEOUS polynomial in two or three variables in a ring of PRIME characteristic
---
--- Output:
---	returns value of the F-signature of the pair (R, f^{a/p^e})
     
fSig = (e, a, f) -> (     
p= char ring f;     
1-(1/p^(dim(ring f)*e))*degree((ring f)^1/(ideal(apply(first entries vars R, i->i^(p^e)))+ideal(f^a))))     

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

threshEst=(f,e)->(
error "help";
p:=char ring f;
n:=nu(f,e);
error "help more";
if (isFRegularPoly(f,(n/(p^e-1)))==false) then n/(p^e-1)
else (
error "help most";
a=threshInt(e,(n-1)/p^e,fSig(e,n-1,f),n,f); 
error "help mostest";
if (isFRegularPoly(f,a)==false) then a
else
{a,(n+1)/p^e}
)
)











