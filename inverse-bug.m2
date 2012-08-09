-- reported by Brett
errorDepth=0
debug Core
R = ZZ/101[x,y]
phi = (minimalPresentation ker matrix{{x^2+1, x, y}}).cache.pruningMap
isIsomorphism phi
 phi^-1 -- fails
f = id_(target phi)
g = phi
assert not M.?relations 
-- from quotientRemainder(Matrix,Matrix) := Matrix => (f,g) -> 
     M = target f
     L = source f
     N = source g
     f = matrix f
     g = matrix g
     ( map(N, L, f//g), map(M, L, f%g) )

The problem is that quotientRemainder doesn't work when M.?generators!
