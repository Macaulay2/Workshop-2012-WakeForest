needsPackage "MultiplierIdeals";

-- Examples from [Shibuta, 2011]
-- arXiv:0807.4302v6 [math.AG]
-- http://arxiv.org/abs/0807.4302
-- Shibuta, Takafumi
-- Algorithms for computing multiplier ideals.
-- J. Pure Appl. Algebra 215 (2011), no. 12, 2829–2842.
-- MR2811565

-- Example 5.3 of [Shibuta, 2011]
R = QQ[x,y];
jumpingNumbers(monomialIdeal(y^2,x^5))

-- Example 5.4 of [Shibuta, 2011]
f = x*y*(x+y)*(x+2*y);
ff = first \ toList factor f;
A = arrangement ff;
jumpingNumbers(A)

-- Example 5.5 of [Shibuta, 2011]
R = QQ[x,y,z];
jumpingNumbers(R,{4,5,6})

-- Example 5.6 of [Shibuta, 2011]
jumpingNumbers(R,{4,6,9})

-- Example 5.7 of [Shibuta, 2011]
jumpingNumbers(R,{4,6,7})

-- Example 5.8 of [Shibuta, 2011]
jumpingNumbers(R,{6,8,11})

-- Example 5.9 of [Shibuta, 2011]
R = QQ[t_1..t_6];
X = genericMatrix(R,2,3);
jumpingNumbers(X,2)

-- Example 5.10 of [Shibuta, 2011]
R = QQ[x,y,z];
jumpingNumbers(R,{3,4,5})


-- Examples from [Berkesch-Leykin, 2010]
-- arXiv:1002.1475v2 [math.AG]
-- http://arxiv.org/abs/1002.1475
-- to appear in ISSAC 2010

-- Example 6.3 of [Berkesch-Leykin, 2010]
R = QQ[x,y,z];
f = (x^2-y^2)*(x^2-z^2)*(y^2-z^2)*z;
ff = first \ toList factor f;
A = arrangement ff;
jumpingNumbers(A)


-- Examples from [Thompson, 2010]
-- arXiv:1006.1915v4 [math.AG]
-- http://arxiv.org/abs/1006.1915v4

-- Example 3.9 of [Thompson, 2010]
-- the (3,4,5) curve


-- Examples from [Thompson, 2012]
-- Multiplier ideals of binomial ideals
-- private communication, May 2012

-- Appendix E of [Thompson, 2012]
-- (4,5,6,7) curve

