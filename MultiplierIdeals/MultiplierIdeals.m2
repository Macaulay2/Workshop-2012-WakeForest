-- -*- coding: utf-8 -*-
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- MULTIPLIER IDEALS -----------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Copyright 2011 Claudiu Raicu, Bart Snapp, Zach Teitler
--
-- This program is free software: you can redistribute it and/or modify it under
-- the terms of the GNU General Public License as published by the Free Software
-- Foundation, either version 3 of the License, or (at your option) any later
-- version.
--
-- This program is distributed in the hope that it will be useful, but WITHOUT
-- ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
-- FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
-- details.
--
-- You should have received a copy of the GNU General Public License along with
-- this program.  If not, see <http://www.gnu.org/licenses/>.
--------------------------------------------------------------------------------

newPackage(
	"MultiplierIdeals",
    	Version => "0.1", 
    	Date => "July 31, 2011",
    	Authors => {
	     {Name => "Zach Teitler"},
	     {Name => "Bart Snapp"},
	     {Name => "Claudiu Raicu"}
	     },
    	Headline => "multiplier ideals, log canonical thresholds, and jumping numbers",
    	PackageImports=>{"Dmodules"}
    	)
--needsPackage "Normaliz"
--needsPackage "MonomialMultiplierIdeals"
--needsPackage "ReesAlgebra"
--needsPackage "HyperplaneArrangements"


-- Main functionality:
-- Multiplier ideals.
-- Input: an ideal, a real number
-- Output: the multiplier ideal
-- For arbitrary ideals, use the Dmodules package
-- When possible, use specialized routines for
--  monomial ideals (implemented in this package)
--  ideal of monomial curve (implemented in this package)
--  hyperplane arrangements (implemented in HyperplaneArrangements)


-- This implementation is based on the algorithm given in
-- H.M. Thompson's paper: "Multiplier Ideals of Monomial Space
-- Curves." arXiv:1006.1915v4 [math.AG] 
-- 
-- http://arxiv.org/abs/1006.1915


--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- EXPORTS ---------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

export {
     multIdeal,
     AutomaticMultIdealStrat,
     DmodulesMultIdealStrat,
     MonomialMultIdealStrat
     }

exportMutable {}

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- PACKAGES --------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------


--setNmzOption("bigint",true);

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- METHODS ---------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------



multIdealViaDmodules := (I,t) -> (
  Dmodules$multiplierIdeal(I,t)
  );


{*
  multIdeal

   Compute multiplier ideal of an ideal, using various strategies.
   - For general ideals, use Dmodules package.
   - For hyperplane arrangement, use HyperplaneArrangements package.
   - For monomial ideals, use Howald's theorem, implemented in this package.
   - For ideal of monomial curve, use Howard Thompson's theorem, implemented
     in this package.
  
   Optional argument: Strategy
   Possible values: DmodulesMultIdealStrat, MonomialMultIdealStrat,
    MonomialCurveMultIdealStrat, HyperplaneArrangementMultIdealStrat,
    AutomaticMultIdealStrat
   Default value: 'AutomaticMultIdealStrat'
   'Automatic' strategy tries strategies from "cheapest" to most general:
   1. if input ideal is a MonomialIdeal, use Monomial strategy
   2. else if input ideal defines a monomial curve, use MonomialCurve strategy
   3. else if input ideal defines a hyperplane arrangement, use that strategy
      (not yet sure how to test for this)
   4. else use Dmodules strategy.
  
   Input:
   With Dmodules strategy:
    * ideal I
    * rational t
   With Monomial strategy:
    * MonomialIdeal I
    * rational t
   With MonomialCurve strategy:
    * ring S
    * list of integers {a1,...,an} (exponents in parametrization of curve)
    * rational t
    OR
    * ideal I which happens to be the defining ideal of a monomial curve
    * rational t
   With HyperplaneArrangement strategy:
    * CentralArrangement A
    * rational t
    * (optional) list of multiplicities M
    OR (can we do this?)
    * ideal I which happens to be the defining ideal of a central arrangement
      (with multiplicities)
    * rational t
  
   Output:
    * Ideal or MonomialIdeal
*}


multIdeal = method(TypicalValue=>Ideal,
                         Options=>{Strategy=>AutomaticMultIdealStrat});

-- with integer input:
-- promote to rational number, keep options the same
multIdeal(Ideal,ZZ) := opt -> (I,t) ->
  multIdeal(I,promote(t,QQ),opt);


multIdeal(Ideal,QQ) := opt -> (I,t) -> (
  if (opt.Strategy == DmodulesMultIdealStrat) then (
    return multIdealViaDmodules(I,t);
  ) else if (opt.Strategy == AutomaticMultIdealStrat) then (
    return multIdeal(I,t,Strategy=>DmodulesMultIdealStrat);
  );
  );



end

