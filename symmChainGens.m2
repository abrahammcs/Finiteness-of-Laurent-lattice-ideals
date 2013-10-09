-------------------------------
--	C. Hillar and A. Martin del Campo, 
--   "Finiteness theorems for invariant chains of Lattice ideals", 2009.
-------------------------------
--    This code is an implementation of the algorithms contained in the paper above 
--
----  Last Modification:    -----
--         Feb 11, 2010     -----
---------------------------------
--    Input: Exponent integer vector v
--    Output: symmGens :: List
--          A list with all the generators for the 
--          chain of Laurent ideals I_v^{+-} that
--          correspons to the toric ideal chain I_v
--
--
---------------------------------
--		EXAMPLE
---------------------------------
-- Let I be the ideal defined as the kernel of the map
-- x_{i,j}\mapsto t_i^2*t_j. The exponent vector of this map
-- is v={2,1}. We feed this vector in our code:
--
-- SymmetricChainGenerators({2,1})
--
-- The output will be a list of binomials that
-- generates the chain of Laurent ideals. After 
-- clearing denominators, the output of this example
-- can be found in the main example of the paper.
---------------------------------

needsPackage "FourTiTwo";

SymmetricChainGenerators = method(TypicalValue => List);
SymmetricChainGenerators(List) := (v) -> (
   n := 2*sum v;
   V1 := partitions(sum v, max v);
   V1 = apply(V1, a -> toList a); --the list of integer partitions of |v|
   M := createPermutMatrix(n,V1#0); -- creates a matrix with all the permutations of v

   L2 := entries transpose M;
      --    L2 is a list of n-dimensional vectors of all permutations 
      --    of the non-zero entries of v. We use it to eliminate unnecessary
      --    substitutions when we create the function \mu
    
   if #V1>1 then for i from 1 to #V1-1 do M = M | createPermutMatrix(n,V1#i);
   L := entries transpose M; --L is the list of column vectors
   Variabs := apply(L, l -> vectorToVariable(l,1));
   R := createRing(Variabs); --Create the polynomial ring on the variables Variabs

   ---------------------
   --now we use 4ti2 to compute the GBasis of the toric ideal defined by M
   I := toricGroebner(M,R); 
   G := first entries mingens I; -- G is a minimal generating set taken from I
   S := permutations n;   
   Gen := {};
      apply(G, g->(
         permg := for i from 1 to #S-1 list(
             applyPermToPoly(Variabs,g,R,(n,S#i))
            );
            cnt := 0;
         apply(Gen, f-> (if not member(f,permg) then cnt = cnt +1;));
         if cnt==#Gen then Gen = toList((set Gen) + (set {g}));
         )  
      );
   --    Gen is the list with all min generators of I mod symmetric gp.
   
   ----------------------------------------------------------
   --    We write a List of integer combinations for the variables:
   ----------------------------------------------------------
   temp := n-#v:0;
   v = v | toList temp;
   Quot := apply(L, l-> if member(l,L2) then {{1,l}} else symDecomp(l,v));
   ---------------------
   -- Quot will store the integer decomposition described in Prop. 4.7 of the paper
   ---------------------
   Qt := apply(Quot, a-> apply(a, b-> {b#0, x_(vectorToVariable(b#1,1))}));
   Monom := for i from 0 to #Qt-1 list(
   	if #Qt#i > 1 then (
   		T1 := {};
   		T2 := {};
   		apply(Qt#i, b-> if b#0 > 0 then T1 = T1 | {b#1^(b#0)} else T2 = T2 | {b#1^(-b#0)});
   		fold(times, T1)/(fold(times, T2))
   	)
   	else Qt#i#0#1
   );
   --------------------
   -- Monom is a list with all the fractions of monomials
   --------------------  
   Replacmnt := for i from 0 to #Monom-1 list ( R_i => Monom#i);
   symmGens := apply(Gen, g-> factor sub(g,Replacmnt));
   symmGens = select(symmGens, a-> value(a) != 0);
   return symmGens;
)

----------------------------
--    FUNCTIONS
----------------------------

------------------------------
-- Input: n - integer
-- 		  v - exponent vector \in\Z^k
--
-- createPermutMatrix will have as
-- input the exponent vector v\in\Z^k
-- it will tag a bunch of zeroes to 
-- make it a vector of size n
-- and create a Matrix A_n by permuting
-- the entries of this vector
------------------------------
createPermutMatrix = method()
createPermutMatrix(ZZ,List) := (n,v) -> (
	if #v < n then (
		for i to n-#v-1 do v = append(v,0);
	);
	M := transpose matrix unique permutations v;
	return M;
)

--------------------------------
-- Creates a polynomial ring with
-- coefficients in QQ using a given
-- list of variables
--------------------------------
createRing = method()
createRing(List) := (V) ->(
	L := for i from 0 to #V-1 list(x_(V#i));
	return QQ[L];
)


----------------------------------
permutedVars = method()
permutedVars(ZZ,List,List) := (n,V,w) ->(
   V = apply(V, a-> apply(a, j->j-1));
   T := apply(V, a->w_a);
   apply(T, a->sort(apply(a, j->j+1)))
)

---------------------------------------
-- Usage:
-- applyPermToPoly(V,f, R,numbperm)
--    V is the list of variables
--      (usually created with CreateVars
--    f a poly in 
--    R = QQ[x_V]
--    numbperm = (n,w), where
--    w a permutation in S_n
--    n is the largest integer in the 
--       index set of the variables
-------------------------------------
applyPermToPoly = method()
applyPermToPoly(List, RingElement, Ring, Sequence) := (V, f, R, numbperm)->(
   -- needed to create a sequence to input more than 4 things:
   (n, w) := numbperm;
   wVar := permutedVars(n,V,w);
   XwV := for i from 0 to #wVar-1 list(x_(wVar#i));
   wR := QQ[XwV];
   LL := for i to #wVar-1 list(x_(wVar#i));
   appPer := map(wR,R, LL);
   g := appPer (f);
   substitute(g,R)
)

--------------------------------
-- vectorToVariable(v,flag)
-- translate the variables for the form
-- {2,1,0,0}, {1,1,1,0}
-- for variables of the form {1,1,2}
-- input: an integer vector {0,1,0,2}
-- output: the index of the variable {2,4,4}
-- the FLAG: 0 if you want it with out repetitions
--           anything else if you want it with reps
--------------------------------
vectorToVariable = method()
vectorToVariable(List, ZZ) := (u,f) ->(
   T := {};
   for i from 0 to (max u - 1) do (
      temp = positions(u,v-> v==(max u - i));
      if f == 0 then (
         T = T | temp;
         ) 
      else (
         T1 := for j from 1 to (max u - i) list(temp);
         T = T | sort flatten T1;
         )
   );
return sort apply(T, b-> b+1);
) 

----------------------------------
-- Example:
-- vectorToVariable ({1,1,2,0,3},0)
-- returns:
-- {5, 3, 1, 2}
-- whereas
-- vectorToVariable ({1,1,2,0,3},1)
-- returns:
-- {5, 5, 5, 3, 3, 1, 2}
--------------------------------

-------------------------
-- symDecomp(u,v)
--
-- INPUT: n dimensional integer vectors (lists) u,v with |v| dividing |u|
--	and GCD(v) = 1 [and the last element of v is zero].
-- (here, |u| is the sum of the entries of u) 
-- OUTPUT: A decomposition of u as a sum
--	u = SUM[c_i*a_i]
-- where a_i are permuted versions of v and c_i are integers.
-- this OUTPUT is given as a list of (multiplicity) lists. i.e. 
-- 			{{m1,l1},...,{mn,ln}}
--  where mi are integers and li are permutations of v
--
-- EXAMPLE:  input is v = {2,1,0,0}, u = {1,1,1,0} then the output should be 
--     {{1,{1,2,0,0}},{-1,{0,2,0,1}},{1,{0,1,2,0}},{-1,{2,0,1,0}},{1,{2,0,0,1}}}
--
-- u = {1,1,1,0}; v = {2,1,0,0};
-- symDiffDecomp(u,v)
--
-- The ALGORITHM that computes this is in the paper
-- Christopher Hillar and Abraham Martin del Campo, 
-- "Finiteness theorems for chains of toric ideals", 2009.
--

symDecomp = method( TypicalValue => List)
symDecomp(List,List) := (u,v) -> (
  n := #v;
  if sum(u)%sum(v) != 0 then ( return "Invalid Input"; );
  if gcd(v) != 1 then ( return "Invalid Input"; );
  -- Step 1: decompose 1 = v1b1 + ... + vnbn
  b := extendedMultGCD(v);
  q := sum(u)//sum(v);
  totMultListu := new MutableList from {{sum(u)//sum(v),v}};
  for j from 0 to (n-2) do (
    if (u#j-v#j*q) != 0 then (
      temp = timesScalarMultList(u#j-v#j*q, formHj(b,v,j));
      totMultListu = sumMultLists(toList(totMultListu), temp);
      --print(toList totMultListu);
    )
  );
  return toList totMultListu;
)

-----------------------
--        FUNCTIONS 
--        symDecomp
--    that Create the symmetric vector decomposition
------------------------
-- extendedGCD(a,b)
--
-- INPUT: two integers a,b
-- OUTPUT: integers x,y such that
--	ax + by = GCD(a,b)
-- The algorithm is the standard extended GCD one

extendedGCD = method( TypicalValue => List)
extendedGCD(ZZ,ZZ) := (a,b) -> (
	if a%b == 0 then  return {0,1}
		else ( T := extendedGCD(b,a%b);
	return {T#1,T#0-T#1*(a//b)}; );
)

-----------------------
-- extendedMultGCD(u)
--
-- INPUT: integral vector list u = {u1,...,un}
-- OUTPUT: integer list x = {x1,...,xn} such that
--	u1x1 + ... + unyn = GCD(u)
--
-- v = {40,6,15};
-- extendedMultGCD(v)
--
-- gives: {1, 26, -13}
--

extendedMultGCD = (u) -> (
  n := #u;
  if n == 2 then return extendedGCD(u#0,u#1);
  x := extendedMultGCD(drop(u,{0,0}));
  d := gcd(drop(u,{0,0}));
  y := extendedGCD(u#0,d);
  -- Now need to merge these two x and y
  z := join({y#0},y#1*x);
  return z;
)


----------------------------
-- timesScalarMultList(m,L)
--
-- INPUT: a "multiList" L = {{m1,l1},...,{mn,ln}} and an integer m
-- OUTPUT: a "multiList" {{m*m1,l1},...,{m*mn,ln}}
--

timesScalarMultList = method(TypicalValue => List)
timesScalarMultList(ZZ,List) := (m,L) -> (
  return apply(L, u -> ( join({m*u#0},drop(u,{0,0}))));
)



----------------------------
-- sumMultLists(L1,L2)
--
-- INPUT: "multiLists" L1 = {{m1,l1},...,{mn,ln}}, L2
-- OUTPUT: a "multiList" S = {{r1,s1},...,{rn,sn}}
-- 	which is the multilist obtained by adding the multiplicities
-- ASSUMPTION: there are no repeats of the lj in the lists
--
-- EXAMPLE:  {{1, {2, 2}}, {2, {2, 3}}, {1, {3, 1}}} + 
--		{{1, {2, 3}}, {3, {0, 1}}, {-1, {3, 1}}}
--	=   {{3, {2, 3}}, {1, {2, 2}}, {3, {0, 1}}}
-- L1 = {{1, {2, 3}}, {3, {0, 1}}}
-- L2 = {{1, {2, 2}}, {2, {2, 3}}, {1, {3, 1}}}
-- L3 = {{1, {2, 3}}, {3, {0, 1}}, {-1, {3, 1}}}
-- sumMultLists(L1,L2)
-- sumMultLists(L1,L3)
-- sumMultLists(L2,L3)

sumMultLists = method(TypicalValue => List)
sumMultLists(List,List) := (L1,L2) -> (
  n1 := #L1; n2 := #L2;
  Hit1 := new MutableList; Hit2 := new MutableList; S := new MutableList;
  for i from 1 to n1 do Hit1 = append(Hit1,0);
  for i from 1 to n2 do Hit2 = append(Hit2,0);
  for i from 0 to (n1-1) do (
    for j from 0 to (n2-1) do ( 
      if (L1#i)#1 == (L2#j)#1 then ( 
        if (L1#i)#0 != -(L2#j)#0 then (
		S = join(S,{{(L1#i)#0+(L2#j)#0,(L1#i)#1}});    
        );
        Hit1#i = 1;  
	Hit2#j = 1;
      );
    );
  );
  for i from 0 to (n1-1) do (
    if Hit1#i == 0 then S = join(S,{{(L1#i)#0,(L1#i)#1}}); 
  );
  for i from 0 to (n2-1) do (
    if Hit2#i == 0 then S = join(S,{{(L2#i)#0,(L2#i)#1}}); 
  );
  return toList S;
)

-------------------------
-- newMultList(m,v)
--
-- forms a new MultList from list v and multiplicity m
-- 
-- newMultList(5,{1,2,3}) is {5,{1,2,3}}

newMultList = method( TypicalValue => List)
newMultList(ZZ,List) := (m,v) -> (
  join({m}, {v}) 
)
-------------------------
swapv = method( TypicalValue => List )
swapv(List,ZZ,ZZ) := (h,j,i) -> (
     -- swap i and j elements in h
     vswap := new MutableList from h;
     temp := vswap#i;
     vswap#i = vswap#j;
     vswap#j = temp;
  return toList vswap;
)


-------------------------
-- formHj(b,v,j)
--
--
-- forms the hj vector from vectors v and b (see the paper)
--

formHj = method( TypicalValue => List )
formHj(List,List,ZZ) := (b,v,j) -> (
   hj := new MutableList from {};
   h2j := new MutableList;
   for i from 1 to (#b-1) do (
     -- swap i and j elements in v
		w:=swapv(v,i,j);
		w2:=swapv(w,j,#v-i);
     if b#i !=0 then (
       if #hj > 0 then ( hj = append(hj,{b#i,w}); );
       if #h2j > 0 then ( h2j = append(h2j,{-b#i,w2}); );
       if #hj == 0 then ( hj = {{b#i,w}}; );
       if #h2j == 0 then ( h2j = {{-b#i,w2}}; );
     )
  );
  return(toList hj | toList h2j);
)

