InvolutionRankNu := function(k, s, DD, NN : Positive := false);
  // computes nu as a function of the squarefree level NN at the split real places s

  NNfact := Factorization(NN);
  assert {ppf[2] : ppf in NNfact} join {1} eq {1}; // NN must be squarefree
  S := [ppf[1] : ppf in NNfact];
  S_DD := S cat [ppf[1] : ppf in Factorization(DD)];
  Sel2, m := pSelmerGroup(2, {Parent(1*Integers(k)) | pp : pp in S_DD});

  h := function(x); if x eq 1 then return GF(2)!0; else return GF(2)!1; end if; end function;
  if Positive then
    Moo := [[h(ux) : ux in RealSigns(Sel2.i@@m)] : i in [1..#Generators(Sel2)]];
  else
    Moo := [[h(RealSigns(Sel2.i@@m)[j]) : j in [1..Degree(k)] | j notin s] : i in [1..#Generators(Sel2)]];
  end if;
  if Degree(k) eq #s then
    Mpgens := [[GF(2) | Valuation(Sel2.i@@m,pp) : pp in S] : i in [1..#Generators(Sel2)]];
  else
    kerM := Kernel(Matrix(GF(2),Moo));
    if Dimension(kerM) eq 0 then
      return 0;
    end if;
    Mpgens := [[GF(2) | Valuation((Sel2!Eltseq(c))@@m,pp) : pp in S] : c in Basis(kerM)];
  end if;
  return Rank(Matrix(Mpgens));
end function;
  
MaximalVolumes := function(k, s, DD, NN, Zeta_arith : verbose := false);
  // computes the volume of the maximal quaternionic arithmetic group
  // over k with discriminant DD and squarefreelevel NN at the split real places s
  // returns maximal holomorphic volume, maximal stable volume, and the index of the 
  // former in the latter; answers are arithmetic (so should be multiplied by pi^2)
  
  RR := RealField();
  pi := Pi(RR);
  assert IsTotallyReal(k);
  r := Degree(k);
  R := Integers(k);

  dk := Discriminant(R);
  zeta2 := Evaluate(LSeries(k),2);
  assert #s eq 2;
//   volX1 := 2*(4*pi)^#s/(4*pi^2)^r*dk^(3/2)*zeta2;
  volX1_arith := 2*4^2*Zeta_arith/2^r;
  if verbose then print "vol(X^1_0) = (", volX1_arith, ")*pi^2"; end if;

  if Norm(DD) gt 1 then
    volX1_arith *:= Norm(DD)*&*[1-1/Norm(ppf[1]) : ppf in Factorization(DD)];
  end if;
  if Norm(NN) gt 1 then
    volX1_arith *:= Norm(NN)*&*[1+1/Norm(ppf[1]) : ppf in Factorization(NN)];
  end if;
  if verbose then print "vol(X^1) =", volX1_arith, "*pi^2"; end if;

  U, mU := UnitGroup(R);
  h := function(x); if x eq 1 then return GF(2)!0; else return GF(2)!1; end if; end function;
  krank := Rank(Kernel(Matrix([[h(ux) : ux in RealSigns(mU(U.i))] : i in [1..Degree(k)]])));
  volXplus_arith := volX1_arith/2^krank;
  if verbose then print "vol(X^+) = (", volXplus_arith, ")*pi^2, pos unit size = ", 2^krank; end if;

  if #s eq 2 then
    ks := 2;
  else
    ks := Rank(Kernel(Matrix([[h(ux) : ux in [RealSigns(mU(U.i))[cs] : 
                          cs in [1..Degree(k)] | cs notin s]] : i in [1..Degree(k)]])));
  end if;
  voltXplus_arith := volX1_arith/2^ks;
  if verbose then 
    print "vol(tX^+) = (", voltXplus_arith, ")*pi^2, unit size = ", 2^ks; 
  end if;
   
  Clplus, mClplus := NarrowClassGroup(k);
  if Norm(DD*NN) gt 1 then
    Clplusmodsq, mClplusmodsq := quo<Clplus | [2*Clplus.i : i in [1..#Generators(Clplus)]]>;
    Mplus := [Eltseq(mClplusmodsq(ppf[1]@@mClplus)) : ppf in Factorization(DD*NN)];
    Mplus := Matrix(GF(2), Mplus);
    w := Dimension(Kernel(Mplus));
  else
    w := 0;
  end if;
  volXw_arith := volXplus_arith/2^w;
  if verbose then 
    print "vol(X^w) = (", volXw_arith, ")*pi^2, Atkin-Lehner size = ", 2^w; 
  end if;

  ClB, mClB := RayClassGroup(1*Integers(k), [j : j in [1..Degree(k)] | j notin s]);
  if Norm(DD*NN) gt 1 then
    ClBmodsq, mClBmodsq := quo<ClB | [2*ClB.i : i in [1..#Generators(ClB)]]>;
        // Assumes NN squarefree here
    M := [Eltseq(mClBmodsq(ppf[1]@@mClB)) : ppf in Factorization(DD*NN)];  
    M := Matrix(GF(2), M);
    tw := Dimension(Kernel(M));
  else
    tw := 0;
  end if;
  voltXw_arith := voltXplus_arith/2^tw;
  if verbose then 
    print "vol(tX^w) = (", voltXw_arith, ")*pi^2, unoriented Atkin-Lehner size = ", 2^tw; 
  end if;
  
  Cl, mCl := ClassGroup(k);
  Cl2 := Kernel(hom<Cl -> Cl | [2*x : x in Generators(Cl)]>);
  Cl2lowp := [x : x in Cl2 | Order((mCl(x))@@mClplus) le 2];
  volXstar_arith := volXw_arith/#Cl2lowp;
  if verbose then 
    print "vol(X^*) = (", volXstar_arith, ")*pi^2, type normalizer size = ", #Cl2lowp; 
  end if;

  ClB2 := Kernel(hom<ClB -> ClB | [2*x : x in Generators(ClB)]>);
  ClB2lowp := ClB2;
  voltXstar_arith := voltXw_arith/#ClB2lowp;

  if verbose then 
    print "vol(tX^*) = (", voltXstar_arith, ")*pi^2, unoriented type normalizer size = ", 
          #ClB2lowp; 
  end if;

  return volXstar_arith, voltXstar_arith, volXstar_arith/voltXstar_arith;
end function;

function IsIsomorphicOverQQ(B, Bp);
  // Check if B and Bp are isomorphic as QQ-algebras.
  k := BaseField(B);
  kp := BaseField(Bp);

  a,b := StandardForm(B);
  ap, bp := StandardForm(Bp);
  if k ne kp then
    bl, iota := IsIsomorphic(kp,k);
    if not bl then
      return false;
    end if;
    ap := iota(ap);
    bp := iota(bp);
  end if;

  // if B and Bp are isomorphic over QQ, then such an isomorphism
  // maps the center to itself, so after applying an automorphism of
  // the base field, it becomes an k-isomorphism...
  Autk := [hom<k -> k | r[1]> : r in Roots(MinimalPolynomial(k.1),k)];
  for iota in Autk do
    if IsIsomorphic(B, QuaternionAlgebra<k | iota(ap), iota(bp)>) then
      return true;
    end if;
  end for;
  return false;
end function;

function MaybeHasUnstableSupergroup2(DD, Soo, NN);
  // Check if there potentially exists an congruence subgroup in
  // the quaternion algebra of discriminant DD ramified at the set
  // Soo of infinite places of level NN with an unstable supergroup
  // k a totally real field
  k := NumberField(Order(DD));
  Zk := Integers(k);
  assert NumberField(Order(NN)) eq k;

  applyiota := function(iota, v0);
    // takes an automorphism of k and an infinite place v
    // and returns the place v circ iota
    v0iotak1 := Evaluate(iota(k.1),v0);
    koo := RealPlaces(k);
    alphas := [Evaluate(k.1,koo[i]) : i in [1..#koo]];
    epsalpha := Min([Abs(alphas[i]-alphas[j]) : i,j in [1..#koo] | i ne j]);    
    eps, minv := Min([Abs(v0iotak1-Evaluate(k.1,koo[i])) : i in [1..#koo]]);
    assert eps lt epsalpha/10;  
      // extra factor 10 for safety, we just need to know that there is only one
      // root in the neighborhood
    return koo[minv];
  end function;

  Autk := [hom<k -> k | r[1]> : r in Roots(MinimalPolynomial(k.1),k)];
  return #[iota : iota in Autk |
            SequenceToSet(Soo) eq {applyiota(iota,v) : v in Soo} and
            ideal<Zk | [iota(x) : x in Generators(DD)]> eq DD and
            ideal<Zk | [iota(x) : x in Generators(NN)]> eq NN] gt 1;
end function;

// This function uses theorem XXX to compute the lcm of the order of torsion elements
// in O_1^*/{+/-1}, which is a divisor of the order of torsion in the normalizer
// (with codivisor equal to 1 or 2)
TorsionLCM := function(k, DiscB, Sprod : verbose := false) 
  torslcm := 1;
  Ok := Integers(k);

  for cycindex in CyclotomicQuadraticExtensions(k) do
    Phis := Factorization(CyclotomicPolynomial(cycindex),k);
    assert &and[Degree(Phi[1]) eq 2 : Phi in Phis];  // sanity check
    Phi := Phis[1][1];  // any minimal polynomial gives isomorphic field
    L := ext<k | Phi>;
    OL := Integers(L);
    passedDD := true;
    for pp in Factorization(DiscB) do
      // locally embeds at pp | Disc(B) <=> pp does not split in L
      if #Factorization(OL!!pp[1]) eq 2 then  
        passedDD := false;
      end if;
    end for;
    
    passedNN := true;
    T := ext<Ok | Phi>;
    discT := Discriminant(T);
    for qq in Factorization(Sprod) do
      // locally embeds at qq | level <=> not (T is unramified and qq is inert in L) 
      if Valuation(Discriminant(T),qq[1]) eq 0 and #Factorization(OL!!qq[1]) eq 1 then
        passedNN := false;
      end if;
    end for;
    if verbose then
      print "Passed obstructions for cycindex =", cycindex, ": DD = ", passedDD, ", NN =", passedNN;
    end if;
    if passedDD and passedNN then
      torslcm := Lcm(torslcm, cycindex div Gcd(2,cycindex));
    end if;
    
    /*
    // Untested code
    if usenormalizer then
      // check for 2*cycindex in normalizer
      ephi := EulerPhi(cycindex);
      if cycindex mod 2 eq 1 then
        passedNN_max := true;
        for qq in Factorization(Sprod) do
          if Valuation(Discriminant(OL),qq[1]) eq 0 and #Factorization(OL!!qq[1]) eq 1 then
            passedNN_max := false;
          end if;
        end for;
        passedabsramind := true;
        for elll in Factorization(cycindex) do
          if Valuation(DiscB*Sprod, elll[1]) eq 0 and RamificationIndex(elll[1]) mod ephi ne 0 then
            passedabsramind := false;
          end if;
        end for;
        passedNN_norm := true;
        for qq in Factorization(Sprod) do
          if not ((#Factorization(OL!!qq[1]) eq 2) or 
                  (Valuation(Ok!cycindex,qq[1]) gt 0 and RamificationIndex(qq[1]) mod ephi eq 0)) then
            passedNN_norm := false;
          end if;
        end for;
        if verbose then
          print "Obstructions for odd normalizer:", passedNN_max, passedabsramind, passedNN_norm;
        end if;
        if passedNN_max and passedabsramind and passedNN_norm then
          torslcm := Lcm(torslcm, 2*cycindex);
        end if;
      else
        torslcm := Lcm(torslcm, 2*cycindex);
      end if;
    end if;
    */ 
  end for;

  return torslcm;
end function;

function HasNontrivialAutomorphism(k);
  return #Roots(MinimalPolynomial(k.1),k) gt 1;
end function;

TwoRank := function(k);
  Z_k := Integers(k);
  Uk, mUk := UnitGroup(k);
  // Stupid function, the isomorphism {1,-1} -> {0,1}.
  hiota := function(u);
    if u eq -1 then
      return 1;
    else
      return 0;
    end if;
  end function;

  UZd := AbelianGroup([2 : i in [1..Degree(k)]]);
  phi := hom<Uk -> UZd |
               [[hiota(Sign(Evaluate(mUk(Uk.i), v))) : v in RealPlaces(k)] :
                i in [1..#Generators(Uk)]]>;
  Ukmodsq, fsq := quo<Uk | [2*u : u in Generators(Uk)]>;
  posunitsize := #fsq(Kernel(phi));
  return Valuation(posunitsize,2);
end function;

MaxProductOfNormPrimeMinusOneOverTwo := function(Vbound_arith, k, Zeta_arith);  
  // return the maximum of the discriminant term in the volume formula for a 
  // minimal covolume group over k with covolume less than Vbound
//  return Vbound*(4*Pi(RealField())^2)^Degree(k)*(2^TwoRank(k)*
//                ClassNumber(k))*2^#PrimesUpTo(2,k)/(8*Pi(RealField())^2*
//                Abs(Discriminant(Integers(k)))^(3/2)*Zeta);
  return Vbound_arith*2^Degree(k)*(2^TwoRank(k)*ClassNumber(k))*2^#PrimesUpTo(2,k)
                  /(8*Zeta_arith);
end function;

LevelProductUpperBound := function(Vbound_arith, k, typenumber, Zeta_arith);  
  // return the maximum of the level term in the volume formula for a maximal 
  // arithmetic group Gamma_{S,O} over k with covolume less than Vbound
//  X := 2^#PrimesUpTo(2,k)*Vbound*(4*Pi(RealField())^2)^Degree(k)*typenumber/
//           (8*Pi(RealField())^2*Abs(Discriminant(Integers(k)))^(3/2)*Zeta);
  X_arith := 2^#PrimesUpTo(2,k)*Vbound_arith*2^Degree(k)*typenumber/
           (8*Zeta_arith);
      // Since nu <= |S|, this comes from equation (4.1)
  
  NuUpperBound := 0;
  nuprod := 1;
  normbnd := 100;  // just a place to start
  pps := PrimesUpTo(normbnd, k);
  i := 1;
  while nuprod le Ceiling(X_arith) do
    NuUpperBound +:= 1;
    nuprod *:= (Norm(pps[i])+1)/2;
    if i eq #pps then // ran out of primes, unlikely to happen!
      assert normbnd lt 1000;  // something is wrong
      normbnd +:= 100;
      pps := PrimesUpTo(normbnd, k);
    end if;
    i +:= 1;
  end while;
  
  return (2^NuUpperBound)*X_arith;
end function;

MaxNormOfRamPrimesFromVolume := function(Vbound_arith, k, Zeta_arith);  
  // return the maximum norm of a prime which ramifies in a fake quadric quaternion 
  // algebra over k in which the minimal covolume is less than Vbound
  return Integers()!Ceiling(2*MaxProductOfNormPrimeMinusOneOverTwo(Vbound_arith,k,Zeta_arith)+1);
end function;

MaxNumberOfRamPrimesFromVolume := function(Vbound_arith, k, Zeta_arith);  
  // return the maximum number of ramified primes in a fake quadric quaternion 
  // algebra over k in which the minimal covolume is less than Vbound
  n:=Degree(k);
  PrimesWhichCouldRamify := PrimesUpTo(MaxNormOfRamPrimesFromVolume(Vbound_arith,k,Zeta_arith), k);
  MaxTerms := 0;
  prod := 1;
  for pp in PrimesWhichCouldRamify do
    prod:=prod*(Norm(pp)-1)/2;
    if prod le MaxProductOfNormPrimeMinusOneOverTwo(Vbound_arith,k,Zeta_arith) then
      MaxTerms:=MaxTerms+1;
    end if;
  end for;
      
  if IsEven(n-2+MaxTerms+1) then
    MaxTerms:=MaxTerms-1;
  end if;

  return MaxTerms;
end function;

MaxNumberOfRamPrimesFromVolumeWithNormAtLeast4 := function(Vbound_arith, k, Zeta_arith);  
  // return the maximum number of ramified primes in a fake quadric quaternion 
  // algebra over k in which the minimal covolume is less than Vbound and norm >= 4
  PrimesWhichCouldRamify := PrimesUpTo(MaxNormOfRamPrimesFromVolume(Vbound_arith,k,Zeta_arith), k);
  MaxTerms4:=0;
  prod:=1;
  for pp in PrimesWhichCouldRamify do
    if Norm(pp) ge 4 then
      prod:=prod*(Norm(pp)-1)/2;
      if prod le MaxProductOfNormPrimeMinusOneOverTwo(Vbound_arith,k,Zeta_arith)*2^#PrimesUpTo(2,k) then
        MaxTerms4:=MaxTerms4+1;
      end if;
    end if;
  end for;
  
  return Minimum(MaxTerms4,MaxNumberOfRamPrimesFromVolume(Vbound_arith,k,Zeta_arith));
end function;

SetsOfRamifiedPrimes := function(k, X, MaxTerms, MaxTerms4);
  // Return the sets of potential Ram(B) for which the number of divisors of 
  // DiscB <= MaxTerms and number of divisors of DiscB with Norm >= 4 is 
  // <= MaxTerms4 and the product of the norm of the primes minus one over 2 
  // (i.e., term from the volume formula) is less than X
  n := Degree(k);
  Ram := SetToIndexedSet({});
  I2 := IdealsUpTo(Floor(2^#PrimesUpTo(2,k)*(8/3)^MaxTerms4*X)+1,k);
  for ideal in I2 do
    if Norm(ideal) gt 1 and IsSquarefree(ideal) then
      if IsEven(n-2+#Factorization(ideal)) and #Factorization(ideal) le MaxTerms then
        ideallist:=[];
        for idealfactor in Factorization(ideal) do
          Append(~ideallist,idealfactor[1]);
        end for;
        Ram := Ram join {Set(ideallist)};
      end if;
    end if;
  end for;
  return Ram;
end function;

SetsOfLevels := function(k,X);
  // Return the potential levels of the maximal arithmetic groups to be checked 
  SetOfS := SetToIndexedSet({});
  Include(~SetOfS, Set([1*Integers(k)]));
  IS := IdealsUpTo(Floor(2^#PrimesUpTo(2,k)*X),k);
  for ideal in IS do
    if Norm(ideal) gt 1 and IsSquarefree(ideal) then
      ideallist := [];
      for idealfactor in Factorization(ideal) do
        Append(~ideallist,idealfactor[1]);
      end for;
      Include(~SetOfS, Set(ideallist));
    end if;
  end for;
  return SetOfS;
end function;

RamToDiscList := function(k,Ram,X,n);
  // Takes a set Ram of ideals which could form a Ram(B) set and creates the set 
  // of associated DiscB ideals.
  // This is subject to the constraint that the product of (N(pp)-1)/2 is less than X
  PossibleDiscs := [];

  for ram in Ram do
    if IsEven(n-2+#ram) then
      ramprod := 1;
      ramprodminus1over2 := 1;
      for pp in ram do
        ramprod := ramprod*pp;
        ramprodminus1over2 := ramprodminus1over2*(Norm(pp)-1)/2;
      end for;
      if ramprodminus1over2 le X and Norm(ramprod) gt 1 then
        Append(~PossibleDiscs, ramprod);
      end if;
    end if;
  end for; // ram in Ram loop

  return [1*Integers(k)] cat PossibleDiscs;
end function;

LevelProducts := function(Zk, sset);
  // Given the set sset of primes dividing the level, return a number of related products
  
  ssetprodover2 := 1;
  ssetprod := 1;
  sprodideal := 1*Zk;
  
  for s in sset do
    if Norm(s) gt 1 then
    	ssetprodover2 := ssetprodover2*(Norm(s)+1)/2;
    	ssetprod := ssetprod*(Norm(s)+1);
    	sprodideal := sprodideal*s;
    end if;
  end for;
    
  return ssetprodover2, ssetprod, sprodideal;
end function;

ProdNormMinusOneOverTwo := function(DB);
  // Given an ideal DB returns the product of (N(pp)-1)/2
  RamTerm:=1;
  for pp in Factorization(DB) do
    RamTerm := RamTerm*(Norm(pp[1])-1)/2;
  end for;
  return RamTerm; 
end function;

TypeNumber := function(k,i,j,DB);
  // Given a totally real number field k, this function returns the type number of the quaternion algebra over k 
  // which is split at real places i and j (in Magma's numbering convention) of k, ramified at all other
  // real places of k, and is ramified at the prime divisors of the ideal DB. That is, the number of conjugacy 
  // classes of maximal orders in the quaternion algebra.
  Zk := Integers(k);
  n := Degree(k);
  G, m := RayClassGroup(1*Zk, [1..i-1] cat [i+1..j-1] cat [j+1..n]);
  GS := quo<G | [(pp[1])@@m : pp in Factorization(DB)] cat 
                      [2*u : u in Generators(G)]>;
  return #GS;
end function;