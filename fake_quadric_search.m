// This code enumerates maximal arithmetic subgroups of PGL_2(R) x PGL_2(R) which 
// may contain the stable subgroup of the fundamental group of an irreducible fake quadric.
// This search is described on pages 19-21 of the paper Commensurability Classes of Fake Quadrics 
// by Linowitz, Stover, and Voight.

load "all_helper.m";

RR := RealField();
pi := Pi(RR);
done := 1;  // index keeping track of total number of fields done so far

verbose := 1;  // verbose level: 0 for only the basics, 1 for some, 2 for a maximum amount

// keep track of data found
found := 0; 
foundfields := 0;
FinalFields := [];
FINALLIST := [];

// loop over all field polynomials provided by T
for fieldpoly in Reverse(T) do
  foundovercurrentfield := false;  // were there examples found over this field?

  // DISPLAY STATUS OF COMPUTATION
  print "------------------------------";
  if verbose ge 1 then
    print "Fields found so far: "; 
    print FinalFields;
  end if;
  
  print "Working on Field ", done, "of ", #T;
  done := done+1;

  // Compute k and its basic invariants
  k := NumberField(Polynomial(fieldpoly));
  n := Degree(k);
  koo := InfinitePlaces(k);
  Zk := Integers(k);
  Dk := Abs(Discriminant(Zk));
  h := ClassNumber(k);
  primesabove2 := #PrimesUpTo(2,k);

  // See Proposition 5.4 of
  // Kirschmer--Voight, "Algorithmic enumeration of ideal classes for quaternion orders",
  // SIAM J. Comput. (SICOMP) 39 (2010), no. 5, 1714-1747. 
  Zpi := Dk^(3/2)*Evaluate(LSeries(k),2)/(2*pi^2)^n;
      // evaluated rigorously to default precision prec(RR) = 30 
  m := Lcm(CyclotomicQuadraticExtensions(k));  
  assert Abs(Round(m*Zpi)-m*Zpi) lt 10^-7;  // enough to check lt 1/2
  Zeta_arith := Round(m*Zpi)/m;
  
  hasautk := HasNontrivialAutomorphism(k);
  if hasautk then
    Vbound_arith := 32;  // Remove factors pi
  else
    // See Theorem 2.3 and bound implied by (4.15)
    Vbound_arith := 16;  
  end if;
  if verbose ge 1 then
    if hasautk then
      print "k has a nontrivial automorphism group, so taking Vbound = 32*pi^2";
    else
      print "k has no nontrivial automorphisms, so taking Vbound = 16*pi^2";
    end if;
  end if;
    
  // Ram(B) must contain all but 2 real places, so next we 
  // compute the primes in Ram(B) for the quaternion algebras B to be checked
  // First bound #Ram(B) (MaxTerms and MaxTerms4), then
  // compute the levels of the Eichler orders to be checked
  PrimesWhichCouldRamify := PrimesUpTo(MaxNormOfRamPrimesFromVolume(Vbound_arith, k, Zeta_arith), k);
  MaxTerms := MaxNumberOfRamPrimesFromVolume(Vbound_arith, k, Zeta_arith);
  MaxTerms4 := MaxNumberOfRamPrimesFromVolumeWithNormAtLeast4(Vbound_arith, k, Zeta_arith);
    // two bounds apply, need to know primes with small norm in particular

  if MaxTerms eq 0 then
    Ram := [1*Integers(k)];  // must be unramified at all primes!
    PossibleDiscs := [1*Integers(k)];
  else // MaxTerms ge 1 then
    maxprodnmm1 := MaxProductOfNormPrimeMinusOneOverTwo(Vbound_arith, k, Zeta_arith);
    Ram := SetsOfRamifiedPrimes(k, maxprodnmm1, MaxTerms, MaxTerms4);
    PossibleDiscs := RamToDiscList(k,Ram, maxprodnmm1, n);
  end if;   

  // For each algebra with finite ramification, compute type number 
  // and ramification term in the volume formula
  for DB in PossibleDiscs do  
    // If the degree of k is odd then the algebra discriminant cannot be trivial
    // If the degree is 2 and the algebra is everywhere unramified, then we have
    // matrices and won't get compact manifolds
    if Norm(DB) eq 1 then
      if IsOdd(n) or n eq 2 then
        continue;
      end if;
    end if;
 
    // The type number may change based on choice of split real places i,j 
    // (numbered in some way by Magma)
    for i in [1..n-1] do
      for j in [i+1..n] do
        if verbose ge 1 then
          print "###################################";
          print "Checking k of discriminant:", Dk;
          print "Checking N(DB): ", Norm(DB);
          print "Checking split places i,j:",i,j;
        end if;

        // This is the minimal volume achieved in the comm. class.
        // Volume bound comes from (4.14); the type number is [K(B):k] and
        // 0 <= nu < #S so we can ignore the term 2^(-nu)*prod_{pp in S}(Nm(pp)+1)
        // Zeta is guaranteed to the default 30 digits, which is much larger than 1/eps
//        PartialMinVol := 8*pi^2*Dk^(3/2)*Zeta*ProdNormMinusOneOverTwo(DB)
//                              /((4*pi^2)^n*TypeNumber(k,i,j,DB));
        PartialMinVol_arith := 8*Zeta_arith*ProdNormMinusOneOverTwo(DB)/(2^n*TypeNumber(k,i,j,DB));

        if verbose ge 1 then
          print "PartialMinVol_arith computed: ", PartialMinVol_arith, "*pi^2";
        end if;

        if PartialMinVol_arith gt Vbound_arith then
          if verbose ge 1 then
            print "Volumes will be too big. Volume is: ", PartialMinVol_arith, "*pi^2", ">", Vbound_arith, "*pi^2";
          end if;
          continue;
        end if;

        if verbose ge 1 then
          print "Computing sets of levels... ";
        end if;
        SetOfS := SetsOfLevels(k, LevelProductUpperBound(Vbound_arith, k, TypeNumber(k,i,j,DB), Zeta_arith));

        for sset in SetOfS do
          ssetprodover2, ssetprod, sprodideal := LevelProducts(Zk, sset);

          if verbose ge 1 then
            if verbose ge 2 then
              print "Checking k of discriminant:", Dk;
              print "Checking N(DB): ", Norm(DB);
              print "Checking split places i,j:",i,j;
            end if;
            print "@@@@@ Checking level: ", Norm(sprodideal);
          end if;
            
          if Norm(Gcd(sprodideal,DB)) gt 1 then
            if verbose ge 1 then
              print "Algebra discriminant and level not coprime";
            end if;
            continue;
          end if;
            
          // Given S, we can refine whether or not there is an unstable supergroup
          VboundS_arith := Vbound_arith;  
          if hasautk then
            if not MaybeHasUnstableSupergroup2(DB, koo[1..i-1] cat koo[i+1..j-1] 
                                                 cat koo[j+1..n], sprodideal) then
              VboundS_arith := 16;  // as above 
            end if;
          end if;
            
          if PartialMinVol_arith*ssetprodover2 gt VboundS_arith then
            if verbose ge 1 then
              print "Volumes will be too big. Volume is: ", PartialMinVol_arith*ssetprodover2, "*pi^2", ">", VboundS_arith, "*pi^2";
            end if;
            continue;
          end if;      
      
          // We are under the hypothesis now that Gamma is of finite index 
          // in the normalizer of an Eichler order; we know the volume of
          // both, so we just need to check if the ratio is indeed an integer
          // so there's a chance for this subgroup to exist in the first place.
          ms := InvolutionRankNu(k,[i,j],DB,sprodideal);  // called nu in the paper
          m := VboundS_arith/(PartialMinVol_arith*ssetprod/2^ms);
          neversubmultiple := not IsCoercible(Integers(),m);
          
          if neversubmultiple then
            if verbose ge 1 then
              print "PROBLEM: Maximal group of this level doesn't have volume a submultiple";
              print "Volume of maximal group is: ", PartialMinVol_arith*ssetprod/2^ms, "*pi^2";
            end if;
            continue;
          else
            m := Integers()!m;
            Vhol_arith, Vst_arith, mholst_arith := MaximalVolumes(k, [i,j], 
                  DB, sprodideal, Zeta_arith : verbose := (verbose ge 1));

            // Sanity check
            if Vst_arith ne PartialMinVol_arith*ssetprod/2^ms then
              if verbose ge 1 then
                print MaximalVolumes(k,[i,j],DB,sprodideal: verbose:=true);
                print "Nu: ", InvolutionRankNu(k,[i,j],DB, sprodideal);
                print "My guess at volume: ", 
                         PartialMinVol_arith*ssetprod/2^InvolutionRankNu(k,[i,j],DB, sprodideal),
                         "*pi^2";
              end if;
              error "PROBLEM: VOLUMES DO NOT AGREE!";
            end if;

            CTL := TorsionLCM(k, DB, sprodideal : verbose := (verbose ge 1));
            
            if 0 ne m mod CTL then
              if verbose ge 1 then
                  print "PROBLEM: Index of fake quadric in maximal group of this " cat
                         " level wouldn't be divisible by torsion LCM";
              end if;
              continue;
            else
              found +:= 1;
              foundovercurrentfield := true;
              Append(~FinalFields, Dk);
              
              ExampleFound:=[* n, Dk, Eltseq(MinimalPolynomial(k.1)), 
                       #Automorphisms(k), [Eltseq(k!t) : t in Generators(DB)],
                       Norm(DB), [i,j], TypeNumber(k,i,j,DB), 
                       [Eltseq(k!t) : t in Generators(sprodideal)],
                       Norm(sprodideal), ms, 
                       CTL,
                       VboundS_arith/m,  
                       MaybeHasUnstableSupergroup2(DB,koo[1..i-1] cat 
                           koo[i+1..j-1] cat koo[j+1..n], sprodideal),
                       mholst_arith *];
                
              Append(~FINALLIST, ExampleFound);

              print "******************";
              print "Degree of Field:", Degree(k);
              print "Field Discriminant:", Dk;
              print "Number of Automorphisms", #Automorphisms(k);
              print "Algebra Discriminant:", Norm(DB);
              print "Number of prime divisors of disc(B):", #Factorization(DB);
              print "Type Number:", TypeNumber(k,i,j,DB);
              print "Infinite unramified places:", i,j;
              print "Cardinality of S:", #sset;
              print "Little s:", ms;
              print "Product of N(pp) for pp in S:", Norm(sprodideal); 
              print "Index in Gamma_{O,S}:", m;
              print "LCM of torsion:", CTL;
              print "Volume of stable group: ", Vst_arith, "*pi^2";
              print "******************";
            end if;
          end if;
        end for; // sset    
      end for; // j loop
    end for; // i loop
  end for; // DB in PossibleDiscs
  
  if foundovercurrentfield eq true then
    foundfields +:= 1;
  end if;
end for; //fieldpoly loop

printf "\n\n\n\n";
print "FINAL LIST:";
print FINALLIST;
