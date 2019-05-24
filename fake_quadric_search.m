load "all_helper.m";

eps:= 10^-7;  
// volumes are computed numerically, but all volumes considered are < 1/eps 
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
  Zeta := Evaluate(LSeries(k),2);  // evaluated rigorously to prec(RR) = 30 
  h := ClassNumber(k);
  primesabove2 := #PrimesUpTo(2,k);
  

  
  hasautk := HasNontrivialAutomorphism(k);
  if hasautk then
    Vbound := 32*pi^2;
  else
    // See Theorem 2.3 and bound implied by (4.15)
    Vbound := 16*pi^2;  
  end if;
  if verbose ge 1 then
    if hasautk then
      print "k has a nontrivial automorphism group, so taking Vbound = 32 * pi^2";
    else
      print "k has no nontrivial automorphisms, so taking Vbound = 16 * pi^2";
    end if;
  end if;
    
  // Ram(B) must contain all but 2 real places, so next we 
  // compute the primes in Ram(B) for the quaternion algebras B to be checked
  // First bound #Ram(B) (MaxTerms and MaxTerms4), then
  // compute the levels of the Eichler orders to be checked
  PrimesWhichCouldRamify := PrimesUpTo(MaxNormOfRamPrimesFromVolume(Vbound, k, Zeta), k);
  MaxTerms := MaxNumberOfRamPrimesFromVolume(Vbound, k, Zeta);
  MaxTerms4 := MaxNumberOfRamPrimesFromVolumeWithNormAtLeast4(Vbound, k, Zeta);
    // two bounds apply, need to know primes with small norm in particular

  if MaxTerms eq 0 then
    Ram := [1*Integers(k)];  // must be unramified at all primes!
    PossibleDiscs := [1*Integers(k)];
  else // MaxTerms ge 1 then
    maxprodnmm1 := MaxProductOfNormPrimeMinusOneOverTwo(Vbound, k, Zeta);
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
        PartialMinVol := 8*pi^2*Dk^(3/2)*Zeta*ProdNormMinusOneOverTwo(DB)
                              /((4*pi^2)^n*TypeNumber(k,i,j,DB));

        if verbose ge 1 then
          print "PartialMinVol computed: ", PartialMinVol;
        end if;

        if PartialMinVol gt Vbound + eps then
          if verbose ge 1 then
            print "Volumes will be too big. Volume is: ", PartialMinVol;
            print "Volume bound: ", Vbound;
          end if;
          continue;
        end if;

        if verbose ge 1 then
          print "Computing sets of levels... ";
        end if;
        SetOfS := SetsOfLevels(k, LevelProductUpperBound(Vbound, k, TypeNumber(k,i,j,DB), Zeta));

        for sset in SetOfS do
          ssetprodover2, ssetprod, sprodideal := LevelProducts(Zk, sset);

          if verbose ge 1 then
            print "@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@";
            print "Checking k of discriminant:", Dk;
            print "Checking N(DB): ", Norm(DB);
            print "Checking split places i,j:",i,j;
            print "Checking level: ", Norm(sprodideal);
          end if;
            
          if Norm(Gcd(sprodideal,DB)) gt 1 then
            if verbose ge 1 then
              print "Algebra discriminant and level not coprime";
            end if;
            continue;
          end if;
            
          // Given S, we can refine whether or not there is an unstable supergroup
          VboundS := Vbound;  
          if hasautk then
            if Norm(sprodideal) gt 1 and not MaybeHasUnstableSupergroup2(DB, koo[1..i-1] cat koo[i+1..j-1] 
                                                 cat koo[j+1..n], sprodideal) then
              VboundS := 16*pi^2;  // as above 
            end if;
          end if;
            
          if PartialMinVol*ssetprodover2 gt VboundS + eps then
            if verbose ge 1 then
              print "Volumes will be too big. Volume is: ", PartialMinVol*ssetprodover2;
              print "Volume bound: ", VboundS;
            end if;
            continue;
          end if;      
      
          // We are under the hypothesis now that Gamma is of finite index 
          // in the normalizer of an Eichler order; we know the volume of
          // both, so we just need to check if the ratio is indeed an integer
          // so there's a chance for this subgroup to exist in the first place.
          ms := InvolutionRankNu(k,[i,j],DB,sprodideal);  // called nu in the paper
          m := ProbableRational(VboundS/(PartialMinVol*ssetprod/2^ms));
          neversubmultiple := not IsCoercible(Integers(),m);
          
          if neversubmultiple then
            if verbose ge 1 then
              print "PROBLEM: Maximal group of this level doesn't have volume a submultiple";
              print "Volume of maximal group is: pi^2 *", 
                        ProbableRational(PartialMinVol*ssetprod/
                        2^ms/pi^2);
            end if;
            continue;
          else
            m := Integers()!m;
            Vhol, Vst, mholst := MaximalVolumes(k, [i,j], DB, sprodideal);

            // Sanity check
            if Abs(Vst-PartialMinVol*ssetprod/2^ms) 
              gt eps then
              if verbose ge 1 then
                  print MaximalVolumes(k,[i,j],DB,sprodideal: verbose:=true);
                  print "Nu: ", InvolutionRankNu(k,[i,j],DB, sprodideal);
                print "My guess at volume: ", 
                  PartialMinVol*ssetprod/2^InvolutionRankNu(k,[i,j],DB, sprodideal);
              end if;
              error "PROBLEM: VOLUMES DO NOT AGREE!";
            end if;

            if Norm(sprodideal) eq 1 then
              CTL := ComputeTorsionLCM(k, DB, i, j);
            else 
              CTL := ComputeTorsionLCMSgroups(k,DB,i,j,sprodideal);
            end if;
      
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
                       VboundS/m,  
                       MaybeHasUnstableSupergroup2(DB,koo[1..i-1] cat 
                           koo[i+1..j-1] cat koo[j+1..n], sprodideal),
                       mholst *];
                
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
              print "Volume of stable group: ", VboundS;
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
