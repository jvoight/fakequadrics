/*
 1 Degree of F
 2 Absolute value of discriminant of F
 3 Eltseq of primitive element of F
 4 Number of automorphisms of F
 5 Eltseq of generators of finite part of discriminant of B
 6 Norm of finite part of discriminant of B
 7 Split real places of B
 8 Type number of B
 9 Eltseq of generators of NN
10 Norm of NN
11 What we decided to call \nu
12 Torsion LCM
13 Covolume of associated maximal stable group
14 true or false flag for “MaybeHasUnstableSupergroup"
15 index of holomorphic stable group in maximal stable group
*/

load "Output/Degree4Data.m";
SetLogFile("Output/Degree4Table.tex");

n := dat[1][1];
d := 0;
DD := 0;
NN := 0;
// pi2 := Pi(RealField())^2;
pi2 := 1;
vol := 0;

// printf "\\begin{tabular}{ccc|c|cccc}\n";
// printf "$d$ & $D$ & $N$ & num & vol & lcm & $\\nu$ & st\\\\\n";
printf "\\begin{tabular}{ccc|ccccc}\n";
printf "$d$ & $D$ & $N$ & vol & hind & lcm & $\\nu$ & st\\\\\n";
printf "\\hline\n";

cnt := 0;

sortf := function(v1,v2);
if v1[1] ne v2[1] then return v1[1]-v2[1]; end if;
if v1[2] ne v2[2] then return v1[2]-v2[2]; end if;
if v1[6] ne v2[6] then return v1[6]-v2[6]; end if;
if v1[10] ne v2[10] then return v1[10]-v2[10]; end if;
if v1[13] ne v2[13] then return v1[13]-v2[13]; end if;
if v1[15] ne v2[15] then return v1[15]-v2[15]; end if;
if v1[12] ne v2[12] then return v1[12]-v2[12]; end if;
if v1[11] ne v2[11] then return v1[11]-v2[11]; end if;
if v1[14] eq v2[14] then return 0; elif v1[14] then return 1; else return -1; end if;
end function;
Sort(~dat, sortf);

dat_skim := [];
for v in dat do
  vl := Roots(PowerRelation(v[13]/pi2,1 : Al := "LLL"),Rationals())[1][1];
//  Append(~dat_skim, [* v[2],v[6],v[10],vl,v[8],v[12],v[11],v[14],v[15], 1 *]);
  Append(~dat_skim, [* v[2],v[6],v[10],vl,v[8],v[12],v[11],v[14],v[15] *]);
end for;
/* Counts; at some point we could remove action by automorphisms.  Ignored for now. */
for j := #dat_skim to 2 by -1 do
  if dat_skim[j] eq dat_skim[j-1] then
//    dat_skim[j-1][10] +:= 1;
    Remove(~dat_skim, j);
  end if;
end for;

for v in dat_skim do
  if v[1] ne d then
    printf "%o", v[1];
  end if;
  printf " & ";
  if v[2] ne DD or v[1] ne d then
    printf "%o", v[2];
  end if;
  d := v[1];
  DD := v[2];
  printf " & ";
  printf "%o", v[3];
  NN := v[3];
  printf " & ";
  
  v4st := Sprintf("%o", v[4]);
  if "/" in v4st then
    printf "$(%o)", v4st;
  elif v4st eq "1" then
    printf "$";
  else
    printf "$%o", v4st;
  end if;
  printf "\\pi^2$ & %o & %o & %o & ", v[9], v[6], v[7];
  if not v[8] then
    printf "$\\star$";
  end if;
  cnt := 0;
  printf " \\\\\n";
end for;

printf "\\end{tabular}";

quit;

