(* ::Package:: *)
(* =====================================================================
   graded_neighborhoods.wl

   Computations of the paper
   "Approximation Spaces Based on Graded Neighborhoods via Two Ideals
    and Their Applications".

   What this file does
     Part A  recomputes the comparison table of Example 31 (all nonempty
             subsets of a four-point universe, four models).
     Part B  recomputes the application on ten objects of the Breast
             Cancer (Ljubljana) data: neighborhoods, graded neighborhoods,
             the ideal Y, and Table 6 (approximations and indices).
     Part C  checks, on random finite relations, the properties proved in
             the paper (graded neighborhoods, approximations, Kuratowski
             closure, topology, comparison with earlier models).

   How to run
     wolframscript -file graded_neighborhoods.wl
     or, inside Mathematica:  Get["graded_neighborhoods.wl"]

   Conventions
     * The universe is X = {1, ..., n}; sets are sorted lists.
     * A relation R is a list of pairs {x, y}, meaning x R y.
     * In a finite universe every ideal is principal, I = P(Y); an ideal
       is therefore represented by the set Y:  B is in I  iff  B is a
       subset of Y.  The structure ideal is struct, the test ideal is test.
     * A neighborhood map is an Association  <| x -> set |>.
   ===================================================================== *)

(* ---------- Part 0: sets, neighborhoods, approximations ---------- *)

subsetQ[a_List, b_List] := Complement[a, b] === {};          (* a is a subset of b *)

afterSet[rel_, x_] := Union[Cases[rel, {x, y_} :> y]];      (* xR  *)
foreSet[rel_, x_]  := Union[Cases[rel, {y_, x} :> y]];      (* Rx  *)

(* intersection of all sets of the family that contain p (empty set if none) *)
minimalSet[family_List, p_] :=
  Module[{s = Select[family, MemberQ[#, p] &]},
    If[s === {}, {}, Intersection @@ s]];

(* the neighborhoods used in the paper: xR, <x>R, R<x>, N(x) = <x>R /\ R<x> *)
neighborhoods[rel_, universe_List] :=
  Module[{after, fore, ang, rang, nbN},
    after = Association[Table[x -> afterSet[rel, x], {x, universe}]];
    fore  = Association[Table[x -> foreSet[rel, x],  {x, universe}]];
    ang   = Association[Table[x -> minimalSet[Values[after], x], {x, universe}]];
    rang  = Association[Table[x -> minimalSet[Values[fore],  x], {x, universe}]];
    nbN   = Association[Table[x -> Intersection[ang[x], rang[x]], {x, universe}]];
    <|"xR" -> after, "Rx" -> fore, "angR" -> ang, "Rang" -> rang, "N" -> nbN|>];

(* graded neighborhood  N^I(x) = { y in N(x) : N(x) \ N(y) in I },  I = P(struct) *)
gradedAt[nbN_Association, x_, struct_List] :=
  Select[nbN[x], Function[y, subsetQ[Complement[nbN[x], nbN[y]], struct]]];
graded[nbN_Association, universe_List, struct_List] :=
  Association[Table[x -> gradedAt[nbN, x, struct], {x, universe}]];

(* approximations with a test ideal J = P(test):
     lower(A) = { x in A : M(x) /\ A^c in J }
     upper(A) = A  U  { x : M(x) /\ A not in J }                       *)
lowerJ[m_Association, a_List, test_List] :=
  Select[a, Function[x, subsetQ[Complement[m[x], a], test]]];
upperJ[m_Association, universe_List, a_List, test_List] :=
  Union[a, Select[universe, Function[x, !subsetQ[Intersection[m[x], a], test]]]];

(* approximations of Yao type (test ideal = {empty set}) *)
yaoLower[m_Association, universe_List, a_List] :=
  Select[universe, Function[x, subsetQ[m[x], a]]];
yaoUpper[m_Association, universe_List, a_List] :=
  Select[universe, Function[x, Intersection[m[x], a] =!= {}]];

accuracy[l_List, u_List] := If[u === {}, 0, Length[l]/Length[u]];

(* the open sets of the topology of the operator upperJ:  lower(A) = A *)
openSets[m_Association, universe_List, test_List] :=
  Select[Subsets[universe], lowerJ[m, #, test] === # &];

(* fixed number of decimals, e.g. fmt[1/4, 3] = "0.250" *)
fmt[x_, d_Integer] :=
  Module[{s = IntegerString[Round[N[x]*10^d], 10, d + 1]},
    StringTake[s, {1, -d - 1}] <> "." <> StringTake[s, -d]];

(* ---------- Part A: Example 31 (comparison table) ---------- *)

Print["== Part A: Example 31 =="];
Module[{names = {"a", "b", "c", "d"}, uni = {1, 2, 3, 4}, rel, nb, nbN, ang, nbNI,
        testA = {1}, setName, rows, expected, bad = 0},
  rel = Union[Table[{i, i}, {i, 4}],
     {{1, 2}, {1, 3}, {2, 1}, {2, 3}, {3, 1}, {3, 2}, {4, 1}, {4, 2}}];
  nb = neighborhoods[rel, uni]; nbN = nb["N"]; ang = nb["angR"];
  nbNI = graded[nbN, uni, {}];                      (* I = {empty set} *)
  setName[a_List] := If[a === {}, "{}", StringJoin[names[[a]]]];
  expected = Association[
  "a" -> {"{},abc,0", "{},a,0", "{},a,0", "{},a,0"},
  "b" -> {"{},abc,0", "b,abcd,1/4", "b,abc,1/3", "b,ab,1/2"},
  "c" -> {"{},c,0", "{},c,0", "{},c,0", "c,c,1"},
  "d" -> {"d,d,1", "{},d,0", "d,d,1", "d,d,1"},
  "ab" -> {"ab,abc,2/3", "ab,abcd,1/2", "ab,abc,2/3", "ab,ab,1"},
  "ac" -> {"{},abc,0", "{},ac,0", "{},ac,0", "c,ac,1/2"},
  "ad" -> {"d,abcd,1/4", "{},ad,0", "d,ad,1/2", "d,ad,1/2"},
  "bc" -> {"{},abc,0", "bc,abcd,1/2", "bc,abc,2/3", "bc,abc,2/3"},
  "bd" -> {"d,abcd,1/4", "bd,abcd,1/2", "bd,abcd,1/2", "bd,abd,2/3"},
  "cd" -> {"d,cd,1/2", "{},cd,0", "d,cd,1/2", "cd,cd,1"},
  "abc" -> {"abc,abc,1", "abc,abcd,3/4", "abc,abc,1", "abc,abc,1"},
  "abd" -> {"abd,abcd,3/4", "abd,abcd,3/4", "abd,abcd,3/4", "abd,abd,1"},
  "acd" -> {"d,abcd,1/4", "{},acd,0", "d,acd,1/3", "cd,acd,2/3"},
  "bcd" -> {"d,abcd,1/4", "bcd,abcd,3/4", "bcd,abcd,3/4", "bcd,abcd,3/4"},
  "abcd" -> {"abcd,abcd,1", "abcd,abcd,1", "abcd,abcd,1", "abcd,abcd,1"}
  ];
  Print["A | Kozae | Kandil (J = P({a})) | second pair | present"];
  Do[
    Module[{cells, l, u},
      cells = Reap[
        l = yaoLower[nbN, uni, a]; u = yaoUpper[nbN, uni, a];
        Sow[setName[l] <> "," <> setName[u] <> "," <> ToString[accuracy[l, u], InputForm]];
        l = lowerJ[ang, a, testA]; u = upperJ[ang, uni, a, testA];
        Sow[setName[l] <> "," <> setName[u] <> "," <> ToString[accuracy[l, u], InputForm]];
        l = lowerJ[nbN, a, testA]; u = upperJ[nbN, uni, a, testA];
        Sow[setName[l] <> "," <> setName[u] <> "," <> ToString[accuracy[l, u], InputForm]];
        l = lowerJ[nbNI, a, testA]; u = upperJ[nbNI, uni, a, testA];
        Sow[setName[l] <> "," <> setName[u] <> "," <> ToString[accuracy[l, u], InputForm]]
      ][[2, 1]];
      Print[setName[a], " | ", StringRiffle[cells, " | "]];
      If[expected[setName[a]] =!= cells, bad++; Print["   MISMATCH, expected: ", expected[setName[a]]]]
    ],
    {a, Rest[Subsets[uni]]}];
  Print[If[bad == 0, "Part A: all 60 entries agree with Table 4 of the paper.",
                     "Part A: " <> ToString[bad] <> " rows differ."]];
];

(* ---------- Part B: application (ten objects) ---------- *)

Print["\n== Part B: application on ten objects =="];
(* coded conditions: age group, tumor size group, involved nodes, grade, caps, irr *)
appData = {{4,1,1,1,0,0}, {3,1,1,1,0,0}, {3,2,1,2,0,0}, {2,1,1,1,0,0}, {3,3,2,2,1,1},
           {3,3,1,3,0,0}, {2,2,1,2,0,0}, {3,3,3,2,1,1}, {4,2,3,3,1,1}, {3,3,1,3,0,1}};
nObj = Length[appData]; appX = Range[nObj];
(* o_i R o_j iff the value of every condition at o_i minus its value at o_j is at most 1 *)
appRel = Select[Tuples[appX, 2],
   Function[pr, AllTrue[Range[6], appData[[pr[[1]], #]] - appData[[pr[[2]], #]] <= 1 &]]];
appNb = neighborhoods[appRel, appX];
appN = appNb["N"]; appAng = appNb["angR"];

(* the ideal Y: the two objects farthest from the median profile, the distance of
   an object being the sum over the six conditions of the absolute differences
   from the median of the condition; the decision is not used *)
medianProfile = Median /@ Transpose[appData];
distances = Table[Total[Abs[appData[[i]] - medianProfile]], {i, nObj}];
appY = Sort[Ordering[distances, -2]];
Print["median profile: ", medianProfile];
Print["distances:      ", distances, "   ->   Y = ", appY];

appNI = graded[appN, appX, appY];
Print["Table 5 (neighborhoods): object, N(x), graded N^I(x)"];
Do[Print["  o", i, "   ", appN[i], "   ", appNI[i]], {i, nObj}];

classNo = Range[5]; classYes = Range[6, 10];

(* one row of Table 6 *)
tableRow[name_, m_Association, test_List, yao_] :=
  Module[{accs, pos = {}, tot = 0, cnt = 0, opens = 0, l, u, cells = {}},
    accs = Table[
      l = If[yao, yaoLower[m, appX, c], lowerJ[m, c, test]];
      u = If[yao, yaoUpper[m, appX, c], upperJ[m, appX, c, test]];
      pos = Union[pos, l]; AppendTo[cells, {l, u}]; accuracy[l, u],
      {c, {classNo, classYes}}];
    Do[
      l = If[yao, yaoLower[m, appX, s], lowerJ[m, s, test]];
      u = If[yao, yaoUpper[m, appX, s], upperJ[m, appX, s, test]];
      If[s =!= {}, cnt++; tot += accuracy[l, u]];
      If[l === s, opens++],
      {s, Subsets[appX]}];
    <|"model" -> name, "classes" -> cells, "acc" -> Mean[accs], "gamma" -> Length[pos]/nObj,
      "mean" -> Total[Length /@ Values[m]]/nObj, "accSub" -> tot/cnt, "open" -> opens|>];

table6 = {
  tableRow["Allam et al.", appAng, {}, True],
  tableRow["Kozae et al.", appN, {}, True],
  tableRow["Kandil et al.", appAng, appY, False],
  tableRow["second pair of Kandil et al. (2020)", appN, appY, False],
  tableRow["present", appNI, appY, False]};

Print["Table 6: model | acc. (classes) | gamma | mean |M(x)| | acc. (subsets) | open sets"];
Do[Print["  ", r["model"], " | ", fmt[r["acc"], 3], " | ", fmt[r["gamma"], 1], " | ",
         fmt[r["mean"], 2], " | ", fmt[r["accSub"], 3], " | ", r["open"]], {r, table6}];
Print["Approximations of C_no and C_yes (lower; upper) for each model:"];
Do[Print["  ", r["model"], "   C_no: ", r["classes"][[1]], "   C_yes: ", r["classes"][[2]]], {r, table6}];

(* comparison with the values printed in the paper *)
expectedB = {{"0.000", "0.0", "6.00", "0.044", 7}, {"0.200", "0.4", "2.70", "0.231", 43},
             {"0.050", "0.1", "6.00", "0.126", 25}, {"0.200", "0.4", "2.70", "0.264", 77},
             {"0.657", "0.8", "1.60", "0.658", 320}};
computedB = Table[{fmt[r["acc"], 3], fmt[r["gamma"], 1], fmt[r["mean"], 2],
                   fmt[r["accSub"], 3], r["open"]}, {r, table6}];
Print[If[computedB === expectedB, "Part B: Table 6 agrees with the paper.",
         "Part B: MISMATCH with the paper:\n" <> ToString[computedB]]];
Print[If[appY === {8, 9} && appNI[4] === {4} && appNI[8] === {5, 8, 9},
         "Part B: Y = {o8, o9} and the graded neighborhoods agree with Table 5.",
         "Part B: Y or the graded neighborhoods differ from Table 5."]];

(* ---------- Part C: random checks of the proved properties ---------- *)

Print["\n== Part C: random checks =="];
SeedRandom[11];
bad = <||>;
chk[name_String, cond_] := If[!TrueQ[cond], bad[name] = Lookup[bad, name, 0] + 1];

randomRelation[n_Integer, p_?NumericQ] :=
  Union[Table[{i, i}, {i, n}], Flatten[Table[If[RandomReal[] < p, {{i, j}}, {}], {i, n}, {j, n}], 2]];
(* preorder generated by a relation: reflexive-transitive closure *)
preorderOf[rel_, n_Integer] :=
  Module[{m = Table[If[MemberQ[rel, {i, j}] || i == j, 1, 0], {i, n}, {j, n}]},
    m = FixedPoint[Function[mm, Unitize[mm + mm . mm]], m];
    Position[m, 1]];
randomSubset[universe_List] := Select[universe, RandomReal[] < 0.4 &];

Do[
  Module[{n = RandomChoice[{3, 4, 5}], uni, rel, nb, nbN, ang, y1, y2, y1b, y2b, nbI, nbIb,
          openList, topoOf, zero = {}},
    uni = Range[n];
    rel = randomRelation[n, RandomChoice[{0.2, 0.4, 0.6}]];
    nb = neighborhoods[rel, uni]; nbN = nb["N"]; ang = nb["angR"];
    y1 = randomSubset[uni]; y2 = randomSubset[uni];
    y1b = Union[y1, randomSubset[uni]]; y2b = Union[y2, randomSubset[uni]];
    nbI = graded[nbN, uni, y1]; nbIb = graded[nbN, uni, y1b];

    (* Section "Graded neighborhoods" *)
    Do[
      chk["N^I <= N <= <x>R", subsetQ[nbI[x], nbN[x]] && subsetQ[nbN[x], ang[x]]];
      chk["x in N^I(x), equality class <= N^I <= {y : N(y) <= N(x)}",
        MemberQ[nbI[x], x] &&
        subsetQ[Select[uni, nbN[#] === nbN[x] &], nbI[x]] &&
        subsetQ[nbI[x], Select[uni, subsetQ[nbN[#], nbN[x]] &]]];
      chk["N^{ {} } is the equality class",
        graded[nbN, uni, {}][x] === Select[uni, nbN[#] === nbN[x] &]];
      chk["nested N^I", AllTrue[nbI[x], subsetQ[nbI[#], nbI[x]] &]];
      chk["monotone in the structure ideal", subsetQ[nbI[x], nbIb[x]]];
      chk["intersection of structure ideals",
        graded[nbN, uni, Intersection[y1, y2]][x] === Intersection[nbI[x], graded[nbN, uni, y2][x]]];
      chk["N is nested (Kozae)", AllTrue[nbN[x], subsetQ[nbN[#], nbN[x]] &]];
      chk["<x>R is nested (Allam)", AllTrue[ang[x], subsetQ[ang[#], ang[x]] &]],
      {x, uni}];

    (* Section "Generalized approximations" *)
    openList = openSets[nbI, uni, y2];
    chk["the open sets form a topology",
      MemberQ[openList, {}] && MemberQ[openList, uni] &&
      AllTrue[Tuples[openList, 2], MemberQ[openList, Intersection @@ #] && MemberQ[openList, Union @@ #] &]];
    Do[
      Module[{b = randomSubset[uni], ac = Complement[uni, a]},
        chk["duality", upperJ[nbI, uni, a, y2] === Complement[uni, lowerJ[nbI, ac, y2]]];
        chk["lower <= A <= upper",
          subsetQ[lowerJ[nbI, a, y2], a] && subsetQ[a, upperJ[nbI, uni, a, y2]]];
        chk["upper is additive",
          upperJ[nbI, uni, Union[a, b], y2] === Union[upperJ[nbI, uni, a, y2], upperJ[nbI, uni, b, y2]]];
        chk["lower preserves intersections",
          lowerJ[nbI, Intersection[a, b], y2] === Intersection[lowerJ[nbI, a, y2], lowerJ[nbI, b, y2]]];
        chk["upper is idempotent",
          upperJ[nbI, uni, upperJ[nbI, uni, a, y2], y2] === upperJ[nbI, uni, a, y2]];
        chk["monotone in the test ideal",
          subsetQ[upperJ[nbI, uni, a, y2b], upperJ[nbI, uni, a, y2]] &&
          subsetQ[lowerJ[nbI, a, y2], lowerJ[nbI, a, y2b]]];
        chk["monotone in the structure ideal",
          subsetQ[upperJ[nbI, uni, a, y2], upperJ[nbIb, uni, a, y2]] &&
          subsetQ[lowerJ[nbIb, a, y2], lowerJ[nbI, a, y2]]];
        chk["boundary equals the frontier",
          Complement[upperJ[nbI, uni, a, y2], lowerJ[nbI, a, y2]] ===
          Intersection[upperJ[nbI, uni, a, y2], upperJ[nbI, uni, ac, y2]]]],
      {a, Subsets[uni]}];

    (* Proposition: the topology of the present model is finer than the earlier ones *)
    topoOf[m_, test_] := openSets[m, uni, test];
    chk["topologies: <x>R, {} <= <x>R, J <= N, J <= present",
      subsetQ[topoOf[ang, zero], topoOf[ang, y2]] && subsetQ[topoOf[ang, y2], topoOf[nbN, y2]] &&
      subsetQ[topoOf[nbN, y2], topoOf[nbI, y2]]];
    chk["topologies: <x>R, {} <= N, {} <= present",
      subsetQ[topoOf[ang, zero], topoOf[nbN, zero]] && subsetQ[topoOf[nbN, zero], topoOf[nbI, y2]]];

    (* Corollary: special cases *)
    chk["I = P(X), J = {}: Kozae et al.",
      AllTrue[Subsets[uni],
        lowerJ[graded[nbN, uni, uni], #, zero] === yaoLower[nbN, uni, #] &&
        upperJ[graded[nbN, uni, uni], uni, #, zero] === yaoUpper[nbN, uni, #] &]];
    Module[{relp = preorderOf[randomRelation[n, 0.3], n], nbp, nNp, nIp},
      nbp = neighborhoods[relp, uni]; nNp = nbp["N"]; nIp = graded[nNp, uni, y1];
      chk["preorder, J = {}: present = Kozae et al.",
        AllTrue[Subsets[uni],
          lowerJ[nIp, #, zero] === yaoLower[nNp, uni, #] &&
          upperJ[nIp, uni, #, zero] === yaoUpper[nNp, uni, #] &]]]
  ],
  {400}];

Print[If[bad === <||>, "violations: none", "violations: " <> ToString[Normal[bad]]]];
