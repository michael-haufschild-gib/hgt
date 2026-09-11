# SQB81: first-atom central-factorial middle reserve

Goal ACTIVE, RH NOT proved. Frontier map READ ONLY, universal STATUS untouched. No computations, Git, launch.sh, SSH, or subagents. One foreground Lean/Lake process. All SQB81 proof/search/lint processes terminal.

## Verified production
New formal/GaloisForLFunctions/RHTower/ThetaCuspFirstAtomCentralFactorial.lean (about 612 lines), wired once in RHTower.lean.
- firstAtomCentralMoment_eq: all seven central-factorial transforms n=0..6, literal reflection jets through12, exact every real x.
- firstAtomEvenEnergy_eq_centralHermite: exact sixteen-entry source quadratic identity, q>3/2.
- firstAtomEvenEnergy_lower_of_seven_halves_le: E1 >=196*f1²*(8q)^6*c3² for q>=7/2.
- firstAtomEvenEnergy_lower_of_four_le: same with282 forq>=4.
- firstAtomCompensatedEvenEnergy_coordinate_lower (line569): for x>=0,q>=4, E1+10^12*G1*c3² >=f1²*((y0+h*y1)²+(7/8)y1²+3y2²+82y3²).
- G1=3f1²+2x f1 f1' is actual derivative source, no surrogate.
All14 public theorem axiom audits: only propext, Classical.choice, Quot.sound.
Scratch: /tmp/sqb81_all.lean and /tmp/sqb81_all_check.txt pass.
Final narrow build: /tmp/sqb81-central-factorial-leaf-audit; lake build GaloisForLFunctions.RHTower.ThetaCuspFirstAtomCentralFactorial. Actual source and existing compiled dependencies, cache symlink into formal/.lake/build/lib/lean/GaloisForLFunctions. Log /tmp/sqb81_build.txt,153sec,2Lakejobs, oneLeanprocess.
Final compiled audit: lake env lean /tmp/sqb81_final_audit.lean, output /tmp/sqb81_final_audit.txt, all14 standard3.
Global lint /tmp/sqb81_formal_lint.txt PASS. First lint had4 unrelated unwired modules; other work wired them and rerunpassed. Do not repair/retest those.
Final owned audit session89832 and build28294 terminal exit0. No owned Lean live.

## Exact mathematics
q=pi exp(2x), f1=thetaCuspSourceTerm x1, g=exp(x/2-q), D=(2q-3)², s=8q,v=1/(2q),h=6/D.
p_n(X)=product_{j<n}(X²+4j²).
m_n=(-1)^n firstAtomReflectionJet(2n)x.
A0=m0,A1=m1,A2=m2+4m1,A3=m3+20m2+64m1,
A4=m4+56m3+784m2+2304m1,
A5=m5+120m4+4368m3+52480m2+147456m1,
A6=m6+220m5+16368m4+489280m3+5395456m2+14745600m1.
A_n=g²*4q²*c_n*q^n*(D+6n), c_n=[1,8,192,7680,430080,30965760,2724986880].
Normalized A_n/(f1² s^n)=(2n-1)!!*(1+n h).
Only through n6 formalized; allorder identity conjectural.

Y=X²/s, basis:
1;Y-1;Y²+(v-6)Y+3;
Y³+(5v-15)Y²+(4v²-15v+45)Y-15.
Coordinates:
y3=s³c3;y2=s²c2-(5v-15)y3;
y1=sc1-(v-6)y2-(4v²-15v+45)y3;
y0=c0+y1-3y2+15y3.
h(1-3v)²=6v².
N=(y0+h y1)²+d1 y1²+d2 y2²+d3 y3²+2b y1y2+2c y1y3+2e y2y3.
d1=2+4h-h²-v(1+h)
d2=(24-72v)(1+4h)+36v²(1+2h)
d3=720+4320h-5400v(1+7h)+13500v²+70200v²h-5400v³(1+3h)
b=12h-6v(1+3h);c=-90vh;e=360h-360v(1+7h)+540v²(1+4h).
q>=4: d1>=15/8,d2>=15,d3>=400,absb<=2,absc<=3,abse<=20.
N>=(y0+h y1)²+(7/8)y1²+3y2²+282y3².
q>=7/2: analogous13/7,20,320,3,5,25; N>=masssquare+(5/14)y1²+y2²+196y3².

Correction proof: 12qx<=q²-9 from 2x<=sinh2x, pi>3.
P0=4q²-6q;P1=-8q³+30q²-15q.
W=629145600q7(2q-3)+10^12(-8q4+30q3+129q²-378q+135)>0 q>=4, exact positive decompositions on [4,5],[5,6],[6,infty).
6q(LG1+200f1²s6)=2q²(2q-3)g² W+Lg²P0P1(12qx-q²+9).
Hence LG1>-200f1²s6 and full coordinate bound above.

Lean debugging lesson: normalize finite sums / Fin.succ, then ring_nf BEFORE field_simp with canonical D=9-12q+4q²; final ring! (not ring) unifies Fin.mk3 with numeral3. maxRecDepth2048 local source identity. Don't repeat giant failed scratch checks. Generic polynomial forms successful. Avoid consecutive /-- doc comments (parsererror).

## Remaining hardest work
Complete source middle sign stillOPEN, allrank extension stillOPEN. Prior complete-source x>=4/5 result unchanged (mem:selberg/sqb-entrywise-tail-four-fifths-2026-09-11).
Next compare actual unequal pair and full tail against four-coordinate reserve, not scalar c3 reserve alone.
Working card updated: docs/drafts/pipeline/1-in-progress/sqb-native-spectral-source-comparison.md, sections starting370 and452, exact formulas and paper candidates.

### New source-compatible signed-square candidate (paper proved, NOT Lean)
For reallambda define finite polynomial functional
T_lambda(P)=sum_{k<=degP} lambda^k/k!*(Delta^kP)(0), Delta P(J)=P(J+1)-P(J).
T_lambda(PQ)=sum_k lambda^k/k!*T_lambda(Delta^kP)*T_lambda(Delta^kQ).
Proof: on tensor polynomial space Delta_product=Delta⊗1+1⊗Delta+Delta⊗Delta; three commuting nilpotent operators, exponentials factor. Equivalently F(s+t)=F(s)F(t)exp(lambda(e^s-1)(e^t-1)).
Tensor2 with lambda=-p,mu=-r has weights(-1)^(k+l)p^k r^l/(k!l!).
Literal seeded atom pair:
e^(x-p-r) (T_-p⊗T_-r)(W(J)W(K) A(J,K)²),
W(J)=4J(J-1)+6J=4J²+2J;
A=sum_i(-1)^i c_i(2(J-K))^(2i), i0..3.
For pair1,2: p=q,r=4q; swappedpair identical.
U=2J+1/2,V=2K+1/2:
WJ WK A²=(UV A)²-(UA)²/4-(VA)²/4+A²/16.
Every lower clock term retained. Need quantitative negative-square bound; none proved. Generic Gaussian translation norm does not supply actual warped source identity; don't substituteGaussian.

Retrieved relevant building blocks, source READ but not yet Lean applicability checked:
Mathlib/RingTheory/Nilpotent/Exp.lean: IsNilpotent.exp_eq_sum, exp_add_of_commute, map_exp. Finite exp for nilpotent rational algebras, commutingfactorization.
HTGeometry/PolynomialForwardDifference.lean: fwdDiff (complexpolys), natDegree_fwdDiff, fwdDiff_iterate_natDegree. ImportsMathlib; readthrough170.
HTGeometry/CharacteristicEquilibriumDefect.lean: tsum_poisson_firstMoment / summable_poisson_firstMoment valid ALLreal lambda, source fromsearchonly.
HTGeometry/ConvolutionAtomBounds.lean: poisson_cauchy finiteantidiagonal factorialidentity (source searchonly).
Mathlib/RingTheory/Polynomial/Pochhammer.lean first150 read; more descendingfactorial API below.
Do not spend turn merely proving genericreceivers without attempting negative-square estimate.

### Two-atom central coefficient alternative (paper only)
a=5q,b=3q,z=e^-3q,Hn=[u^n]e^(2au)cos(2b sqrt(u(1-u))).
Bn=(a²-b²+9-6a)Hn+12a H(n-1)+6b ∂bHn.
In units4q²exp(x-2q), retained centralmoment:
c_n q^n(D+6n)+8z(2n)! Bn(5q,3q)+16z² c_n(4q)^n((8q-3)²+6n).
Card has finite sum formula. Not Leanchecked.

## Search/literature already done; don'tredo
Deep allviews300 cached /tmp/sqb81_*_search.json:
cumulant,schur_cumulant,appell,head_bound,central_factorial,
coherent,mixed_squares,mehler,poisson,difference_squares. Everycandidate/sourcearg/proofideas/ingredientset inspected. Some empty; allpartialcoverage; severaldeadline/filter_and_judge. No absenceclaim.
Generation823339/823340, files56536..56578, declarations723510, methodsready706108 stale779, compiledsnapshot48, mostsource/compilerpending.
Broad arxiv own termsmajorization,caustics,squeezing,tunneling.
Read2607.28061v1 Poset-refinedmajorization: orthonormal spectralbases+posetLU approximation, no appliedsourcebound.
Read2608.04197v1 throughsecIII ApplicationsSpinDependentGeneralizedSqueezing: truncatedMagnus phases requirehigherordercontrol, no importedsourceestimate.
User2607.08139v1 alreadyreadolderturn; cardrecords.
Serena initial instructions re-read this continuation; no need again (huge memorylistoutput).
