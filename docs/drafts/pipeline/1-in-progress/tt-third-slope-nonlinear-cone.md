# TT: third-slope sign after the nonlinear source barrier

- ID: tt-third-slope-nonlinear-cone
- Conjecture: C73
- Stage: 1-in-progress
- Route: TT, actual normalized native odd third-minor slope.
- Hard target: prove the global actual third-slope sign, then the full source
  quadratic needed for the transported fourth Schur gap. RH remains open.

## Corpus basis

C71 (`ThetaCuspRatioQuadraticSlopeBoundary`) proves that along
t=r*b(h)+a*h², the second slope coefficient is 54C(144a−r²).
C72 now has a successful scratch Lean audit of the unconditional actual
inequality q−Tq²>b(h), where h=1/k, T=9−u², b=1/12−7h/72.
In compact source coordinates r=k²T, t=k(1−3J/u), this is exactly
t−h²t²>r*b(h). Fourteen C72 production leaves are in final direct audit.

Searches: `/tmp/tt_c72_to_third_slope_search.json` (deep, partialfalse,
source-only candidates, older coverage snapshot); focused lexical
`scaledSlope` finds the exact InfinitySlope field and ActualSlopeTail;
`third jet` restricted to ThetaCuspRatio returns no declaration.
No searched theorem settles C73. These are retrieval results, not proof
that the corpus contains no other applicable lemma.

## Conjecture and first hard test

Does the strict coarse source cone together with
t−h²t²>r*b(h) force the full scaled third-slope polynomial positive?
The actual orbit satisfies these premises by already proved source laws.
This would be a sufficient pointwise theorem, not itself an RH proof.

First derive the exact third slope jet on the nonlinear boundary. Its
Taylor-matching polynomial is

    t=r*b(h)+(r²/144)h²−(7r²/432)h³.

The C71 second slope jet vanishes on this sheet. Its next sign must be
derived from the complete polynomial source field, including transverse
derivatives. No numerical sampling or external polynomial computation.

## Paper derivation in progress

Use triangular coordinates s=t−B(h,r), with B the displayed cubic.
At h=s=0 the minor has P0=P1=0 and P2=2A, independent of r, where
A=axisMinorMass. The transformed field has Fh0=Fh1=0, Fh2=−72,
Fr0=−108r, and Fs0=Fs1=Fs2=0. The exact C72 boundary field predicts
Fs3=−63r²/4. If p3(r) is the third h-derivative of the transformed minor,
then the cubic coefficient of the transformed slope should be

    1944A−108r*p3'(r)−189C*r².

These new jet identities are conjectural until algebra and Lean audits.
Derive p3 and its r-derivative from the existing split moment polynomials;
do not assume the expression has a desired sign. A failure must produce
its strongest positive survivor and a revised actual-source target.

C72 production integration complete: direct final audits, twenty imported
standard3 axiom audits, umbrella wiring, index and scratch cleanup. Lint
has the same seventeen unrelated umbrella omissions; no C72 findings.
C73 NonlinearFlow: full triangular source-field conjugacy kernel-passed.
Third transverse field jet is still unverified: raw full polynomial derivative
simplification hit default recursion depth; splitting derivatives also hit
it. Specialized to the source plane via the existing affineLine homomorphism;
its polynomial normalization passed, but bundled coefficient extraction hit
recursion depth. Now splitting the four coefficient goals. No limits raised,
no evidence of a false mathematical identity from these elaboration failures.
JetAlgebra pass4 exited0, standard3: exact third directional product rule.
MomentThird pass1 currently auditing exact third jet of the existing split
moment polynomials. This targets the unknown p3 term in the cubic slope law.

MomentThird pass1 exited0: all five norm capstones standard3. The exact
first jets of moments 2/4/6, second jet of moment8 and third jet of moment10
are now kernel-certified from their existing split source polynomials.
MinorThird assembly and generic nonlinear shift third-chain rule written.
The source-plane field coefficient audit is being repaired by separating
its four coefficient goals; no mathematical sign conclusion from it yet.

MinorThird pass5 and MinorFormula pass1 exited0, standard3. New exact
symbolic identity (after dividing by C=principalMass): the candidate third
minor jet on the nonlinear cubic sheet is

    p3(r)/C = 28160/9 − (7/12)r².

Here p3 is affineJet3 + (r²/24)affineJet1(partial_J P)
−(7r²/72)criticalValue(partial_J P). Its incidence with the nonlinear
coordinate third jet is written in NonlinearJets but not yet audited.
Together with the predicted transverse field jet, the slope cubic
coefficient becomes 1944A−63Cr². The sign mechanism is now explicit;
source-field coefficient and full conjugacy audits remain. No external
numeric or polynomial computation used: identity comes from the Lean
proof state of the kernel-certified symbolic moment assembly.

NonlinearFlow pass7 and NonlinearJets pass7 exited0, standard3. The
third-chain-rule incidence is now proved; nonlinearMinor P2=2A is exact.
NonlinearMinor pass7 proved p3=C(28160/9−7r²/12) and p3′=−7Cr/6,
standard3; two ancillary zero-field/clock statements missed nonlinearCoord
in their simp lists. Fixed. Source-field coefficient proof now uses separate
B,W,H,R,T components and cached lower coefficients, avoiding the repeated
recursion-depth failure of the full expanded field. Driver pass8 runs
FieldCoefficients, NonlinearMinor, NonlinearSlope serially. BoundarySign
is written but not audited. Predicted cubic coefficient1944A−63Cr² yields
exact threshold r²=122880/7 on the matching cubic sheet. Global cone and
actual global third-slope remain open even if that boundary test passes.

FieldCoefficients pass8 reduced to three routine omissions: sourceLines
already closed before redundant refine, missing coeff_one/map_ofNat, and
constant-polynomial powers. Pass9 was stopped by its owned Lean PID once
the known remaining omissions were identified (exit143 confirmed before
replacement). Pass10 showed that putting reverse Polynomial.C_pow into
norm_num creates a simplifier cycle with the forward map-power rule.
Replaced it with a direct coefficient-of-constant-power lemma proved by
one explicit rewrite. Pass11 serial audit active. No heartbeat/depth limit
raised; no failed cache imported. This distinguishes the coefficient
rewrite loop from the earlier large derivative-expression failure.

FieldCoefficients pass11 exited0, standard3: complete transverse third
field jet is now certified, Fs3=−63r²/4 with lower jets zero. The direct
coeff_const_pow lemma fixed the rewrite cycle without changing limits.
The same serial driver continues with NonlinearMinor, NonlinearSlope,
BoundarySign. Exact paper proof is recorded in P2
`tt-third-slope-nonlinear-boundary.md`; production migration remains pending.

NonlinearMinor and NonlinearSlope pass11 exited0, standard3. Exact cubic
slope coefficient 1944A−63Cr² now kernel-certified with full transverse
flow. BoundarySign pass13 exited0, standard3 after real-cast simplification:
the cubic matching sheet has the exact h³ factor and two sign alternatives.
Ten production leaves prepared for final serial direct audits. This is
new boundary information; global C73 remains open.

Next hard attack retains the exact geometric seam factor of the full
square-coordinate slope. The source conjugacy forces slope(V=0)=0;
quotient by V should recover the already-proved positive tangent
alpha(k)+z*beta(k) on the seam. That quotient, rather than the vanishing
full polynomial, is the appropriate global-cone sign target. No global
positivity conclusion yet.

New interior strategy from the audited cubic law: seek the joint normal
form Q(h,r,B+s)=s*A(h,r,s)+h³*L(h,r), with A(0,r,s)=7776C and
L(0,r)=1944A−63Cr². On the actual kinetic range the latter is uniformly
positive. The nonlinear barrier itself forces t>B without an asymptotic
assumption: put a=r*b≥0. From t−h²t²>a obtain t>a and t>a+h²a²;
meanwhile a+h²a²−B=49r²h⁴/5184≥0. Thus s>0 globally.
For small h the coarse speed condition bounds t uniformly, so compactness
of the r,s face and positivity of both normal-form coefficients would give
a uniform nonlinear-cone tail, not merely the existing actual flat-orbit
tail. Together with the reduced seam polynomial, this would leave an
explicit compact interior sign problem. Joint normal form and uniform
positivity are new unverified conjectures; no sign assertion from this
paper outline until exact algebra and Lean checks finish.

Cubic boundary production complete: ten direct final exits0, twenty
imported capstones standard3, umbrella wired, index exit0. Lint exit1
reports fourteen unrelated umbrella omissions and no C73 error. Original
ten scratch sources/caches cleaned. P2 paper moved to P3.
SeamFactor pass2 and SeamValue pass2 exited0, standard3: exact quotient
by V has seam value alpha(k)+z*beta(k)>0 on the corpus seam box.
CoordinateDivision pass2 exited0, standard3. NormalForm pass2 had three
proof-engineering errors (unfolded coordinate match, map_mul normalization,
let-bound scalar inequality). Repaired; no mathematical counterexample.
NormalForm/ConeTail serial pass3 auditing.

Uniform nonlinear-cone tail SCRATCH CLOSED: NormalForm pass4 and
ConeTail/ConeTailIncidence pass7 all exited0, standard3. There is one
positive clock neighborhood where every strict coarse-cone state with
t−h²t²>rb has positive full square-chart third slope. No actual flatness
premise or fixed r is used. Exact normal form Q(h,r,B+s)=s*A+h³*L,
A(0,r,s)=7776C, L(0,r)=63C(122880/7−r²), plus barrier⇒s>0 and
compactness, proves it. Proof-engineering repair: separate generic
continuity/compactness from large concrete polynomials and specify
Tendsto base points. Default limits unchanged. Production migration next.

Remaining hard sign is the interior. Full Q vanishes on V=0, so a
positive-coefficient normal form for Q cannot be extended blindly across
that face. New exact algebra attack: carry the proven square-slope V
factor through compactification. Any source polynomial has a polynomial
regularization after some power of h (structural induction). This gives
V | h^n*Q. The Bezout identity (V+rh²)/9=1 makes V coprime to h, so
V | Q without a degree estimate or numerical computation. Scratch
TTC73ScaledDriftFactor written and auditing. Its quotient is the intended
remaining global interior sign target, not yet a positivity certificate.

Do not extrapolate the cubic normal-form coefficient signs globally:
B−rb=r²h²(1−7h/3)/144 changes sign, whereas the true nonlinear
boundary is implicit and remains above rb. The uniform tail uses only
small h and is sound. Global interior work must retain the exact barrier
E=t−h²t²−rb (or its algebraic boundary), as well as the seam factor V.
The quartic lower comparison rb+h²(rb)² is valid globally, but no slope
sign on that larger polynomial sheet is currently proved. This is a
structural limitation of the truncation argument, not a failure of C73.

## Next hard conjectures after the uniform-tail closure

Keep C73's full pointwise question; do not replace it by more tail jets.
Let Rbar=reducedScaledSlope, V=9−rh², E=t−h²t²−r*b(h), and
F=compactSpeed. The exact remaining domain is

    0<h<4/5, 0<r<361/25, V>0, 0<t, h*t<1, F>0, E>0.

Target: Rbar(h,r,t)>0 on this whole domain. Since V>0 and
Q=V*Rbar, this is exactly the original scaled-slope sign problem.
The uniform tail is solved; the intervening region is not.

C73a (unproved): for fixed h,r, the real t-derivative of Rbar is
nonnegative throughout each admissible interval starting at the lower
E=0 branch. This would reduce the interior sign to its exact algebraic
boundary, if true. Test/prove this full polynomial sign, not just its
limit or a few values. Its failure would require locating the exact
remaining monotone regions or critical-point classification; it would
not by itself falsify C73 or RH.

C73b (unproved): Rbar is strictly positive on that admissible E=0 branch.
Use the entire relation t−h²t²=r*b(h), not B's truncation. The corpus
`failure_small_branch` proves h²t<1/6 on this boundary under the kinetic
and source constraints (q=t/r, V=9−rh²). Thus the correct branch is
already selected; no new root-choice premise is needed.

Available corpus algebra: `MvPolynomialPseudoReductionAt` in
`DifferentialCharacteristicPseudoReduction` gives exact pseudo-division
at the r coordinate. `GammaFirstJetRiccatiKernel` gives the analogous
monic boundary/remainder principle, but its Z−W² relation is not directly
our E. Neither theorem supplies a positivity certificate. If used, retain
the divisor orientation: D=r*b−t+h²t²=−E has initial b>0 on h<4/5.
Then b^N*Rbar=E*H+remainder uses H equal to minus the pseudo-quotient.
Retain that sign, the exact remainder, and the source-dependent quotient;
do not hide their signs behind hypotheses.
New work must obtain those signs or a rigorous counterexample and its
positive survivor, rather than formalize only the generic reduction.

Production integration of the seven tail/seam/factor leaves: all final
lake --old env lean exits0, fourteen imported capstones standard3,
umbrella wired, index exit0. Final lint/cleanup pending at this entry.
P3: tt-nonlinear-cone-uniform-tail. RH/global third slope/full quadratic/
fourthgap/join/allrank remain OPEN.

Final C73 tail integration complete: seven final direct leaf audits and fourteen imported capstones passed; umbrella wired; index exit0; lint exit1 with eighteen unrelated umbrella omissions and no C73 finding. Superseded C73 scratch sources/caches cleaned; logs and manifests retained. No owned Lean or search process remains. Next hard work is C73a/C73b above, not further tail expansion.

2026-10-04 continuation: classify previous turn as PROGRESS (17 final
leaves, 34 axiom audits, uniform cone tail and exact seam factor).
Before attempting a full transverse monotonicity certificate, inspect a
necessary interior-boundary condition that the current cone still allows:
fixed 0<h<4/5, r→0, t=q*r. The axis r=t=0 is an exact polynomial limit
at finite h, not the already-proved h→0 limit. Cone feasibility requires
b(h)<q<(1−2h/3−4h²/9)/(6+4h). If axisSlopeCore changes sign at any
such finite h, continuity gives a rigorous nonlinear-cone obstruction.
If it stays positive, extract the exact full-axis sign theorem and keep
attacking the interior. This is an algebraic classification target, not
numerical sampling or another asymptotic expansion. Corpus searches
`tt_c74_interior_search.json` and `tt_c74_axis_sign_search.json` running.

C74 finite-clock axis test: exact moment2/4/6 axis polynomial certificates
passed scratch Lean, standard3. Full normalized axis minor and slope
assembly now auditing. Searches both partial (generation1228562/1228563),
all candidate/source/idea sections inspected: existing axis code gives
only h=0 sign, not the complete finite-clock classification.
Feasibility of the r→0 test is substantive: A(h)−(6+4h)b(h)=
1/2−5h/12−h²/18 is strictly positive for 0≤h≤4/5. Thus q can lie strictly
between b(h) and A(h)/(6+4h), leaving both the nonlinear barrier and
positive source speed for sufficiently small positive r. The exact axis
sign is therefore a necessary condition for the full C73 cone claim.
No numerical evaluations or external algebra computations are used.

C74 axis condition CLOSED positively in scratch Lean (all capstones standard3):
Q(h,0,0)=A*h³*q(h), and q(h)>0 on 0≤h≤1. Exact complete degree16 q
has negative terms only in degrees6,7,8. Their magnitudes are absorbed
by degree5 using h5*[c+(1−h)(a6+a7(1+h)+a8(1+h+h²))],
c=3491/16−4619/288−454729/5184−51673/1152>0. All remaining
coefficients are positive. This proves the whole finite-clock axis sign,
not samples or a tail expansion. Scalar evaluation before normalization
was essential to combine rational constant-polynomial casts; no heartbeat
changes or external algebra computation used. Production promotion now
uses three leaves AxisCompleteMoments/Minor/Slope. Next: hard global
transverse sign under E>0,F>0; C74 does not prove the full cone claim.
Search tt_c74_transverse_search partial, all sections inspected: no global
transverse sign theorem returned; only planeSlope_J and boundary jets.

C75 interior attack, retaining C73a/C73b rather than changing the goal:
normalize each full moment by 6^(n+2)*24^(n/2). Every complete third-minor
product then has common scale 6^24*24^9; the extra axis mass is720.
Use exact full moment identities to form the complete t derivative,
then apply the nonlinear relation and positive source-speed domain.
No truncation or numerical sampling is permitted. This normalization
changes representation, not the conjecture; an algebra identity alone
will not be counted as a solved frontier sign. Full-moment scratch
certificates TTC75Moment2/4/6/8/10 prepared from the literal corpus
parts. Next derive the complete transverse operator and exact-boundary
remainder; neither sign is established yet.

C74 final integration complete: three final direct leaf audits exit0;
seven imported capstones standard3; umbrella wired; index exit0.
Lint exit1 with nineteen unrelated umbrella omissions, no C74 finding.
P3 tt-complete-finite-clock-axis-slope and frontier map updated.
C75 fullMoment2ValueNorm scratch passed standard3; remaining full-moment
certificates are auditing serially. This is algebraic preparation for the
unsolved complete transverse sign, not a new sign theorem.

C75 all five full scalar moment certificates passed scratch Lean, standard3.
Their complete symbolic expressions are printed in
/tmp/tt_c75_moment_expressions_pass3.log (no omitted terms). The initial
print settings pp.maxDepth/pp.width were invalid; corrected from installed
Lean source to pp.deepTerms/format.width and pp.maxSteps. These affect
display only; proof heartbeat/recursion settings remain unchanged.
Expressions were transcribed by textual cast/variable substitution into
TTC75Polynomial2/4/6/8/10.lean; their polynomial equalities are auditing.
Do not assume those pass from the scalar audits alone.

Exact-boundary attack planned from the corpus formulas: D=6−7h>0 and
E=0 imply r=72t(1−h²t)/D. Each normalized moment has r-degree at most
n/2; determinant at most9 and complete slope at most10. Thus clearing
D^10 gives an exact two-variable boundary polynomial. The drift factor
becomes 9*(D−8h²t+8h⁴t²)/D. The C73 cubic contact predicts an h³
factor after exact boundary substitution, but this full identity and its
remaining sign are NOT yet proved. Establish the complete factor and
positive remainder retaining F>0 and the kinetic constraint; do not count
generic denominator clearing or another boundary jet as sign progress.

C75 checkpoint: all five fullMomentNValueNorm certificates are valid
standard3 scratch leaves TTC75Moment2/4/6/8/10.lean. The attempted
additional scalar-to-polynomial transcription is NOT complete: moment2
and4 passed, but moment6 global association exceeded default recursion
even after per-block evaluation certificates. No resource limits were
raised. No mathematical conjecture was falsified by these tactic failures.
All transcription files/caches and the unverified assembly were removed;
retain the five valid scalar leaves/caches and exact expression log.
No owned Lean or search process remains. C74 production is fully audited
and integrated.

Assessment: C74 closed a necessary whole finite-clock boundary sign.
C75 work since then is algebraic preparation, not another hard sign
advance. Next attack the exact nonlinear boundary BEFORE unrestricted
three-variable expansion; no need for the failed extra polynomial lift.
Use the literal source polynomials and the exact E=0 substitution, with
D=6−7h>0, retaining the complete flow derivative. The existing
ThetaCuspRatioQuadraticBarrierBranch.failure_small_branch proves
w=h²t<1/6 on the admissible boundary (q=t/r,V=9−rh²). E=0 then gives
t<6rb/5≤r/10<361/250. These are domain consequences, not a proposed
bound-improvement project. The hard conjecture is positivity of the
complete D-cleared, h³- and drift-divided boundary remainder under these
constraints. Its exact factorization and sign remain unproved; global
transverse monotonicity remains unproved as well. Keep attacking these
signs, not more tail/axis jets or general-purpose polynomial plumbing.

2026-10-04 C75 continuation, previous turn classified PROGRESS by C74;
later C75 normalization did not advance a sign. Direct boundary review
reveals a better exact relation in original squared coordinates: writing
Y=1−3Z, K=k, T=9−V, the compact barrier E=t−h²t²−r*b(h) is
K*Y−Y²−K*(6K−7)*T/72. Thus B=Y²−K*Y+K*(6K−7)*T/72 is MONIC
in Y. No D-denominator is needed for reduction in this variable.
Important: substituting B=0 into the minor before differentiating loses
the normal derivative. Retain the first normal jet modulo B². Every
polynomial then has form a+bY+B(c+dY) modulo B². With
d0=K*(6K−7)*T/72, multiplication byY sends (a,b,c,d) to
(−d0*b,a+K*b,b−d0*d,c+K*d). The actual determinant's full B²
reduction, followed by its literal source flow, should yield a complete
affine-Y boundary slope. Target its actual coefficients and sign, not a
generic existence-of-remainder theorem. Boundary small branch isY/K<1/6;
retain0<Y<1 and K²T<361/25. Search monic first-jet corpus underway.

C75 implementation simplification from source audit: reduce the FULL
already-differentiated square slope itself in QuadraticAlgebra, not the
minor followed by an induced quotient derivation. This preserves the
normal jet automatically and avoids building a new dual extension.
Use Z directly as quadratic root: Z²=a+bZ,
a=(K−1−K*(6K−7)*(9−V)/72)/9, b=(2−K)/3.
Evaluate each literal moment and its literal squareLie image into this
algebra, then assemble the full determinant slope. Their two components
give the exact affine-Z boundary expression. Mathlib QuadraticAlgebra
API inspected from installed sources. Full scalar-to-polynomial lifting
from last turn remains unnecessary. No sign theorem yet.

C75 boundary algebra now PASSED standard3: TTC75BoundaryAlgebra provides
boundaryHom_eval, boundary_root_iff and compact_boundary_mass.
TTC75BoundaryPowers provides verified omega powers through11;
TTC75BoundaryNumerals corrects numeral projections;
TTC75BoundaryDynamics expands the full source flow before reduction.
First moment2 re/im remainder coefficients passed and are true v,k
polynomials; initial flow normalizations left a finite sum unevaluated,
so they were valid identities but NOT coefficient normal forms. Fixed
by rewriting squareFlow_explicit75 before simplification; serial full
moment/flow driver now auditing. One mistaken early dependent launch
failed on missing Numerals import while its producer was still running;
that consumer exited1 and no replacement started until producer exit0.
Subsequent builds are gated on confirmed terminal producer success.

New branch/sign route to assess with the ACTUAL affine coefficients:
a=(K−1−d0)/9 is positive throughout K≥5/4, K²(9−V)≤361/25, since
648K*a=72(K−5/4)²+(534/25)(K−5/4)+382/25+
(6K−7)(361/25−K²(9−V)). Thus the monic Z quadratic has one positive
and one negative root. If the literal boundary slope remainder isA+ZB,
positivity of A and its quadratic norm A²+bAB−aB² suffices at the
positive root. This is a PROPOSED global sign certificate; neither A>0
nor its norm sign is proved. No extra small-branch premise may be added.

For coefficient assembly, exact Euler cofactor identity for the cubic
determinant D gives normalized slope as sum cof_i*((6K−1)*dm_i−
2*m_i*seedFlow), seedFlow=6*squareFieldK. This retains every source
term and may cancel leading terms before large products. Corpus
cofactor search underway; do not replace sign work by a generic
Jacobi-identity wrapper.

C75 next continuation: the explicit-flow audit initially hit recursion
limits because coordinate inequalities (e.g. K≠U) remained unresolved
inside partial derivatives. Supplying all six constructor inequalities
fixes this without changing proof limits. Full boundary moment/flow
coefficients for 2,4,6 now pass standard3. Moment6 flow required exact
additive blocks of four existing source parts to fit default heartbeats;
no truncation. Moment8/10 use the same full-source block scheme. The
pending cofactor search completed partial (generation1229385; query,
reranking/filter deadlines); all result categories inspected. It adds
no existing solution of the boundary sign. Euler cofactor decomposition
is being checked locally, with normalized full flow moments—not a
quotient derivation. No new sign theorem or global closure yet.

C75 full moment8/flow8 and the exact Euler/cofactor slope identity now
pass standard3. Moment10's full flow passed all additive blocks and
assembly; its two unsplit value proofs timed out at nested-proof
abstraction. Split these values as well, and separated Flow10 into an
independent leaf so value edits do not rebuild it. Failed Moment10 cache
removed. Full boundary affine slope/sign remains unproved.

A second corpus search (third slope exact quadratic boundary forcing
factor) returned partial generation1229659/pending coverage, deadline
and filter stages unfinished. Every declaration/candidate/source/idea
category inspected. No existing full boundary factor/sign found. The
forcing theorem only asserts boundary negativity for h≤2/3; high-clock
C72 closure used a source dynamical trap. Do not assume forcing has the
needed sign on the entire abstract cone.

Retain exact physical branch in C75: positive kinetic a makes the Z
quadratic's other root negative. E>0 puts physical Z below its positive
boundary root. The known affine seam certificate (positivity at Z=0 and
Z=1/3) suggests a simpler interval certificate, but its upper endpoint
need not remain positive away from the seam: the cubic-sheet asymptotic
is close to critical cancellation, while the true boundary moves below
Z=1/3. This is motivation for retaining the exact quadratic norm, NOT a
proved failure or a replacement sign theorem. Alternative exact
rationalization is already corpus-grounded by boundary_core_polynomial:
w=h²t, V=9-w(1-w)/b(h), K=h⁻¹, Z=(1-w/h)/3. Keep as an option after
testing the actual affine coefficient/norm; do not abandon the current
full-source sign attempt over expression size.

C75 all20 moment/flow coefficient identities now pass standard3;
TTC75BoundaryExpressions audit exited0 and every RHS identifier is only
v,k,Nat/Int/Rat/NNRat raw numeric syntax. Thus these are full scalar
polynomials, not identities with unevaluated coordinate/evaluation atoms.
Moment10 scalar witnesses needed proof-wrapper separation before
multiplication: TTC75BoundaryScalar10 copies the exact Lean-emitted
expressions, reassociates addition into blocks, and proves all four
value equalities by norm_num/ring. No coefficient arithmetic outside
Lean. Initial raw-cast transcription and then an annotation-parentheses
error failed; both failed caches were removed. Correct Scalar10 pass3
has four standard3 capstones. Cofactor10 and twisted flow10 components
now pass standard3 (pass3); the other cofactors are auditing serially.
No mathematical sign conjecture has yet been proved or refuted.

C75 sign-attack plan after the ACTUAL affine coefficients are assembled:
use compact quadratic variable W=h*Z. Its relation is W²=a_h+b_h*W,
a_h=(h-h²-r*h²*(6-7*h)/72)/9 and b_h=(2*h-1)/3. If full slope
remainder is A+Z*B, define A_h=h^23*A(9-r*h²,h⁻¹),
B_h=h^22*B(9-r*h²,h⁻¹). These exponents are conservative degree
predictions from the literal moment/flow structure, still to audit.
Then h^46*Norm(A+ZB)=A_h²+b_h*A_h*B_h-a_h*B_h². This keeps
compact parameters and exact root geometry. The positive branch is
W≈h/3; the conjugate branch is W≈-1/3 as h→0. Existing C73 cubic
boundary cancellation predicts a substantial h-factor (tentatively h^7)
in this norm and h-divisibility of A_h. Neither divisibility nor sign
has been proved yet; extract exact factors from the complete source
coefficients, then attack the remaining polynomial sign. Do not replace
this test with another local asymptotic theorem.

Important refinement for the forthcoming global sign test: strip the
already-proved U/V factor BEFORE forming the quadratic norm. The
corpus slope_seam_factor says slope=XU*reducedSlope; otherwise both A
and B vanish at V=0 and their norm has an avoidable V² factor. Every
cofactor-twisted flow T_n should itself carry V (full moment flow has
V, as does seedFlow). Once the T_n expressions are emitted, formalise
T_n=V*RT_n from those exact scalar polynomials, then assemble
R=Σcof_n*RT_n. Test the actual A_R and norm of R. This is an algebraic
factor removal already forced by the source, not a new sign premise.
Do this before the currently prepared Product_n scratch files, which
still multiply unreduced T_n and should be updated to RT_n.

C75 all20 cofactor/twisted-flow scalar identities now pass standard3.
Cofactor2Re only failed in redundant norm_num cleanup AFTER successful
raw ring normalization; removing that cleanup closes it at unchanged
limits. Full source assembly and boundary evaluation pass standard3 in
TTC75BoundarySlopeAssembly (pass2; only missing map_ofNat in seed
helpers caused pass1 failure). Both the kinetic a>0 proof and the
A>0/N>0 positive-root criterion pass standard3 in TTC75BoundarySign.
These do NOT establish the actual coefficient signs.

Cofactor expressions audit exited0. Next: syntax-only extraction into
balanced CofactorValues_n plus formal T_n=V*RT_n factor proofs, then
reduced product assembly. The generating text job unexpectedly ran
longer than10seconds; use run_guarded for future reruns of it. No
arithmetic on coefficients outside Lean; V-power shifts are written as
(n-1) expressions and verified by Lean ring proofs.

Additional paper-derived geometry for the SAME boundary sign attack
(not yet novelty-audited/formalised): C72 failure_small_branch gives
w=h²t<1/6 on E=0. Write b=1/12-7h/72, A0=1-2h/3-4h²/9,
V=9-rh². From E=0, t(1-w)=r*b and r*h²*b=w(1-w).
The full forward speed F=r*A0-(2/9)(3+2h)*V*t obeys
(1-w)F=r*H, with
H=A0*(1-w)-(6+4h)*b+(2/9)(3+2h)*w*(1-w).
An exact positive decomposition on 0≤h≤4/5, 0≤w≤1/6 is
H=191/4050+(5/12)(4/5-h)+(1/18)((4/5)²-h²)
 +(1/3)(1/6-w)+(46/45)((1/6)²-w²)
 +(4/9)(4/5-h)*w²+w*(10h/9+4h²/9).
Thus forward speed should be automatic on the entire physical nonlinear
boundary under the already-used kinetic/branch conditions. This is a
domain simplification for the full boundary sign problem, not a new
numerical target. The actual A_R/norm positivity remains the main gap.

Interior continuation suggested by the exact same monic source model
(PAPER CONJECTURE ONLY): E=9*(a+bZ-Z²), so retaining positive E replaces
the quadratic relation by Z²=(a-E/9)+bZ. Full source reduction then has
finite form Σ E^j*(A_j(V,K)+Z*B_j(V,K)), with j=0 the current boundary
remainder. If B_0≤0 and every j≥1 coefficient is nonnegative for
0≤Z≤1/3, boundary positivity would imply whole-cone positivity because
E>0 places Z below its positive boundary root. This offers an exact
surplus decomposition alternative to proving the full transverse
derivative sign. No coefficient sign or global interior statement is
proved. It reuses the same source moments and quadratic-algebra powers;
it is not a reason to leave the current boundary norm attempt unfinished.

C75 continuation: all five exact twisted-flow V-factor identities and
boundaryReducedSlope_evaluate75 passed direct Lean audits with standard3.
Reduced Product10 passes standard3; Product8 is the current sole owned
Lean process. The complete reduced affine source coefficients, then
actual compact A/norm signs, remain the immediate target. This algebra
preserves normal derivatives and removes the source's proven V factor;
it does not yet advance the global sign theorem.

Corpus search tt_c75_actual_norm_search.json completed with partial
snapshot generation1230412 (inventory complete, most compiler entries
pending/stale; several refined queries/reranking unfinished). All
candidate/source/idea/ingredient categories inspected. Bernstein
monomial reconstruction is relevant; the proposed ingredient set mixing
sqrt-slope estimates with eventual source-slope positivity does not
supply the needed quadratic norm sign. No new mathematical premise
accepted. Use exact source polynomial positivity over the compact domain,
not another axis/tail result.

Important live sign conjecture refinement (paper only): do not demand
A>0 and norm>0 before reading the full coefficients. The nonphysical
quadratic root is asymptotic to -K/3, and its full source slope can have
the opposite orientation. If B>0 and N=A²+bAB-aB²<0, physical-root
positivity follows instead: the two affine root values have opposite
signs and the larger root has the larger affine value. Thus N<0 may be
the correct certificate, not failure of boundary positivity. No actual
coefficient sign asserted yet. Complete products10,8,6 now pass standard3;
Product4 is auditing. Full source assembly is still required before
choosing the sign branch.

C75 all ten reduced product scalar identities (Products2,4,6,8,10) pass
standard3. ProductExpressions audit exited0; all RHS tokens are pure
v,k and rational numeric syntax. Full-sum normalization attempt1 failed
inside norm_num with default recursion depth; attempt2 (dsimp then raw
ring_nf) failed at default heartbeats. Failed caches removed. These are
formalization failures, not mathematical sign counterexamples. New
ProductValues files copy exact emitted raw coefficients into balanced
16-term parts. Reassociation via dsimp/ac_rfl also hits default recursion
on the old long form; failed Value2 cache removed. Current repair proves
each balanced value from the original factored C_n*RT_n expression,
using the already-audited cofactor values, then sums balanced values.
No limits raised and no coefficient arithmetic outside Lean.

The generic opposite-norm sign rule now passes standard3 in
TTC75BoundaryOppositeSign: a>0,z>0,z²=a+bz,B>0,N<0 implies A+zB>0.
This is a criterion only. No actual global A/B/norm sign proved yet.

Exact compact certificate construction to try after the actual A/B/norm
is available: corpus Bernstein reconstruction can be implemented in the
positive orthant without numerical sampling. Homogenize a polynomial
P(h,r) under h=(4/5)/(1+x), r=(361/25)/(1+y), multiplying by
(1+x)^d(1+y)^e. Nonnegative monomial coefficients then prove the desired
sign on the whole positive rectangle; x=(4/5)/h-1 and
y=(361/25)/r-1 recover every h,r>0 in it. Exponents d,e must be
kernel-verified, and all coefficient normalization stays inside Lean.
This is only a certificate mechanism, not an assertion that coefficients
or the actual norm have either sign. If the stronger rectangle fails,
retain the physical V>0 constraint rather than infer source failure.

All five balanced ProductValues modules now pass direct Lean audits;
ten value equalities have standard3 axioms. Value2 pass2 (proof from
factored source) and Values4/6/8/10 pass1. The complete affine coefficient
normalization is now running as SlopeCoefficients pass3, using balanced
value equalities before norm_num/ring_nf. ProductExpressions has ten
complete scalar RHS blocks; whitespace-normalized source inspection finds
K exponents through23 and V exponents through18. This is syntactic
support for conservative compact scaling, not a formal degree theorem
or a sign result.

Full affine normalization pass3 still timed out at the default200000
heartbeats in Ring.Common.evalAdd; its cache was removed. Repair now
splits by literal powers of V before combining the five products.
TTC75BoundaryProductColumns rewrites each balanced product as nineteen
V-columns with univariate K coefficients, copied syntactically from the
same audited expressions. No rational arithmetic in the generator.
Pass1 was interrupted by its owned PID before completion after finding
missing mul_zero cleanup for the identically zero Im V^18 columns;
terminal exit130 confirmed, its cache deleted, then pass2 started.
At the current checkpoint the first five column-reconstruction capstones
pass standard3; no sign theorem inferred. ColumnNorms is prepared with
38 separate univariate normalizations. SlopeCoefficients has been
rewritten to reassemble these exact columns with ac_rfl and imported
column normalizations; it is not yet audited in this new form.

C75 ProductColumns pass2 completed: all10 capstones standard3.
ColumnNorms pass1 completed: all38 capstones standard3. Reconstructed
SlopeCoefficients pass4 completed: all4 capstones standard3. The full
boundary affine source is therefore assembled exactly, with each
V-column normalized separately. ColumnExpressions audit exited0: all38
RHS use only k and rational numeric syntax. Both V^18 columns vanish;
remaining Re columns have K powers at most22, Im at most21. No sign
asserted. CompactRe/CompactIm are now prepared with degrees22/21;
map each literal K^p term to h^(d-p) times its copied coefficient, with
subtraction and reciprocal clearing proved inside Lean. CompactRe is
the current sole owned build. The older speculative23/22 scaling is
unnecessary;22/21 will be kernel-verified by these identities.

C75 CompactRe pass2 (pass1 only had redundant tactics after the zero
column closed), CompactIm pass1, CompactAssembly pass1 all pass standard3.
Full identity now proved for h≠0 and exact original root z:
h^22*mass^-1*eval(sourceSlope)=V*(A75(h,r)+h*z*B75(h,r)).
CompactZero pass1 proves A75(0,r)=0 and B75(0,r)=268435456/2187>0.
Thus choosing a norm orientation blindly was unsound. A first-order A
sign or an actual norm sign has NOT yet been proved; do not claim the
positive-A/positive-norm conjecture formally refuted from B0 alone.

New paper insight for the SAME full boundary sign target: set
b(h)=1/12-7h/72 and t=b(h)*s. Then E=0 is solved POLYNOMIALLY by
r=s*(1-h²*b(h)*s), so V=9-h²*s+h^4*b(h)*s² and
Z=(1-h*b(h)*s)/3. Unlike w-parametrization this has no denominator b
and no square root. b>0 throughout 0<h≤4/5, so every physical E=0
state has s=t/b(h). C72's selected branch w=h²t<1/6 and r≤361/25
imply 0<s≤(6/5)*(361/25). The full actual compact boundary expression
is exactly A75(h,r(s))+(h/3)*(1-h*b(h)*s)*B75(h,r(s)). This discards
no normal derivative because A/B came from full source flow before
boundary evaluation. It avoids having to impose a sign on the
nonphysical conjugate branch, a structural reason to test this exact
physical polynomial, NOT an effort-driven abandonment of the sign task.
Global sign and any h-divisibility remain open. Corpus novelty search
for this parametrization started in tt_c75_boundary_parameter_search.json.

C75 exact physical polynomial parametrization is now formalized in TWO
minimal production leaves, without importing the large affine-remainder
scratch chain:
- ThetaCuspRatioNonlinearBoundaryParameter.lean
- ThetaCuspRatioNonlinearBoundaryCore.lean
Both passed final direct `lake --old env lean -o ... <file>` audits;
/tmp/tt_c75_production_axioms.lean imports production Core and audits all
nine capstones. All use exactly propext, Classical.choice, Quot.sound.
Both leaves are wired into RHTower.lean; no umbrella/full build.
P3 card: tt-exact-nonlinear-boundary-core.md. Frontier map TT updated.

Exact production result: every admissible E=0 state is recovered by
s=t/b(h), with 0<s<(6/5)*(361/25). Write R=s*(1-h²*b*s), T=b*s,
V=9-R*h², Z=(1-h*T)/3. The whole source slope S obeys
h^16*S(V,h⁻¹,Z)=C(h,s), where
C=L(h,R)+h*J(h,s)*A(h,R,h^4*J(h,s)) and
J=b*s³*(2-h²*b*s)*(1/144-7h/432)+49s²/5184.
This follows from the exact gap T-B_cubic(h,R)=h⁴J and the existing
complete cubic normal form. C(0,s)=1944*axisMinorMass-63*principalMass*s².
No sign proved and no derivative taken after boundary substitution.

NEXT HARD CONJECTURE: prove positivity of this complete physical core,
preferably after factoring its forced V factor. Do NOT demand strict
positivity of C on the entire enclosing h,s rectangle: C vanishes at
V=0 and may change sign outside the physical domain. A quotient is the
appropriate candidate for a closed-rectangle certificate. Source route
for a polynomial V-factor: substitute the polynomial R,T into the
already-proved scaledSlope=driftSquare*reducedScaledSlope and the exact
h³*C identity. V=9-h²*R is coprime to h (same Bezout identity as
ThetaCuspRatioScaledDriftFactor); cancel h³ divisibility algebraically.
Then attack the full quotient sign, not another tail/axis bound.
Interior/transverse slope, full source quadratic, fourth gap, join,
all-rank closure and RH are still open. No mathematical no-go declared.

The parametrization corpus search was partial snapshot generation1231138,
complete65537-file inventory, mostly pending/stale compiler records,
deadline/semantic-coverage incomplete. All candidate/source/idea/ingredient
categories inspected. failure_small_branch is directly relevant;
Bottcher/ray-avoidance ingredient suggestions are unrelated and unused.

Final lint: exit1, 21 unrelated umbrella omissions plus one unrelated
active sorry in LiClockThetaGeneratorLogSlope.lean:280. No new-leaf
finding; production imported capstones remain standard3. Do NOT report
repository-wide lint green. Scoped git diff --check exited0.
All owned Lean/search/lint processes finished. Failed caches removed
before retries. Seven superseded temporary code generators removed;
audited C75 scratch Lean files and emitted coefficient records retained
as active research evidence. Goal remains active, not achieved.

C76 started: previous goal turn classified PROGRESS (two production leaves,
full-source boundary identity and coverage), not a sign closure. Current
production files/frontier/log revalidated. Hard target remains actual
boundary quotient positivity, then full interior/transverse third slope.
Next exact algebra: represent the C75 boundary core in the existing
MvPolynomial Coord ℂ ring, pull back the already-proved drift factor,
use V=9-h²R coprime to h to divide the full core by V. Then work on the
actual quotient sign. No branch-sign or RH premise may be added.
