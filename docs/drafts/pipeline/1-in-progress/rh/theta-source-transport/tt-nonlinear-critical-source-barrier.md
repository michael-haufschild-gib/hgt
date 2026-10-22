# Nonlinear critical source invariant beyond the second transverse slope

- **ID:** tt-nonlinear-critical-source-barrier (C72)
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Route:** TT, global actual third-minor slope.
- **Statement:** Prove on the actual ray x>0 that
  q−(9−u²)q²>1/12−7/(72k), with no added source or RH premise.

## Why this attacks the hard sign

C71 gives the exact second transverse coefficient
54C(144a−r²) for t=r*b(h)+a*h². C70's affine barrier leaves both
signs possible even inside the strict coarse cone. The proposed
nonlinear invariant cancels that precise adverse coefficient; it is
not a numerical refinement of an existing bound. Global S positivity
still requires a separate full polynomial/dynamical proof.

Corpus search /tmp/tt_c72_quadratic_barrier_search.json: partialfalse,
generation1225902, inventorycomplete. All candidate/source/ingredient
sets inspected. It returns the actual C70 barrier, q first-order limit,
compact incidence and flatness; no nonlinear invariant or inward force
sign. These are the basis for the new conjecture.

## Exact algebra already kernel-verified

Use h=1/k,V=u²,T=9−V,b=1/12−7h/72 and C70's polynomials D,A,G,Hh.
For y=q−Tq²−b,

    Hy=6T*R+6(1−2Tq)A*y,
    R=(1−2Tq)(D+q²A)+(7/216)q*Hh+2Vq².

This split passed in /tmp/TTC71QuadraticField.lean (standard3), still
scratch while the actual normalized-defect proof is developed.

Set z=y/T. The exact intended source ODE is

    z′=(k/u)*([A(1−2Tq)+2V]z+R).

C70 implies z≥−q². Bounded actual q therefore gives a lower bound on z
on every tail. The existing first-order q=b+o(h) and all-order kinetic
flatness suggest R/h→−7/16, so bounded negative escape should force
z>0 eventually. Initial positivity can be checked using the already
formalized exact seam ratio and its k(0) range.

## Hard open step under attack

Prove H R<0 at R=0 while z≤0, using the complete available source
constraints; then apply the two-function trap and exclude equality.
The failure region has b≤q≤b/(1−h) from C70 and Tq<h. Retain the
kinetic constraint T<(361/25)h²: it excludes spurious small-V states
at clocks below the actual seam range. Do not silently drop it.
The forcing sign has NOT been proved, nor assumed.

At V=0 the exact algebra suggests that on R=0,
H R=972q(1−18q)*y. This is nonpositive in the failure region when
q≤1/18. The V-dependent remainder is the mathematical obstruction
to resolve. This boundary identity is still awaiting Lean verification;
it motivates an exact forcing decomposition, not a sign claim.

## Status

C70 complete production; C71 production leaves passed and umbrella
wired, final imported audit/index/lint running. No RH proof or
falsification. No actual nonlinear invariant claimed.

C72 first forcing audit PASSED: /tmp/TTC72QuadraticForce.lean audit1
exit0, normalized_quadratic_field and quadratic_forcing_seam_nonpos
standard3. The V=0 forcing sign is now exact, not conjectural.
The tail residual normalized in Lean to
 R(h,9,b(h))=−7h/16+125h²/288+49h³/288+49h⁴/2592.
No nonzero-V forcing sign has been asserted.

Next exact decomposition to attack the hard nonzero-V sign:
set f=1−2Tq, m=Hh/V=−(4/3)h(3+h)(h−Tq), y=q−Tq²−b.
If R_h,R_V,R_q are the partials of R, source differentiation gives
 f*HR=6T R_q R+6f A R_q y+V*K,
 K=f*(R_h*m+12T R_V)+R_q*(−7m/72−12Tq²).
This follows from f*Hq=6T R+6f A*y−7Hh/72−12VTq².
It isolates the exact remainder to sign on R=0, y≤0, with
0<h<4/5, 0<V<9, q≥b, Tq<h and T<(361/25)h².
Do not assume A*R_q≥0: it may change sign and may need absorption
using −Tq²≤y≤0. This decomposition is currently paper algebra,
not yet kernel-certified; next audit should certify it and its sign.

Further paper reduction (not yet audited): write f=1−2Tq and
 L=f²*q²*(2/3)(1+h/3)T+2T*((7/216)q*m+2q²)
   +(7/216)f*(m+q*(4/3)h(3+h)T)+4qf.
Then f*R_q=−2TR+2q f² A+V L, and therefore
 f*HR=(6T R_q−12ATy)R+12q f² A² y+V*(K+6A L y).
At R=0,y≤0,q≥0 the square term is automatically nonpositive.
The true polynomial sign left is K+6A L y<0, retaining all source
constraints; no separate assumption A*R_q≥0 is necessary.
Scratch /tmp/TTC72CompletedForcing.lean prepared, NOT yet audited.

ForcingDecomposition audits1–4: algebraic forcing_direction_split
passed standard3. Scalar partial derivative scripts failed because
the imports did not expose deriv_fun_add and deriv_fun_sub. Earlier error-only grep missed error(lean.unknownIdentifier).
Use broad 'error' matching and the mandatory /tmp name probe before
all imported mathlib names. Failed decomposition cache removed.
Probe2 also lacked deriv_add/deriv_sub. Source import inspection resolves
the cause: Deriv.Mul imports FDeriv.Add, not Deriv.Add. Adding the
explicit Deriv.Add import made probe3 pass. No stale-library conclusion
is supported. No mathematical failure or changed statement.

ForcingDecomposition audit5 exit0: exact forcing_direction_split plus
all three scalar partial derivative identities dRh/dRv/dRq standard3.
The earlier implementation issue was solely a missing Deriv.Add import.
CompletedForcing audit1 now active; no completed remainder sign claimed.
FailureBranch scratch prepared to prove f=1−2Tq>0 on the full failure
region using the kinetic constraint. Its key exact identity is
 4/441−h²b(h)=(h−4/7)²(7h+2)/72.
This selects the small quadratic branch needed by the forcing argument;
it is a structural denominator sign, not a target bound optimization.

CompletedForcing audit2 exit0, both completed_forcing_split and
forcingDrift_neg_of_completed standard3. Important corrected identity:
 f HR=(6T R_q−12ATy)R+12q f² A² y+V*(K+6A L y).
No extra factor of f belongs in the V remainder. The earlier square
term now has a verified sign without an A*R_q sign assumption.
The remaining completed remainder K+6A L y is UNSOLVED on R=0.
FailureBranch audit1 active. Search /tmp/tt_c72_source_quadratic_search.json
active for a direct source positivity mechanism for the same invariant.

Equivalent scalar source inequality (paper algebra):
 72(1−3Z)(k−1+3Z)>k(9−u²)(6k−7), Z=J/u.
A source moment/covariance identity proving this would close the same
C72 goal directly. Do not infer such an identity from terminology.

FailureBranch audit1 exit0, failure_factor_pos standard3. Search source_quadratic
finished partialtrue (filter_and_judge malformed JSON; generation1226260,
inventorycomplete, mixed source/compiler freshness). All candidates/source
arguments/ingredient sets inspected; none provides applicable ratio inequality.
No direct covariance identity inferred. Next structural consequence: with
w=Tq, failure gives w(1−w)≤Tb≤(361/25)*(4/441)<5/36. Already f>0
selects w<1/2, so w<1/6. This separates the forcing from its singular
branch and is aimed at proving its sign, not optimizing constants.

BranchSharp audit1 exit0: failure_small_branch proves Tq<1/6 on full
failure region, standard3. In w=Tq coordinates, exact boundary identity
BoundaryPolynomial audit1 exit0 gives
 (1−w)^2 R(h,9−w(1−w)/b,b/(1−w))=P(h,w),
 P=−7h/16+125h²/288+49h³/288+49h⁴/2592
 +w(4/9+37h/432−647h²/864−665h³/2592)
 +w²(−1/2+71h/108+17h²/81−7h³/324)
 +w³(−1/9+h/36+7h²/324).
This is a boundary identity only, NOT off-boundary forcing closure.
The original completed remainder sign is still open. Do not silently
replace R by P in the two-function trap: off-boundary drift sign needs proof.
Low-clock upper certificate normalization audit1 exit0, all negative
coefficients after h=(2/3)s/(1+s). Next use that identity to prove P<0
for 0<h≤2/3 with kinetic incidence; also attack completed remainder
on h≥2/3 using q≤(6/5)b from small-branch separation.

LowBoundary audit1 and LowCrossing audit1 exit0, standard3. New proved
sign: at y=0, 0<h≤2/3, full source cone and kinetic constraint imply
R<0 and Hy<0. Proof uses P≤pTail+w*pWUpper, an exact positive-remainder
identity, w≤18h²b, then a homogeneous all-negative clock polynomial.
No numeric evaluation used; all identities checked by Lean ring/field algebra.
ActualLowCrossing audit1 failed only on `(boundaryRatio ^ 2) x` versus
`boundaryRatio x ^ 2` (missing Pi.pow_apply); its source sign capstone
already passed standard3, derivative declaration carried sorryAx and the
failed olean was deleted. Audit2 applies Pi.pow_apply before normalization.
HighForcingTrial audit1 hit default200000 heartbeat in whnf. No limit
raised. This does not establish or refute the proposed high-clock box sign.
Box-certificate search partialfalse generation1226597, no model errors;
all returned candidates/source/ingredient sets inspected. Bernstein algebra
exists; no applicable forcing sign certificate found. Do not replace the
hard sign by a conditional final theorem.

ActualLowCrossing audit2 exit0: actual derivative and actual low-clock
zero-crossing sign standard3. ScaledForce audit1 exit0 proves unconditionally
 k(x)*R_actual(x) → −7/16.
The proof is exact polynomial first-order assembly from the corpus limits
h→0, V→9, q→1/12, kT→0, k(q−1/12)→−7/72. It introduces no source-sign
assumption. NormalizedDynamics audit2 exit0 (audit1 had redundant ring after
field_simp): E=y/T obeys E′=(k/u)(rate E+R), rate→54, and E≥−(3/(2u(1)²))²
on x≥1. Tail and full low-clock positivity audits next.

New hard-sign trial, based on low-clock certificate and small branch:
R<0 on the box 2/3≤h≤3/4, 0≤V≤9, b≤q≤(6/5)b. If proved, R=0 on the
failure region must have h>3/4, where q≤1/80 considerably simplifies
the completed forcing sign. This is a structural zero-set exclusion,
not a final bound objective. Trial not yet audited. Full completed
remainder high-clock sign still OPEN.

PositiveTail audit2 exit0; LowClockGlobal audit1 exit0. Main new actual
capstone: boundaryRatio_gt_quadratic_barrier_of_low_clock, standard3,
proves q−Tq²>b(h) for every actual x>0 with h≤2/3. PositiveTail audit1
was a parsing failure from unparenthesized squared argument; failed cache
deleted before audit2. The low-clock result is unconditional within its
stated domain. Whole-ray C72 and all later TT/RH targets remain open.
Nine production leaves have been prepared under ThetaCuspRatioQuadratic*;
serial final audits use lake --old env lean, beginning with Algebra.
Paper proof /tmp/tt-c72-low-clock-paper.md ready for P3 after production audit.

New structural high-clock proof mechanism (paper algebra, not yet audited):
put T=9−V, f=1−2Tq, m=−(4/3)h(3+h)(h−Tq),
E0=−7m/72−12Tq², L=qDerivativeRemainder, y=quadraticError.
The existing L simplifies exactly to
 L=−(7/162)h(3+h)[h−2Tq(1−Tq)]
      +4q(1−Tq)+f²q²*(2/3)(1+h/3)T.
For h≥3/4 and q≤(6/5)b≤1/80, failure y≤0 gives L<0 by
Tq(1−Tq)≤Tb and Tb≤3/32. This avoids expansion of the completed K.
At R=0, the verified f*Rq identity gives a second completion
 f*completedK = f²*M + L*(V*E0+6*f*A*y),
 M=m*Rh+12T*Rv+2q*A*E0.
The last bracket is nonnegative: C70 supplies y≥−Tq²; A≤(25/4)V,
f≤1, −m≥153/64, Tq²≤9/6400. Thus it is bounded below by
V[(7/72)(153/64)−(99/2)(9/6400)]>0 when V>0.
Writing mh=∂h m, mv=∂V m, exact cancellation yields
 M=m(f Dh−7qA/36+7Tq/18)+f*m*q²*Ah+(7/216)Vq*m*mh
   +12Tf*Dv+12Tf*q²*Av+(7/18)VTq*mv+24Tq²+24TqD.
Two displayed terms are nonpositive. On the same box use
f≥31/40, Dh≥7/12, A≤48, Av≤25/4, D≤1/30,
−m∈[153/64,13/4], −mh≤9, Dv≤19/25920.
The first term is ≤−(153/64)(161/480); all five positive upper
terms sum to less than 1/2. Hence M<0, so completedK<0.
These constants merely certify the sign; the research object is this
exact source-force cancellation. None of this high-clock sign is yet
kernel-verified. Mid-clock R-zero exclusion is also still required.

MidForcingTrial audit4 exit0, standard3. The mid-clock box has a positive
homogeneous certificate for −R: 2/3≤h<3/4, 0≤V<9, b≤q<(6/5)b.
Audits1–3 did NOT expose a negative coefficient or counterexample:
positivity did not recognize NNRat.rawCast. A tiny /tmp probe confirmed
that cause. Explicitly unfolding NNRat.rawCast/Nat.rawCast after raw-mode
normalization closed the proof without raising any limit. The rational
parameterization-to-box theorem /tmp/TTC72MidRegion.lean is now auditing,
followed serially by rebased ForcingDecomposition/CompletedForcing and
new HighBounds/HighCoefficients/SecondCompletion. No concurrent Lean build.
The actual low-clock production theorem already excludes y≤0 at h≤2/3;
therefore this new box sign should force h≥3/4 whenever actual y≤0,R=0.
The remaining mathematical work is the second-completion high-clock
sign and source/global propagation. Nine completed low-clock production
leaves are wired, indexed, imported-axiom audited; lint has seventeen
unrelated umbrella omissions, none in C72.

MidRegion pass2 exit0, standard3: full real box parameterization proved.
ForcingDecomposition and CompletedForcing rebase pass2 exit0, standard3;
now import production QuadraticBarrierAlgebra. Superseded low-clock
scratch sources/caches and failed full-box trial were cleaned after rebase.
HighBounds passes2–3 failed only tactic/elaboration details: redundant exact
after gcongr, nonpositive goal passed to positivity, and an all-numeric
calc RHS inferred as Nat (9*(1/80)=0). Use explicit ℝ on such calc RHS.
No mathematical bound failed. Pass4 active, then HighCoefficients,
SecondCompletion, HighMiddle, HighSign, serially. These high sign lemmas
remain unverified until successful terminal exits and axiom audit.

HighBounds, HighCoefficients, SecondCompletion, HighMiddle, HighSign pass5
all exited 0. The high-clock second completion and strict forcing sign are
kernel-proved, printed capstones standard3. Together with MidRegion pass2,
this closes the remaining polynomial obstruction. ForceChain pass1 exited0,
both composition/source derivative capstones standard3. Seam pass1–2 failed
only parsing (≤s notation consumed first letter of seamRatio), eta-expansion
of slope limits, and redundant ring after field_simp. ActualTrap and global
strict propagation scripts now written; serial audits in progress. These
source/global capstones remain unverified until their successful exits.

WHOLE-RAY BREAKTHROUGH: Seam, ActualTrap, Global, Strict pass3 all exited0.
Every printed capstone standard3. Actual-source theorem for every x>0:
q−(9−u²)q²>1/12−7/(72k), no source-sign/RH premise. The actual forcing trap
combines low-clock positivity, mid-clock exclusion, high-clock second
completion; positive seam and tail imply global nonnegativity by the
existing two-function trap. Strictness follows from negative second
derivative at a putative zero/global minimum. Fourteen production leaves
prepared; final direct lake --old env lean audits running serially.

Next hard conjecture C73: Does the full strict coarse source cone, strengthened
by t−h²t²>r*b(h), force the normalized third-slope numerator positive?
Corpus basis: C71 exact second jet and C72 actual nonlinear invariant.
This is a pointwise sufficiency conjecture, not an RH claim. Its boundary
has cancelled the C71 adverse second jet, so the next test is the third jet
of the exact nonlinear boundary, retaining full source-field conjugacy.
Search tt_c72_to_third_slope_search: partialfalse, gen1227432; coverage snapshot
older, semantic unmeasured, source-only candidates. Broad deep hits mostly
irrelevant, no sufficient theorem. Focused lexical scaledSlope search locates
InfinitySlope exact polynomial field and ActualSlopeTail capstone. C73
will derive its missing sign mechanism from those exact source polynomials.

C72 global nonlinear barrier COMPLETE: for every actual x>0, q−Tq²>b(1/k). Fourteen new production leaves passed final lake --old env lean; twenty imported capstones standard3; umbrella wired; index exit0; lint exit1 only seventeen unrelated umbrella omissions. Scratch sources/caches cleaned. Proof and audit: P3 tt-global-nonlinear-source-barrier. Next hard target C73 global third-slope sign under t−h²t²>rb(h), P1 tt-third-slope-nonlinear-cone. No RH/global-third-slope/fourth-gap closure claimed.
