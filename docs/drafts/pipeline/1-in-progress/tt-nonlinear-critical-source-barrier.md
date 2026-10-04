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
