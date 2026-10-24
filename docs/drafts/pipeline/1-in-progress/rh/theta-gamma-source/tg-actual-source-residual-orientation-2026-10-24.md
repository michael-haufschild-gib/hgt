# TG — actual source residual orientation

- **ID:** tg-actual-source-residual-orientation-2026-10-24
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `docs/reports/rh-current-frontier-map.md`, route TG;
  `docs/reports/rh-killed-routes.md`; current Lean sources.
- **Goal:** unconditional Lean proof of RH through the actual Euler/Gaussian
  source, positive-residual cubic transgression, and integer trace below one.

## Completion requirements

1. Construct the residual from the original arithmetic source, retaining
   normalization, both reflection directions, proper prime powers, Gamma and
   polar terms, and every mixed matrix term.
2. Prove the actual chain/area identity
   `E_base = E_residual + Tr T_D`, with `E_residual ≥ 0`, on every admissible
   strict-right contour. An assumed chain or assumed sign does not discharge it.
3. Apply the existing sub-unit base cap and integer multiplicity identity to
   exclude every strict-right zero, then obtain `RiemannHypothesis`.
4. Direct Lean checks, transitive `#print axioms` audit, umbrella wiring, no
   placeholders, added analytic assumptions, computations, or limit overrides.

The alternative TG producer is an exponent-zero upper bound for the literal
central Gaussian prime-minus-continuum gap. Existing equivalences are receivers,
not candidate new results. No stronger constant, new receiver, regularity-only
classification, or abstract obstruction counts as closing the requested gap.

## Current source audit

- `FormationAnchoredCubicSpecialization`: anchored trace is actual enclosed
  Xi multiplicity; positive-anchor continuity and exact cubic channels exist.
- `BurnolBaseGraphCapArea`: actual graph-cap area lies strictly below the
  actual all-prime cubic source budget, which lies below one.
- `BurnolBaseCapPrincipalLift`: no-bubbling theorem has two unproved-for-TG
  inputs: the residual chain relation and nonnegative residual area.
- `SoninPrimePolarJetLcmCovariance`: exact finite signed covariance keeps
  complete high-LCM fibres, both prime/polar cross terms and terminal square.
  It supplies no infinite arithmetic energy bound.
- Earlier native first-jet/ordinate regularity classification explicitly
  distinguishes bounded ordinate modulation from actual Gaussian amplitude
  damping. It does not identify the needed residual filling.

## Conjecture loop

### C1 — arithmetic residual filling

Construct the actual completed Euler/Gaussian family as a filling of the same
determinant-line boundary as the Burnol cap, with nonnegative signed residual
area and integer defect equal to the literal contour multiplicity.

**[OPEN CORE]:** source-preserving filling construction and its signed area.
Boundary holonomy equality alone determines area only modulo integers. The
normalization by the complete source in its logarithmic derivative cannot be
dropped or replaced by the square-summable column covariance.

### C2 — direct central Gaussian source cancellation

For the literal functions in `GaussianCentralGapExplicitCriterion`, prove
`P(y) - C(y) ≤ -1/10 + 32 sqrt(y)` for every `0 < y ≤ 1` directly from arithmetic.
This is the existing TG target, not a new criterion. Investigate the exact
von Mangoldt divisor convolution before estimating its inverse; retain the
polar continuum and endpoint terms throughout.

**[OPEN CORE]:** one-sided bound uniform as `y → 0`. Positive-damping
summability, compact-away-from-zero estimates and a zero-side expansion do
not prove it.

### Exact paper calculation for C2: keep the continuum through inversion

For `y>0`, put `f_y(x)=x^(-1/2) exp(-y x²)` on `x≥1`,
`D(y)=P(y)-C(y)`, and `H_N=Σ_(1≤k≤N) 1/k`. The literal divisor identity
`Σ_(d|n) Λ(d)=log n` gives

```
Σ_(m≥1) m^(-1/2) D(m²y)
  = Σ_(n≥1) log(n) f_y(n) - ∫_1^∞ H_floor(x) f_y(x) dx
  =: R(y).
```

The continuum term is essential: changing variables gives
`m^(-1/2) C(m²y)=(1/m)∫_m^∞ f_y(x) dx`, so its sum is the
harmonic-number integral, not the logarithmic integral. All rearrangements
are absolutely convergent for fixed positive `y`: regrouping the prime
double sum gives `Σ log(n)f_y(n)`, and `H_floor(x)≤1+log x` controls the
continuum. These bounds justify the subtraction only after both sums have
been evaluated.

The cumulative forcing has the elementary exact form

```
A(x) = log(floor(x)!) - x H_floor(x) + floor(x),   x≥1.
R(y) = -∫_1^∞ A(x) f_y'(x) dx < 0.
```

Proof of the sign: `A(1)=0`, and at every integer `N≥2`,
`A(N)-A(N-1)=log N-H_(N-1)<0`, by integrating `1/t` over
the unit intervals from `1` to `N`. On `[N,N+1)`,
`A(x)=A(N)-(x-N)H_N`. Thus `A(x)<0` for every `x>1`.
Integration by parts is justified by `A(x)=O(x log x)` and Gaussian
decay; its lower boundary vanishes. Since `f_y'<0`, the sign follows.

This is a sign of the **dilation average**, not a sign of `D`. Exact
Möbius inversion is

```
D(y) = Σ_(m≥1) μ(m)m^(-1/2) R(m²y).
```

For fixed `y`, the double absolute sum is bounded by a Gaussian series
with divisor multiplicities, so the divisor regrouping is legitimate.
At the cumulative-measure level the same inversion is precisely

```
Σ_(m≤x) μ(m) A(x/m) = ψ(x) - x + 1.
```

Indeed the atomic term is `Λ=μ*log`; the continuous density is
`Σ_(m≤x) μ(m)H_floor(x/m)/m = Σ_(k≤x)(Σ_(m|k) μ(m))/k = 1`.
Consequently the forcing sign alone has not paid the original arithmetic
error. No bound for its signed inverse is claimed.

This paper calculation is an intermediate identity, not a qualifying
solution, new RH criterion, or no-go. It is not recorded as a formalized
theorem or as frontier movement.

### C3 — preserve the source sign under literal finite Euler inversion

Let `Q` be the product of a finite set of distinct primes and define
`R_Q(y)=Σ_(d|Q) μ(d)d^(-1/2) R(d²y)`. Investigate a source-derived
upper bound uniform jointly in `Q` and small positive `y`, before passing
to the cofinal inverse. The exact insertion is

```
R_(Qp)(y)=R_Q(y)-p^(-1/2)R_Q(p²y),  p∤Q.
```

The concrete sign-preservation candidate is `R_Q(y)≤0` for every finite
prime set and `y>0`. This is an unproved, potentially stronger source
conjecture, not an accepted substitute for C2. Its base `Q=1` is the paper
calculation above; its insertion step requires an actual two-scale
comparison. A negative summand does not establish that comparison.

The complete coefficient calculation also gives
`R_Q(y)=Σ_((m,Q)=1) m^(-1/2)D(m²y)`. For fixed `y>0`, these sums tend to
`D(y)` along prime exhaustion. To justify all fixed-`y` rearrangements,
the elementary bounds `P(t)≤Σ_n n exp(-tn)` and
`C(t)≤exp(-t)/t` give `|D(t)|≤K_y exp(-t)` for `t≥y`.
The double dilation sum is then bounded by
`K_y Σ_k d(k)k^(-1/2)exp(-yk²)`, which converges since `d(k)≤k`.
No uniform domination as `y→0` follows from this argument.
Thus assuming every finite-stage sign would already supply the desired
all-`y` sign after the limit; it is the missing estimate, not a new known
input. No such assumption is added to Lean.

Corpus audit: `MonotoneMobiusPositivity` concerns the different operator
`Σ μ(k)k^(-2)g(u/k)` with a nonnegative monotone density. It does not
apply to `Σ μ(k)k^(-1/2)R(k²y)`. The exact prime-density inversion module
retains those different weights and hypotheses. Likewise, positivity of
prime-deleted theta atoms does not identify the present completed
prime-minus-continuum source. No transfer between them has been proved.
`ThetaMovingCuspTotientReconstruction` makes the reflected issue explicit:
its actual reflected coefficients are
`A_S(m)=∏_(p∈S,p|m)(1-p)`, not positive prime-deletion coefficients.
Its positive totient reconstruction does not sign the original reflected
source. These are source-inspected existing facts, not new results here.

**Next proof obligation:** prove or disprove the actual two-scale
comparison for `R_Q`, retaining its harmonic continuum and moving prime
set. If it does not hold, return to signed inverse cancellation; do not
weaken the ultimate TG target or add the comparison as an assumption.

## Status

RH unproved. Neither C1 nor C2 has a complete paper proof. The continuum
prime-tower bridge below is proved and kernel-audited; the aggregate signed
payment needed by TG is still open. External searches and novelty checks excluded by user instruction.
Existing unrelated worktree changes preserved.

## Formalization requested

User subsequently requested formalization of noteworthy paper proofs.
The initial candidate was the unconditional strict negative sign of the
literal dilation average, its exact von Mangoldt/continuum identity, and
the proved inversion identities. The user's subsequent clarification
requires a theorem or premise discharge that significantly advances a
hard TG obstacle. The averaged-sign calculation alone does not meet
that requirement. No repository Lean module has been added for it.
It remains a proved-on-paper intermediate calculation; the missing
signed inverse comparison remains the target. No unproved C2/C3 sign
will be introduced as an input.

For the sign, a shorter dependency-closed proof avoids Stieltjes calculus:
on every cell `[n,n+1]`, `∫ f_y ≥ f_y(n+1)`, while
`H_n ≥ log(n+1)`. Summing gives the desired comparison between the
harmonic continuum and the logarithmic lattice. The first cell is strict
since `log 2 < H_1 = 1` and `f_y(2)>0`. Gaussian/geometric majorants
prove every series summable before passage to the limit.

An API-only scratch probe was run while considering this formalization;
some exploratory names were absent. It proved no mathematical statement
and is not a certificate. Do not count it as progress on TG.

## Verification

`lake --old env lean /tmp/hgt_tg_actual_source_audit_20261024.lean`
passed. The four existing endpoints
`burnolBaseCapArea_lt_one`, `cubicArithmeticRectangleSource_winding`,
`exists_faithful_arithmetic_rectangle_cubic`, and
`riemannHypothesis_iff_gaussianCentralGap_le_explicit` depend only on
`propext`, `Classical.choice`, and `Quot.sound`. This audits existing
compiled endpoints; it is not verification of a new closing theorem.

## Further source inspection after the significance clarification

The cubic aperture-gauged continuum construction is already certified in
`HTGeometry.CubicApertureGaugedSynthesis` and `CubicApertureGradedCarrier`.
Its card explicitly leaves the coefficient-native cyclic boundary map and
the trace comparison open. Separate nuclearity of both source legs is not
a proof of the sign of their difference. Re-formalizing this construction
would not discharge C1.

`XiGaussianAnnihilatorPrimeCancellation` identifies the complete signed
prime--Gamma--polar residual with the polynomial Gaussian zero trace.
Its absolute bound uses `xiGaussianNativeEnergy`, and its annihilating
polynomials are indexed by finite sets of `XiZeroCopy`. Neither statement
proves nonnegative residual area or the central Gaussian bound C2.

`XiWardCubicPositiveShiftArithmeticCovariance` identifies the literal
pole--Gamma--von-Mangoldt difference quotient in the absolute-Euler
chamber and continues its multiplicity residues. This establishes source
provenance, but supplies no sub-unit trace estimate.
`XiWardCubicReflectionAbsorptionCompletePositivity` proves positivity
with denominator `(w_i-1/2)+conj(w_j-1/2)`; its unshifted kernel has a
different denominator. The shifted theorem cannot discharge the required
unshifted comparison.

The older prospective identity `SoninSemilocalFluxNormalization` is already
refuted by `SoninSemilocalTraceObstruction.not_soninSemilocalFluxNormalization`.
It is not a live premise to discharge. No new obstruction is claimed here.

The completed-source Suzuki first-variation paper was also inspected.
It concerns recovery of the complete Weil form from a critical source
limit, and explicitly does not prove its positivity. No connection from
that limit to C1's residual filling has been proved here.

**Outcome:** no qualifying new theorem or premise discharge. C1, C2, and
C3 remain open. No new Lean module, conditional substitute, or frontier
advancement is recorded. The exploratory API scratch and the completed
endpoint-audit scratch were removed after their results were recorded.

## Cross-programme conjecture loop

The fourteen programmes named by the user were inspected, with direct source
checks for the AOT tower statements, AIP continuum crossing bridge, SAEI path
certificate, ACT theta source equations, and ACCC compensation coordinates.
The useful combination is ACT's actual signed theta supersolution, AIP's
crossing-to-ratio bridge, SAEI's shared-edge packing, and ACCC's instruction
to retain prime--polar cancellation before taking norms. TTPC's averaged
close-pair localization does not give TG's every-contour estimate.

### C4 — actual continuum path payment

The target is payment of the reflected difference energy of the literal
shifted theta gauge by its complete same-side energy and source term, with
all cutoffs admitted and no assumed allocation certificate. The signed
two-sided supersolution is already explicit. The unpaid theorem is the
construction and estimate of shared path weights, including the Gamma and
polar terms. No path certificate is introduced as a hypothesis.

**Attempt 1: transfer lattice tower positivity.** The source theorem
`towerTotalOddForm_ge_half_towerArchDiagForm` retains a signed Toeplitz
correlation. It is not full positivity for arbitrary-sign profiles.
Moreover the continuum reflection exchanges different logarithmic fibres;
it does not remain the single lattice Mellin square.

**Attempt 2: pay continuum atoms by pointwise archimedean coefficients.**
This does not prove a form comparison. Prime crossings are supported on
lines in the two-variable plane; the archimedean part is a continuous
measure. A valid comparison needs integration through intermediate points
and a total edge-use bound. Sampling inequalities cannot be passed to the
continuum while ignoring these measures.

**Attempt 3: nearest-ratio routing.** For a crossing `x+y=log n`, the
candidate same-side modulus is near `n exp(-2x)`. Its individual critical
weight is larger by roughly `exp(x)`, but compressing the prime scale
loads roughly `exp(2x)` crossings onto each output scale. The individual
weight comparison is therefore not a packing proof. These factors are a
heuristic diagnostic, not a proved asymptotic statement. The polar term
must remain in the aggregate comparison.

### Paper bridge: the complete continuum tower has a positive decomposition

Let `F` be a real continuous compactly supported function on `(0,infinity)`,
extended by zero, `L>0`, and `0<r<1`. Define

```
M = integral_(0,infinity) F(x)^2 dx,
R = sum_(k>=1) r^k integral_(0,infinity) F(x) F(x+kL) dx,
H = sum_(k>=1) r^k integral_(0,kL) F(x) F(kL-x) dx,
U_j(theta) = sum_(i>=j) r^(i-j) F(theta+iL),  0<theta<L.
```

All sums are finite, uniformly in the integration variables, by compact
support. With all norms below on `(0,L)`,

```
M + 2R - H = (1-r) ||U_0||^2
  + (r/2) ||U_0 - U_0(L-.)||^2
  + (1-r^2) sum_(j>=1) ||U_j||^2 >= 0.
```

**Dependency-closed paper proof.** Partition the half-line into cells
`x=theta+iL`. The scalar finite KMS identity applied to
`u_i=F(theta+iL)` gives
`M+2R=||U_0||^2+(1-r^2)sum_(j>=1)||U_j||^2` after integration.
In the reflected term set `k=i+j+1` and
`kL-x=(L-theta)+jL`; finite reindexing gives
`H=r integral_0^L U_0(theta)U_0(L-theta) dtheta`.
Reflection preserves the integral of `U_0^2`, so expanding the reflection
difference square gives the displayed identity. The coefficients are
nonnegative. At `L=log p`, `r=p^(-1/2)`, multiplication by `log p` gives
the full prime-power tower, with both correlations retained.

**Status and limit.** This is a source-coordinate bridge, not a new RH
criterion or an all-prime estimate. Its diagonal payment `M` is charged
once per prime, so this proof alone does not give the required aggregate
bound. The exact result is formalized in
`ArithmeticOrientationTheory.ContinuumTowerReflectionCholesky`, with a
separate equality to the literal von Mangoldt tower and its unconditional
compensated positivity theorem. The source-copy check and transitive axiom
audit passed; only `propext`, `Classical.choice`, and `Quot.sound` occur.
The final direct source check passed without warnings. Its paper proof and certificate
are recorded in `3-formalized/continuum-prime-tower-reflection-cholesky.md`.
The next construction must retain
the reflected fibre term and pay the shared diagonal from the complete
source; merely summing the nonnegative tower identities would not do so.

The finite KMS mechanism was already known internally. The proved addition
is the continuum identification, not a new bound for the complete Weil form.
Do not count a routine all-L2 extension, a separate Laplace-column admission
lemma, or a per-prime constant improvement as the next significant TG step.
The next loop must use the complete signed source to prove joint payment or
construct the actual residual transgression. C1 and C4 remain the open cores.

## Further conjectures: Gaussian correlation and finite Euler deletion

### C5 — Gaussian divisibility correlation

For `sigma>0` and `y>0`, put
`Z_sigma(y)=sum_(n>=1) n^(-sigma) exp(-y n^2)`. The candidate

```
Z_sigma(y) Z_sigma(a^2 b^2 y)
  <= Z_sigma(a^2 y) Z_sigma(b^2 y),  a,b>=1,
```

would give nonpositive covariance of the two divisibility indicators for
coprime natural `a,b` under the literal normalized Gaussian integer measure.
Indeed the masses of the divisibility events are
`a^(-sigma) Z_sigma(a^2 y)/Z_sigma(y)` and the corresponding expressions
for `b` and `ab`. No independence assumption is used in this calculation.

A sufficient assertion is concavity of `t -> log Z_sigma(exp t)`.
Differentiating the absolutely convergent Gaussian series shows that its
second derivative is

```
y^2 Var_y(n^2) - y E_y(n^2).
```

The different theta kernel cannot be substituted directly. A positive
integral representation now supplies the missing mathematical connection:
with `alpha=sigma/2`,

```
Z_sigma(pi exp(2t)) = pi^alpha/Gamma(alpha+1) exp((sigma-1/2)t)
  * integral_0^infinity K_sigma(w) Theta(t+w) dw,
K_sigma(w) = exp(w/2) integral_0^w (exp(2r)-1)^alpha exp(-r) dr.
```

The causal kernel is a convolution of two functions satisfying the
multiplicative four-point inequality. The exponential-increment factor
has four-point difference
`exp(2x)(exp(2a)-1)(exp(2b)-1)>=0`. Integral composition preserves the
inequality by the two-by-two determinant identity. The actual theta
log-concavity therefore proves C5 for every `sigma>=0`.

The dependency-closed paper proof is in
`3-formalized/gaussian-integer-divisibility-negative-correlation.md`.
The literal Gaussian four-point law, coprime divisibility covariance,
and finite-product divisibility bound are Lean-checked. Their transitive
axiom audit contains only `propext`, `Classical.choice`, and `Quot.sound`.

**[OPEN CORE]:** transfer from this proved real Gaussian covariance sign
to the complete prime--Gamma--polar residual. Nonpositive coprime
covariances do not by themselves dominate an arbitrary signed matrix,
or preserve the sign under all Euler deletions. C1--C4 remain open.
No C5 or TG sign assumption has been added to Lean.

### C6 — the exact positive measures left by finite Euler deletion

Let `Q` be squarefree, with selected prime set `S`. The same finite Euler
inverse used in C3 has the exact representation

```
R_Q(y) = sum_(n>=1) b_Q(n) f_y(n)
           - integral_1^infinity H_Q(x) f_y(x) dx,
H_Q(x) = sum_(m<=x, gcd(m,Q)=1) 1/m,
b_Q(n) = sum_(d|gcd(n,Q)) mu(d) log(n/d).
```

Both measures in this difference are nonnegative. More precisely, if
`J={p in S : p divides n}`, then

```
b_Q(n) = log n,    if J is empty;
b_Q(n) = log p,    if J={p};
b_Q(n) = 0,        if card J>=2.
```

**Paper proof.** For the continuum, change variables in each of the
finitely many dilation integrals. Its density becomes
`sum_(d|Q,d<=x) mu(d) H_floor(x/d)/d`. Writing `m=dk` gives
`sum_(m<=x) (1/m) sum_(d|gcd(m,Q)) mu(d)`, which is `H_Q(x)`.
For the atoms the same reindexing gives the displayed definition of
`b_Q`. Expand `log(n/d)=log n-sum_(p|d) log p`. The coefficient of
`log n` is `(1-1)^(card J)`; the coefficient attached to each fixed
`p in J` is `(1-1)^(card J-1)`. This gives all three cases, including
the empty set separately. Fixed positive `y` supplies the Gaussian
absolute convergence already justified above.

This isolates actual joint divisibility incidence, rather than replacing
the source by independent prime variables. It does **not** compare the
atomic and continuous measures. A pointwise comparison of their cumulative
masses cannot be assumed: when `Q` contains every prime at most `x`, that
comparison is exactly the sign of `psi(x)-x+1`.

**Next exact conjecture:** compare the displayed atomic and continuous
measures on the Gaussian tests themselves, uniformly over the selected
prime set. A proof must use their common integer source and keep the
one-selected-prime atoms; discarding them changes `R_Q`. C6 is a proved
paper identity, not a qualifying TG sign discharge. It is not promoted to
a formalized card or a new positivity criterion.

## Log

- 2026-10-24 — Read attached task and TG ledger; inspected actual source
  statements and previous TG attempts. Began direct source-comparison and
  Gaussian divisor-convolution investigation.
