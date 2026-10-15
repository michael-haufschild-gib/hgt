# Route RN: full-divisor orientation from renewal boundary charge

Status: IN PROGRESS. RH is not proved.

## Fixed objective

Orient the complete Xi divisor through the physical renewal boundary charge;
obtain an unconditional Lean proof of RH. No self-adjoint eigenvalue detour.
Use current Lean sources and corpus research; no numerical experiments or
external novelty claims. Existing unrelated working-tree changes are outside scope.

## Plan

1. Audit exact renewal and full-divisor interfaces in current Lean.
2. State and attack source-level orientation conjectures, retaining the full divisor.
3. Close a paper proof before formalization; record failures and positive survivors.
4. Audit changed modules with foreground `lake env lean`, wire imports, run formal lint.
5. Continue until unconditional RH is verified; partial identities do not complete goal.

## Evidence, 2026-10-15

- `ThetaRenewalFeedbackLoop.lean`: A=(1/4+lambda)D(lambda),
  B=(1/4-lambda)D(-lambda), Xi(2 i lambda)=A+B. A and B are
  nonzero in the critical strip. Boundary charge Im A(iy)>0 for y>0.
- Same module: loop gain on the right of the axis takes both orientations;
  Pick kernel has arbitrarily large positive and negative definite packets.
- `ThetaRenewalNuclearBoundary.lean`: on positive simple critical ordinates,
  d=-X'/v is absolutely summable and has infinitely many entries of each sign.
- `ThetaSeamCouplingFamily.lean` and `ThetaSeamCouplingContacts.lean`:
  positive scaled renewal inputs retain causal denominator nonvanishing but
  acquire nonreal zeros; physical seam matching is essential.
- `ThetaRenewalPhaseLevel.lean`: full strip zero equation is the single
  probability-phase level Phi=pi/2 in the positive-frequency half-strip.
- Corpus search ran successfully. Index has source coverage but many pending or
  stale compiler records; search hits require direct source and Lean verification.
- Serena symbol retrieval rejects Lean paths as ignored; use source reads and
  corpus symbol search instead. No update_plan tool is available in this session.

## First attack

Universal positivity of the raw renewal Pick boundary values is FALSE, already
disproved by current Lean. This is not a new result and does not retire RN.
Positive survivor already formalized: signed trace-class boundary charge.
Hard task remains to extract a divisor orientation that retains, rather than
discards, its alternating signs and the exact physical seam.

## Open core

Prove that the physical, two-ended renewal channels cannot cancel off axis.
Positivity of either causal channel alone and a positive renewal input do not
prove this. Investigate a nonlinear charge identity involving both channels,
with source-level proof and no RH-equivalent premise.

## Cycle 2: analytic extension of the physical charge

Conjecture: C(lambda)=(A(lambda)-B(lambda))/(2i) has strictly positive
real part throughout |Re lambda|<1/4, Im lambda>0, and division by C
preserves the full local divisor of Xi(2i lambda), including multiplicities.
Verdict: BRIDGE. This does not orient the divisor or prove RH. Exhaustive
source-reference search of thetaLoopA/B/Charge found no existing extension.
No external novelty assessment is claimed, per the user restriction.

Dependency-closed paper proof: write lambda=x+iy and a=1/4. The existing
quadrant theorem gives Re D(lambda)>0, Im D(lambda)>0,
Re D(-lambda)>0 and Im D(-lambda)<0. Consequently
Im A=(a+x)Im D(lambda)+y Re D(lambda)>0 and
Im B=(a-x)Im D(-lambda)-y Re D(-lambda)<0.
Thus Re C=(Im A-Im B)/2>0. A and B are entire, so C is entire;
on this domain C is an analytic unit. The quotient F/C, F=Xi(2i lambda),
is analytic there and its analytic order is ord(F)+ord(1/C)=ord(F).
At lambda=iy, B=conj A gives C(iy)=v(y), so the normalization is
exactly the existing physical boundary charge, not a freely chosen gauge.
Its boundary quotient is X(y)/v(y); at every simple critical zero its
derivative is X'(y)/v(y)=-d(y). Alternating crossing signs therefore remain.

Next hard conjecture under attack: source renewal might force positivity
of a *two-channel* current after this analytic normalization. It cannot
force positive raw crossing slopes. Any claimed current positivity must
be derived from the physical source and checked against seam-coupling
counterexamples, not introduced as a hypothesis.

## Cycle 3: direct two-channel nodal separation

Let G=|A|^2-|B|^2 and H=Im(A conjugate(B)). Algebra gives

  Xi(2i lambda)/C(lambda) = (4 H + 2i G)/|A-B|^2.

Since C is a source-proved unit on the upper strip, the full Xi divisor is
exactly the simultaneous zero set G=H=0, retaining analytic multiplicity
through the complex quotient. The source quadrant inequalities remove the
extraneous constructive channel A=B: the real-product branch at a joint
node must be A=-B.

The desired source theorem is that G and H have no common zero for
0<Re lambda<1/4, Im lambda>0. This is a precise RN target, not a proved
theorem or a permitted premise. Its reformulation alone is BRIDGE.

Attacks on stronger shortcuts:
- G has one sign: FALSE by existing `exists_loop_gain_gt_one` and
  `exists_loop_gain_lt_one`. Keep the two-channel nodal problem.
- Positive real-rate mixture for the odd renewal kernel: FALSE by
  `not_exists_complexLaplaceMeasure_thetaRenewalOddKernel` in
  `ThetaRenewalPhaseKernelNotMonotone.lean`, even allowing bounded complex
  densities with finite weighted variation. Positive survivor already in
  the corpus is the actual renewal/complex resonance representation.
- Positivity of transverse Xi energy from divisor locations: CIRCULAR as
  a proposed source proof; the corpus's theorem explicitly consumes a
  zero-half-plane bound. Need a renewal derivation, not that premise.
- Positivity of the *normalized* energy everywhere cannot be adopted
  without checking the seam: C is odd and vanishes at zero while Xi(0)>0.
  F/C introduces a seam pole outside the open upper domain. A claim about
  global normalized-energy monotonicity would have to handle that pole.

Next calculation: derive G and H from the actual renewal Laplace input,
preserving signed oscillatory cross terms and the exact physical seam.
Do not replace this with a new name for RH or an assumed positive current.

## Source correlation calculation (paper, not yet Lean)

Write lambda=x+iy, a=1/4, c=Theta(1), nu=thetaRenewalIncrement.
All integrals below converge absolutely, including their products, by the
existing all-exponential-moment bounds for nu. Thus Fubini and interchange
of t,u apply. Set Z=D(lambda) conjugate(D(-lambda))=R+iT. Direct expansion
of D=c-N and symmetrization in t,u give

  R = c^2 - 2c integral nu(t) cosh(xt) cos(yt) dt
      + double-integral nu(t)nu(u) cosh(x(t-u)) cos(y(t+u)) dt du,
  T = 2c integral nu(t) cosh(xt) sin(yt) dt
      - double-integral nu(t)nu(u) cosh(x(t-u)) sin(y(t+u)) dt du.

Here all time variables range over (0,infinity). The exact cross flux is

  H = (a^2-x^2-y^2) T + 2ay R.

Put Mplus=|D(lambda)|^2 and Mminus=|D(-lambda)|^2. Then

  G = (a^2+x^2+y^2)(Mplus-Mminus) + 2ax(Mplus+Mminus),
  Mplus-Mminus = 4c integral nu(t)sinh(xt)cos(yt) dt
      - 2 double-integral nu(t)nu(u)sinh(x(t+u))cos(y(t-u)) dt du,
  Mplus+Mminus = 2c^2 - 4c integral nu(t)cosh(xt)cos(yt) dt
      + 2 double-integral nu(t)nu(u)cosh(x(t+u))cos(y(t-u)) dt du.

This exposes the precise unresolved coupling: cross flux samples sum-time
oscillations, while imbalance samples difference-time oscillations. Both
must retain the linear seam term and the quadratic renewal correlation.
Taking absolute values discards the correlation needed to distinguish
joint nodes. No sign or nodal-separation proof has been obtained.

Additional attack checked in current Lean:
`compact_critical_strip_zero_engineering` preserves positivity, strong
log-concavity, every chosen finite set of moments, critical source charge,
and all finite prime-deletion positivity while forcing a nonreal strip
zero. Thus these source summaries cannot discharge the joint-node theorem.
This is an existing corpus obstruction, not new scientific knowledge.

## Verification so far

- New module: `formal/GaloisForLFunctions/RHTower/ThetaRenewalFullDivisorCharge.lean`.
- `lake --old env lean GaloisForLFunctions/RHTower/ThetaRenewalFullDivisorCharge.lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/ThetaRenewalFullDivisorCharge.olean`
  passed, exit 0, no warnings after import minimization.
- Imported from the RHTower umbrella; no umbrella/full build run.
- `git diff --check` passed.
- `scripts/formal_tools.py lint` failed on five unrelated concurrent modules:
  EvenSectorAbelAveraging, EvenSectorAbelLaplace, EvenSectorAbelPinning,
  EvenSectorAbelRigidity, EvenSectorFarBumpPoleFreeCombination.
  All five errors were missing umbrella reachability. They were not edited.
- Full axiom audit of all 19 new definitions/theorems passed via a `/tmp`
  scratch file and `lake --old env lean`. Every declaration depends only
  on `propext`, `Classical.choice`, and `Quot.sound`; no added axioms or
  `sorryAx`. Temporary API, audit and search files were removed afterward.

## Honest scope audit

The charge extension, divisor preservation and joint-node characterization
are verified bridges. They are not RH, a new orientation law, or evidence
of novelty beyond the corpus/literature. The exact physical-source sign
problem remains open. No work was declined because of duration or effort;
the next cycle must attack the sum-time/difference-time renewal correlation
itself, with the theta arithmetic intact. Do not start another scalar
positivity reformulation or change route.

## RN continuation: source audit and level-flow falsification

Route and goal remain unchanged. No unconditional exclusion of an off-axis
joint node has been obtained in this cycle.

The current Lean source audit found stronger existing obstacles than the
initial positive-charge calculation alone records:

- `ThetaCuspChargeRenewalIncrement.thetaGroup_modular_criticality_full`:
  exactly modular deformations can retain positive source and positive
  renewal increment and still have off-axis zeros.
- `ThetaGroupDeformationPrimeTwo.thetaGroupDeformation_primeTwo_iff`:
  the exact prime-two identity selects the undeformed theta function in
  that family. Generic modularity therefore cannot replace the original
  arithmetic source.
- `ThetaReflectionPreservingZeroSurgery`: positive renewal mass, exact
  reflection, all universal even renewal seam jets, any prescribed finite
  set of literal seam jets, and positivity after every finite prime deletion
  are compatible with planted off-axis zeros. These hypotheses do not
  supply the missing orientation law.
- `ThetaCuspWignerProductFiberNormalForm` and
  `ThetaCuspCompletedProductFiberWignerNoGo`: the exact product-fiber
  decomposition already exists; individual fibers can have the wrong
  Fourier sign. Recreating this decomposition is not a new result.
- `ThetaRiccatiGaussianCountermodel` and
  `ThetaRiccatiThreeChargeCountermodel`: the global reflected Riccati
  inequalities and the literal mass/reflected charges do not suffice.

Research searches were checked against source statements. Some returned
partial results or stale/source-only compiler coverage; no absence or
applicability claim is inferred merely from their ranking. External search
and numerical experiments were not used.

### Candidate attacked: inward negative-level motion forces axis landing

This candidate was considered as a way to follow the known subcritical
coupling zeros back to the physical coupling. It is false as a general
analytic principle, even when every negative real level has the favorable
logarithmic slope in the right upper quadrant.

Here is the exact paper counterexample, with no numerical experiment.
For arbitrary `a,b > 0`, put

```
P(z) = (z² - (a²-b²))² + 4a²b²,
P'(z) = 4z(z²-(a²-b²)).
```

It has an off-axis zero at `a+ib`. For `z=x+iy`, `x,y>0`,

```
Im P(z) = 4xy (x²-y²-(a²-b²)).
```

Thus its entire real-level locus in this quadrant is the hyperbola
`x²-y²=a²-b²`. On that hyperbola,

```
Re P(z)  = -4(x²-a²)(x²+b²),
Re P'(z) = -8xy².
```

Every negative real level consequently has `Re(P'/P)>0`. Nevertheless,
the negative-level branch lands at `a+ib`, not on the imaginary axis.
Explicitly, at level `P=-t`, `t>0`,

```
x(t)² = (a²-b² + sqrt((a²+b²)²+t))/2,
y(t)² = (b²-a² + sqrt((a²+b²)²+t))/2.
```

Both coordinates decrease as `t` decreases to zero and tend to `a,b`.
The sharp positive survivor is the exact inverse-flow law

```
Re(P/P') = (x²-a²)(x²+b²) / (2x(x²+y²)).
```

It measures approach to the displaced endpoint. The ratio of this
quantity to `x-a` tends to one at the endpoint; its ratio to `x` tends
to zero. A favorable slope sign therefore provides no positive lower
bound on distance transported toward the critical axis.

This is an elementary falsifier of a proposed inference, not a theta
counterexample, a new scientific novelty claim, or a retirement of RN.
The surviving problem is still to derive an axis-landing or nodal
separation law from the literal renewal source, keeping its arithmetic
correlations. Assuming such a law would merely restate the obstacle.

### Formal status of the level-flow falsifier

The algebraic classification, root, actual complex derivative, positive
logarithmic slope on every negative level, and exact inverse-flow identity
are formalized in
`formal/GaloisForLFunctions/RHTower/ThetaRenewalLevelFlowObstruction.lean`.
The explicit square-root parametrization and its endpoint limits above
are paper calculations, not claims about additional Lean declarations.

The new module passed the required foreground
`lake --old env lean GaloisForLFunctions/RHTower/ThetaRenewalLevelFlowObstruction.lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/ThetaRenewalLevelFlowObstruction.olean`
audit with exit 0 and no warnings. Its import was added to the umbrella;
no umbrella/full build was run. `git diff --check` passed.

The current full formal lint run failed on two unrelated concurrent
modules missing umbrella reachability: `EvenSectorNegPartAbelRigidity`
and `ParitySectorJointRigidity`. Neither was edited by this RN cycle.

Anti-theatre audit: the falsifier is elementary, not new scientific
knowledge or a theta-specific orientation theorem. No RH progress is
claimed from adding its formal file. It prevents one invalid step in the
fixed route. The hard physical-source joint-node exclusion is unresolved.

All 10 declarations in the new module passed a separate `/tmp` axiom
audit using `lake --old env lean`: only `propext`, `Classical.choice`,
and `Quot.sound`; no `sorryAx` or custom axioms. Temporary search JSON,
scratch proofs, axiom audit, and lint log were removed after recording
their results. No numerical experiment, commit, or push was performed.

## RN continuation: a global coordinate from the literal exit law

The preceding cycle counts as verified progress in rejecting an invalid
inference, not as a theta-specific zero exclusion. The raw two-port Pick
kernel has infinite index of both signs, so it cannot be the positive
conservation form sought for the full divisor.

### Exact conjecture and paper proof

The literal full charge has no folds on the entire closed critical strip.
More precisely, write `a=1/4`, `c=Theta(1)`, `q=thetaRenewalMass`, and
`g=thetaRenewalExitDensity`. The existing source theorems give

```
g(t)>0, integral g=1, integral t*g(t)=q/a, 0<q<1,
A(lambda)=c*lambda + a*c*integral exp(-(a+lambda)*t)*g(t).
```

If `Re s, Re r >= 0`, integration of the derivative of the exponential
along the straight segment gives
`|exp(-s*t)-exp(-r*t)| <= t*|s-r|` for `t>=0`. The exit law's finite
first moment justifies integration and yields

```
|A(lambda)-A(mu)-c*(lambda-mu)| <= c*q*|lambda-mu|
```

throughout `Re lambda, Re mu >= -a`. Set
`C(lambda)=(A(lambda)-A(-lambda))/(2i)`, exactly the existing full
charge. Apply the preceding inequality to both reflected pairs. For
`|Re lambda|, |Re mu| <= a`,

```
|C(lambda)-C(mu)+i*c*(lambda-mu)| <= c*q*|lambda-mu|,
c*(1-q)*|lambda-mu| <= |C(lambda)-C(mu)|.
```

Since `c*(1-q)>0`, `C` is injective on the closed strip. Its existing
reflection law gives `C(-conj lambda)=conj(C(lambda))`; hence its value
is real exactly when `Re lambda=0`. On that axis, the same inequality
and the real-valued charge identity give, for `u<v`,

```
c*(1-q)*(v-u) <= thetaLoopCharge(v)-thetaLoopCharge(u).
```

This proves a globally increasing physical boundary clock and an injective
analytic extension to the full strip, without selecting zeros or assuming
RH. All integrals used above are dominated by either `g` or `t*g`.
Taking difference-quotient limits at an interior point also gives
`|C'(lambda)+ic|<=cq`, hence `Im C'(lambda)<0`. In particular the
derivative never vanishes, and the centered charge has analytic order
exactly one at every interior point. This is a coordinate for the full
divisor, with no branching introduced by the coordinate itself.

Preliminary verdict: **BRIDGE**. This is a qualitative geometric statement
about the original source, not a new numerical optimization. It does not
prove the required divisor orientation: showing that every full-divisor
point has real charge remains the same unresolved core. No external
novelty claim is made. The full goal remains unconditional RH through RN.

### Charge-coordinate verification and scope audit

Formal module:
`formal/GaloisForLFunctions/RHTower/ThetaRenewalChargeCoordinate.lean`.
It contains 12 public theorems, plus three private analytic/integrability
helpers. The final foreground command

```
lake --old env lean GaloisForLFunctions/RHTower/ThetaRenewalChargeCoordinate.lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/ThetaRenewalChargeCoordinate.olean
```

passed with exit 0 and no warnings. A separate scratch audit of all 12
public theorems passed; their complete dependencies use only `propext`,
`Classical.choice`, and `Quot.sound`. There is no `sorryAx` or added axiom.
The module is imported by the RHTower umbrella. No full or umbrella build
was run. `git diff --check` passed.

The authoritative full lint run failed on three unrelated concurrent
modules missing umbrella reachability: `RHTower.LogSineStieltjesRepresentation`,
`HTGeometry.NormalSeriesStrictFDeriv`, and `Hurwitz.JointAnchorContinuity`.
They were not modified in this cycle.

Process correction: two scratch Lean commands briefly overlapped because
a polling result was not checked before the next command started. The
newer command was terminated by its verified owned PIDs; exit 143 and
the older command's exit 0 were confirmed before restarting. All later
Lean runs were sequential. This was a workflow violation, not a proof
failure; do not repeat the unchecked poll/start pattern.

Anti-theatre/anti-laziness audit: the coordinate theorem is an actual
source-specific geometric fact, but it follows from a general small-mean
exit-law argument. It is a bridge, not an established scientific novelty
or an RH proof. The attempted positive conservation identity did not
close; the existing infinite mixed Pick index explains why the raw form
cannot do that job. No work was omitted because of duration or difficulty.

The next cycle must attack the exact arithmetic sum-time/difference-time
renewal correlations at a full-divisor point. Do not spend another cycle
proving more coordinate properties. The assertion that a full-divisor
point has real charge is now transparently the remaining exclusion
problem; it must be derived, not introduced as a premise or advertised as
a new conjectural reduction. RN stays active and is not retired.

### Arithmetic deletion cycle: a forced positive-real denominator zero

The initial conjecture in this cycle was that literal prime deletion could
be iterated inside the stable renewal class, allowing the positive
renewal charge to survive arithmetic shell removal. Verdict: **FALSE**.
This is a failure of that proposed operation, not retirement of RN.

Write `a=1/4`, `P=thetaLogProfile`, `R=thetaLogTail`, and
`nu=thetaRenewalIncrement`. For `h>0`, put `b=exp(-a*h)` and

```
P_h(t) = P(t)-b*P(t+h) = R(t)-b*R(t+h),
nu_h(t) = nu(t)-b*nu(t+h),
c_h = P_h(0),
D_h(lambda) = c_h - integral_0^infinity exp(-lambda*t) nu_h(t) dt.
```

At `h=2 log p`, the translated `n`th Gaussian shell has index `pn`:
`nu_n(t)=n^(-1/2) nu_1(t+2 log n)`. Thus this operation removes the
prime-multiple shells. Crucially, it also removes the growing vacuum
`exp(a*t)` from `P`. Keeping the old seam instead of `c_h` would be a
different operation and is not justified by this calculation.

Dependency-closed paper proof of the survivor: `R>0` and is strictly
decreasing on the positive ray. Since `0<b<1`, `P_h(t)>0` for `t>=0`.
The existing superexponential bounds for `R` and `nu`, applied also at
`t+h`, show that both differences and every exponentially weighted
version are integrable on the positive ray, and their weighted endpoint
values tend to zero. Differentiating the displayed definition gives
`P_h'=a P_h-nu_h`. Therefore integration of

```
(exp(-lambda*t) P_h(t))'
  = (a-lambda) exp(-lambda*t) P_h(t)
    - exp(-lambda*t) nu_h(t)
```

from zero to infinity gives the exact entire identity

```
D_h(lambda) = (lambda-a) integral_0^infinity exp(-lambda*t) P_h(t) dt.
```

The integral is strictly positive for every real lambda. Hence the exact
real zero set of `D_h` is `{a}`, and its real sign is the sign of
`lambda-a`. In particular `D_h(0)<0`. At `lambda=-a`, the same formula
gives `integral exp(a*t) nu_h = c_h + 2a integral exp(a*t) P_h > c_h`.
The naturally normalized deleted renewal mass is supercritical, not
subcritical. This is a qualitative phase change, not an estimate.

This survivor is a **BRIDGE**, obtained by integration by parts; no
external novelty claim is made. Its purpose is to prevent an invalid
arithmetic conservation step in RN. The hard orientation law remains
unproved.

The same calculation retains the finite translation boundary explicitly.
With `r=exp((lambda-a)h)` and `I_h(lambda)=integral_0^h P(t)exp(-lambda*t)dt`,

```
D_h(lambda) = (1-r)D(lambda) - (a-lambda)r I_h(lambda).
F_h(lambda) = (1-b cosh(h lambda)) F(lambda)
  - 2 i b sinh(h lambda) C(lambda)
  - 2 b (a^2-lambda^2) integral_0^h P(t)cosh(lambda(h-t))dt.
```

Here `F_h=(a+lambda)D_h(lambda)+(a-lambda)D_h(-lambda)` is the
reflection completion of the causal deleted channel. It is not the
bilateral prime-deleted source transform: that source loses evenness.
These two additional boundary formulas are now Lean-audited in the
equivalent multiplier/finite-prefix notation. They follow from translation of the convergent half-line
Laplace integral, the finite-interval version of the same derivative
identity, and `A=F/2+iC`, `B=F/2-iC`.

The positive repair must also be retained. If the original seam `c` is
kept, the denominator is instead
`D_h^credit = D_h + b P(h)`. On the positive ray,
`0 < nu_h <= nu`: strict decrease of `nu` there follows from the existing
weighted-increment monotonicity theorem with exponent zero. Hence the
same original Laplace majorant gives
`Re D_h^credit >= c(1-q)>0` on `Re lambda>=-a`. Thus literal deletion
with a carried vacuum credit remains stable; deletion with the remaining
profile seam does not. The credit is exact, positive, and unavoidable in
switching between the two normalizations. The two-ended return changes
by the constant `2a b P(h)`. Proving that such boundary terms orient the
original divisor, rather than merely moving its level, remains open.

### Arithmetic deletion verification and scope audit

`ThetaRenewalPrimeDeletion.lean` proves 27 public theorems and defines seven
public objects, including both seam normalizations and the exact two-ended
transport identity at every full-divisor point. The final foreground command
`lake --old env lean GaloisForLFunctions/RHTower/ThetaRenewalPrimeDeletion.lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/ThetaRenewalPrimeDeletion.olean`
passed with exit 0, no warnings. All 34 public declarations were audited
through a separate scratch `#print axioms` run; only `propext`,
`Classical.choice`, and `Quot.sound` occur. The umbrella import is present;
no umbrella/full build was run. All Lean processes in this cycle ran
sequentially, with terminal status checked before starting the next.

The authoritative lint gate failed on one unrelated concurrent module:
`RHTower.CHMDStage2KleinGordonTransmutationAndTContourBochner` lacks umbrella
reachability. That module was not modified here.

Anti-theatre/anti-laziness audit: this is an exact structural bridge, not an
established novelty or an RH exclusion theorem. The false conjecture was
closure of the remaining-seam deletion operation in the subcritical class;
the positive survivor includes the exact real phase classification and the
stable credited normalization. The full-divisor transport retains both the
physical charge and finite prefix, so it does not make the charge real.
No work was omitted for difficulty or duration. RN remains active. The next
attack concerns the source-derived arithmetic current with its complete
Gamma, pole, and boundary terms, not further coordinate estimates.

### Subsequent arithmetic-current audit

The corpus already contains `ThetaPrimeShiftNoetherAction`,
`ThetaZeroDivisionSource`, and `ThetaPrimeDeletionCausalMode`: the literal
prime action has a complete Gamma/pole first variation, and a full-divisor
zero has a two-ended rapidly decaying causal response. These ingredients
do not establish stationarity of its normal field. In particular, no
identity setting a positive prime difference-square energy to zero has
been derived. Introducing that vanishing as a premise would merely insert
the unresolved orientation pressure.

The corpus also contains the complete Doob jump-energy decomposition in
`WeilPhiDoobArchimedeanJumpAndHalfLineFolding`; its remaining subtraction
is explicitly equivalent to RH. Repackaging it supplies no new theorem.
The deep corpus search completed, but its proposed ingredient combinations
were inapplicable; source-only/compiler-stale results were not accepted as
verified dependencies. No new sign, stationarity, or charge-reality claim
is made from this audit. RN remains on the same full-divisor problem.

### Compensated prime-boundary Ward cycle

The attempted positive Gram law for the deletion/inversion commutator is
already disproved in `ThetaCommutatorKernelInertia`, even on prime scales.
A positive bulk jump form after division by the one-signed theta derivative
also cannot be assumed: the theta-null derivative family and the corpus's
nonclosability obstruction invalidate that shortcut. Neither observation
retires RN; its sought orientation remains a boundary law.

Exact conjecture selected for proof: the arithmetic prime boundary current
retains an absolutely convergent finite-prefix compensation for every
complex parameter, and at every full-divisor point its seam value is the
physical renewal charge. This is a **BRIDGE**, not a new zero-exclusion
criterion or a claim of scientific novelty. External searches are omitted
as instructed. The sign of the resulting complete balance is the open core;
no sign or stationarity assumption is inserted.

Paper proof. Let `S` be any existing `ThetaSource`, `k=S.k`,
`a_n=Lambda(n)/sqrt(n)`, `h_n=log n`, and `w` arbitrary complex. Put

```
H(w) = integral_0^infinity k(t) exp(wt) dt,
I_n(w) = integral_0^(log n) k(t) exp(wt) dt,
J_n(w) = a_n exp(-w log n) [H(w)-I_n(w)].
```

Translation of an absolutely convergent tail integral gives exactly
`J_n(w)=integral_0^infinity a_n k(t+h_n) exp(wt) dt`.
Choose real `r>max(Re w,1/2)`. On `t>=0`, the norm of this integrand is
bounded by that at parameter `r`. The existing full-line prime-source
absolute Fubini theorem at `r` bounds the sum of these half-line norm
integrals by a finite number. Thus `sum_n |J_n(w)|<infinity`, and Fubini
identifies its sum with the half-line transform of the literal full prime
source. This keeps the subtraction inside each summand; it never splits
the two generally divergent Euler-weighted pieces.

For the actual theta source the complete pointwise equation is

```
P k = Gamma k + Pole_(1/2) k + Pole_(-1/2) k - (t+archConstant) k.
```

If `Re w<=3/4`, every term on its positive-ray transform is integrable:
use the existing full-line Gamma and polar bounds at `r=3/4`, multiplying
on `t>=0` by `exp((w-r)t)` of norm at most one. The `k` and `t k` terms
have all exponential moments. Hence the compensated prime sum equals the
sum of these literal Gamma and two pole transforms, minus the source
moment and local Archimedean term, with all signs retained.

Finally set `w=-2 lambda`, `c=Theta(1)`. The already proved seam identity
gives `H(-2lambda)=A(lambda)-c lambda`. At an arbitrary full-divisor point
`F(lambda)=A(lambda)+B(lambda)=0`, the definition
`C(lambda)=(A(lambda)-B(lambda))/(2i)` gives `A(lambda)=i C(lambda)`.
Therefore each summand becomes

```
a_n exp(2lambda log n)
  [i C(lambda)-c lambda-I_n(-2lambda)].
```

The compensated sum converges absolutely and obeys the complete arithmetic
balance throughout the critical strip, without a critical-axis or
simplicity premise. This completes the paper proof of that exact bridge.
It supplies no justification for discarding the prefix, Gamma, pole, or
source-moment terms to infer that `C(lambda)` is real.

The paper calculation also gives a sharp counterterm classification. For
`Re w<=1/2`, the unpaired coefficients
`b_n(w)=a_n exp(-w log n)` are not absolutely summable. On prime indices
their norms are `log p * exp(-(Re w+1/2)log p) >= log 2 / p`, and the
prime reciprocal series diverges. Consequently

```
sum_n |b_n(w) [z-I_n(w)]| < infinity  iff  z=H(w).
```

Indeed, subtract the already summable compensated current at `H(w)`.
If `z-H(w)` is nonzero, absolute summability would imply that of `b_n(w)`,
a contradiction. Conversely the established tail compensation applies.
For the actual renewal charge, `z=iC(lambda)-c lambda=H(-2lambda)-F(lambda)/2`.
Thus for `Re lambda>=-1/4`, admission of this literal boundary-charge
current to absolute prime summation is exactly full-divisor membership.
This is a unique-counterterm law, not a proof that the admitted charge is
real; it includes hypothetical off-axis divisor points faithfully.

The sharp law extends across the Euler boundary with no new hypothesis.
If `Re w>1/2`, the bare coefficient sequence is absolutely summable by the
existing von Mangoldt Dirichlet-series theorem. Adding
`b_n(w)(z-H(w))` to the compensated sequence therefore admits every `z`.
Thus globally the exact condition is `Re w>1/2 or z=H(w)`. For the renewal
charge this becomes `Re lambda<-1/4 or F(lambda)=0`. In particular the
left half-plane cannot be mistaken for an additional Xi zero set. This
extension is part of the same paper proof and remains a structural bridge.

### Prime-boundary verification and scope audit

The completed module is
`formal/GaloisForLFunctions/RHTower/ThetaRenewalPrimeBoundary.lean`.
Its 15 public theorems and three definitions prove the full counterterm
classification, the exact admission set, and the complete Gamma--pole
balance. The final foreground command

```
lake --old env lean GaloisForLFunctions/RHTower/ThetaRenewalPrimeBoundary.lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/ThetaRenewalPrimeBoundary.olean
```

passed with exit 0 and no warnings. A separate scratch audit covered all
18 public declarations and found only `propext`, `Classical.choice`, and
`Quot.sound`. Every Lean process was run sequentially, checking terminal
status before launching the next. The umbrella import is present; no full
or umbrella build was run. Targeted whitespace checks passed.

The authoritative lint gate failed on three unrelated concurrent modules
missing umbrella reachability: `RHTower.EvenSectorPolarRigidity`,
`RHTower.EvenSectorPolarStripCeiling`, and
`RHTower.EvenSectorPoleFreeNodeTests`. None was modified here.

Anti-theatre audit: no external novelty assertion is made. Counterterm
uniqueness is a general tail-compensation theorem, instantiated at the
literal renewal charge; it is not a proof of its reality. The complete
Gamma--pole identity uses actual theta arithmetic, but no sign consequence
at an admitted full-divisor point has yet been derived. The zero-exclusion
frontier therefore has not moved. The proved advance is a rigorous prime
boundary domain and complete balance on which that missing consequence
must be tested. Earlier Gram and bulk-positivity proposals met existing
obstructions rather than producing new exclusions.

Anti-laziness audit: no step was skipped because it was difficult or long;
the actual remaining orientation problem was attacked, but not solved.
Do not spend the next cycle deriving more generic admission corollaries.
Use the literal Gamma/pole/prime balance to seek a nonlinear constraint
on the admitted charge, retaining the finite prefixes. Pure summability
already faithfully admits hypothetical off-axis zeros and cannot by
itself force reality. RN and the unconditional RH goal remain active.

### Causal-field Ward attack: derivative forcing remains

This cycle attacked the proposed implication from full-divisor admission
to stationarity of a prime scaling field. No orientation theorem was
obtained. RN is not retired. No new Lean module or generic admission
corollary was added.

Corpus checks used the documented research command and Lean source only.
The first deep search completed with `partial=false`, but its compiler
coverage was mostly pending/stale/source-only. A narrower causal/Green
search returned `partial=true`, with text retrieval unfinished; its
available hits were used. The subsequent cached lexical search supplied
no useful exact causal arithmetic identity. Direct source inspection found
`ThetaPrimeGammaScalingEnergy` and `ThetaGammaPolarGroundDifference`:
the latter retains the continuous cross term and reduces the actual
relative form to **prime energy minus signed continuous energy**. Merely
applying the already proved positive prime energy omits that second term.
External novelty checks remain omitted as instructed.

The following is an analytic working derivation, not a checked Lean
theorem. Its complete operator-domain/Fubini certification remains to be
written before it can count as a dependency-closed paper result. It is
recorded to prevent a false stationarity argument and to expose the exact
remaining sign problem, not to claim a new proof of a Weil criterion.

Put `k=thetaCuspFullSource`, `G(w)=integral_R exp(wt) k(t) dt`, and

```
U_j(w,x) = integral_0^infinity t^(j-1)/(j-1)! exp(wt) k(x+t) dt,
U_1 = rightCausalResponse k w.
```

Write `A+` for the literal forward action
`-archConstant + Gamma + Pole_(1/2) + Pole_(-1/2) - Prime`, so the
established source equation is `A+ k = x k`. Write `A- = R A+ R`,
where `R f(x)=f(-x)`, and `S=A+ + A-`. This notation does not supply or
assume a self-adjoint realization; zeros are not being obtained as its
eigenvalues.

Right translation and the causal integral give the candidate exact law

```
A+ U_j(w,x) = x U_j(w,x) + j U_(j+1)(w,x).
```

The additional term cannot be dropped. For `j=1` it is the parameter
derivative `partial_w U_1`. The required exchanges are concrete: on a
fixed right ray, exponential decay of `k` dominates the prime-power sum
by `sum log(n) n^(-M-1/2)` with `M>1/2`; the Gamma subtraction must stay
inside its integral, using the derivative bound near zero; both polar
integrals retain their exponentially weighted tails. Reflection requires
two-ended decay, hence the full-transform vanishing conditions below.

Suppose `w` has exact multiplicity `m>=1` as a zero of `G`. For `j<=m`,
the vanished lower transform jets give two-ended causal fields and

```
U_j(w,-x) = (-1)^j U_j(-w,x).
```

More precisely, direct splitting of the full moment at `x` gives

```
U_(j+1)(w,x) + (-1)^j U_(j+1)(-w,-x)
  = exp(-wx)/j! * sum_(r=0)^j binom(j,r) (-x)^(j-r) G^(r)(w).
```

Combining this identity with the forward action yields

```
S U_j(w,x) = 0                         (1 <= j < m),
S U_m(w,x) = G^(m)(w)/(m-1)! exp(-wx).
```

Thus the top admitted causal field has nonzero arithmetic forcing at
every finite-multiplicity divisor point. Full-divisor membership alone
cannot justify annihilation of the entire causal chain. In the simple
case the surviving term is `G'(w) exp(-wx)`. Differentiating a formula
valid only on the discrete divisor would incorrectly erase precisely
this term.

The associated normal-pair calculation explains why this attack has not
proved orientation. Let `d_w=G^(m)(w)/m!`, `V_w=U_m(w)/d_w`, and
`eta=-conj(w)`. Evenness and reality give the same multiplicity at eta.
The causal ODE gives the removable entire transform

```
Laplace(V_w)(z) = G(z)/(d_w (z-w)^m),
Laplace(V_w)(w) = 1,
S V_w(x) = m exp(-wx).
```

For the arithmetic pairing `Q(f,g)=integral conj(f) Sg`, a distinct
reflected pair would therefore have the exact matrix

```
           V_w   V_eta
V_w         0      m
V_eta       m      0
```

and `Q(V_w-V_eta,V_w-V_eta)=-2m`. At a fixed reflected point the
normalized field has self-pairing `m`, and the normal difference is zero.
This is a physical-source derivation of the familiar reflected-pair
indefiniteness mechanism, not independent arithmetic positivity.

In the RN parameter `w=-2 lambda`, fixed reflection is `Re lambda=0`.
The proved renewal charge-coordinate theorem already identifies this
with reality of `C(lambda)`. For a simple root, the seam of the normalized
field is

```
V_w(0) = -2 [i C(lambda)-c lambda] / F'(lambda).
```

The derivative normalization must not be silently identified with the
physical renewal charge. Multiplying a negative test by `Im C(lambda)`
would only insert the sought obstruction into a scalar prefactor; it
would not prove its vanishing.

Exact surviving hard target: establish the actual prime-versus-continuous
inequality on these admitted normal causal fields, directly from theta
arithmetic. With `chi=(V_w-V_eta)/k`, the signed continuous coefficient is

```
b(u) = exp(u/2)+exp(-u/2)-exp(-u/2)/(1-exp(-2u)),
E_p(chi) = sum_n Lambda(n)/sqrt(n) * integral_R
  k(x) k(x+log n) |chi(x+log n)-chi(x)|^2 dx,
E_c(chi) = integral_(u>0) b(u) * integral_R
  k(x) k(x+u) |chi(x+u)-chi(x)|^2 dx du.
```

The sought inequality is `E_p(chi)>=E_c(chi)`. The complete arithmetic
form, once its domain identification is certified for these fields, is
`Q(k chi)=E_p(chi)-E_c(chi)`, so this would contradict the negative pair
above. It is an unresolved RH-strength inequality, not a usable premise.
The existing prime scaling theorem proves only `E_p>=0`; it gives no
comparison with `E_c`. The continuous coefficient changes sign, so the
Gamma and pole channels cannot be assigned a common favorable sign.

Anti-theatre audit: this cycle did not move the zero-exclusion frontier.
The reflected-pair reduction is REDISCOVERED/BRIDGE in mathematical
content; its physical operator-domain proof is still unfinished. No
scientific novelty or Lean verification is claimed for this calculation.
Anti-laziness audit: the nonlinear Ward candidate was attacked through
its full arithmetic forcing and multiplicities. It was not replaced by
another route or by a stronger assumed positivity statement. Continue
on the actual normal-field inequality or find a different boundary
mechanism within RN; do not treat formalizing this reduction alone as
solving the orientation problem.

### Literal causal arithmetic action: domain audit in progress

The next cycle rechecked the live Lean corpus. `CCMThetaGroundRHCriterion`
already proves the complete energy comparison equivalent to RH on the
full smooth source core. Thus the unrestricted inequality is not new.
No comparison on RN's normal causal fields has been proved. Searches for
a modular-period or squared-parameter positivity law did not supply the
missing implication. No such implication will be inserted as a premise.

The selected concrete proof obligation is the actual forward arithmetic
forcing law, including its operator domain, rather than a definition of
the action by the desired answer. For the literal kernels defining `A+`
above and `U=rightCausalResponse k w`, prove, for `Re w<=3/4`,

```
A+ U(x) = exp(-wx) integral_(t>x) t exp(wt) k(t) dt.
```

Paper proof. Translate the causal integral to obtain
`U(x+u)=exp(-wx) integral_(t>x) exp(wt) k(t+u) dt`.
For Gamma and each pole, use the existing absolute product-integrability
theorems at real parameter `r=3/4`. On `t>x`, replacing `exp(rt)` by
`exp(wt)` multiplies its norm by at most `exp((Re w-r)x)`.
Consequently the same product remains absolutely integrable on the
restricted ray. Keep the Gamma subtraction together throughout this
argument. For primes choose any real `r>max(Re w,1/2)` and apply the
existing absolute full-line prime Fubini theorem, then the same restriction
and bounded-weight argument. These bounds justify every exchange with
the causal integral. The local Archimedean term commutes by linearity.
After all exchanges, the literal complete source equation `A+ k(t)=t k(t)`
identifies the right-hand side. This proves the forward forcing formula
without a zero or simplicity assumption. Subtracting `x U(x)` leaves
the causal first moment, not zero.

The plan is to verify this exact kernel statement in Lean and then use
the verified action in the normal-field sign attack. Its classification
is BRIDGE; verifying it alone does not settle orientation or establish
scientific novelty. The arbitrary-multiplicity reflected-pair calculation
above remains separate until its remaining analytic domains are checked.

The forcing law also has a nonstationarity consequence with no divisor
or simplicity assumption. Put `R_w=A+U_w-x U_w` and
`M_w=rightCausalResponse (t k(t)) w`. The proved forward formula identifies
`A+U_w=M_w`. The ordinary causal equations give

```
U_w' = -w U_w-k,
M_w' = -w M_w-x k,
R_w' = -w R_w-U_w.
```

If `R_w` vanished identically, its derivative equation would force
`U_w=0`; the first equation would then force `k=0`, contradicting actual
theta positivity. Thus no parameter in the stated domain produces a
stationary causal field for `A+-x`. This kills that specific shortcut,
not RN or the possible normal-field inequality. The positive survivor is
the exact, nonvanishing arithmetic forcing and its causal transport law.

### Next nonlinear conjecture and its extremal-jump test

The unrestricted nonlinear strengthening of the desired Hessian sign is
now an exact test, rather than an unspecified appeal to convexity. For a
real smooth compactly supported profile `chi`, define

```
N_chi(a) = sum_n Lambda(n)/sqrt(n) * integral_R k(x) k(x+log n)
               [cosh(a [chi(x+log n)-chi(x)])-1] dx
  - integral_(u>0) b(u) * integral_R k(x) k(x+u)
               [cosh(a [chi(x+u)-chi(x)])-1] dx du.
```

The candidate `N_chi(a)>=0` for all `chi,a` would imply the desired
quadratic sign at `a=0`, but the following analytic attack predicts it is
FALSE for actual theta arithmetic. This is not a falsification of the
normal-causal-field comparison or of RN.

Take two nonnegative smooth bumps with disjoint supports, each bounded
by one and equal to one on a nonempty interval. Put `chi=phi-psi`.
Place their supports so every positive cross difference lies beyond
`screwSignThreshold` and inside an open gap between consecutive integer
logarithms. Thus no prime-power link joins the two supports, while the
continuous coefficient `b` is strictly positive on their cross product.
Such gap geometry is already present in `ThetaPrimeLogCellPositivePairs`
and `ThetaFarPositiveInterference`; the required plateau choice still
needs an exact Lean construction, and must not be confused with the
existing ground-normalized physical bumps, which need not have flat tops.

The positive survivor of this proposed no-go is a sharp extremal-jump
law. For `|d|<=2`, `a>=0`,

```
0 <= exp(-2a) [cosh(a d)-1] <= d^2/8,
lim_(a->infinity) exp(-2a) [cosh(a d)-1]
  = 1/2 if |d|=2, and 0 otherwise.
```

The bound follows from convexity of `sinh` on the positive ray:
`sinh(a|d|/2) <= |d| sinh(a)/2`, then
`cosh(a d)-1=2 sinh(a d/2)^2` and
`exp(-2a)[cosh(2a)-1]=(1-exp(-2a))^2/2<=1/2`.
The existing absolute squared-increment bounds therefore give a single
dominating integrable function for both the discrete and continuous
actions, including the singular Gamma endpoint.

Dominated convergence predicts the exact limit

```
lim exp(-2a) N_chi(a)
  = (prime mass of links with |Delta chi|=2
      - continuous signed mass of links with |Delta chi|=2) / 2.
```

For the separated opposite plateaus the first mass is zero and the
second is strictly positive, hence `N_chi(a)->-infinity`. This would
separate local quadratic stability from global nonlinear stability
without changing the literal arithmetic coefficients. The core nonlinear
limit was not found by the completed deep corpus search; no external
novelty claim is made. Its status is an analytic candidate with an explicit
proof plan, NOT a verified Lean theorem. Next: verify the scalar bound,
dominated-convergence statement, and actual plateau geometry; formalize
the exact survivor if the audit holds. Then return to the special normal
causal fields, whose additional constraints cannot be replaced by an
unrestricted global-minimum assertion.

### Causal arithmetic verification and scope audit

Completed `formal/GaloisForLFunctions/RHTower/ThetaRenewalCausalArithmetic.lean`
and wired its import immediately after `ThetaRenewalPrimeBoundary` in
`formal/GaloisForLFunctions/RHTower.lean`. The final foreground command

```
lake --old env lean GaloisForLFunctions/RHTower/ThetaRenewalCausalArithmetic.lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/ThetaRenewalCausalArithmetic.olean
```

passed with exit 0 and no warnings. A separate `/tmp` scratch audit of
all 27 public declarations passed with exit 0 and no warnings; every
declaration depends only on `propext`, `Classical.choice`, and `Quot.sound`.
The formal lint gate passed (existing large-file warnings only).
Whitespace and the single umbrella import were checked. No full or
umbrella build, heartbeat increase, commit, or push occurred. Own Lean
processes were sequential, with terminal status checked before each next
launch.

The verified result now includes absolute admission of each literal
causal Gamma/pole action, absolute summability of every prime-power
action, their complete moment identity at every cutoff, the sourced
residual ODE and nonstationarity. At cutoff zero the prime action is
exactly the already defined physical renewal current at every full
divisor point. The seam identity keeps the full `F/2` defect away from
the divisor. These statements use no critical-line or simplicity premise.

Anti-theatre audit: this closes an actual formal analytic gap and
certifies the nonstationarity obstruction. It is a BRIDGE, not a new
zero-exclusion theorem, proof of the full reflected-pair calculation, or
established scientific novelty. The broader energy equivalence was
already in the corpus and is not counted as new knowledge.
Anti-laziness audit: no step was omitted because of effort or duration;
the literal kernels and their domains were proved. The required
normal-field sign is still open. The next exact nonlinear conjecture
above was attacked analytically while the proof audit ran; it must be
checked and its positive extremal-jump survivor formalized if it holds,
without mistaking failure of global nonlinear minimization for failure
of RN. The full-divisor orientation goal remains active and RH unproved.

### Nonlinear extremal-jump cycle: dependency-closed paper argument

Conjecture under attack: the literal complete cosh action is nonnegative
for every real compact smooth profile and every real amplitude. Verdict:
FALSE by the following analytic argument; Lean verification is pending.
This is a falsifier of unrestricted nonlinear positivity, not of RN.

Write K_a(d)=exp(-2a)(cosh(ad)-1). For a>=0, |d|<=2, convexity
of sinh on the nonnegative ray gives
sinh(a|d|/2)<=|d| sinh(a)/2. The double-angle identity and
exp(-2a)sinh(a)^2=(1-exp(-2a))^2/4<=1/4 give
0<=K_a(d)<=d^2/8. Expanding cosh as two exponentials gives
K_a(d)=(exp((d-2)a)+exp((-d-2)a))/2-exp(-2a).
Thus its limit is 1/2 at d=2 or d=-2, and zero elsewhere
in [-2,2].

For any measure, measurable real jump d, real weight w, bound
|d|<=2, and integrable w*d^2, dominated convergence applies to
w*K_a(d) with majorant |w*d^2|/8. Consequently
exp(-2a) integral w(cosh(ad)-1) tends to
integral (if |d|=2 then w/2 else 0). This is the exact positive
survivor: an extremal-link mass law valid for signed weights. For the
prime and continuous theta actions, the existing absolute quadratic
integrability theorems verify the required majorants. No integral of
the uncompensated Gamma coefficient is asserted.

Choose disjoint smooth bumps F,H, valued in [0,1], with supports in
balls centered at 0,c of common radius r, and equal to 1 on the
closed balls of radius r/2. The corpus's atom-free radius construction
allows c-2r arbitrarily large and the entire difference interval
(c-2r,c+2r) free of every log(n), n>=2. Choose also
c-2r>max(0,screwSignThreshold). Let chi=F-H. It has |chi|<=1.
An extremal increment requires one endpoint with F=1 and the other
with H=1; hence every positive extremal shift belongs to that
difference interval. No prime extremal link exists (indices 0,1 have
zero von Mangoldt coefficient). Every continuous extremal link has
strictly positive kernel b. Moreover a nonempty open rectangle near
(u,x)=(c,0) consists of extremal links, with positive source density.
Its product Lebesgue measure is positive. Absolute integrability above
and positivity on this rectangle imply a strictly positive continuous
extremal mass. The exact limit is therefore strictly negative.
Since exp(2a) tends to infinity, the complete unscaled action tends
to minus infinity. Choosing the separation beyond the existing
far-gap coercivity threshold also gives strictly positive complete
quadratic energy for the same profile chi. Thus the obstruction
separates local quadratic stability from global nonlinear stability
on actual arithmetic sources, without a critical-line premise.

Plan: verify scalar concentration and signed-integral law; apply both
literal theta link measures; construct the plateau witness and prove
negative limiting mass. Keep full-divisor normal-field orientation as
the unresolved target. External novelty search omitted as instructed.

### Nonlinear cycle verified

Added ThetaNonlinearExtremalJump.lean and ThetaNonlinearPlateauEscape.lean,
with one import each in RHTower.lean. Both final foreground commands
`lake --old env lean <module> -o <module olean>` exited 0. The first
emitted three informational algebra-tactic suggestions, no warnings;
the second emitted no diagnostics. The separate scratch axiom audit
covered all 26 public declarations, exited 0, and used only propext,
Classical.choice, Quot.sound. Formal lint passed with existing large-file
warnings only. New-file whitespace and umbrella import counts passed.

Verified exact survivor:
`tendsto_thetaNonlinearAction_scaled` identifies the limiting signed
extremal-link mass. `integrable_thetaNonlinearAction_terms` proves both
literal terms integrable for every real amplitude when |chi|<=1.
`exists_positive_quadratic_negative_nonlinear_limit` constructs an actual
compact smooth profile, bounded by 1, with positive full quadratic
energy, zero prime extremal mass, and strictly positive continuous
extremal mass. `exists_positive_quadratic_nonlinear_escape` proves the
same profile's complete nonlinear action tends to minus infinity.
No critical-line, hypothetical-source, or simplicity premise occurs.
The complete quadratic is the existing literal arithmetic form; the
small-amplitude Taylor-limit identity for this new nonlinear action has
not been separately formalized here.

Verdict: unrestricted nonlinear minimization is FALSE. RN remains active.
This is an actual-source obstruction plus an exact positive classification,
not full-divisor orientation. Dominated convergence is the parent method;
the corpus already supplied far-gap quadratic coercivity. No external
novelty claim is made, and no independent RH exclusion was obtained.

### Next normal-field diagnostic: finite causal jets

The direct source equation suggests an exact diagnostic, not an estimate:
for w nonzero and U_f(w,x)=integral_(t>0) exp(wt)f(x+t), repeated integration
by parts gives

U_k = sum_(j<N) (-1)^(j+1) k^(j)/w^(j+1)
      + (-1)^N U_(k^(N))/w^N.

The full reflected arithmetic action S is formally translation invariant
and annihilates k, so it should annihilate every finite derivative jet.
At a simple full zero, G_(k^(N))'=(-w)^N G_k'; therefore the normalized
causal remainder is exactly the derivative-source normalized field.
This would put the divisor information in the remainder after every
finite inverse-frequency expansion. The claim is an analytic diagnostic:
commutation, whole-line domains, and the literal form's radical pairing
must be proved before using it as a theorem. No such new Lean theorem
is claimed in this cycle.

Corpus audit found related dense-radical/nonclosability laws in
HedenmalmThetaNullTemperedDenseRadicalUniversalityLaw and
XiThetaSchwartzL2Nonclosability. Those statements have explicit form
symmetry/positivity/nullity premises; they cannot be silently applied to
the unproved native RN sign. CCMQuartetResolventPolarization already
contains the algebraic negative transverse square. Do not rediscover it.
The new deep searches completed without partial coverage, but compiler
coverage was mainly source-only; only compiled applications count as
formal verification. The unresolved objective remains the actual
renewal-charge orientation, including every multiplicity. A finite jet,
ordinary L2 closure, or unrestricted nonlinear minimum supplies no proof.

Anti-theatre: a proposed actual sign mechanism was falsified, its exact
survivor formalized, and its limits stated. No scientific novelty or RH
progress beyond that obstruction is asserted. Anti-laziness: no hard step
was dropped on effort grounds; all infinite prime and singular continuous
terms were retained. The next cycle must attack the constrained causal
remainder's arithmetic sign or a direct charge identity within RN.

### Reflected causal action: exact full-divisor forcing

Current corpus searches: renewal logarithmic representation, positive
remainder, and mixed cut/normal-field sign. All three completed, with
partial snapshot/compiler coverage reported. Existing logarithmic renewal
series and positive single-cut current do not prove the mixed-field sign.
No external search was made. The target remains full-divisor orientation.

Exact bridge, not an orientation conjecture: put k=thetaCuspFullSource,
G(w)=integral k(t)exp(wt), and U_w(x)=exp(-wx) integral_(t>x) k(t)exp(wt).
Define A- literally from A+ by replacing each x+u and x+log(n) by x-u and
x-log(n), retaining the local term, compensated Gamma kernel, both pole
kernels, and every original prime-power coefficient. If G(w)=0 and
-3/4 <= Re(w) <= 3/4, then

  (A+ + A-)U_w(x) = G'(w) exp(-wx).

Dependency-closed paper proof: k is even and its exponential moments are
absolutely integrable. Splitting the zero whole-line integral at x gives
U_w(x)=-exp(-wx) integral_(t<=x) k(t)exp(wt). Substitution t=-s gives
U_w(x)=-U_(-w)(-x). Each literal backward kernel is therefore the negative
of its forward counterpart at (-w,-x). Existing forward-domain theorems
at -w prove absolute integrability of Gamma and both poles and absolute
summability of all prime terms. Thus A-U_w(x)=-A+U_(-w)(-x). The verified
forward forcing identity, followed by t=-s, changes this into
exp(-wx) integral_(t<=x) t k(t)exp(wt). Add the forward tail moment;
absolute first-moment integrability justifies splitting the whole line.
That whole-line moment is G'(w), by the existing derivative theorem.
This uses no simplicity or critical-axis assumption. At multiple zeros
the right side can vanish; higher causal jets are not covered by this
first-moment statement. The global source weld identifies G(-2 lambda)
with XiC(2 i lambda), so the theorem applies to the actual full divisor.

Verdict: BRIDGE. Reflection and causal integration are parent methods;
this is not a claim of new scientific knowledge or a sign proof. Its
purpose is to close the unverified literal reflected action/domain step
before attempting a native arithmetic sign argument. The unresolved
conjecture is positivity of the appropriate normal-field pairing with
the renewal boundary charge retained, including multiplicities. No
positivity, eigenvalue realization, or RH premise is introduced here.

Plan: (1) verify integral/reflection APIs; (2) formalize literal backward
terms, their domains, exact forcing, and actual-divisor specialization;
(3) audit the remaining sign mechanism against this exact identity;
(4) foreground module and axiom audits, lint, umbrella wiring, cleanup.

Refinement before formalization: the moment-reflection calculation itself
does not require G(w)=0. Throughout the same strip,
A+U_w(x)-A+U_(-w)(-x)=exp(-wx)G'(w). The backward field here is exactly
U_w(x)-exp(-wx)G(w), as follows from the unrestricted reflection defect.
At a full zero it becomes the literal backward field. At x=0, in the RN
coordinate w=-2 lambda, this correction changes the right seam
i C-c lambda+F/2 into i C-c lambda-F/2. Thus the subtraction retains the
actual full divisor defect; it is not an imposed critical-axis condition.

For the charge specialization set F(lambda)=G(-2 lambda) and R=F/C.
The chain rule gives F'=-2 G'(-2 lambda). At F=0 and C nonzero, the
quotient rule gives C R'=F'. Hence the full arithmetic action is
-exp(2 lambda x) C(lambda) R'(lambda)/2. All differentiation hypotheses
follow from the already proved entire source transform and entire charge;
C is nonzero in the upper critical strip. This first-order identity
remains valid but can vanish at a multiple zero. It is not a multiplicity
exclusion or a positivity statement.

### Reflected action verified; orientation still open

Added ThetaRenewalReflectedArithmetic.lean (224 lines) and one umbrella
import. Final foreground module audit, with `lake --old env lean` and an
explicit olean output, exited 0 without diagnostics. Separate scratch
axiom audit exited 0: all 21 public definitions/theorems depend only on
propext, Classical.choice, Quot.sound. Formal lint passed, with existing
large-file warnings. New-module whitespace and unique umbrella import
checks passed. No full or umbrella build, heartbeat increase, numerical
computation, or extra axiom was used.

Verified statements: unrestricted causal reflection defect; literal
backward Gamma/pole/prime identities; absolute backward domains at every
full zero; full forcing exp(-wx)G'(w); its pre-divisor regularized version;
actual Xi specialization; and the exact renewal-charge coefficient
-exp(2 lambda x) C(lambda) (F/C)'(lambda)/2 at full divisor points in the
upper strip. The charge coefficient can vanish at a multiple zero.
No simplicity or critical-axis hypothesis was inserted.

Further corpus audit: the three subsequent deep searches (causal mixed
pairing, theta mixed Weil sign, and prime/jet Schur completion) completed
with partial=false but mostly source-only compiler coverage. Read the
actual candidate Lean statements. PaperThetaSchurFiniteStageLimit proves
strong finite-stage convergence but makes norm convergence exactly RH;
it supplies no missing sign. EulerDeletionDirichletGram's equal-parameter
Hermitian pairing depends only on twice the real abscissa, losing the
frequency. PrimeBurnolConfluentMomentGram proves finite Gram invertibility,
not a native completed-form identification or uniform passage to it.
ThetaCompactStripZeroEngineering retains positivity of every finite
prime deletion under compact source surgery. None of these is an RN
orientation producer. The dense-radical/nonclosability law has explicit
positivity and symmetry hypotheses; it cannot be used to assume the
native sign. It also rules out a nonzero ordinary-L2-closable completion
once those hypotheses are established.

Exact next sign target, retaining multiplicity: for a full zero w of order
m, write d=G^(m)(w)/m! and

  U_j(w,x)=integral_(t>0) t^j/j! exp(wt) k(x+t),
  V_w=U_(m-1)(w,.)/d, eta=-conj(w).

The expected all-order extension is S V_w=m exp(-wx), with Laplace
transform G(z)/(d (z-w)^m). Its reflected normal field is V_w-V_eta.
The literal arithmetic pairing should then have normal value -2m when
Re(w) is nonzero. That calculation is a diagnostic for the required sign,
not an exclusion. The all-order domains and the whole-line mixed pairing
are NOT formalized in the new module. At the boundary, the lower G jets
vanish, leaving the corresponding derivatives of the actual renewal
charge seam; no independent boundary datum may be fitted.

[OPEN CORE] Prove nonnegativity of that literal mixed normal-field form
from the actual prime/Gamma/pole kernels and renewal boundary charge,
or obtain a direct charge identity forcing its normal component to vanish.
Neither positive single cuts, arbitrary positive finite Gram matrices,
nor an assumed Schur-limit identification proves this. A finite-jet
subtraction in an ordinary L2 metric is not a proposed solution: it loses
the required nonzero boundary form. No separate route was substituted.

Anti-theatre: this cycle closes an exact arithmetic-domain bridge, not the
orientation gap. No new scientific knowledge beyond parent reflection
and causal-integral methods is claimed. Anti-laziness: the full sign was
investigated directly and the apparent finite-form shortcuts audited;
it remains unproved. Next cycle must attack that actual mixed sign and
its multiplicity data, not accumulate normalization corollaries.

### Native mixed-pairing audit

Previous cycle classified as progress: verified reflected literal action,
not orientation. Current mission remains RN charge orientation. No external
searches or old reports read. Mixed-cut search returned partial coverage;
atom-quadratic search completed but did not produce an applicable native
positive factorization. The atom expansion proposal has an unclosed cusp
interchange: each atom has zero critical Mellin charge while the completed
source has nonzero charge. An unsigned whole-line atom Gram cannot be
substituted without proving that exact missing boundary contribution.
The first-atom positive-ray domination theorem does not close this step.

Selected exact diagnostic: evaluate the whole-line pairing of the literal
full arithmetic actions on two admitted causal fields. This is BRIDGE,
not a claim of a new positivity theorem. Unlike a generic quartet algebra
identity, the integral here must use the actual full arithmetic action and
prove its whole-line admission. The sign question is not replaced by it.

Dependency-closed paper proof for the first-order sector: assume G(w)=0.
The established two-ended exponential bounds on U_w imply that
x^j exp(zx) U_w(x) is absolutely integrable for every complex z and every
natural j: choose decay exponent |Re z|+2, dominate by a constant times
|x|^j exp(-2|x|). The causal ODE gives

  (exp(zx) U_w)'=(z-w) exp(zx) U_w-exp(zx)k.

Both the function and its derivative are integrable; whole-line FTC gives
(z-w) L(U_w)(z)=G(z). At z=w use instead the derivative of
x exp(wx)U_w: its integral is L(U_w)(w)-G'(w)=0. Thus L(U_w)(w)=G'(w).
These identities require neither an off-axis assumption nor simplicity.

When G'(w) is nonzero, V_w=U_w/G'(w) has transform 1 at w and zero
at every distinct zero of G. At a full zero v in the arithmetic strip,
the already verified literal action on V_v is exp(-vx). Therefore

  B(w,v)=integral conj(V_w(x)) [S U_v(x)/G'(v)] dx

is absolutely integrable and equals conjugate L(V_w)(-conj(v)). For
eta=-conj(w), reflection and real-source symmetry make eta a zero and
G'(eta) nonzero whenever G'(w) is nonzero. If Re(w) is nonzero,
B(w,w)=B(eta,eta)=0 and B(w,eta)=B(eta,w)=1. Consequently the complete
linear-combination action paired with V_w-V_eta is exactly -2. At a
critical simple zero the self-pairing is 1. This is the exact native
first-order indefinite block, not a proof that it cannot occur.

Plan: verify FTC/derivative APIs; prove weighted admission and exact
Laplace evaluations; evaluate literal mixed action; audit its connection
to the signed jump form without assuming positivity; run foreground Lean,
axiom and lint gates, wire module, clean scratch. Higher-order charge jets
and the native nonnegativity proof remain required for full orientation.

Verification result: ThetaRenewalMixedArithmetic.lean compiles with
`lake --old env lean` (terminal exit 0). All 23 public declarations were
checked by scratch `#print axioms`; dependencies are only propext,
Classical.choice and Quot.sound. The module is imported once by RHTower.
The compiler emitted a tactic suggestion, not an error. `git diff --check`
passed. Repository lint exited 1 because the unrelated untracked module
GaloisForLFunctions.RHTower.DeningerMeyerNativeClockBoundaryDefect was not
reachable from its umbrella. No changes were made to that module.
Its import subsequently appeared from concurrent workspace work. A second
lint run exited 1 on another unrelated untracked module,
GaloisForLFunctions.RHTower.DeningerMeyerExactXiCapSource. The RN module
remained imported exactly once; repository lint is not claimed passing.

Domain audit: thetaFullArithmeticQuadratic accepts Schwartz ground
profiles chi and proves prime jump energy minus the complete continuous
jump energy. The new pairing instead integrates the complete pointwise
action on U/G'. Its inner prime/Gamma/pole expressions are the literal
ones, and the resulting whole-line density is absolutely integrable.
This does NOT yet prove that (U/G')/k is Schwartz or justify every
termwise whole-line rearrangement needed to identify it with the older
ground-profile form. No such equality is used in the new theorems.

The final boundary-orientation deep search completed with partial=false;
compiler coverage remained mostly pending or stale. Candidate lemmas,
source arguments and ingredient sets were inspected. Hits included the
already proved RN admission/reflected-action identities, positive finite
divisor Grams with different definitions, and unrelated normal-boundary
results. None supplied the native mixed sign. The finite divisor Gram
must not be identified with this pairing merely because both are Grams.
Broadening to a lexical OR search restricted to ThetaRenewal returned
the existing charge-coordinate, admission and reflected-action results;
no additional orientation proof was obtained from those hits.

Current classification: BRIDGE. New verified content is the exact
whole-line action pairing and its simple-zero reflected block, with
weighted admission proved rather than assumed. Parent methods are causal
integration, whole-line FTC and polarization; no scientific novelty or
orientation theorem is claimed. The all-order formula in the previous
entry remains a paper outline, not a formal theorem. Full multiplicity,
native nonnegativity and unconditional RH remain open in this work.

Direct sign attack retained: factor the actual prime-minus-continuous
mixed form through the theta atom/divisor identities while carrying the
modular cusp charge. The atom critical-charge mismatch prevents dropping
that contribution. A finite positive divisor Gram, a single-cut tail
identity, or the finite modular seam jet algebra supplies no proof that
the missing contribution has the required sign. No positive factorization
has been obtained. RN remains active; the mixed sign and cusp contribution
remain the hard target, not tighter scalar estimates or an operator-zero
realization.

Owned search/API/axiom/lint scratch files were removed after their commands
terminated. No own Lean or search process remains running.

### Full mixed sign, with the cusp term retained

Previous goal turn: progress, since the actual mixed pairing was proved
and audited. User now explicitly requires the native mixed sign with
modular cusp charge and all multiplicities. No weakening to simple zeros,
individual cuts, finite positive Grams or an operator-zero realization is
accepted as completion.

Current-state corpus audit finds CCMThetaGroundRHCriterion: the complete
ground energy comparison on all smooth compact source cores is exactly
equivalent to RH. Its comparison is explicitly unproved in that module.
The finite-pair/two-node theta tail signs concern different kernels and
cannot be silently substituted. The exact atom transform is also checked:
its factor a-1/2 vanishes at the boundary where the completed charge is 1/2.

Plan: derive the cusp correction in a native mixed factorization; attack
its sign without importing RH or choosing only critical/simple zeros;
carry all divisor jets in the proposed identity. Only a dependency-closed
paper result will be sent to Lean. Keep every failed factorization and
its surviving exact content explicit. No external search is used, per
the user's research constraint.

Candidate A: on a natural native-action domain containing k, write
Q(f)=P(f)+alpha*|M(f)|^2, where P is nonnegative, alpha>0 and
M(f)=integral exp(x/2) f(x) dx is the actual retained cusp functional.
Verdict FALSE. Complete_theta_source_equation at x and -x, together
with evenness, gives S k=0 pointwise for the full two-sided arithmetic
action. Hence Q(k)=integral conj(k) S k=0. The completed half-density
identity gives M(k)=1/2, so the proposed right side is at least alpha/4.
This is a complete paper falsification of that independent positive
cusp-summand repair. It does not exclude coupled factorizations, and it
does not by itself apply to a domain deliberately excluding k.

Positive survivor of A: any sum-of-squares factorization of this native
form must annihilate k componentwise; if it has the native translation
symmetry, it must annihilate the complete theta translation orbit.
The corpus already proves the corresponding stronger positive-form
radical/ordinary-L2 nonclosability classification in
HedenmalmThetaNullTemperedDenseRadicalUniversalityLaw. This is
REDISCOVERED parent positivity/radical theory, not a new sign theorem.
The correction must enter with coupled cancellation; appending a positive
charge square is not a valid solution.

Candidate B: a scalar correction with uniformly bounded orders at the
two ports completes every finite Euler stage without losing the reflected
charges. Verdict FALSE by the existing ThetaEulerTwoPortJetPole theorem
thetaEulerStage_divisor_price: its required orders are -1 at +1/2 and
|P| at -1/2. PrimeExhaustion.tendsto_card makes the second unbounded.
The exact positive survivor, already formalized there, is this divisor
order law and the normalized right-port derivative charge 1/2. This
rules out bounded-order scalar repairs, not every scalar function or a
matrix correction of fixed dimension with unbounded analytic order.

The stronger remaining candidate must preserve the actual complete
charge as a holomorphic function and couple its entire boundary data
to the arithmetic bulk. Merely postulating a Hilbert norm equal to Q is
CIRCULAR: it is positivity restated. No explicit, independently defined
positive factorization has been found. Full divisor multiplicities are
still required, and none are silently replaced by G'(w) != 0.

### Native-sign audit after the repeated proof request

The requested nonnegativity is not proved. No new repo Lean module or
orientation theorem was added in this pass. The existing simple-zero
mixed-action theorem is not an all-multiplicity sign proof.

The scratch audit of the two rejected repairs now terminates with exit 0
under `lake --old env lean /tmp/rn-native-cusp-audit.lean`. Its first
example proves the integral of k times its complete two-ended action is
zero, using both actual source equations. Its second example proves the
scalar contradiction with a separate positive square of the actual
half-density charge 1/2. Five imported theorem axiom audits list only
propext, Classical.choice and Quot.sound. An earlier scratch rewrite
failed on the syntactic distinction between `-(1/2)` and `-1/2`; it was
corrected before this successful audit. These are verifications of the
stated rejected repair, not a native nonnegativity proof.

Further attack: positive real part of the nonvanishing renewal charge
cannot, by itself, convert an indefinite native form into a positive
one. At a zero of order m, multiplication by an analytic unit acts on
the truncated local jet algebra by a triangular matrix whose diagonal
is the nonzero constant coefficient of that unit. It is invertible at
every finite m. For any Hermitian form H and this map T, the transported
form is H(Tx,Ty); any negative witness v remains the negative witness
T^{-1}v. Thus positivity of the transported form is equivalent to
positivity of the original. This is an elementary coordinate-change
argument, classified REDISCOVERED, not an assertion that the full native
jet-form identification has already been formalized. An additional
arithmetic identity would still be needed to establish the sign.

The current deep native-mixed search completed with partial=false. Its
compiler coverage remained mostly pending/stale; candidate lemmas,
source arguments and proposed ingredient sets were inspected. The
suggested combination of mixed symmetry and modular cusp identities
does not imply positivity. A lexical search for the two exact energy
names returned their separate definitions, nonnegativity of the prime
energy, and decomposition/rigidity theorems; none of those returned
statements supplies the required comparison. No external search was
used, as requested.

Anti-theatre/anti-laziness assessment: no new scientific knowledge or
native orientation advance in this pass. The positive charge and
coordinate facts are existing results; the elementary congruence audit
does not justify novelty. No step was omitted because of estimated
effort. The hardest sign was attacked, but its positive producer was not
found. Continue RN with the exact coupled bulk/cusp arithmetic identity
as the target; do not replace it by more normalization corollaries,
simple-zero restrictions, assumed positivity, or operator eigenvalues.

### Coupled null-source cusp reduction and the all-order native pairing

Previous turn: no progress on the native sign. This pass keeps the exact
sign target. The following is a paper bridge, not a positivity theorem;
its all-order native integral statements have not yet been formalized.
The external novelty phase remains omitted by the user's instruction.

Write k=thetaCuspFullSource, G(z)=integral exp(z*x)k(x)dx, and let S be
the literal sum of the forward and backward prime/Gamma/two-pole actions.
Use the sesquilinear convention B(f,g)=integral conjugate(f) Sg.
The existing source equation and evenness give Sk=0. Every translate
k_h(x)=k(x-h) is also null, since every term of S is translation
invariant. This statement concerns the complete action, not each term.

Paper domain: finite linear combinations of translates of k and causal
jets at zeros. Every function and its x derivative decays faster than
every exponential. Products in the mixed action are absolutely admitted:
for every A>0, the cross-correlation integral of absolute values is
bounded by C_A exp(-A*|u|), by taking decay exponent 2A and using
|x|+|x+u|>=|u|. The all-prime exchange then follows from
Lambda(n)<=log(n), choosing A>1/2. At u=0 the compensated Gamma numerator
is O(u) in L2, since ||f(.+u)-f||_2<=u||f'||_2 for 0<u<=1; the other
coefficient difference is O(u). Cauchy--Schwarz admits its pairing with
f. For u>=1 the Gamma coefficients decay or are bounded by a decaying
exponential. Both polar terms are admitted by the arbitrary exponential
cross-correlation bound. These arguments justify symmetry and translation
invariance on this domain without a source-quotient Schwartz hypothesis.

All-order causal construction: if w is a zero of G of exact order m>=1,
put

  U_j(w,x) = integral_(t>0) t^j/j! exp(w*t) k(x+t) dt,
  d_w = G^(m)(w)/m!,       V_w=U_(m-1)(w,.)/d_w.

For j<m, all whole-line moments through order j vanish. The equivalent
tail formula is exp(-w*x)/j! times the integral over t>x of
(t-x)^j exp(w*t)k(t). Splitting its zero whole-line polynomial moment
turns it into the negative left tail. Evenness therefore gives

  U_j(w,x)=(-1)^(j+1) U_j(-w,-x).

The right and left tails prove arbitrary exponential decay. One way to
make the bound explicit is to expand (t-x)^j and apply the existing
rightCausalResponse exponential estimate to each real source t^r k(t),
whose exponential moments are finite and whose w-moment is zero for
r<=j. Multiplication by a fixed power of x is absorbed by one more
exponential margin. Differentiation gives U_0'=-w U_0-k and, for j>0,
U_j'=-w U_j-U_(j-1), so derivatives have the same admission.

The forward arithmetic exchange is valid at all these orders. For
|Re w|<1/2 and r=t-x>0,

  r^j/j! * exp(Re(w)*r) <= 4^j exp(3*r/4).

This follows from the jth nonnegative term of exp(r/4). It dominates
the weighted joint absolute source integrands by the existing
integrable_gammaLaplace_rightRay, integrable_polarLaplace_rightRay and
integrable_primeLaplace_rightRay at real abscissa 3/4. Hence Fubini
commutes the causal integral with each literal action. The forward
source equation yields

  A+ U_j = x U_j + (j+1) U_(j+1).

For j<m, the reflection formula gives the literal backward action by
the reflected forward one, including its absolute domain. Adding gives

  S U_j(w,x) = exp(-w*x) G^(j+1)(w)/j!.

In particular S U_j=0 for j<m-1 and S V_w=m exp(-w*x). No parameter
derivative of an identity restricted to the zero set is used here.

The bilateral transform obeys

  (z-w)^(j+1) L(U_j)(z)=G(z),             j<m.

Proof: integrate the displayed x-ODE against exp(z*x), with the
two-ended decay proving every integration by parts; start with
(z-w)L(U_0)=G and induct. At z=w, split the x integral at zero and use
the right-tail representation on x>=0 and the negative left-tail
representation on x<=0. Fubini integrates the polynomial over 0<=x<=t
or t<=x<=0, respectively, and gives

  L(U_j)(w)=G^(j+1)(w)/(j+1)!.

All double integrals in this split are absolutely bounded by the
(j+1)st absolute exponential moment of k. Thus L(V_w)(w)=1, while
L(V_w)(v)=0 at every other zero v. Reflection eta(w)=-conjugate(w)
preserves the exact order m; the actual source-moment classification
and reflections already occur in XiHedenmalmThetaJetSource.

It follows that on the top causal jets the native pairing is

  B(V_w,V_v) = m_v if w=eta(v), and 0 otherwise.

Every lower jet is in the radical of this finite jet pairing: its
action is zero, and the reverse mixed pairing vanishes by the same
transform evaluations. A critical top jet contributes weight m_w;
an off-axis reflected pair has matrix [[0,m_w],[m_w,0]], so
Q(V_w-V_eta(w))=-2m_w. This is the exact multiplicity diagnostic, not
the opposite inequality needed to exclude the pair.

The actual renewal seam is retained at each order. With w=-2lambda,
F(lambda)=G(-2lambda), c=Theta(1), and C the full renewal charge, the
existing seam identity and differentiation of absolutely convergent
half-line integrals give, for j<m,

  (-2)^j j! U_j(-2lambda,0)
    = i C^(j)(lambda) - c (d/dlambda)^j lambda.

The omitted F^(j)/2 term is zero by exact order, not by a simplicity
assumption. With R=F/C, the nonzero terminal normalization is

  d_w = C(lambda) R^(m)(lambda) / ((-2)^m m!).

Here all lower R jets vanish and C(lambda) is the actual source-proved
unit. This uses the complete charge, including its higher seam jets.

Coupled cusp reduction: define M_+(f)=integral exp(x/2)f(x)dx and
M_-(f)=integral exp(-x/2)f(x)dx. For a fixed nonzero real h, write
r=exp(h/2), D=r^2-r^(-2), p=M_+(f), q=M_-(f), and set

  alpha=2(r*p-r^(-1)*q)/D,
  beta =2(r*q-r^(-1)*p)/D,
  P_h f=f-alpha*k_h-beta*k_(-h).

The existing completed source moments G(1/2)=G(-1/2)=1/2 show that the
moment matrix of (k_h,k_(-h)) is
(1/2)[[r,r^(-1)],[r^(-1),r]], with nonzero determinant D/4.
Thus M_+(P_h f)=M_-(P_h f)=0. The cusp data remain recoverable in the
two explicit coefficients alpha,beta; they have not been set to zero
in the original field.

On the transform side the subtraction is exactly
L(P_h f)(z)=L(f)(z)-G(z)(alpha*exp(h*z)+beta*exp(-h*z)).
At every full zero of G of order n, this changes none of the transform
jets of orders 0 through n-1. Thus the correction preserves all divisor
jet data, not merely its values at distinct or simple zeros.

For every causal top jet, its mixed pairing with k_h is zero because
S V_w=m exp(-w*x) and L(k_h)(-w)=exp(-w*h)G(-w)=0. Lower jets have
zero action. The reverse pairing is zero because S k_h=0. Hence

  B(P_h f,P_h g)=B(f,g)

on every finite span of the admitted causal jets, with no bound on
multiplicity. The full polar action itself is exactly

  S_polar f(x)=exp(x/2) M_-(f)+exp(-x/2) M_+(f),

since exp(|x-y|/2)+exp(-|x-y|/2)=2cosh((x-y)/2). Consequently
the projected field has zero polar action, and its prime--Gamma pairing
equals the original complete pairing. This is a coupled null-source
cancellation, not the false addition of a separate positive cusp square.

Status and next obstruction: this paper reduction leaves the native
sign exactly intact. At a hypothetical off-axis zero, the projected
normal field still has prime--Gamma value -2m. Proving that this value
must be nonnegative requires a genuine prime--Gamma positivity producer;
moment neutrality supplies none. The reduction is classified BRIDGE /
REDISCOVERED parent null-form algebra, not new scientific knowledge.
No all-order Lean result or RH result is claimed. Formalization of the
displayed native higher-jet domains/action and coupled projection is
pending; the existing simple-zero module alone does not verify them.

Verification: the current existing all-order source-jet module
XiHedenmalmThetaJetSource.lean passed a foreground
`lake --old env lean GaloisForLFunctions/RHTower/XiHedenmalmThetaJetSource.lean`
audit, terminal exit 0 without diagnostics. This verifies its actual
multiplicity/source-moment and reflection inputs, not the new native
higher-jet action or projection proof above. Both current deep searches
completed with partial=false and mostly pending/stale compiler metadata.
Their candidate lemmas, source arguments and proposed ingredient sets
were inspected. No returned statement supplied native positivity.

Anti-theatre: no scientific novelty is claimed; the new record is a
paper coupling of established source identities with causal integration
and null-form algebra. The native-sign frontier has not moved. The
useful advance is explicit preservation of every divisor jet while
carrying the two cusp moments as recoverable coefficients. Anti-laziness:
no step was omitted for estimated effort; the direct prime--Gamma
comparison was examined and remains unproved. Corpus checks were run.
Keep the positive arithmetic producer as the next hard target; merely
assuming positivity on the cusp-neutral representatives is circular.

### Native higher-jet action: formal verification in progress

The next verification target is the all-order literal arithmetic action
in the paper proof above. Polynomial causal weights require absolute
joint admission before exchanging the prime series and compensated Gamma
and pole integrals. Establish the weighted-tail bound using the open
exponential margin from Re(w) <= 1/2 to 3/4, then commute the literal
actions. No simple-zero assumption and no positive-form hypothesis may
enter this bridge. The native mixed sign remains unproved.

The current producer search completed with partial=false; refresh reports
background_indexer_running, and compiler coverage remains mostly pending
or stale. Candidate lemmas, source arguments and ingredient sets supplied
no checked native-sign producer. Formal verification is therefore not
being presented as a solution of the sign inequality.
