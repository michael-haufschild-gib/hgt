# Reflection-orbit exclusion from the actual arithmetic source

- **ID:** RH-REFLECTION-SOURCE-SIGN-20260926
- **Stage:** 1-in-progress
- **Type:** RESEARCH — no unconditional RH proof or falsification
- **Goal:** An unconditional, closed Lean proof of RH or its negation. A new criterion is not completion.
- **Constraints:** No numerical experiments; one foreground Lean process; scratch checks before a named leaf build; no full builds.

## Frozen target and route test

Prove the full arithmetic source moment form nonnegative on every real polynomial, or find an exact negative test. Corpus `ReciprocalAtomPolynomialApproximation` already converts polynomial positivity into exclusion of every free reflection orbit. The hard input is the source sign, not a missing detector. A finite minor is useful only if its proof exposes a mechanism extending to arbitrary degree.

## Scientific interrogation

- **What would a scientist do?** Identify the exact source-specific step, freeze a falsifiable mechanism, test its boundary cases symbolically, and distinguish established evidence from a proposed proof.
- **Right problem?** The source-to-sign implication is required. Reproving ordinate injectivity, orbit counting, or polynomial isolation would not advance it.
- **Where is arithmetic used?** In the exact full theta density and its modular boundary cancellations; generic positive measures and finite shell prefixes do not inherit the target sign.
- **What is being removed?** The omitted theta tail. Retain it: every nonempty finite prefix has a nonzero boundary slope whose leading Fourier contribution is canceled by the complete tail.
- **Symmetry invariant?** Reflection-even quantities can detect a free orbit, although they cannot distinguish its two orientations. Their vanishing requires an independent source proof.
- **Primitive/derived reversal under examination:** Treat full-source boundary cancellation as constitutive data for the moment form, rather than regarding the omitted tail as an error estimated in absolute value. No universal law or positive representation has yet been established.

## Research plan

1. Inspect the full-source score/Schur identities and existing no-gos.
2. Freeze and symbolically attack a mechanism that retains exact boundary cancellation at every degree.
3. Formalize only a dependency-closed result, audit its hypotheses and axioms, and record its consequence for the whole route.

## Frozen mechanism test C1: monotone-source contraction

**Classification:** derived mechanism conjecture, not a new universal RH conjecture.
For every even probability density decreasing on the positive half-line, conjecture
`0 <= B <= D`, where `B` is the sign-adjusted coefficient matrix of the
denominator-cleared logarithmic moment kernel and
`D_ij = mu_(i+j+1)/((2i+1)!(2j+1)!)` is the odd raw Gram matrix.

**Motivation:** the existing actual-theta Gram comparison card leaves this representation
open; uniform interval sources have `B=D`; existing theta diagnostics suggest contraction.
The universal claim is stronger than the actual-theta statement and has a cheap exact falsifier.

**Symbolic experiment:** mix equal amounts of uniform laws on `[-1,1]` and `[-4,4]`.
The even moments are `(1+4^(2k))/(2*(2k+1))`. Test `D-B` on coefficient
indices `{1,2}` and vector `(-13,17)`. Lean verifies the exact value
`-119221/32256`. No floating-point experiment was run.

**Positive survivor, Lean-proved:** for two uniform radii with squared radii `A,B`,
the determinant of the difference-source cleared block at indices `{1,2}` is
`(A-B)^4 * (-3*A^4+36*A^3*B-2*A^2*B^2+36*A*B^3-3*B^4)/4572288000`.
For a mixing proportion `t`, the covariance block is multiplied by `t*(1-t)`.
This gives an exact sharp boundary for that compression, not an all-degree classification.

**Whole-route consequence:** monotonicity cannot establish the proposed
positive-contraction representation. The actual theta inequality remains undecided and
would need arithmetic information beyond a decreasing density. Failure of `D-B >= 0`
does not refute `B >= 0`, and neither is an RH counterexample.

Closed mechanism and exact paper proof:
`../5-failed/monotone-source-gram-contraction.md`.

## Pivot and relevance gate

The next source-sign attack must use the exact full theta assembly in the nonlinear
cumulant form. Merely adding finite moment controls or generic shape assumptions
does not meet the route test: the existing paper countermodels in
`../2-fully-proven/theta/theta-compact-critical-strip-zero-engineering.md`
preserve evenness, strong log-concavity, finite moments, exact tails and half-density
charges while inserting a nonreal strip zero. That result remains paper-only.

No new universal conjecture is frozen here: a positive-contraction representation
with an extra unspecified theta hypothesis would merely rename the missing sign.
The exact all-order theta cumulant recurrence and boundary cancellation must instead
be tested together. No source sign has been obtained, and the RH goal stays open.

## Concrete finite-prefix falsification: Lean transfer closed

The corpus already contains a paper proof that every nonempty fixed theta-shell
prefix has infinitely many nonreal Fourier zeros (`k-rvm-finite-sixth-moment-bracket.md`,
paragraph headed “Every fixed theta-shell prefix”). This is prior research, not a new
conjecture or novelty claim. `ThetaFiniteShellNonrealZeros` now closes its concrete
entire/subquadratic-growth transfer from the literal source envelope and combines
`ThetaFiniteShellFourierBoundary` with `FiniteZeroSubquadraticTwoRayDecay`. It proves
infinitely many nonreal zeros and finitely many real zeros for every nonempty cutoff.

**Route test:** this excludes every fixed-prefix real-zero foundation, not merely
the numerically tested first two. The positive survivor is the already formalized
exact full-tail compensation. It does not supply full-source Hankel positivity.

**Verification:** scratch proof and named leaf build passed. All ten public theorem
axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
Corpus index refreshed; `scripts/formal_tools.py lint --check-generated` passes
with existing large-file warnings. No numerical experiment was used.

Exact proof and survivor: `../5-failed/theta-fixed-prefix-nonreal-zeros.md`.

## Remaining source problem

The full-source all-polynomial sign remains unproved. The finite-prefix no-go is now
closed; further fixed-cutoff certification would not establish this sign. A next
producer attempt must retain literal infinite arithmetic assembly and supply its
sign, beyond the already available recurrence, symmetry, and boundary cancellation.
No all-degree producer or new universal conjecture is claimed.

## Boundary mechanism attack

Two exact tests now close a new generic no-go. The dyadic law retains an arbitrary
anti-periodic primitive; its complete bounded solution space is reconstructed with
a geometric remainder. More strongly, continuous nonvanishing solutions with zero
mean and both normalized theta endpoint anchors realize every winding `-(2*k+1)`.
`ThetaBoundaryDyadicClassification` proves these statements in Lean. This defeats
generic dyadic winding rigidity; it does not identify the examples with the literal
theta renewal loop. The open step is the source-specific index map and its control
of the retained odd primitive.

Card and positive survivor: `../5-failed/theta-dyadic-boundary-winding-rigidity.md`.

The next source-specific attack derives the signed imaginary-axis arc charges of
the literal theta source. `ThetaCuspComplexWard` now proves
`RHTower.ThetaImaginaryArc.source_complex_ward`, closing the strip-wide differential identity.
The differentiated cusp-flatness, both exact arc charges and an unconditional
interior imaginary source zero are now Lean-closed. The negative sine charge
forces a negative source value, while the seam value is positive. Consequently
the literal source admits no exponential representation on its whole strip.
Full proof and positive survivor:
`../3-formalized/rh-theta-imaginary-arc-charge-2026-09-26.md`.
The stronger near-cusp eventual-negativity asymptotic remains paper-only.

**Route gate:** this closes the explicit source-logarithm stop test in route2.
It does not close linear boundary continuation or the source-specific winding
map. Further source-zero refinements would not supply the missing RH producer.

The dyadic and Ward leaves retain their 43 standard-only axiom audits. The three
new cusp/arc leaves add 23 standard-only public theorem audits; their named builds
pass. Corpus index regenerated; `lint --check-generated` passes with existing
large-file warnings. RH remains unresolved. No new universal producer is claimed.

The source audit also finds the global Abel pairing and continuous-`Q` one-port
formula already paper-proved in `theta-rational-cusp-boundary-law.md`, equations
(5)–(8). Reconstructing that representation is not a new producer. The remaining
attack must constrain its source-specific complex phase and distinguish it from
the dyadic arbitrary-winding examples.

## Evidence and status

Separate fact log: `rh-reflection-source-sign-2026-09-26-facts.md`.
Search outputs are discovery evidence, not compilation certificates. Existing unrelated GL3 work is outside this research scope.

## Joint cold-aperture / degree result

The refreshed frontier retires route2's Mellin-diagonal prime-2 winding mechanism (KR-R2).
The next source-sign test attacked the cooperative Gaussian moment-curvature hierarchy.
Its two endpoint regimes leave a joint cold-aperture / degree corner uncovered.

`GaussianMomentColdDegreeCorner` first supplied an exact positive-source falsifier, sharp sign
classification and signed joint limit. The literal theta transfer is now fully Lean-closed:
for every `u>0`, `L_n=(n+1/2)/u` gives

`L_n^4*S_n(-L_n) -> (log(Phi(sqrt(y))))'''(u)`.

At `u=9` the limit is strictly negative, hence actual theta curvature is eventually negative.
`RHTower.ThetaColdCorner.not_all_degree_aperture_curvature_nonnegative` has no input hypotheses.
This retires global all-degree aperture convexity as a maximum-principle input. Degree-zero GABTC
and RH remain open. The strongest positive survivor is the exact signed incoming-profile law.

Paper proof, all six formal modules and validation:
`../3-formalized/rh-cold-degree-corner-2026-09-26.md`.
No-go closure:
`../5-failed/rh-global-all-degree-aperture-convexity-root-2026-09-26.md`.
All current-turn named builds and 39 public theorem axiom audits pass. Global lint fails only on
six other unwired theta-charge modules, listed in fact F38. No git commands or numerical experiments.

**Route audit:** degree-zero GABTC would close one block, with an all-order gap still open (F39).
The decisive target remains the actual source sign at every degree.


## Positive hyperbolic-mode construction: exact failure and survivor

Frozen C3 asked whether the actual normalized potential
`V(x)=log Phi(0)-log Phi(x)` has a nonnegative quadratic term plus a positive summable family
`sum a_n(cosh(b_n*x)-1)`. The exact source envelope refutes this representation in Lean.
It also refutes every sublinear signed repair. This is one representation test; no general
Lee–Yang theorem for arbitrary cosh potentials was assumed.

The strongest positive survivor is an exact edge-mass law and unavoidable correction charge.
A positive mode source with `exp(-2x)*P(x)->pi` has frequency-2 mass `2pi`, hence
`P(x)>=2pi(cosh(2x)-1)`. The actual residual divided by `x` tends to `-9/2`.
Any exact correction negligible at the leading exponential scale must therefore have
`r(x)/x < -9/2+eps` eventually for every `eps>0`.

Paper proof, precise class, unconditional no-go and all certificates:
`../5-failed/rh-positive-cosh-potential-root-2026-09-26.md`.
Named build and all 16 public theorem axiom audits pass; latest global lint passes.
No git commands or numerical experiments. All owned jobs exited.

**Whole-route consequence:** retain the exact signed source prefactor in a future construction.
This closes C3; refining this rejected positive-mode class is not the next RH task. The source-specific
all-order Hankel sign or an exact interacting source incidence remains unproved. RH remains open.


## Local Gram realization: all fixed derivative orders excluded

The next representation test now has an unconditional source answer. Arbitrary signed
reweighting cannot realize the cleared matrix as an odd-monomial Gram matrix. More generally,
`ThetaLocalGramObstruction.theta_no_finite_local_jet_gram` excludes every fixed finite
local differential order, including arbitrary signed cross-moment coefficients.

Positive survivor: after multiplying entry (i,j) by `(2i+1)!(2j+1)!` and dividing by
moment `m_(i+j+1)`, row zero is exactly one and every fixed positive row tends to zero.
Along a common anti-diagonal this is incompatible with bounded polynomial degree;
local derivative energies necessarily have that bounded-degree property. All links,
including the descending-factorial polynomial representation, are Lean-checked.

Closed card and exact scope: `../5-failed/rh-local-gram-source-root-2026-09-26.md`.
Named build and 24 public theorem axiom audits pass. This [BRIDGE] excludes a producer
mechanism; it does not produce the remaining source sign. Nonlocal constructions and
order growing with degree remain open. The charge-line Hardy rigidity found during
this audit was already present and was not duplicated.

Latest repository gate: global lint remains red on three concurrently added charge-power
modules missing umbrella imports and API/overview staleness. The new local-Gram leaf has
no reported lint error. Other workers' files were preserved; all root-owned jobs exited.

## Nonlocal tail: exact rank obstruction and literal-source bridge

The logarithmic-Cauchy coefficient model now has a Lean-proved no-go and positive
survivor: no fixed diagonal level, nor a uniformly energy-bounded repair, gives
positivity in every rank. Its transition is pinned to a width-one window around
`2h_m`, and `2h_m-log m -> 2log 2+gamma`. The exact adverse sign pattern and
required repair cost are also proved. This is a model statement, not an RH
counterexample. See `../5-failed/rh-log-cauchy-rank-root-2026-09-26.md`.

The literal kernel bridge is now formalized and audited:
`ThetaTailCauchyAsymptotic` proves its two-term Cauchy asymptotic and eventual
strict positivity for every fixed finite distinct-node set. Full theta assembly
is retained throughout. Both named builds and all 52 public theorem axiom audits pass; final global
formal lint passes. Source proof card:
`../3-formalized/rh-theta-tail-cauchy-root-2026-09-26.md`.

**Whole-route gate:** the model and source results leave a joint rank/translation
problem. Neither fixed-rank positivity nor a pointwise vanishing correction
controls the coefficient form when rank grows. Existing quantitative source
jet bounds at order below the Morse scale are available, but their conversion
to this kernel form has not been proved. Live card:
`rh-nonlocal-tail-root-2026-09-26.md`. RH remains unresolved.

## Positive correction and uniform model repair

The literal source's next tail term is now Lean-identified as the positive
squared-Cauchy correction with coefficient 7. Its Cayley coefficient form is
an exact positive weighted difference energy, unbounded relative to ordinary
energy. This explains why the earlier bounded-repair no-go cannot eliminate
it. Exact source bridge:
`../3-formalized/rh-theta-tail-first-correction-root-2026-09-26.md`.

The new all-rank theorem proves the logarithmic-Cauchy model plus c/(u+v)^2
PSD whenever c>0 and L+log(c)>=2. Its quantitative lower bound is
[L+log(c)-2]*CauchyEnergy. At the literal correction scale, the reserve is
[log(7r/pi)-2]*CauchyEnergy, and r>=pi*exp(2)/7 suffices for model PSD.
This is a uniform producer for the explicit corrected model. The full source
remainder comparison remains unproved. Paper and formal certificates:
`../3-formalized/rh-log-cauchy-uniform-repair-root-2026-09-26.md`.

Both new named builds and all 25 public theorem axiom reports pass. Next
attack tests the exact first atom before attempting uniform source transfer;
its frozen scope is in `rh-first-atom-tail-audit-root-2026-09-26.md`.
No unconditional RH proof or falsification has been obtained.

The exact first-atom audit also closes: its normalized exp(2x) scale moment is
75/(44*pi), forcing a negative full-line center energy and a negative incoming
tail diagonal. Global bare-atom PSD is therefore false. The exact positive
invariant and paper proof are in
`../5-failed/rh-first-atom-global-tail-psd-root-2026-09-26.md`.
No positive-tail negative direction is yet proved; the analytic locality
specialization remains the next scoped test. All three new named builds and
all 38 public theorem axiom audits pass; final global formal lint passes.

## C7b/C8: the all-rank comparison must lose its strict Cauchy margin

C7b closes the previously open analytic bridge: every real tail contains a
negative finite real Gram packet for the exact first atom. The complete theta
source also has a verified analytic L2 realization; every real tail preserves
its full finite negative-index profile. Three named builds, 27 public theorem
axiom audits, and final lint pass.

C8 attacks the actual complete source. For any a and c>0, some finite nodes
x_i>a give a negative quadratic form for
`K_Phi(x,y)-c*Phi(x)*Phi(y)/(exp(2x)+exp(2y))`.
Scratch, named build, all 17 public axiom reports, and final lint pass. The proof uses
exact reflection and the incoming diagonal asymptotic, an added analytic
rank-one feature, dense tail sampling, and a Cauchy Schur complement.

**Whole-route correction:** C6 is an exact positive model, but a strictly
positive part of its Cauchy-energy reserve cannot remain in the literal source
uniformly in rank. A sharp comparison leaving zero, or another reference norm
compatible with both reflected ends, remains open. No claim that the complete
theta kernel is indefinite and no RH conclusion follows.

Closed mechanisms and positive survivors:
`../5-failed/rh-first-atom-positive-tail-psd-root-2026-09-26.md`;
`../5-failed/rh-full-theta-positive-cauchy-reserve-root-2026-09-26.md`.

## C9: charged-cusp boundary admissibility is necessary

C9 is falsified for the complete source: with q(x)=exp(2x)+exp(-2x), every
real tail and every c>0 contain a finite real negative packet for
`K_Phi-c*Phi(x)*Phi(y)/(q(x)+q(y))`. Exact phase alignment at
z_N=log(N^(-2)+2i)/2 gives source size at least A*N^5, while the actual
complex tail diagonal is at most D*N^10 and the comparison diagonal grows
at least as N^12. Analytic locality and the complex Cauchy projection carry
the obstruction to real tail samples. No sign decision for K_Phi follows.

**Whole-route correction:** symmetry and both real-end asymptotics do not
suffice for a valid comparison. The positive survivor is a complex boundary
admissibility law, with the uniform necessary rate floor
`u_N >= c*(12*pi^2*exp(-4*pi))^2/(24*486^2)` whenever
`c*|Phi(z_N)|^2 <= u_N*J(z_N,z_N)`. Nonvanishing rate is not proved sufficient.
The stronger integrated ratio tending to zero remains open; current bounds
only show a bounded ratio. Do not claim that sharpening without a new proof.

The three C9 leaves and the C8 compatibility refactor pass named builds;
all 63 public axiom reports pass. User-requested optimization preserves
statements, reduces measured Gaussian elaboration, and removes C8's import
graph from C9, with no raised limits. Exact proof, survivor, and final lint
status: `../5-failed/rh-reflection-compatible-comparison-root-2026-09-26.md`.
