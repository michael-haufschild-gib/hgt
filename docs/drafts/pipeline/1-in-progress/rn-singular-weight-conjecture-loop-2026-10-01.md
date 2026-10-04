# RN: arithmetic phase and gauge conjecture loop

- **ID:** RN-SW-2026-10-01
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** docs/reports/rh-current-frontier-map.md, Route RN; current Lean corpus.
- **Statement:** Find an unconditional arithmetic source law excluding off-real Xi spectral values, with every completed intermediate theorem checked in Lean.

## Goal and constraints

Only an unconditional Lean proof of RH or its negation completes the user goal.
No subagents, numerical experiments, added axioms, assumed RH-strength inputs,
full builds, umbrella builds, or heartbeat increases. One owned foreground Lean
process at a time. Audit finished leaf modules with `lake env lean`; use Lake's
`--old` option for necessary targeted dependency builds. Preserve unrelated work.

## Working plan

1. Audit RN source declarations and current corpus search results.
2. Conjecture a source-specific improvement; give a complete symbolic argument
   or identify its exact failure before formalizing.
3. Formalize the exact unconditional result; wire its leaf import; run leaf and
   axiom audits plus formal lint. Record actual output, not inferred success.
4. Extract positive content from failures and advance to the next conjecture.

## Baseline audit

- Frontier ledger explicitly reports RH open and separates receivers from producers.
- RN's positive renewal mass, reflection and finite deletion constraints are
  nonselective; literal square-lattice/Euler information must enter the missing law.
- `ThetaCuspSchwartzTranslationCurve.thetaCuspSchwartzTranslationCurve_hasDerivAt`
  already proves complex differentiation in the original Schwartz topology.
  `ThetaTemperedTranslationAnnihilator` already identifies original derivative
  annihilation with real and strip translation annihilation. The ledger's open
  Schwartz-curve item is stale. Do not duplicate these results.
- `ThetaWeightedHistoryProperness` constructs actual real Fourier evaluation on
  every positive theta-weight carrier with exponent below two; it supplies no
  bound uniform in the exponent.
- `ThetaTemperedEvaluationBoundary` classifies tempered Fourier evaluation:
  precisely real frequencies. This does not exclude off-real weighted modes.
- Initial search: `research 'theta renewal phase singular cofinal'`, hybrid,
  60-second budget, reported `partial=false`, 64031 indexed files, no pending
  source files; most compiler snapshots pending/stale/source-only. Search hits
  are discovery evidence, not fresh Lean verification.

## Conjecture RN-SW-1: quantitative weight boundary

Write k for the literal even positive theta source and
M(q,b) = integral_R k(x)^q exp(2 b x) dx, q>0. Proposed asymptotics:

- M(q,0) / log(1/q) tends to 1 as q tends to zero from above.
- For fixed b>0, q^b M(q,b) tends to Gamma(b)/(2 pi^b).
- M(q,-b)=M(q,b).

Reason to test: the squared norm of Fourier evaluation at z on
L2(k^(-q)dx) should be M(q,-Im z). The literal theta tail
k(x) ~ 4 pi^2 exp(9x/2 - pi exp(2x)) suggests a logarithmic versus power
boundary after the substitution u=q pi exp(2x). This derivation is a
conjecture until all errors and limiting operations have been justified.

Adversarial audit: (1) boundedness at each q gives no uniform bound;
(2) real frequencies also diverge, so boundedness alone is the wrong selector;
(3) the positive norm discards cancellation and does not distinguish Xi zeros
from other frequencies. Even a sharp norm asymptotic is not an RH proof.

Next producer question: does literal arithmetic impose the slower real-frequency
growth class on every divisor-faithful evaluation? No such bound is assumed.

## Log

- 2026-10-01 — Initialized corpus-grounded loop; no new Lean theorem yet.
  Session tools lack `update_plan`; this file is the persistent plan and log.
  Optional docs/architecture.md and docs/testing.md are absent.
- 2026-10-01 — User steering: every turn must identify RN, its hard open
  mathematical problems, and whether previous work moved them. Audit corrected
  stale metadata but did not solve the arithmetic winding or singular transport
  gate. RN-SW-1 is set aside: its anticipated norm asymptotics describe the
  obstruction without supplying an arithmetic producer. No Lean code was
  written for it. Now inspect the exact renewal phase-level equation and seek a
  literal lattice/Euler constraint that rules out its off-axis solutions.

## No-go closure

No route retired. Duplicate Schwartz-curve proposal rejected by existing corpus,
not by a mathematical obstruction. RN-SW-1 and arithmetic producer remain open.

## RN-G-2: finite-order scalar gauge rigidity

The direct producer attempts did not close the phase-level equation. The
left-half-plane renewal divisor does not supply a sign after its genus-one
correction; the corpus already proves opposite phase-crossing orientations.
The moving-cusp/totient inverse retains the unresolved zero divisor as shifted
reciprocal-zeta poles and cancels it in the seed. Neither is a confinement proof.

The next precise conjecture strengthens the existing finite-exponential-type
gauge theorem to every finite-order zero-free entire gauge. The unrestricted
growth version remains a separate conjecture; no general meromorphic second
main theorem has been verified sufficient to close it in this corpus.

Write K(w)=thetaHalfLaplace(w), H(w)=K(-w), X=K+H and
gK+g#H=X, where g#(w)=conj(g(-conj(w))). Finite-order Hadamard gives
g=exp(P), g#=exp(Q) for polynomials P,Q. Put

    W=(P'-Q')KH+K'H-KH',
    B=X'H-X(Q'H+H').

Differentiating the symmetry identity and eliminating exp(Q) gives gW=B.
Both W and B have order-one envelopes: polynomial factors, sums, products
and derivatives preserve the theta port's exp(C(1+r)log(2+r)) envelope.
At a simple critical Xi zero, X=0, X'!=0 and H!=0; hence B!=0 and W!=0.
The quotient proximity bound and Poisson estimate in
QuotientProximityBound.lean transfer this same envelope to zero-free g.
OrderOneEnvelope.subquadratic and the corpus's zero-free Hadamard theorem
then give g(w)=g(0)exp(bw). The existing thetaHalfLaplace_gauge_eq_one
applies, proving g=1.

This is a dependency-identified paper argument, pending fresh Lean verification
of each bridge. Its positive statement is uniqueness of the exact entire
half-port normalization throughout the finite-order class. It does not prove
RH or the unrestricted-growth conjecture. The remaining RH producer is still
the arithmetic phase-level confinement or divisor-faithful singular transport.

### Formalization checkpoint

- `OrderOneEntireQuotient.lean`: leaf audit passed; targeted `lake --old build`
  passed. Includes polynomial, derivative and zero-free quotient closure for
  the precise order-one envelope.
- `OrderOneEntireUnitEquation.lean`: leaf audit passed; targeted `lake --old
  build` passed. Differentiated elimination proves the order-one bound for
  finite-order units in `g A + h B = C`, with a simple zero of `C` and nonzero
  `B` there.
- Both generic leaves wired into `HTGeometry.lean`; umbrella not built.
- `ThetaHalfLineFiniteOrderGauge.lean`: leaf audit and targeted `lake --old build`
  passed. Reflected differentiation uses the corpus's exact reflection identity.
  No mathematical premise was added. Wired into `RHTower.lean`; umbrella not built.
- Scratch `#print axioms` audit passed for the three main declarations, with only
  `propext`, `Classical.choice`, `Quot.sound`. New leaves have no Lean warnings.
- Repository lint ran: ten unrelated modules lacked umbrella imports. Exact
  error names and proof certificate recorded in
  `../3-formalized/theta/rn-finite-order-half-port-gauge-rigidity.md`.
- Next producer screening: existing
  `ThetaCuspCompletedProductFiberWignerNoGo` proves literal completed first-fibre
  Wigner negativity. Termwise/product-fibre positivity is unavailable. Any next
sign argument must retain the full signed cross-fibre assembly.

## Next conjecture RN-P-3: full signed source current

The finite-order classification advances RN's normalization boundary but does
not solve either hard RH gate. Next attack must target the actual sign producer.
Write `X(w)=integral exp(wu) k(u) du` for the full literal even theta source.
Candidate source inequality:

    Re (X'(sigma+i*t) conj(X(sigma+i*t))) > 0
    for 0 < sigma < 1/2 and every real t.

An off-axis Xi zero in this half-strip would make the left side zero; reflection
covers the other half-strip. Thus this is an RH-strength producer target, not
an assumed input. For the source-moment port `E=X/2+lambda X'`, lambda>0, the
reflected norm imbalance is twice lambda times this current.

Direct bilateral expansion, symmetrization and coordinates
`a=(u+v)/2`, `b=(u-v)/2` suggest the exact source formula

    Re(X' conj X) = 4 integral_(a>0) a sinh(2 sigma a) W(a,t) da,
    W(a,t) = integral_R k(a+b) k(a-b) cos(2 t b) db.

This formula and its applicability must be checked against the corpus before
any new code. The missing mathematical statement is positivity of the full
signed integral. Do not substitute positivity of individual completed product
fibres: the corpus refutes that stronger proposal. No proof of RN-P-3 yet.

### RN-P-3 audit: no new producer obtained

- `ThetaCuspWignerProductFiberNormalForm` already proves the full current's
  absolutely convergent completed-product-fibre expansion and its positive-cone
  integral. Its `thetaCuspCofinalCoupledConeKernel_negative_witness` rules out
  pointwise positivity even after the full source is assembled. Reproving the
  expansion would not advance this problem.
- `ThetaCuspCompletedProductFiberCofinalDropRepair` proves that the higher fibres
  strictly over-repair a first-fibre seam rise. This supplies monotonicity of the
  source product, not the sign of its oscillatory transform. The completed
  first-fibre Wigner negativity obstruction remains in force.
- Tested Bessel self-adjoint energy as a possible sign producer. The existing
  `BesselOrderPolyaRealZeros` energy proof controls a single Bessel order zero.
  The assembled theta current instead has the mixed arithmetic channel in
  `ThetaWignerEisensteinCrossEnergy`. Its completed square retains an uncontrolled
  reciprocal-symbol energy. Neither result supplies the required comparison.
- The paper `theta-wigner-eisenstein-orientation-current.md`, equations
  (18m)--(18s1), already performs the full Eisenstein boundary calculation.
  The cusp correction cancels exactly, returning the derivative of the Xi
  modulus square. Maass--Selberg norm positivity does not orient this derivative.
  No new automorphic sign claim or Lean receiver was added.
- Tested prime-shift conservation as a producer of the RN normal-jet neutrality.
  `ThetaPrimeShiftNoetherCurrent.completeTheta_primeShiftWard_balance` retains
  Gamma/pole exchange and the term `-2*x*k(x)^2`; it is not the required
  neutrality law. The positive prime jump energy in
  `ThetaPrimeGammaScalingEnergy` is a diagonal-minus-cross identity, not a
  bound on the complete signed source form.
- `CCMThetaGroundRHCriterion.riemannHypothesis_iff_thetaGroundEnergyComparison`
  already identifies the missing full comparison exactly: continuous
  Gamma/pole jump energy is at most prime jump energy on every smooth compact
  source written as `k*chi`. Its strict reversal is a falsification witness.
  Repackaging that equivalence does not prove the comparison.

Assessment: this turn screened proposed mechanisms against existing proofs but
did **not** move the hard mathematical frontier. RN-P-3 remains unproved; no
route is retired, no new theorem is claimed, and no Lean source/build was added.
The useful positive statements from the rejected shortcuts are already in the
corpus and do not need duplicate formalization.

### Next attempt RN-P-4: the signed energy on a two-ended root mode

Narrow the producer attempt to a source selected by the zero equation itself.
For `XiC(z)=0`, put `U_z=-i*thetaTwoEndedSourceSolution(z)`, equivalently
the existing `sourceModeU thetaSource z`. Its two formulas are

    U_z(x) = -i exp(-i*z*x) integral_(-infinity,x) exp(i*z*t) k(t) dt
           =  i exp(-i*z*x) integral_(x,infinity) exp(i*z*t) k(t) dt.

Differentiating these integrals gives the trial profile equation for `chi_z=U_z/k`
(paper calculation here, not a newly checked Lean declaration):

    chi_z' = -(k'/k + i*z)*chi_z - i.

Producer question: can the literal prime/Gamma source equation, this forced
ODE, and both endpoint conditions prove a strict signed-energy comparison
incompatible with an off-real zero? The comparison must retain all prime
powers, the continuous cross term, and the cofinal boundary contribution.
No such estimate, admissibility bridge, or contradiction has been proved here.
In particular, a positive norm or the universal Hardy chirality of this mode
cannot replace that missing comparison; the one-port variogram paper already
shows that the latter orientation holds for generic even positive sources.

Search record: deep queries for full signed current, kernel real-zero criteria,
renewal zero-specific lattice cancellation, and root ground-energy profiles
returned partial results; the latter two reported pending coverage generations
1179979 and 1180113. No applicable sign producer was returned. A lexical
ThetaPrime query located the Ward/energy declarations above; its JSON omitted
coverage and partial fields. Source files, not search ranking, supplied the
statements recorded here. No numerical experiments were used.

### RN-P-4 continuation: keep the mixed terminal modes

User reminder: stay with the hard sign problem; missing mathematics is not a
reason to replace it with easier infrastructure. This continuation has not
proved that sign. It did not add a receiver or an admissibility-only Lean leaf.

The precise mode matters. `HedenmalmCompletedDividedEnergy` identifies the
ordinary positive L2 norm of the first divided Xi function with quantile root
energy. That is not its Weil energy. At a multiple zero, the first divided
function still vanishes at that zero. Thus strict Weil positivity of every
first divided mode would also demand simplicity, an extra unproved statement
not needed for RH.

The multiplicity-exact replacement is already available in
`GaussHodgeWeilEntireDetection` and `XiHedenmalmMultiplicityChain`. Let alpha be
a divisor point of multiplicity m and define the normalized terminal function

    F_alpha(w) = [XiC(w)/(w-alpha)^m] /
                 [XiC(w)/(w-alpha)^m]_(w=alpha),

using the removable divided chain. Its divisor values are 1 at alpha and 0
at every other support point. The denominator is nonzero. The reflection
bijection preserves multiplicity.

Directly from these values and the definition of the Weil pairing, for
nonreal alpha the two terminal functions at alpha and conj(alpha) have Gram
matrix

    m * [[0, 1], [1, 0]].

Indeed a diagonal summand could survive only at both alpha and conj(alpha),
which are distinct. In the mixed entry exactly the m copies of alpha survive.
Consequently the sum has energy 2m, the difference has energy -2m, and each
individual diagonal has energy zero. At a real alpha the individual terminal
energy is m. These are deductions from the inspected definitions and terminal
vanishing theorem, not new Lean audit claims. The existing entire odd-witness
theorem already formalizes the negative combined direction.

This rules out using nonnegative individual mode energies as the producer:
they do not detect the off-line pair. It also prevents silently replacing Weil
energy by the positive ordinary mode norm. The unchanged hard task is to prove
the full arithmetic comparison on the multiplicity-exact paired source modes,
with their mixed prime and Gamma/pole terms. No inequality establishing that
comparison has been obtained.

The forced ODE alone does not discharge it. For a link y=x+h, write
`s=k'/k`, `T chi=chi'+s*chi`, and use the conductance `k(x)k(y)`.
Integration by parts in x formally gives the score identity

    2 Re <chi,T chi>_link
      = integral k(x)k(y) (s(y)-s(x))
          (|chi(y)|^2-|chi(x)|^2) dx.

For the first mode, `T chi=-i*z*chi-i`, so its left side is
`2 Im(z) E_link(chi)` since constant profiles have zero increment. Source
log-concavity fixes the sign of `s(y)-s(x)`, but not the other difference.
Summing with the literal signed prime/continuous coefficients retains that
uncontrolled correlation. This is the remaining term in this attempted
energy proof, not an estimate that can be dropped. The displayed integration
by parts has not been promoted to a theorem without its boundary/integrability
audit; no positivity conclusion rests on it.

One ledger check tested a possible direct limit argument. The small-parameter
real-zero theorem for `thetaPowerXiC a` does not approximate Xi: the inspected
`ThetaPowerCuspConstantSplit` retains a divergent Gamma pair. Its failed-route
card already explains that subtracting this pair changes the zero problem.
No Hurwitz argument was obtained and no new code was written for this detour.

Searches `theta two ended source divided zero prime Gamma energy` and
`divided Xi Weil pairing nonreal zero null vector` returned partial results.
Their inventory snapshots covered 64091 and 64103 files respectively with no
pending source files, but predominantly pending/stale compiler metadata.
Exact source reads supplied the conclusions above. No numerical experiments,
Lean builds, or umbrella changes were made in this continuation.

### RN-P-4 continuation: the mixed cut kernel remains the producer

**Outcome:** no new sign theorem, unconditional RH proof, or falsification.
The source equation and the three-energy identity were inspected with every
Gamma, polar, and prime-power term retained. The equation supplies an exact
balance; it does not supply the missing comparison on paired terminal modes.

The attempted transfer from the prime-deletion Bernstein cone does not apply
to a divided mode. `ThetaZeroDivisionRateTomography` already proves that a
nontrivial zero-division perturbation has a signed cofinal rate density and
eventually fails complete monotonicity. This is not a reason to discard the
paired mode; it is a reason not to assert that this mode belongs to the
positive cone of the original source. No new no-go route is being retired.

An attempted finite source-derivative expansion has the same sign gap.
`TruncatedRiemannKernelWeilEnergy.paperFT_kernelComb_at_zero` already puts every
finite combination of source derivatives in the exact Weil radical. Thus,
at the level of divisor evaluations, subtracting such a combination from a
test preserves its entire Weil pairing. This does **not** justify a global
asymptotic expansion of the ground profile or a bound on its remainder.
Neither was proved here. The corpus's existing truncated-radical tail bounds
bound absolute energy, not its sign. Do not recode this observation as progress
on positivity.

The concrete next producer candidate is positivity of the literal kernel for
pairs of cuts. Write `k = thetaCuspFullSource`,

    b(h) = 2 cosh(h/2) - exp(-h/2)/(1-exp(-2h)),
    a_n = vonMangoldt(n)/sqrt(n),
    d = |x-y|, l = min(x,y), r = max(x,y),
    A_h(x,y) = integral_[r-h,l] k(t) k(t+h) dt  if d<h,
               0                             otherwise,
    B(x,y) = sum_(n>=2) a_n A_(log n)(x,y)
             - integral_(h>0) b(h) A_h(x,y) dh.

This is the proposed polarization of the jump form on threshold profiles
`H_x(t)=1_(x<t)`: both jumps are one precisely for `r-h<t<=l`.
On the diagonal it matches the existing crossing-current formula
`B(x,x)=J(x)=integral_(t>x) 2t k(t)^2 dt>0`.
The hard assertion is the full finite-matrix inequality

    sum_(i,j) conj(c_i) c_j B(x_i,x_j) >= 0

for all thresholds and coefficients, proved from the displayed arithmetic
expression. Its first mixed test is `|B(x,y)|^2 <= J(x)J(y)`. Neither this test
nor the all-rank assertion has been proved. Positive diagonal values do not
imply either assertion. A passage from step profiles to the smooth CCM domain
also needs a convergence proof; it must not be silently assumed. These are
paper definitions and a producer conjecture, not a new Lean criterion.

The source Ward equation controls the diagonal derivative `J'=-2xk^2`.
Direct differentiation of the off-diagonal expression instead retains
truncated prime/Gamma convolutions. At gaps `|x-y|=log(n)` the prime terms
also require one-sided treatment. No closed positive evolution for `B` was
obtained. The next attempt must attack these full mixed convolutions, rather
than estimate the already-positive diagonal or improve absolute tail bounds.

Four corpus searches in this continuation returned partial results; usable
source declarations were inspected directly. Newly inspected material also
included `CCMThetaArithmeticLocalization` (exact, signed localization errors)
and the opening/source-radical portions of `RiemannKernelWeilRadical` and
`TruncatedRiemannKernelWeilEnergy`. No numerical experiments or Lean code
changes were made. This continuation clarified unsuccessful sign arguments
but did not advance the proven RN positivity frontier.

### RN-P-4 continuation: factorization and translated-source test

Previous turn classified **no progress** on the hard positivity producer.
Current-state frontier-map and log reads still leave the full mixed comparison
open. The search `theta mixed cut kernel prime Gamma factorization` returned
partial results; no applicable positive factorization was found.

The attempted factorization keeps `B = B_prime + B_Gamma - B_polar`.
For an exponential continuous link coefficient `exp(-r h)`, its off-diagonal
cut integral factors, for `x<=y`, into

    (integral_(s<x) exp(r s) k(s) ds)
      * (integral_(t>y) exp(-r t) k(t) dt).

The Gamma coefficient is the sum of these exponentials with
`r=2j+1/2`; the polar coefficient uses `r=1/2` and `r=-1/2`.
This algebra retains the sign of the subtraction: separate positivity of
the three link forms does not compare them. It is not a positive
factorization of their difference. No exchange-of-sums/integrals theorem or
new sign theorem was claimed from this paper calculation.

A second attempt uses the source equation on a finite combination of literal
translates. Its prospective half-line bilinear current leads to the kernel

    H(x,y) = integral_(s>0) (x+y+2s) k(x+s) k(y+s) ds.

The corpus already defines exactly this function as
`thetaTailFirstMomentKernel`; its shift-tail formula, pointwise nonnegativity,
reflection symmetry, and finite separated-packet positivity are existing
results. A new bridge to a cut Weil form would not by itself solve the
missing matrix sign, and was not coded. In particular the mixed kernel here
is `H`; it must not be identified with the earlier threshold kernel `B`
solely because their diagonal entries agree.

The proposed common-translation propagation of `H` is definitively unavailable:
`ThetaTailCommonTranslationLoewnerNoGo` gives its negative derivative as

    G_a(x,y) = (x+y+2a) k(x+a) k(y+a).

The determinant at distinct nodes is
`-(x-y)^2 k(x+a)^2 k(y+a)^2 < 0`. This is already formalized in the corpus,
not a new result from this continuation. Integrating that indefinite generator
cannot be justified as an integral of positive matrices. Its negative
determinant does not assert that `H` itself is indefinite.

The next sign attempt must therefore treat the complete square-lattice source
inside the full quadratic form. Fixed-rank far-tail positivity, entrywise
positivity, and positive diagonal currents cannot replace an all-rank sign
proof. No new Lean theorem, source edit, build, numerical experiment, or
unconditional RH conclusion was obtained in this continuation. The failed
factorization is recorded to prevent reusing it as a positivity argument.

### RN-P-5: endpoint commutator comparison, literal-source test

The exploratory CP-3 card confused the sign of the endpoint double
commutator. Writing `C_j(x,y) = integral_(s>0) s^j k(x+s) k(y+s) ds`,
the exact identity is

    H = 2 sqrt(X) C_0 sqrt(X) + D_0 + 2 C_1,
    D_0(x,y) = (sqrt(x)-sqrt(y))^2 C_0(x,y).

Thus `2 C_1 >= -D_0` is sufficient; the previously proposed `2 C_1 >= D_0`
does not imply positivity by this identity. The card now records that
correction. Neither inequality has been proved.

New conjecture, grounded in `ThetaTailCauchyAsymptotic` and
`ThetaTailCauchyFirstCorrection`: both `2 C_1 - D_0` and `2 C_1 + D_0`
have negative quadratic forms on the actual two-node pattern `(r,r+1)`
for all sufficiently large `r`, although the full `H` matrix there is
positive definite by the corpus theorem. This tests a genuine proposed
positivity producer, not a generic toy source.

Paper mechanism to formalize: put `A=pi*(exp(2x)+exp(2y))`,
`P(r)=k(x+r)k(y+r)`, `E(r)=exp(-2r)`, `D(r)=E(r)P(r)`.
The missing tail-mass asymptotic is

    (C_0(x+r,y+r)/D(r) - 1/(2A))/E(r) -> 7/(4A^2).

It follows by l'Hopital from the existing `baseSlope_error_div_exp_limit`.
Together with the existing first correction for `H`, it yields
`r C_1(x+r,y+r)/D(r) -> 0`. Rationalizing the square roots gives
`r D_0(x+r,y+r)/D(r) -> (x-y)^2/(8A)`.
Normalized coefficients `(1/k(r), +/-1/k(r+1))` should then give a strictly
negative limit for the appropriate comparison. This was the initial proof
plan; the completed audit below needs only a positive lower bound for the
commutator term. The positive survivor must retain
the full `H`, rather than either endpoint commutator remainder.

Completed (2026-10-02): the new leaf
`ThetaTailEndpointCommutatorObstruction.lean` proves both comparison failures
on the actual theta source, the tail-mass first correction, its leading limit,
the exact `H = (x+y+2r) C_0 + 2 C_1` identity, and `r C_1/D -> 0`.
The common-shift lemmas identify every moving-cut moment with the zero-cut
moment at the translated nodes. The joint positive survivor states that
the full kernel is positive definite on the same packets.

Audit evidence:

- `lake --old build GaloisForLFunctions.RHTower.ThetaTailEndpointCommutatorObstruction`
  passed; only this target was requested.
- Final `lake env lean GaloisForLFunctions/RHTower/ThetaTailEndpointCommutatorObstruction.lean`
  passed without warnings. The leaf is wired into `RHTower.lean`.
- `/tmp` axiom/name audit passed. The first-correction, moment-decomposition,
  negative-packet, and joint-survivor theorems use only `propext`,
  `Classical.choice`, and `Quot.sound`. No added axioms or premises.
- `scripts/formal_tools.py lint` failed on twelve unrelated unreachable
  modules: `CCMApertureChainProfile`, `CCMApertureTranslationChains`,
  `CCMExponentialRampPrimeMoment`, `CCMExponentialRampSourceDissipation`,
  `CCMExponentialRampTerminalEntropy`, `CCMRetainedChainKernelLower`,
  `MobiusDivisorCriticalLogProfile`, `MobiusDivisorCriticalLogProfilePrimitive`,
  `MoebiusMollifiedCriticalMoment`, `MoebiusMollifiedErrorThreeLines`,
  `ThetaMovingShellFirstOrderPhase`, and `ZetaZeroDensityPowerSaving`.
  The new leaf was not flagged.

The failure and strongest retained statement are recorded in
`../5-failed/theta-endpoint-commutator-comparisons.md`; the original CP-3 card
now marks both signs falsified. This is new literal-source knowledge, not
a proof or falsification of RH. The hard RN obligation remains full mixed
positivity for arbitrary finite families. Its next producer must retain
the leading endpoint Gram term and the signed remainder together; neither
endpoint remainder alone can supply positivity.

### RN-P-6: complete two-point comparison in squared coordinates

Previous turn is progress: both literal-source CP-3 comparisons are now
formally excluded, with the full-kernel positive survivor retained.
The hard all-rank RN sign remains open. Current source searches and the
frontier map confirm no producer of the full mixed sign. The channel-Gram
difference is already in the corpus and is not itself a sign proof.

New positive conjecture, based on
`ThetaCuspLogFourthNegative.iteratedDeriv_four_thetaCuspLogSource_neg_all`
(actual namespace `RHTower`) and the complete tail-kernel integral:
every two distinct positive real nodes have a positive definite full
theta tail matrix, without a separation or large-translation condition.
Existing `ThetaTailSeparatedPacketPositivity` only gives a comparison
with a separation factor; the proposed statement removes that restriction.

Paper proof mechanism: let `f=log k`. Evenness gives `f'(0)=f'''(0)=0`.
The proved `f''''<0` implies `f'''<0` on the positive ray, hence
`d/dx (x f''(x)-f'(x))=x f'''(x)<0`. Thus
`u -> f(sqrt u)` is strictly concave for `u>0`.

For `x>=y>0`, `s>0`, set `t=s*(x+y+s)`. The pairs

    ((x+s)^2, (y+s)^2),  (x^2+t, y^2+t)

have equal sum, and the first is more spread out. Squared-coordinate
log-concavity therefore gives

    k(x+s) k(y+s) <= k(sqrt(x^2+t)) k(sqrt(y^2+t)),

strictly when `x>y`. The Jacobian is `dt=(x+y+2s)ds`, exactly the full
tail-kernel weight. Cauchy--Schwarz in `dt` then gives

    H(x,y)^2 <= H(x,x) H(y,y).

The strict off-diagonal version would give positive definiteness. This is
not yet Lean-audited. The key difference from the failed CP-3 comparison is
that the full weighted integral is kept. Entrywise domination by the new
Gram kernel does not imply all-rank PSD, so that implication must not be
claimed. The all-rank producer remains the final hard obligation.

Equivalent proof chosen for Lean: use the diagonal current `J(x)=H(x,x)`
already formalized as `thetaPrimeGammaCutEnergy`, with
`J'=-2x k(x)^2`, `J>0`, and `J(+infinity)=0`.
The strict increase of `p(x)/x`, `p=-(log k)'`, implies by integrating
`2p(t)k(t)^2 > (p(x)/x) 2t k(t)^2` over `t>x` that

    (p(x)/x) J(x) < k(x)^2.

Hence `R(x)=k(x)/sqrt(J(x))` is strictly increasing for `x>0`.
For fixed `0<x<y`, the full difference

    F(s)=sqrt(J(x+s))*sqrt(J(y+s))-H(x+s,y+s)

has exact derivative

    -sqrt(J(x+s))*sqrt(J(y+s))
      *(R(y+s)-R(x+s))*((y+s)R(y+s)-(x+s)R(x+s)) < 0.

All three original terms tend to zero at infinity. Thus `F(s)>0` for
`s>=0`, proving strict two-point Cauchy--Schwarz for the complete kernel.
This avoids a new substitution framework while proving the same structural
positive statement. Lean work is in `ThetaTailTwoPointPositivity.lean`;
currently unfinished and unwired.

Stronger paper conjecture RN-P-6b: **all distinct real node pairs**, including
the seam-crossing case, have a strictly positive full-kernel minor. This is
forced by retaining the already-proved evenness of `J` and `k`: `R` is even
and strictly increasing on `[0,infinity)`. If `x<y` and `x+y>=0`, then for
every `s>0`, `|x+s|<y+s`, so both factors in the displayed derivative are
strictly positive, including when `x+s<0`. The same decreasing-gap proof
works. If `x+y<0`, use the exact kernel reflection on `(-y,-x)`. This is
the current Lean target; no rank-three or all-rank conclusion is inferred.

The analytic core and unconditional quadratic/matrix PSD capstones of
RN-P-6b passed `lake env lean` on 2026-10-02 without warnings. The leaf is
wired into `RHTower.lean`; targeted
`lake --old build GaloisForLFunctions.RHTower.ThetaTailTwoPointPositivity`
passed, including the required fourth-log-derivative source dependencies.
The `/tmp` axiom audit of all seven main public results passed with only
`propext`, `Classical.choice`, and `Quot.sound`. Final
`lake env lean GaloisForLFunctions/RHTower/ThetaTailTwoPointPositivity.lean`
passed without warnings after those checks. No added axioms or premises.
Formal lint found no error in this leaf, but failed on thirteen unrelated
unreachable modules: `CCMApertureChainProfile`, `CCMApertureTranslationChains`,
`CCMExponentialRampPrimeMoment`, `CCMExponentialRampSourceDissipation`,
`CCMExponentialRampTerminalEntropy`, `CCMFiniteEulerDenominator`,
`CCMRetainedChainKernelLower`, `CCMScatteringEulerCurrent`,
`MoebiusMollifiedCriticalMoment`, `MoebiusMollifiedErrorThreeLines`,
`ThetaCuspCurvatureDefectGrowthTransferFlow`, `ThetaMovingShellFirstOrderPhase`,
and `ZetaZeroDensityPowerSaving`. No unrelated module was edited to clear it.

### RN-P-7: Schur residual orientation for the literal source

The two-point result is progress, but does not establish the all-rank sign.
The next conjecture attacks that precise gap, keeping the complete kernel.
The deep corpus query `theta tail Schur complement residual source positivity`
returned partial results (64,313 indexed files; compiler enrichment largely
pending/stale/source-only). Its candidate lemmas and source arguments did not
supply the required producer. A lexical `Schur` query and the actual
`ThetaTailCauchyCoercivityObstruction` source distinguish the existing Cauchy
reserve obstruction from the proposed full-kernel residual sign. No assertion
of exhaustive search or a new all-rank theorem is made.

Let `x_1<...<x_n<y` all be positive, and translate every node by `s>=0`.
Put `M_ij(s)=H(x_i+s,x_j+s)`, `h_i(s)=H(x_i+s,y+s)`,
`u_i(s)=k(x_i+s)`, `v_i(s)=(x_i+s)k(x_i+s)`, and `c=M^{-1}h`
where the leading block is positive definite. Define

    A(s)=k(y+s)-u(s)^T c(s),
    B(s)=(y+s)k(y+s)-v(s)^T c(s),
    S(s)=H(y+s,y+s)-h(s)^T M(s)^{-1}h(s).

Differentiating the already-proved common-translation identity gives the
exact paper identity `S'=-2*A*B`. This is a calculation with the literal
kernel, not a new premise-free sign theorem. The candidate producer is
`A>0` and `B>0` for every positive ordered node family. Together with
the existing fixed-pattern far-tail positivity and its asymptotics, such
a producer would inductively retain positivity down to every positive cut.
The corpus's analytic-locality receiver would then address all real cuts.

The new RN-P-6b theorem proves the first residual step on paper:
`R(x)<R(y)` and `H(x,y)<sqrt(J(x)J(y))` imply
`H(x,y)*k(x)<J(x)*k(y)`, hence `A>0`; then
`J(x)*B=(y-x)*J(x)*k(y)+x*(J(x)*k(y)-H(x,y)*k(x))>0`.
For larger blocks, pairwise inequalities do not control the signs of
`M^{-1}h`. The genuinely open task is a source-specific sign law preserved
under this projection. No conditional RH wrapper is being added to Lean.
Do not extend the candidate to arbitrary negative cuts: reflection changes
the individual residual orientation, even though two-node positivity survives.

Further corpus check: the lexical `thetaTailFirstMomentKernel derivative Gram`
query had no hits; after removing `Gram`, the `thetaTailFirstMomentKernel deriv`
query returned the common-shift derivative theorem already used above.
`ThetaTailGermExpansion` concerns far-tail primitive/symbol expansions, not
the mixed kernel jet sign needed for this induction. These checks supply no
higher-rank sign producer and do not certify exhaustive absence.

RN-P-6/6b is recorded in stage 3 as
`theta/rn-full-tail-two-point-positivity.md`, and the RN frontier-map entry
records both this positive result and the prior endpoint-comparison
obstruction. All owned scratch probes/search outputs were removed, and all
owned builds/searches exited. This turn is progress: literal-source two-node
positivity is now unconditional and domain-unrestricted. RH remains neither
proved nor falsified; RN-P-7 is the unresolved all-rank producer, not a claim
of completion.

### RN-P-7a: test the proposed all-order curvature mechanism

This turn continues the all-rank Schur-sign problem. Direct differentiation
of its residuals produces an additional projected source-score term; the
proved scalar increase of `p(x)/x` does not bound that signed term. No
preservation theorem or falsification of RN-P-7 itself has been obtained.
The current deep Schur search was partial (64,325 indexed files, compiler
metadata largely pending/stale/source-only) and supplied no applicable
all-rank sign producer. The Riccati countermodel's fourth cumulant lower
bound is not an upper sign bound for the literal source and cannot be used
to dismiss or prove the proposed induction.

A concrete branch to test is eventual nonpositivity of all even logarithmic
center jets, extending the successful fourth-derivative sign. The corpus's
`ThetaImaginaryArc.exists_imaginary_source_zero` instead forces a finite
Taylor radius for the even meromorphic germ `z*k'(z)/k(z)`. This germ is
analytic at every real point because the literal source is positive there.
Vivanti--Pringsheim should therefore exclude either eventual coefficient
orientation: after subtracting a finite Taylor polynomial, a one-signed
tail would force a singularity on the positive real ray. Its coefficient
of degree `2m` has the sign of `(log k)^(2m)(0)` for `m>0`.

Paper target: arbitrarily high even logarithmic center jets of the actual
source have both signs. This would falsify the all-order one-sign curvature
branch, with an infinite signed-jet survivor, while leaving the actual
Schur-product conjecture open. The proof must use the retained literal
source zero and analytic continuation, without numerical jet evaluation.
The corpus's `LiEvenCrossEulerJetOscillation` already has the global
meromorphic version of the Pringsheim argument; its private helpers need
a strip-local adaptation for this source. The existing native-center jet
oscillation theorem concerns the source square, not its logarithm.

The strip-local paper proof is now recorded in stage 2 as
`rn-logarithmic-center-jet-oscillation.md`; its complete Lean leaf is under
foreground audit. The finite Taylor radius is proved from the actual nonzero
residue, not postulated. Finite polynomial subtraction preserves that radius,
so the argument excludes eventual signs rather than just an all-index sign.

For the next direct RN-P-7 attack, retain the exact projected-score system.
Put `α=uᵀM⁻¹u`, `β=uᵀM⁻¹v`, `γ=vᵀM⁻¹v`,
`W=k'(y+s)-u'ᵀc`, and
`C=(y+s)k'(y+s)-(diag(x_i+s)u')ᵀc`. Then
`c'=-M⁻¹(v A+u B)`, `A'=W+β A+α B`, and
`B'=C+(1+γ)A+β B`, alongside `S'=-2 A B`.
These identities are derived on paper wherever the existing leading block
is positive definite. The genuinely missing producer is a signed projection
estimate for `W,C` preventing an adverse first crossing of `A B`; neither
pairwise positivity nor eventual even-curvature signs supplies it. No
conditional matrix-identity wrapper is being counted as frontier progress.

RN-P-7a audit update: the full new proof plus API-name checks passed
`lake env lean /tmp/rn_log_jet_check.lean` with exit 0. The source leaf
`ThetaCuspLogJetOscillation.lean` is wired in `RHTower.lean`; its targeted
`lake --old build` passed. The axiom audit of all five public theorems passed
with only `propext`, `Classical.choice`, and `Quot.sound`. Final direct leaf
audit passed with exit 0 and no output:
`lake env lean GaloisForLFunctions/RHTower/ThetaCuspLogJetOscillation.lean`.
The retired branch and exact formalized survivor are now
recorded in `5-failed/theta-logarithmic-one-sign-curvature.md`.
Formal lint found no new-leaf issue, but failed on 11 unrelated unreachable
modules: CCMApertureChainProfile, CCMApertureTranslationChains,
CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation,
CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower,
MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines,
Sieve.VonMangoldtTwistPolynomialWindow, ThetaMovingShellFirstOrderPhase,
and ZetaZeroDensityPowerSaving. Their unfinished work is outside this leaf.

The new projected-score deep search finished with 64,346 indexed files,
no applicable sign producer, and compiler metadata mostly pending/source-only;
semantic coverage was unmeasured and refresh still background-incomplete.
The exact `ThetaCuspAllRankNativeTail` source theorem was also inspected:
each finite native shifted Hankel matrix is positive beyond a threshold
depending on rank and shift. This neither signs the full first-moment
kernel on the compact region nor makes the tail threshold uniform in rank.

Next direct RN-P-7 attack: use the actual projected-score system at a first
loss of residual positivity while moving backward from the far tail. Its
orientation matters: at an actual boundary `A=0, B>0`, the strict barrier
would be `W+α B<0`; at `B=0, A>0`, it would be
`C+(1+γ)A<0`. These would contradict the nonnegative forward derivative at
the first backward exit. Simultaneous vanishing still needs treatment;
the induction hypothesis must retain positivity of the leading block so
that its inverse remains defined. These are conjectural boundary
estimates for the literal integral projection `c=M⁻¹h`, not estimates for
arbitrary interpolation coefficients and not a claim that `A` or `B` is
globally decreasing. The verified logarithmic-jet theorem rules out the
one-sign all-even shortcut; it does not refute these boundary estimates.

RN-P-7a is complete as a route obstruction with a formalized nontrivial
survivor. Public capstones: `ThetaLogJet.logJet_cofinal_positive` and
`ThetaLogJet.logJet_cofinal_negative`; supporting `radius_lt_strip` and
both coefficient cofinality theorems are also audited. No axiom, numerical
experiment, raised heartbeat, or full umbrella build was used. The RN
frontier map records the new theorem. All owned search/build/audit processes
are terminal; owned scratch files were removed. RH is still neither proved
nor falsified. RN-P-7 remains the direct unresolved all-rank problem.

### RN-P-7b: actual simultaneous residual zeros

The next attack retains the literal projection rather than arbitrary signed
coefficients. The deep residual query (64,356 indexed files, compiler data
largely pending/source-only; semantic coverage unavailable and refresh
background-incomplete) found no applicable simultaneous-zero theorem.

For the first higher projection, take `0<x₁<x₂<y`, normalize
`L(x,z)=H(x,z)/(k(x)k(z))`, and suppose both actual residuals vanish.
The two endpoint equations force
`c₁ k(x₁)/k(y)=(x₂-y)/(x₂-x₁)` and
`c₂ k(x₂)/k(y)=(y-x₁)/(x₂-x₁)`.
The actual normal equations then force both

    L(x₁,y)=a L(x₁,x₁)+b L(x₁,x₂),
    L(x₂,y)=a L(x₂,x₁)+b L(x₂,x₂),

with these same affine weights `a<0`, `b>1`, `a+b=1`.
This paper reduction identifies the concrete source burden: exclude a
common affine-extrapolation intersection of the two actual rows. It is
not being counted as a new sign theorem or a solution. Uniform row
convexity/concavity must be tested, not assumed from two-node positivity.

RN-P-7b row test: the literal kernel's existing first correction yields a
counterexample to both uniform row-curvature orientations, on paper and
without evaluating any jets. For `L=H/(k k)`, `E(r)=exp(-2r)`, and `h>0`,
put `v=exp(2h)`. The centered row gap divided by `E(r)` tends to
`-h(v-1)/(2π(1+v))<0`. The adjacent right gap divided by `r E(r)` tends
to `(v-1)^3/(2π(1+v)(1+v²))>0`. The same far positive row therefore has
both midpoint-gap signs. This is a structural obstruction to using
individual row convexity in the simultaneous-zero argument, not an
optimization of a tail bound. The paper proof and positive survivor are
recorded in `5-failed/theta-tail-uniform-row-curvature.md`; new
leaf `ThetaTailNormalizedRowCurvature.lean` is fully audited and wired.
The actual coupled two-row intersection exclusion remains open.

The complete row-curvature leaf passed the targeted `lake --old build`,
the four-capstone axiom audit (only `propext`, `Classical.choice`, `Quot.sound`),
and final `lake env lean GaloisForLFunctions/RHTower/ThetaTailNormalizedRowCurvature.lean`
with exit 0 and no output. No change to the all-rank conjecture is asserted.

A positive replacement, derived on paper for the next source attack, is
strict decrease of `L(x,y)` as the larger endpoint `y≥x≥0` increases.
The ratio `p(z)/z` already proved strictly increasing should supply it.
For `a(t)=k(x+t)k(y+t)/(k(x)k(y))`, write `P(t)=p(x+t)+p(y+t)`
and `s(t)=x+y+2t`. Differentiation followed by the exact boundary identity
`∫(a-tP a)=0` gives

    ∂ᵧL(x,y)=∫ a(t)[t P(t)-s(t)(p(y+t)-p(y))] dt.

The bracket is strictly negative for `t>0,y>0,x≤y`: use
`p(x+t)/(x+t)≤p(y+t)/(y+t)` first, then
`p(y+t)/(y+t)>p(y)/y`. This source-specific comparison does not require
uniform row convexity. Differentiation/integrability and the alternative
finite common-shift-plus-gap comparison remain to be audited against the
corpus before calling the monotonicity theorem proved in Lean. This is
stronger than the already obtained endpoint comparison `L(x,y)<L(x,x)`.

The ordered-row-decrease paper proof is now written in
`2-fully-proven/rn-ordered-normalized-row-monotonicity.md` (RN-P-7c),
including the uniform local domination and the vanishing integration-by-parts
boundary. Lean is still pending. The direct formula for the derivative is
the preferred proof path; it needs only the already proved `p(z)/z` increase.
The alternative common-shift-plus-gap path would require additional convexity
of `p'` and should not be silently inferred from `p(z)/z` increase alone.

Row-curvature lint audit: 12 unrelated unreachable modules remain:
CCMApertureChainProfile, CCMApertureTranslationChains, CCMEulerBoundaryQuotient,
CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation,
CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower,
MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines,
ThetaCuspInheritedOddCompensationBoundary, ThetaMovingShellFirstOrderPhase,
and ZetaZeroDensityPowerSaving. No new-leaf lint issue. All owned processes
are terminal; owned scratch files were removed. RH remains unproved and unrefuted.

### RN-P-7c formalization in progress

The complete positive row-decrease proof is now in the new leaf
`ThetaTailOrderedRowMonotonicity.lean`, pending Lean checks. Its analytic
ingredients are local dominated differentiation of the literal common-tail
integral and the exact vanishing integral of `(t k(x+t)k(y+t))'`.
No new source hypothesis is introduced. Strict negativity reduces to the
two already-proved comparisons of `p(z)/z`.

The next mathematical gap is a *coupled* row-drop comparison. With two
earlier nodes, normalized entries `Lij`, and `y>x₂`, the first source
residual has the sign of

    (L11-L12)(L22-L2y) - (L12-L22)(L12-L1y).

This follows by expanding the two-by-two inverse numerator. Individual
row decrease does not determine its sign. Seek source-specific control of
these coupled drops; do not claim the monotonicity theorem closes the
higher-rank residual problem.

RN-P-7c: the targeted `lake --old build` passed. Both public theorem axiom
audits report only `propext`, `Classical.choice`, `Quot.sound`. The final
direct leaf audit is running; umbrella import is wired.

### RN-P-7d: simultaneous-zero transversality

New paper proof in `2-fully-proven/rn-two-node-simultaneous-port-transversality.md`;
Lean implementation `ThetaTwoNodePortTransversality.lean` awaits its first
check. At `A=B=0` with two earlier nonnegative nodes, normalized coefficients
are exactly the affine-extrapolation weights. Strict convexity of `p` and
`x*p(x)`, obtained from the corpus's second/third/fourth logarithmic signs,
forces `W<0` and `C<0`. Both ports cross with the same orientation, so this
corner cannot locally enter `AB<0`. This is independent of the uniform row
curvature shortcut that failed.

The live barriers remain `W+αB<0` at `A=0,B>0` and `C+(1+γ)A<0` at
`B=0,A>0`, followed by arbitrary-node projection control. Negative free
terms alone do not dominate these positive feedback terms. The formal
free-derivative theorem will not be reported as a full Schur-flow proof.

Search audit: the 60-second deep row-difference/Schur query was partial,
coverage pending, compiler metadata source-only, refresh incomplete.
All returned candidate/source names were inspected; no applicable coupled
row theorem appeared. Targeted lexical `Schur residual --module Theta`
returned unrelated Hawking/prime-arch moment results; the exact decay-slope
convexity query had no hits. The new argument uses directly inspected
actual-source theorems, not an asserted absence from an incomplete index.

RN-P-7c and RN-P-7d completion audit: both leaves passed targeted
`lake --old build` and final direct `lake env lean <leaf>` audits with
no leaf diagnostics. All six public theorem axiom audits report only
`propext`, `Classical.choice`, `Quot.sound`. Both imports are wired.
Cards moved to `3-formalized/theta/rn-ordered-normalized-row-monotonicity.md`
and `3-formalized/theta/rn-two-node-simultaneous-port-transversality.md`.
The latter formalizes source signs and coefficient elimination; the full
Schur-flow continuation is still paper work, not a completed Lean theorem.

RN-P-7e now tracks the actual single-zero barriers in
`1-in-progress/rn-two-node-schur-single-zero-barriers.md`. This turn did
advance the route: row decrease and both simultaneous-zero source signs
are now kernel-checked. The next attack must use `Mc=h` to dominate the
positive inverse-matrix feedback; the new free-source signs alone cannot.

Latest formal lint still fails on 12 unrelated unwired leaves:
CCMApertureChainProfile, CCMApertureTranslationChains,
CCMEulerBoundaryKernelShell, CCMEulerBoundaryNonFredholm,
CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation,
CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower,
MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines,
ThetaMovingShellFirstOrderPhase, ZetaZeroDensityPowerSaving.
Neither new RN leaf is implicated. No full umbrella build was run.
RH remains unproved and unrefuted; the goal stays active.
All owned processes are terminal. The 17 owned scratch/audit/search files
from this turn were removed after preserving the results above.

### RN-P-7e/f: exact axis forcing and failed source-only extension

Previous turn classified as progress: ordered row decrease and corner
free-source signs were built, wired and audited. This turn inspected the
current card/frontier and re-searched the actual tail Schur problem.
The deep search was partial (64,396 files inventoried; most compiler
metadata pending/source-only/stale; refresh incomplete). All candidate
and source-result names were inspected; no direct actual-tail barrier
theorem was found. This is not a corpus-wide absence claim.

New paper proof gives `W=jA-sB-k(y)E`, `C=rA-tB-k(y)F`, with positive
strict extrapolation defects `E,F`. It falsifies the source-only extension
of the corner orientation: for each `0<x₁<x₂<y`, explicit coefficients
give `A>0,B=0,W>0,C>0`. They are not actual projection coefficients.
Positive survivor: exact affine classification, `W<0` on `A=0,B≥0`,
and both free signs negative on `B=0` when `x₁=0` regardless of A.
New leaf `ThetaTwoNodePortBoundaryClassification.lean` passed all but one
unnecessary `dsimp` in its first check; that was removed and the targeted
`lake --old build` is running. No claimed RH or actual-barrier closure.

The actual hard comparisons are now exactly `(α-s)B<k(y)E` and
`(1+γ+r)A<k(y)F` on their respective axes. Scalar row decrease does not
supply these inverse-matrix comparisons. The full projection equations
and integral orthogonality must enter; local source signs alone cannot.

RN-P-7f complete: targeted `lake --old build` passed; the final direct
`lake env lean GaloisForLFunctions/RHTower/ThetaTwoNodePortBoundaryClassification.lean`
audit exited 0 with no diagnostics. All eight public axiom audits report
only `propext`, `Classical.choice`, `Quot.sound`. Import wired. No actual
Schur barrier has been refuted: the constructed coefficients are arbitrary.

RN-P-7g paper proof now in `2-fully-proven/rn-two-node-signed-sturm-energy.md`.
For the actual old-node span, `f'=jf-sv` yields
`cᵀMc=f(0)²/s(0)+∫w f²`, with `w=2j/s+(1/s)'`.
Monotonicity of s makes the reciprocal derivative integrable, and Schwartz
decay closes the boundary term. The actual source representer G obeys
`α-s(0)=-(s(0)/α)∫wG²`. Projection orthogonality gives a second exact
weighted integral identity against the residual. This provides a direct
source integral for the missing inverse-matrix term. The compensating sign
comparison remains open, and w is strictly negative at a center anchor.
Do not replace it by a positive density. Lean for these integral identities
is pending. Mathlib discovery found
`MeasureTheory.integrableOn_Ioi_deriv_of_nonpos'` in IntegralEqImproper,
lines 901ff, which supplies the reciprocal-derivative integrability once
its finite monotone limit is formalized. This is the next concrete step.

Latest lint: ten unrelated unwired leaves remain (CCMApertureChainProfile,
CCMApertureTranslationChains, CCMExponentialRampPrimeMoment,
CCMExponentialRampSourceDissipation, CCMExponentialRampTerminalEntropy,
CCMRetainedChainKernelLower, MoebiusMollifiedCriticalMoment,
MoebiusMollifiedErrorThreeLines, ThetaMovingShellFirstOrderPhase,
ZetaZeroDensityPowerSaving). No new-leaf lint issue. All owned processes
are terminal; the nine owned scratch/search/audit files are removed below.
RH remains unproved/unrefuted; goal remains active.

### RN-P-7g formalization and RN-P-7h actual feedback conjecture

`ThetaTwoNodeSignedSturmEnergy.lean` now contains the exact signed-energy
and inverse-Gram representer identities, pending a clean leaf audit.
The density is proved strictly negative at a center anchor. The proof
retains the finite reciprocal-secant limit and establishes integrability
against arbitrary squared two-translate packets.

New paper proof: `2-fully-proven/rn-actual-center-feedback-positive.md`.
Strict convexity of p gives `p'(0) H(0,0)<k(0)²` by a positive integral.
The actual inverse-Gram square decomposition gives
`α(0,z)≥k(0)²/H(0,0)`. Since `p(z)/z→p'(0)`, actual feedback excess is
strictly positive for all sufficiently small positive z. This rules out
the universally nonpositive feedback shortcut using actual coefficients,
and forces negative signed energy for their representers. It does not
settle the compensated barrier. Lean for this second result is next.

RN-P-7h strengthened before audit: the existing strict diagonal-tail law at
z, combined with the inverse-Gram square law using z as the distinguished
node, proves α(0,z)>s(0,z,0) for every z>0. The near-center limiting argument
is unnecessary. The new leaf now formalizes this global center-anchor law
and its actual negative representer energy. A source-zero old-span packet
has strictly positive signed energy; the signed form cannot be replaced by
a positive form even on this exact span. Next attack remains projection
compensation, not a sign assumption on the feedback.

Both new leaves now pass targeted `lake --old build`: signed Sturm energy
(408 lines) and center feedback (100 lines). Both are wired into RHTower.
Axiom audit is running; required direct leaf audits remain next. No added
heartbeat settings. Latest lint still has no issue in either leaf, but
fails on eleven unrelated unwired modules (the previous ten plus
SoninTimeBandTaylorSourceDirection).

RN-P-7i is recorded in `rn-center-source-four-point-projection.md`.
The exact substitutions u=t(t+z) and u=(z+v)²-z² turn a literal source
four-point inequality into L(0,z)<L(z,z). Together with proved row decrease,
this makes both actual source-representer coefficients positive and forces
A>0 for every center-anchored ordered triple. A concrete sufficient producer
is T(x)=x²p''(x)-3xp'(x)+3p(x)>0. This is not supplied by p''' positivity;
the fourth-order terms cancel. The Peano kernel of the four-point functional
is positive and annihilates radial polynomials of degree ≤2. No source
sign is assumed. Actual T positivity and the full compensation gates remain
hard open targets. Searches were partial/source-only; reflected sixth
Hankel positivity does not imply an individual sixth-log sign.

### RN-P-7g/h final audit and next attack

Both final commands passed, exit 0, no diagnostics:
- `lake env lean GaloisForLFunctions/RHTower/ThetaTwoNodeSignedSturmEnergy.lean`
- `lake env lean GaloisForLFunctions/RHTower/ThetaTwoNodeCenterFeedback.lean`

All 26 public theorems have exactly the standard propext/Classical.choice/
Quot.sound axiom baseline. No heartbeat change, new axiom, admitted proof,
full build, umbrella build, or numerical experiment. P7h moved to
`3-formalized/theta/rn-actual-center-feedback-positive.md`; the failed
nonpositive-feedback shortcut has a P5 card with its positive survivor.
P7g remains P2 because its actual residual orthogonality equation (3) is
paper-proved but not yet formalized. The frontier map distinguishes these.

Next RN hard target is the actual four-point source inequality, through
T(x)=x²p''-3xp'+3p. The new paper reduction identifies
T=(1/8)∫₀ˣ(x²-u²)² r⁽⁶⁾(u)du=(1/2)∫₀ˣ(3u²-x²)r⁽⁴⁾(u)du,
r=-log(k/k(0)). This retains the actual source and avoids assuming every
sixth jet has one sign. Prove this weighted sign or analytically falsify it;
do not merely search and move to another route. The full compensated
barriers, coordinate residual, arbitrary-rank positivity, and RH endpoint
remain open. All owned processes are terminal; nineteen exact owned
scratch/search/audit files are removed at cleanup. Goal remains active.

### RN-P-7i: necessary center sign audit

Current turn attacks T=x²p''-3xp'+3p, not a replacement route. Exact modular
center raw jets are available in ThetaCuspDefect.thetaSource_centerRawJet
and centerSixthNumerator. A symbolic Lean sign probe is checking the
negative chamber of centerSixthNumerator above the already certified
self-dual scale threshold. This is an exact algebraic proof attempt, not
a numerical sample. If negative, the actual sixth log jet is positive,
forcing T<0 near the center and falsifying its proposed global positivity.
The existing actual far-tail limits for -logJetTwo/scale and
-logJetThree/scale would still force T>0 eventually, exposing an actual
sign change as the nontrivial survivor. No sign conclusion is claimed
until the probe and source transfer pass.

The full radial leaf's first check proves the actual center transfer:
`L6(0)>0`. Remaining reported errors are three derivative-expression
normalizations (identity-function coercions and a successor-index constant),
now repaired. The leaf also contains the near-center negative T regime,
eventual positive T, a positive zero, and the strict reverse source product
inequality at sufficiently small equispaced pairs. Targeted build is next.

RN-P-7j records the exact signed integral for
N(z)=L(z,z)-L(0,z) and its equality in sign with the actual first representer
coefficient. Local reversal of the pointwise producer does not determine
N. Preserve this nonlocal comparison, the actual projection equations,
and the distinction between the prospective full-tail H and the retained
arithmetic cut kernel. Full-tail positivity alone has not been declared
an unconditional RH endpoint.

### RN-P-7i build and RN-P-7k denominator implementation

The targeted `lake --old build GaloisForLFunctions.RHTower.ThetaRadialSourceCurvature`
completed successfully. The eight public theorems passed the scratch axiom audit;
only propext, Classical.choice and Quot.sound occur. The leaf is now wired;
its final direct-file audit is running. This closes the actual pointwise
four-point producer, with the radial sign-change theorem as positive survivor.

RN-P-7k has a dependency-closed paper proof in
`2-fully-proven/rn-confluent-center-source-residual.md`: the literal source
residual is positive for fixed y>0 and sufficiently small old node z>0.
The inverse coefficient signs are unnecessary: their finite limiting sum
is k(0)/H(0,0). The new `ThetaTailConfluentCenterGram` implementation proves
the exact positive-current candidate for the confluent denominator; compilation
is pending. The second-order kernel limits remain to be formalized.

A fresh deep search for second-derivative quotient limits and Schwartz
integrals was partial (complete source inventory, mostly pending/stale
compiler metadata; background refresh running). Candidate/source-argument
lists were inspected. They did not supply the actual theta projection limit;
Mathlib L'Hopital and the existing local Schwartz integration proofs supply
the needed analytic mechanism. No absence claim is inferred from this search.

The required final direct audit of `ThetaRadialSourceCurvature.lean` exited 0
with no diagnostics. Its paper card moved to P3/theta, the failed-route card
records the audited positive survivor, and the RN frontier now records this
actual obstruction. RH and the actual compensation gates remain open.

### RN-P-7k actual limit implementation; RN-P-7l next sign

`ThetaTailConfluentCenterLimits` now contains an unverified implementation
of dominated Schwartz correlation differentiation, exact center quotient
limits, the actual determinant and representer limits, and eventual actual
source-residual positivity at each fixed y>0. No sign of either individual
representer coefficient enters the final theorem. Compilation is pending.
The scratch API check needed explicit universe levels; no mathematical
assumption was introduced to repair that elaboration issue.

RN-P-7l records the exact remaining confluent coordinate residual:
`B_*/k=[2I y+K²(L'-pL)]/β`. Its cubic center invariant is
`J₂−3qI+qK²`. Both its global sign and this integrated center sign remain
open. This is the next genuine port sign problem, not a consequence of the
source residual. The source-residual formalization remains the active work.

`ThetaTailConfluentCenterGram` now compiles in the targeted `--old` build.
Its source-current identity and strict positive integral are accepted by Lean.
Initial elaboration failures were unresolved measure type, pointwise-function
coercions in derivative/integral rewrites, and the affine-space subtraction
inside `slope`; explicit types and `change` repaired them. No extra assumption,
axiom or heartbeat increase was used. The dependent actual-limit leaf is checking.

The complete RN-P-7k targeted build passed: both `ThetaTailConfluentCenterGram`
and `ThetaTailConfluentCenterLimits`. The final theorem is eventual positivity
of the literal `sourceResidual z y` for every fixed y>0 as z→0⁺. The residual
uses the actual inverse-Gram representer definitions from `ThetaSturm`;
no coefficient sign premise appears. Both leaves are wired into RHTower;
required direct-file and 16-public-theorem axiom audits are running sequentially.

The original four-point attempt card moved from P1 to
`5-failed/rn-center-source-four-point-projection.md`; its full attempted
reduction is preserved. RN-P-7j's integrated coefficient sign remains an
optional stronger condition, not a gap in RN-P-7k. RN-P-7l is the active next
coordinate-port target. The recent moment and slope searches completed their
configured deep stages (partial=false), but refresh/compiler metadata remain
incomplete. They returned the known source Ward and Riccati facts, not the
required integrated coordinate sign. No global sign is inferred from them.

### RN-P-7k final audit and next hard comparison

Both final direct commands exited 0 with empty diagnostics:
`lake env lean GaloisForLFunctions/RHTower/ThetaTailConfluentCenterGram.lean`
and `lake env lean GaloisForLFunctions/RHTower/ThetaTailConfluentCenterLimits.lean`.
All 16 public theorems have exactly the standard axiom set propext,
Classical.choice, Quot.sound. Together with RN-P-7i, this turn audited
24 public theorems in three wired leaves. No heartbeat raises, sorries,
added axioms or numerical source computations were used. RN-P-7k moved to
`3-formalized/theta/rn-confluent-center-source-residual.md` and the frontier
ledger now records its actual projection region.

Repository lint exited 1 solely for ten unrelated unreachable RHTower modules:
CCMApertureChainProfile, CCMApertureTranslationChains,
CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation,
CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower,
MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines,
ThetaMovingShellFirstOrderPhase, ZetaZeroDensityPowerSaving.
No full or umbrella build was run. Unrelated files were not changed.

A further paper derivation in RN-P-7l gives
`H_x(0,y)/(y K k(y))=∫C_y w R_y>0`, with
`C_y=t[p(t+y)-p(t)]/y-p(t)`, `w=k(t)²/K²`,
`R_y=K k(t+y)/(k(t)k(y))`. Boundary integration and strict slope convexity
prove the positive mixed-row sign. The actual coordinate compensation is
exactly `∫C_y w R_y<∫C_0 w`; its pointwise analogue fails near t=0 by
vanishing order. Attack this integral sign directly next. Its positive
mixed-row identity is paper-proved, Lean pending; no global coordinate
sign, arbitrary-rank positivity or unconditional RH result is claimed.

All owned Lean/build/search sessions are terminal. Removed the 28 owned
scratch/probe/search/audit files from /tmp after recording results above.
Cross-session memory saved as
`rh/rn-radial-obstruction-and-actual-confluent-source-port-2026-10-02`.
The RH goal remains active and unmet; the next hard comparison is RN-P-7l.

### RN-P-7l continuation: coordinate compensation and its cubic current

Previous turn classified as progress: audited actual source-residual region,
positive confluent entry, and actual four-point obstruction are present in
current sources and RN ledger. This turn revalidated those statements, ran
fresh corpus searches, and attacked the coordinate comparison. Search metadata
are partial/source-only with background refresh; no search result supplies the
coordinate sign.

The new candidate G_q in RN-P-7m has exact Gaussian cancellation and positive
actual center and cofinal signs. Its sign on the remaining interval is still
open. The integral identity needs an explicit audit of its logarithmic flux
`t p³ k²`; Schwartz regularity alone does not justify division by k. The raw
polynomial current obtained before subtracting that flux has unconditional
Schwartz integrability. Do not silently import a logarithmic-growth premise.

The exact mixed-row positive current from RN-P-7l will now be formalized and
connected to the literal coordinate projection limit. This retains the actual
upper-comparison obligation rather than claiming that a positive mixed row
settles the coordinate residual.

### RN-P-7m global current proof and integrated energy proof

The proposed mixed-row-only implementation was deferred when a stronger
producer emerged from the inspected corpus. `ThetaCuspCurvatureProjectiveGlobal`
proves the actual global reserve P=c'c''−cc'''>0. This yields R'=-P/c²<0.
The new paper proof integrates three exact primitives:
T=c'−pR, W=c²−q²−pc', F=p(c+2q)−qt(2c+q), with
T'=pP/c²>0, W'=cT>0, F'=W+2(p−qt)c'>0. Center parity gives zero
initial values. Therefore G=tW+F+2t(c−q)²>0 globally. This resolves the
intervening-interval sign rather than estimating it numerically.

The logarithmic flux caveat has a paper resolution: r=c/p²→0 follows from
actual source/first-atom slope and curvature limits. Then
`t k'³/k=(t k'k'')/(1-r)→0` by Schwartz products. The primitive
A(b)=∫₀ᵇ P_raw−b k'(b)³/k(b) has positive derivative G(b)k(b)²,
zero initial value, and limit 4E. Hence E>0. No integrability of Gk² is
assumed. The new leaves `ThetaConfluentCoordinateCurrent` and
`ThetaConfluentCoordinateEnergy` contain implementations; verification is
in progress. First current build failed only at conversion goal handling
and the closed half-line endpoint membership; those issues were corrected.
No claimed Lean success yet. Global B_*(y)>0 and actual finite-pair coordinate
transfer remain open beyond this cubic energy result.

The current comparison deep search was partial, with source-only/stale
compiler metadata and background refresh. Candidate lemmas and source
arguments were inspected; direct source reading exposed the global projective
reserve. Exact lexical search located the actual source slope tail theorem.

The global current leaf now passed `lake --old build` and is wired into
RHTower. The first integrated-energy check exposed coercion-normalization
and pointwise-function rewrite issues; typed derivative and integrability
helpers resolved them. The second check left only two function-expression
conversions in Tendsto, now explicitly changed to lambda form. The final
energy recheck is running. No mathematical premise or heartbeat override
was added. The next local projection target remains the exact third-order
mixed-row derivative and the literal coordinate-residual limit.

### RN-P-7m completed formal audit

Both `ThetaConfluentCoordinateCurrent` and `ThetaConfluentCoordinateEnergy`
passed targeted `lake --old build`. Final direct `lake env lean` audits on
both actual leaves exited 0 with empty diagnostics. All eleven public
proofs were checked with `#print axioms` in /tmp: only propext,
Classical.choice and Quot.sound. The unconditional theorem
`RHTower.ThetaCoordinate.coordinateEnergy_pos` closes E>0. Both modules
are wired; the certificate moved to
`3-formalized/theta/rn-confluent-coordinate-energy.md`, and RN's frontier
entry was updated. No full umbrella build was run.

Lint exited 1 solely for the same ten unrelated unreachable RHTower modules:
CCMApertureChainProfile, CCMApertureTranslationChains,
CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation,
CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower,
MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines,
ThetaMovingShellFirstOrderPhase, ZetaZeroDensityPowerSaving.
No owned proof source changed after its final audit. Temporary search,
probe and build/audit files are being removed after recording these results.

Assessment: this iteration solved the hard center integral sign rather
than merely reducing it. The next route obligation is the actual mixed-row
cubic limit and coordinate projection near the center; global comparison
(3), global compensation, arbitrary rank and RH transfer remain unproved.
The RH goal is active and unmet.

### RN-P-7n: actual coordinate transfer after strict energy positivity

Previous turn classified as progress: both current and strict integral sign
were proved and audited. Fresh source inspection confirms those theorems.
The new corpus query is partial with background refresh and source-only
metadata; inspected candidates recover the existing source/determinant limits
but no coordinate producer. The active mathematical target remains
B_*(y)>0 and the actual finite-pair residual. The exact cubic center jet
is the immediate bridge from the new E>0 theorem.

Added a public mixed-row derivative API to CenterLimits, reusing its proved
Schwartz correlation differentiation. A new CoordinatePort leaf retains
literal inverse-Gram coefficients and proves their candidate confluent
limit. Both are undergoing verification. Serena symbol lookup rejected the
Lean path as ignored, so the existing source was edited with a read-based
patch. No subagents or additional hypotheses were introduced.

RN-P-7n targeted builds now pass: extended CenterLimits, extended
CoordinateEnergy, CoordinatePort and CoordinateJets. The last leaf proves
`confluentCoordinateResidual_cubic_limit`,
`eventually_confluentCoordinateResidual_pos`, and
`eventually_actual_ports_pos`. The final statement is nested: for sufficiently
small y>0, then sufficiently small 0<z<y, both literal ports are positive.
This is not a uniform two-variable neighborhood or global propagation.
Both new leaves are wired. Direct file and axiom audits are next.

Global attack note: put d_y(t)=[p(t+y)−p(t)]/y,
C=t d_y−p(t), w_y=k(t)k(t+y)/(Kk(y)), and N=∫Cw_y.
The exact differentiated current is
N'=∫[∂y C−(p(t+y)−p(y))C]w_y. Subtracting one half of the
vanishing t-boundary derivative gives integrand
(1/2)[c(t)−d_y+(t/y)(c(t+y)+c(t)−2d_y)
 +(2p(y)−y d_y)C]. A uniform negative pointwise extension is suspect:
actual tail p(t+y)/p(y)→exp(2t) makes its dominant quadratic coefficient
positive at fixed 0<t with exp(2t)<2. This tail calculation is paper-only,
not a Lean no-go, and no route is retired on its basis.
The source-adapted flow λ=[p(t+y)−p(y)]/[p(t)+p(t+y)] cancels the
weight score, leaving ∂yC−λ∂tC−(∂tλ)C. The minus sign on ∂tλ is
essential: an earlier working derivation had a plus sign and its claimed
near-center obstruction was invalid. With a(y)=p(y)/y−c(0), the true
leading term near t=0 is t[a'(y)−2c(y)a(y)/p(y)]. For fixed t>0 and
y→∞, the leading term is [p(t+y)/y](exp(−2t)−1)<0. These are paper
checks only; the global sign and the adapted flux boundary/integrability
still require proof. The canonical current is now the direct global
conjecture. The new local chamber supplies its proved starting region.

### RN-P-7n final audit and next interior sign

The four actual leaves (CenterLimits, CoordinateEnergy, CoordinatePort,
CoordinateJets) passed final `lake env lean` with empty diagnostics.
All 26 public theorem axiom queries passed with only propext,
Classical.choice and Quot.sound. The new leaves are wired at the RHTower
umbrella. No full or umbrella build ran. P3 certificate:
`theta/rn-confluent-coordinate-chamber.md`; frontier and energy gates updated.
Lint exited 1 with twelve unrelated unreachable modules: the previous ten
plus CCMFiniteNeumannRemainderQuadratic and
ThetaCuspCurvatureDefectGrowthMixedPairAbsorption. No owned proof violation.

For the canonical current, write a=p(t), b=p(t+y), r=p(y),
u=c(t), v=c(t+y), A=a+b. Direct paper algebra gives

    y²A²J = y(2t+y)[a(a+r)v+b(b−r)u]
             −(b²−a²)[tA+y(b−r)].

The true endpoint coefficient is negative from the already audited chord
reserve: with m=p(y)/y, it is −(m²+mc−2qc)/p(y).
The bound m>q(2c+q)/(c+2q) makes the numerator strictly positive;
at equality it is q²(c−q)²/(c+2q)². This corrects the discarded false
endpoint obstruction; no global sign is inferred from it.

A direct corpus query for projective three-point inequalities completed
without partial truncation, but compiler metadata is source-only/stale and
background refresh is incomplete. Candidate lemmas, source arguments and
proposed ingredient sets were inspected. The suggested unrelated divided
differences and Hawking-source identities do not prove this inequality.
Direct source inspection recovers the actual global projective reserve and
the existing two-point ratio-descent mechanism; no three-point producer.

Next mathematical mechanism: in slope coordinates s=p(t), write
F(s)=c'(p⁻¹(s)). Then F'=c''/c>0 and F''=(c''/c)'/c<0. Thus the actual
acceleration is increasing and concave as a function of slope. This is a
paper reformulation of the audited projective law, not an assumed global
coordinate sign. Test whether it forces the exact three-point current
inequality above; its weighted integral and vanishing canonical boundary
still need an independent audit. If pointwise sign fails, retain the
original integrated comparison rather than claiming a route obstruction.

Assessment: this iteration closes the literal coordinate transfer and
actual nested two-port chamber. The global-current exploration has produced
an exact target and corrected a sign, but has not yet solved global
compensation. Global comparison, arbitrary rank and RH transfer remain
hard open obligations. RH goal remains active and unmet.

### RN-P-7o: exact global-spacing boundary of the canonical current

Previous turn: progress, with the literal nested chamber fully audited.
Current source inspection confirms the projective theorem and pending
global three-point conjecture. Fresh canonical-current corpus search is
partial, compiler metadata source-only, with pending/background refresh;
candidate and source-argument lists were inspected. No matching global
producer was returned. Unrelated conditional RH receivers were not used.

Interior work: projective descent implies that acceleration p'' is increasing
and concave in the slope p. Attempted to derive the full three-point margin
from two-point ratio descent and shifted chord reserves. The compensation
terms retain p(y), so the existing two-point theorem does not directly close
the inequality. No global proof or falsification resulted.

The exact endpoint identity in the P1 card does close a stronger boundary:
for every fixed y>0, the literal canonical current is negative for all
sufficiently small t>0. New leaf ThetaCoordinateCanonicalBoundary defines
the differential current (including −λ_t C), proves its exact negative
margin formula, and targets this all-spacing boundary from the previously
audited chord reserve. Its targeted build is in progress; no Lean success
claim yet. No new RH premise, axiom, computation or heartbeat setting.

Next interior attack: at a first zero Q(t,y)=0, retain the exact relation
Q=(b²−a²)M−y(2t+y)S, M=t(a+b)+y(b−r),
S=a(a+r)v+b(b−r)u. Its derivative uses
M_t=a+b+t u+(t+y)v and
S_t=2(a+b)uv+a(a+r)c'(t+y)+b(b−r)c'(t).
Eliminating M with Q=0 may give a first-zero barrier using projective and
chord reserves. This is an unproved next conjecture, not a consequence of
the endpoint theorem alone.

RN-P-7o final verification: the target passed `lake --old build`, then
final direct `lake env lean` on the actual source path with empty diagnostics.
All six public theorem axiom checks contain only propext, Classical.choice
and Quot.sound. The leaf is wired; no umbrella build. Serena symbol lookup
again rejected the ignored Lean path, so corrections used read-based patches.
The failed checks exposed composition/instance normalization and generated
scalar-goal handling; no mathematical premise changed.

Formal lint exited 1 solely for twelve unrelated unreachable modules:
CCMApertureChainProfile, CCMApertureTranslationChains,
CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation,
CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower,
MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines,
SuzukiMatchedOddPoleProfile, ThetaCuspCurvatureDefectGrowthDeepNextReservePolynomial,
ThetaMovingShellFirstOrderPhase, ZetaZeroDensityPowerSaving.
No owned proof violation. P3 certificate and RN frontier updated.

Assessment: the new theorem supplies the actual all-spacing boundary
condition for the proposed global current comparison. It does not solve
the interior sign, the weighted-integral transfer, Schur compensation,
arbitrary rank or RH. The next turn should attack a first-zero barrier
or the equivalent fixed-source-potential ratio decrease, not add another
unrelated endpoint estimate. Search/probe/audit scratch is being removed;
all owned build/search handles are terminal. RH goal remains active.

### RN-P-7p: global interior cross compensation

Previous turn: verified progress on the all-spacing boundary. Direct source
inspection confirms it. The first-zero search is partial with stale/source-only
metadata and background refresh; candidates and source arguments were inspected.
The lexical tail query locates the exact actual jet limits but reports no
coverage/freshness metadata. Direct source reads supply the scaled likelihood
variance and third-cumulant error producers.

Corrected a fresh product-rule error before using it: exp(−2t)(c'−2c)
does not have curvature-defect derivative. The right current is
exp(2t)(2c−c'), with derivative −exp(2t)(c''−4c)<0. Its eventual sign
requires the subleading actual limit S(2c−c')→24, not only c/S→4 and
c'/S→8. Exact first-atom algebra gives 24(S/q_a)^3; scaled likelihood
variance/third-cumulant errors vanish. This proves global 2c−c'>0, then
cc''−c'²=c(c''−4c)+(2c−c')(2c+c')>0.

This curvature law yields an interior result: the slope elasticity tc/p
strictly increases because M=pc+tpc'−tc² has
(M/c)'=pc'/c+tp(cc''−c'²)/c²>0. A reciprocal-sum comparison then proves
Q_cross(x,z)=p(z)²−p(x)²−(x+z)[p(z)c(x)−p(x)c(z)]>0 for ALL 0<x<z.
The canonical margin decomposes exactly as Q_base+y[p(t+y)−p(t)−p(y)]Q_cross.
Both factors in the added term have strict source signs. Full Q_base/Q
compensation remains open; this is a global interior term, not another
endpoint estimate.

P1 paper card: rn-interior-cross-current.md. New leaves
ThetaCuspCurvatureLogConvex and ThetaCoordinateCrossCurrent are implemented.
The first curvature build found only an unresolved constant in a Tendsto
expression; an explicit constant-one limit corrected it. Recheck is running.
No proof-success claim yet; no new axiom or heartbeat setting.

### RN-P-7q: global base compensation from source-potential geometry

New dependency-closed paper proof: V=cc'−pc''>0 follows from the proved
projective primitive. K=3tc²−3pc−tpc' has K(0)=0 and
K'=tV+4c'(tc−p)>0. Thus c'/p strictly decreases and
((tc−p)/p³)'=−K/p⁴<0. In the potential U=−log k, U'=p, these
are strict concavity of c and strict convexity of t/p.
For x<z, differentiating endpoint tangent gaps gives both strict trapezoids:
Hc=p(z)²−p(x)²−(U(z)−U(x))(c(x)+c(z))>0 and
Hg=(U(z)−U(x))(x/p(x)+z/p(z))−(z²−x²)>0.
The exact base decomposition is
Q_base=p(x)p(z)[Hc(x/p(x)+z/p(z))+Hg(c(x)+c(z))]>0.
Together with RN-P-7p, this proves the paper-level global Q>0 and J<0.
ThetaCoordinateCanonicalGlobal implements this proof; validation pending.

Targeted build results so far: ThetaCuspCurvatureLogConvex passed;
ThetaConfluentCoordinateCurrent (new projectiveSlopeReserve_pos) passed;
ThetaCoordinateCrossCurrent passed after two elaboration repairs
(explicit derivative function and endpoint set membership). Final direct
Lean audits and axiom checks remain pending.

The next weighted-transfer search returned unrelated partial/source-only
flux candidates; none was used as a theorem. A lexical refinement recovered
schwartzCorrelation_integrable, centerMixedRow_zero, and the existing
cumulativeCurrent mechanism. Its metadata reports no coverage/freshness.
The actual centerMixedRow differs from the canonical raw moment numerator
L=(t+y)k'(t)k(t+y)−tk(t)k'(t+y) by the derivative of tk(t)k(t+y).
Both endpoints of that correction vanish. The derivative of the normalized
moment is a raw Schwartz correlation combination. Subtracting canonical
flux from its finite primitive should give derivative Jw<0; the flux tends
to zero since 0<speed<1 and L tends to zero. This supplies a direct path to
global B_* positivity without assuming quotient-current integrability.

Global leaf targeted build passed after removing one redundant tactic and two
unused simp arguments. All four direct file audits completed without diagnostics;
the 24-public-theorem axiom audit is running. The three new sign leaves are wired.
The next leaf ThetaCoordinateCanonicalFlux is written, not yet checked: it proves
bounded canonical speed, decay of the literal flux, an exact divergence identity,
and strict negativity of the raw parameter-derivative integral by a finite
primitive. Only raw Schwartz products enter its integrability claims.

All 24 global-sign theorem axiom audits passed: propext, Classical.choice,
Quot.sound only. P3 certificate is theta/rn-global-canonical-current.md;
RN frontier map now records the closed interior sign problem.

ThetaCoordinateCanonicalFlux first check found composition normalization,
an invalid lambda character inside an identifier, and a finite-primitive
limit elaboration issue. These are repaired; targeted recheck runs.
The actual divergence algebra, raw integrability and canonical speed bound
had no reported mathematical failure.

ThetaTailConfluentCoordinateGlobal is now written, unbuilt. Its exact target
is B_*(y)>0 for all y>0, followed by the literal two-port chamber at every
fixed positive spacing. It identifies T with the raw moment using the
zero-boundary derivative (tk(t)k(t+y))', identifies the negative transport
integral with N'=d[T/(yk(0)k(y))]/dy, and obtains N(0+)=β/k(0)² from the
already audited cubic residual limit. No new center-jet assumption or
quotient-Schwartz premise is inserted. This is the next direct transfer,
not finite-pair propagation or arbitrary-rank/RH closure.

The cleaned ThetaCoordinateCanonicalFlux leaf now passes its targeted
dependency rebuild without own diagnostics. The global residual leaf is
compiling. The 12 flux and 7 residual public theorems have a prepared /tmp
axiom audit; it will run after successful source checks.

Next finite-pair card: rn-center-schur-coordinate-row-flow.md. It retains
actual inverse-Gram coefficients and derives B_z(y)=yk(y)[1−E(z,y)/E(z,z)]
for the center-removed normalized kernel E. The source-driven PDE exposes
an explicit complete forcing for E_y. Its sign, not the confluent initial
condition alone, is the new hard barrier. The deep search is partial with
semantic/reranking timeouts and pending coverage; inspected source-only
hits include known normalized rows and our unbuilt current file, which
was not treated as evidence of a theorem.

### RN-P-7r completed: global literal coordinate residual

The first global residual check exposed explicit-function versus Pi-function
integral rewrite mismatches and Schwartz coercions under derivatives. Typed
integrability sums, the exact source coercion, and typed source derivative
facts repaired these; two redundant closing tactics were removed. The
corrected leaf builds cleanly. Both transport leaves passed final direct
lake env lean file checks, followed by all19 public theorem axiom checks.
Together with RN-P-7p/q: six directly checked leaves,43 public theorem
axiom audits, all using only propext, Classical.choice, Quot.sound.

Closed hard source problems this continuation: global curvature log-convexity,
global canonical-current negativity, its actual weighted integral transfer,
and B_*(y)>0 for EVERY y>0. The resulting actual two-port chamber is now
valid at every fixed positive outer spacing; the small-z threshold still
may depend on y. P3: theta/rn-global-confluent-coordinate-residual.md.

All five new modules are wired. Repository lint reports11 unrelated
unreachable modules listed in the P3 certificate; no owned proof violation.
No full/umbrella build, computation experiment, added axiom, heartbeat
increase, subagent or commit. Every owned build/search handle is terminal.
Owned search/probe/build/audit scratch is being removed after recording
these results. The RH goal remains ACTIVE and unachieved.

Next hard mathematical problem: actual finite-pair contact compensation
for Γ=E_y in rn-center-schur-coordinate-row-flow.md. The complete source
forcing, with Γ=0 retained as its actual integral identity, must be proved
negative. The proved N'<0 supplies the boundary on each y−z=d>0
characteristic. It is not a replacement for this missing source law.
Finite-pair propagation, general anchors, arbitrary rank and retained
arithmetic RH transfer remain open. Do not repeat the completed audits or
return to the now closed small-y or interior canonical-current questions.

Cleanup complete: all26 owned search, probe, build, lint and audit scratch
files removed. No owned job remains running. Completed proof sources,
umbrella wiring, P3 certificates, current RN ledger and both checkpoint
memories remain in the workspace. Next turn attacks the finite-pair
source contact law; RH goal remains active.

### RN-P-7s completed: global actual center Schur cross positivity

Route RN. Previous global confluent closure was genuine progress, but did not
supply finite-pair propagation. This turn retained that hard target. The direct
contact-forcing route and the original double-integral integrand did not yield
a sign: the latter has a negative diagonal term. Shifted-source Wronskian
control alone was not shown to imply actual inverse-Gram compensation.
No unproved contact or Wronskian theorem was installed as a premise.

A new exact Gaussian coarea, u=t(t+x+y), removed the first-moment weight.
The actual normalized kernel is the integral of exp(-V). Its exact mixed
potential derivative is strictly negative from actual c''>0. Center amplitude
ratios decrease in u and lie in(0,1]. Strict potential submodularity plus the
complete nonnegative covariance prove, for EVERY x,y>0,

    H(0,x)H(0,y) < H(0,0)H(x,y).

This closes a genuine global finite-pair source comparison. The positive old-node
coefficient of the actual center-anchored projection is therefore always
strictly positive. No coefficient or Gram-positivity premise was assumed.
It does not yet supply the strict upper bound needed by the coordinate port.

Completed leaves: ThetaTailGaussianCoarea, ThetaTailGaussianSubmodular,
ThetaTailCenterSchurCross. All three targeted --old leaf builds passed;
all three final direct lake env lean file audits passed with no diagnostics.
All34 public theorem axiom checks returned only propext, Classical.choice,
Quot.sound. All three modules are wired into RHTower. P3 certificate:
`theta/rn-gaussian-coarea-center-schur.md`; RN frontier map updated.

Formal lint reports11 unrelated unreachable modules and no owned violation;
exact list retained in the P3 certificate. No umbrella/full build, numerical
experiment, heartbeat increase, subagent, added axiom, or commit.

Next hard target remains E_y<0 for the actual center-removed normalized kernel,
or a weaker direct coordinate-port upper bound. The new decomposition is
G/C=expectation(B_xy)+covariance(A_x,A_y), with B_xy>0. Its derivative must
retain the covariance. A partial corpus search found the actual full-line
Brascamp--Lieb theorem and half-line Stein identity with its endpoint current.
The latter is relevant because the coarea density is nonzero at0. The corpus
also explicitly proves that subtracting the first Popescu correction from an
upper bound requires zero retained resolvent remainder. Do not reuse that
invalid shortcut. Exact statements and remaining sign target are recorded
in rn-center-schur-coordinate-row-flow.md.

All owned build, search, direct-audit and axiom handles are terminal.
RH goal remains ACTIVE and unachieved. Finite-pair upper compensation,
general anchors, arbitrary rank and arithmetic RH transfer remain open.

RN-P-7s cleanup complete: all17 owned search/API/build/audit scratch files
removed. No owned process remains running. The formal sources, umbrella wiring,
P3 certificate, frontier update, working log and checkpoint memory are retained.


### RN-P-7t completed: arbitrary-anchor actual Schur cross positivity

Route RN. Previous center Schur closure was progress. This turn first tested
the finite-coordinate monotonicity conjecture at joint coalescence. The exact
inverse-Gram correction introduces the necessary sign
S/6-2qI+2qP/3+I^2/J>=0; its sign and the joint Taylor remainder remain
unproved. The paper diagnostic is recorded in the flow card and was not
installed as a premise or claimed as a falsification.

The same source coarea mechanism exposed a solvable missing anchor term.
For s=a+t, r=x+t, L=s+r, P1=p(s)+p(r), the endpoint mass-rate numerator is

    (x-a)(L*c(r)-P1)+L*s*(c(r)-c(s))
      +a*(L*(c(s)+c(r))-2*P1) > 0.

All terms have actual-source signs. Thus comparison amplitudes decrease
above EVERY nonnegative anchor. Strict submodularity plus complete positive
covariance closes

    H(a,x)H(a,y)<H(a,a)H(x,y), 0<=a<x, a<y.

The actual larger old-node projection coefficient is consequently positive.
This extends the center-only finite-pair result; it does not solve the upper
coordinate-port bound. The old proof code was generalized, with existing
center declarations preserved as specializations.

Modified Lean leaves: ThetaTailGaussianSubmodular, ThetaTailCenterSchurCross.
Both targeted lake --old builds and both final direct lake env lean file
checks passed. All29 public theorem axiom checks returned only propext,
Classical.choice, Quot.sound. Existing umbrella imports cover both leaves.
Formal lint found12 unrelated reachability errors, none in these leaves;
exact list is in the new P3 certificate. No full/umbrella build, numerical
experiment, subagent, added axiom, heartbeat increase, or commit.

P3 certificate: theta/rn-gaussian-coarea-arbitrary-anchor.md. RN map and
current flow card updated. Next hard step remains the compensated finite-pair
upper sign, including its necessary joint-center invariant. Full port signs
at general anchors, arbitrary rank and arithmetic transfer are also open.
RH goal remains ACTIVE and unachieved.

RN-P-7t cleanup complete: all9 owned /tmp search/build/audit files removed.
All owned process handles are terminal. Formal sources, certificates, working
log, frontier update and checkpoint memory retained.


### RN-P-7u completed: actual joint-center inverse-Gram compensation

Route RN. Previous arbitrary-anchor Schur lower sign was progress, but left
coordinate-port upper compensation open. This turn attacked the necessary
joint-center sign directly. Merely reusing coordinateEnergy>0 leaves an
uncontrolled inverse-Gram correction; the sign of the stronger integrated
diagonal-comparison shortcut also remained unknown.

New knowledge: the actual source has the globally positive current

    G=pc+3tc^2-tpv-12qtc+20qp-12q^2t
     =t*slopeEnergy+(c+20q)/(c+2q)*chordReserve
        +2t(c-q)^3/(c+2q)>0.

Existing unconditional projective source reserves prove every term's sign.
With I=integral t*k_prime^2, S=integral t*k_second^2, P=k(0)^2,
q=c(0), J=H(0,0), the retained logarithmic flux gives

    F=2S-12qI+8qP-3q^2J>0,
    D=S/6-2qI+2qP/3+I^2/J
     =F/12+(I-qJ/2)^2/J>0.

The proof uses exact Schwartz polynomial integrals and the existing vanishing
flux; it assumes no logarithmic-quotient integrability, projection coefficient
bound, covariance sign, or new source axiom. Equivalently,
F=2*coordinateEnergy-3q*(2I+qJ-2P); it pays the possible adverse diagonal
comparison without resolving that comparison's sign.

Five new public theorems in the existing ThetaConfluentCoordinateCurrent
and ThetaConfluentCoordinateEnergy leaves. The old coordinateEnergy proof
shares a private flux receiver with the new proof; public statements preserved.
Both targeted --old builds and both final direct lake env lean checks passed
without leaf diagnostics. All20 public theorem axiom queries returned only
propext, Classical.choice, Quot.sound. Existing umbrella imports cover both
leaves. Lint reports12 unrelated reachability errors, listed in the P3
certificate, and no owned violation. No full/umbrella build, computation
experiment, heartbeat increase, subagent, added axiom, or commit.

P3 certificate: theta/rn-joint-center-coordinate-compensation.md.
RN frontier and main flow card updated. The source sign is closed; the exact
joint Taylor/Hessian identification is NOT yet formalized. The P3 card records
a paper route to a uniform triangular chamber 0<z<y<epsilon using
E_yy(0,0)<0 and E_yx(0,0)+E_yy(0,0)=-D/P<0. Then full finite-pair propagation,
arbitrary rank and arithmetic transfer remain hard open obligations.
RH goal remains ACTIVE and unachieved.

Implementation lessons: field_simp normalized the denominator C+2Q to C+Q*2;
provide both nonzero forms after scalar generalization. Explicit pointwise
Integrable annotations are needed before integral_add rewrites, and a typed
Schwartz product bridges source coercions. The Energy leaf had no actual H
kernel import previously; ThetaTailTwoPointPositivity supplies the literal J.
A shallow dslope search found Mathlib DSlope continuity/basic differentiation,
but no ready joint smooth division theorem was verified. Its formal extension
is still a next-step obligation, not an installed premise.

RN-P-7u cleanup complete: all12 owned /tmp search, algebra, build and audit
files removed. All owned process handles are terminal. Formal sources, existing
umbrella wiring, P3 certificate, frontier update, working log and checkpoint
memory retained.


## RN-P-7v completed — 2026-10-03

PROGRESS. Conjecture: one epsilon works for both actual center Schur ports
for every 0<z<y<epsilon, with arbitrary relative approach. Proved unconditionally
as ThetaJoint.exists_actual_ports_pos_triangle. This closes the joint-center
identification/propagation gap exposed by RN-P-7u, not the global RH problem.

The exact actual Schwartz correlation calculus proves the full raw mixed
origin jets. A double unit-square average gives x*y*Q=T, including both
axes, and continuous needed derivatives. Normalize by k(x)k(y); actual Hessian
entries are -2*coordinateEnergy/(3P) and -jointCoordinateCompensation/P for
the pure-right and diagonal-direction sums. Both are strictly negative by the
previous source certificates. Diagonal then vertical integration gives the
uniform coordinate comparison. The source side retains qJ<=P<2I from the
actual diagonal tail limit and centerEntry>0. Thus the actual source deficit
g has g(0)=g'(0)=0 and g''(0)=(2I-qJ)/J>0; its convex chord inequality pays
the same literal projection coefficient and proves the source port.

Seven new leaves, all namespace RHTower.ThetaJoint: ThetaTailJointCorrelation,
ThetaTailJointCenterJets, ThetaTailSchurAxisExtension,
ThetaTailNormalizedSchurHessian, ThetaTailCenterSourceConvexity,
ThetaTailSmallNodeCoordinate, ThetaTailSmallNodePorts.
All targeted --old builds passed; all seven final lake env lean actual-file
checks passed with empty diagnostics. All109 public theorem axiom queries
returned only propext, Classical.choice, Quot.sound. Printed capstone type
has no extra premises. All seven umbrella imports verified; no full or umbrella
build. Lint12 unrelated unreachable modules are recorded in the P3 certificate;
no owned-leaf violation. No new axiom, admitted proof, heartbeat increase,
numerical experiment, subagent, commit or push.

P1 card promoted to P3: theta/rn-uniform-small-node-coordinate-chamber.md.
RN frontier and main finite-pair flow card updated. The next hard target remains
global finite-pair upper compensation. The main card records the full weighted
coarea current inequality retaining covariance. Searches for a global upper
producer, translated Wronskian bridge and feedback closure did not supply it.
The actual secant<feedback sign has the adverse orientation for a proposed
feedback upper shortcut. Do not reuse it in the wrong direction. Search
metadata mostly partial/source-only; exact used declarations were read and
audited. The search engine's suggested ingredient sets were unverified and
not accepted as proofs.

Implementation lessons: explicit pair-valued composition functions are needed
before fun_prop; unresolved composition metavariables do not infer coordinates.
The continuous-partial diagonal chain rule needs an explicit base point and
an explicit diagonal inner function. integral_pow is a root declaration.
Pi.pow_apply/Pi.sub_apply must be reduced before field_simp. Avoid recursive
simp with moving-tail identities: rewrite a single function equality instead.
An explicit Tendsto pair replaces an expensive inferred neighborhood expression
without raising heartbeats. field_simp often closes exact quotient identities
itself; remove redundant ring tactics.

Full RH goal remains ACTIVE and unachieved. Global finite-pair compensation,
general anchors, arbitrary rank and arithmetic transfer remain hard open.

### RN-P-7v checkpoint and RN-P-7w successor — 2026-10-03

Saved memory rh/rn-uniform-small-node-schur-ports-2026-10-03. Removed all32
owned scratch sources, search responses and audit logs from the completed
local proof after all owned jobs terminated. Formal leaves and certificates
remain. No code changed after the successful final audits.

The next global-current investigation produced no new global sign. It rejected
a circular Cauchy–Schwarz shortcut: the needed center Schur PSD includes the
still-open three-node positivity. It derived the paper boundary diagnostic
kappa_x(0,y)=(3p(y)-y c(y)-2c(0)y)/y² for the coarea interaction current.
For K(y)=3p(y)-y c(y)-2c(0)y, K-yK'=ThetaRadial.radialDefect and
(K/y)'=-radialDefect/y². These identities explain why an isolated factor sign
cannot be read off from potential submodularity. Their derivation and exact
unproved status are saved in rn-center-schur-coordinate-row-flow.md.

Assessment: RN-P-7v solved the uniform joint-center gap. RN-P-7w has not yet
solved global finite-pair compensation. Continue with the full signed current
C*(R-yR_y)-h(x)*(h(y)-y h'(y)), retaining covariance and endpoint terms.
Do not substitute generic PSD assumptions or discard the adverse term.

### RN-P-7x: positive finite-pair primitive and strict correction — 2026-10-03

Closed a new global source problem. For all x,t>0, with J=H(0,0),
O_x(t)=H(0,x)H(t,t)-J H(t,t+x) strictly exceeds
x*t*J*k(t)*k(t+x). Thus B=O/(xJktkx+t)>t. The proof uses two decreasing
actual density ratios, exact zero total signed mass, and Schwartz tail limits.
The corrected ratio's sign follows from c''<2c², giving M=2pc-c'>0 and
F=x*(p(t+x)²-p(t)²-c(t+x)-c(t))+2*(p(t+x)-p(t))>0.

Leaves ThetaTailPositiveBalancePrimitive and ThetaTailTransportPrimitiveFloor
built with targeted --old commands and passed final direct lake env lean
source audits with empty logs. All25 public theorem #print axioms results are
exactly [propext, Classical.choice, Quot.sound]. Both leaves wired into RHTower.
Repository lint reported12 unrelated unreachable modules, none in these leaves;
no forbidden declaration was reported. P3 certificate and RN frontier updated.

Searches: canonical transport, positive zero-total primitive, native finite
secant energy, and signed-Sturm crossing. All used local corpus. The crossing
query was partial with complete inventory65043; compiler metadata mostly
pending/source-only. No ready single-crossing producer was found. Proposed
ingredient set "curvature decreases" was not applicable and not accepted.
Actual curvature strictly increases, while its projective ratios have separate
laws. Exact statements were read before use.

Successor: the full finite-pair moment is a+s_y B. N=a+s_x B has forcing
s_x'-2j s_x, of indefinite sign; even positivity of N would leave an unproved
second current coefficient. Keep actual source packet a. The actual normalized
row theorem gives the paper relation a+B*kt²/Htt>0, but this alone is not a
uniform current sign. No circular rank-three Cauchy–Schwarz assumption used.

The improper transport identity has a dependency-closed paper proof: ratio r_y
is bounded; U=r_y O vanishes; U'=r_y f-G with G>=0. A finite primitive of G
has finite limit, proving its integrability. A non-partial corpus search
(inventory65045, mostly source-only compiler metadata) recovered the actual
Mathlib improper monotone-derivative API; all required APIs passed a /tmp
Lean check. ThetaTailFinitePairTransport implementation and audit in progress.

Contribution assessment: primitive positivity and its strict correction are
new global finite-pair knowledge. The full current remains the hard open sign;
no RH proof/falsification or arbitrary-rank producer has been obtained.

### RN-P-7x improper-transfer audit completed — 2026-10-04

ThetaTailFinitePairTransport built and passed final actual-file lake env lean
with empty diagnostics. All14 public theorem axiom closures are exactly
[propext, Classical.choice, Quot.sound]. Total for this advance: three leaves,
39 public theorems, all directly audited, all wired. No full/umbrella build.
A fresh lint after wiring still reports the same12 unrelated unreachable
modules; no new leaf error. Certificate and frontier updated.

Implementation lessons: Pi subtraction under Integrable needs an explicit
function equality via convert!, sometimes even after simp only Pi.sub_apply.
For integral_sub rewrites, give the nested difference a typed lambda integrability
lemma. An unconstrained FTC have needs (a := 0). This toolchain's scalar rule
is MeasureTheory.integral_div, not integral_div_const; actual API audited in
/tmp before use. No heartbeat changes or numerical experiments.

Next hard conjecture remains the full finite-pair current sign. A second exact
paper identity eliminates a using D=B-t>0:
  w*(a+s_y B)=(wD/(2t))'+w*(t*s_y-Sigma_x/2+Q*D),
  Q=s_y+(p(t+y)-p(t))/(2t)+1/(2t²)>0.
P1 records its unformalized improper-transfer obligations, the proposed Q
current sign, and its exact numerator and endpoint diagnostic. Neither that
sign nor payment of the explicit C0=t*s_y-Sigma_x/2 has been proved. This
keeps the hard nonlocal compensation visible instead of silently replacing
it by positivity of one component. RH remains unproved; goal stays ACTIVE.

Checkpoint cleanup: all owned jobs terminated. Removed19 owned /tmp search,
API and audit files after recording results. Formal leaves and certificates
preserved. Final scoped git diff --check passed. No code changed after its
successful direct-file audit. Memory rh/rn-finite-pair-positive-transport-primitive-2026-10-03 updated.
