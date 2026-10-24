# WD global signed trace contraction

Status: IN PROGRESS. No global contraction proved.

## Exact task

Prove the global signed source-to-divisor trace contraction required by route WD,
unconditionally. The prior parabolic source landing is local and finite-packet only;
it cannot be substituted for this task. Do not assume positivity, an infinite-packet
interchange, or source shorting. No numerical computation, web search, or external
novelty audit; use the current Lean corpus. Paper proof before new Lean declarations.

## Working plan

1. Identify the exact current global signed pairing, target theorem, and proved no-go laws.
2. Conjecture structural mechanisms on the literal arithmetic source; attack each against
   the entire corpus and exact algebra. Record failures and positive survivors.
3. Complete a dependency-closed paper proof of the actual global statement.
4. Formalize, audit leaf modules and axioms, wire umbrellas, lint, and clean scratch.

## Corpus frontier

`XiWardGlobalCapRightZeroSum` already proves absolute convergence and exact global cap
evaluation as `-8*pi*tau` times the right-zero Stieltjes sum. For `0<tau<=12` its real
part is nonnegative, strictly positive if a zero lies right of the cap. Vanishing of
the almost-everywhere cap family is equivalent to RH. There is no missing cap convergence
lemma that can by itself prove the desired sign.

`XiWardCubicPrimeGammaSecantFundamentalSymmetryGap` proves that replacing the literal
Weil cup by its positive fundamental-symmetry energy costs half the reflection-difference
energy; even one fixed nondegenerate secant has zero gap iff RH. The quadratic opposite-radial
current has a negative norm-square boundary signature (`XiWardCubicOppositeRadialBoundarySignature`).
Scalar reflection-compatible shorting preserves that signature.

The prior parabolic source averaging extracts linear multiplicity and realizes the cubic
directional mask on finite packets. It proves neither the global sign nor infinite interchange.

## Conjecture ledger

1. Continue the zero cap from the absolute-Euler chamber through the strip. **REJECTED:**
   the global cap identity records exactly the residues crossed; analyticity in the level
   is the unproved/false intermediate. The positive survivor is the already-proved exact
   Stieltjes jump accounting, not a new theorem.
2. Insert the unconditional Weil fundamental symmetry and apply Hilbert contraction.
   **CIRCULAR:** its erased defect is already RH-equivalent for one fixed source secant.
   Any survivor must keep this defect in the source comparison.
3. Integrability in the logarithmic transverse level would force cap vanishing, since each
   strict-right zero contributes a positive constant on a half-line of levels. **OPEN / NOT
   A SOLUTION:** no source proof of that stronger integrability; ordinary cap integrability
   concerns height, not logarithmic level. This only relocates the hard core.
4. Differentiate the exact theta Doob identity `M Phi=-cosh(x/2)` and use `-Phi'` as a
   positive odd-sector supersolution. **OBSTRUCTION FOUND:** folding prime jumps produces
   reflected sum squares, not a positivity-preserving half-line generator. A ground-state
   transform cannot discard those signed off-diagonal terms. Investigating corpus coverage.
5. Diagonalize the all-prime Doob form on divisor graphs: prime-power ratio edges form
   complete graphs along exponent coordinates, with complement reflection `m -> N/m`.
   **OPEN CORE:** the exact theta product fibers are signed, so finite graph positivity
   alone does not yield the integrated source sign. Need an exact modular reassembly of
   those fibers, not another spectral-gap estimate. Investigating this mechanism.
6. Use the existing mixed Euler/Xi Burnol Gram as the global contraction. **REJECTED:**
   `FrankensteinPrimitiveXiMixedBurnolSchurGap` proves strict mixed Schur residual at every
   primitive/Xi pair. Ordinary positive block compression has the wrong direction. Its exact
   survivor is already formalized: signed completion must occur before positive compression.
7. Apply the infinite signed Möbius recovery and the matrix Hardy contraction of the Ward
   phase. **INSUFFICIENT, WITH AN EXACT ORIENTATION WARNING:**
   `GammaSewnMobiusXiWardHardySaturation` proves strict contractivity of this phase exactly
   when RH fails. RH requires unitary saturation. `GammaSewnSynchronizedRecoveryContraction`
   preserves both the literal full-source tangent and, separately, the selected anti-causal
   tangent, but its Hardy bound is on the latter. No budget-preserving identification of the
   requested residue trace follows. `HedenmalmThetaSourceJuliaPythagoras` already identifies
   the surviving discrepancy coordinate; unit normalization does not erase it.
8. Pass the exact finite prime-depth cubic commutator cancellation to the completed source.
   **UNDER INVESTIGATION:** `PrimeBurnolThetaCubicTraceCancellation` proves zero for each
   admitted fixed-reference finite trace, while explicitly leaving the unbounded completed
   source domain unproved. Need an actual trace-ideal realization of the coupled source,
   not an assumed cyclicity or a newly defined vanishing reporter.
   `SoninGammaClockNuclearLimit` admits the Gamma clock with a fixed Schwartz test, explicitly
   not the joint prime/polar source. `SoninCoherentWardCubic` has zero first trace but an exact
   negative cubic interference square. Neither identifies the requested joint cubic.
9. Preserve both Green--Stokes channels and assign the interior its natural Krein sign.
   **REJECTED FOR THIS CANDIDATE:**
   `SourceHorizontalWoldBVCompleteSplitPrimitiveBudgetFirewall` proves that the signed limit
   is `8/3 * normSq c`, still strictly above its literal primitive budget for `c != 0`.
   This rules out mere sign reassignment; it is not a no-go for every possible WD producer.
10. Use source-native causal Xi splittings to obtain a faithful Hilbert contraction.
    **ADMISSION GAP REMAINS:** `DeningerMeyerFiniteXiCausalSplitting` gives actual finite
    full-multiplicity projectors commuting with the generator, but no such norm comparison.
    `DeningerMeyerHalfDensityXiGraphClosure` gives explicit graph-null sequences off line:
    completion norm tends to zero while Xi evaluation stays nonzero. Closing the full-source
    graph cannot supply a single-valued repair. `BurnolPoissonSubordinateWall` also shows that
    prime-log smoothness does not supply the missing all-prime inverse admission.
11. Complete the bilateral Loewner kernel by its single shared ghost and use that completion's
    trace. **INSUFFICIENT:** `XiWardCubicBilateralSharedGhostCompletion` already proves
    `K_a = P_a P_a* - G_a G_a*`, with `P_a(lambda)=2lambda/(lambda^2-a^2)` and
    `G_a(lambda)=2a/(lambda^2-a^2)`. Adding the ghost is positive, but increases the positive
    column's norm strictly when `a>0`. Need an independently derived Gamma/polar cancellation
    of that amplified corner. Rescaling it back by definition would change the source.

### Divisor-graph paper observation (not yet a global proof)

For `N = product p^(a_p)`, the graph implicit in `PhiDivisorEnergy.divisorEnergy` is the
Cartesian product of complete graphs on the exponent coordinates, with each p-edge weighted
by `log p`. Every vertex has weighted degree `sum a_p log p = log N`. Its Laplacian has exact
tensor eigenvalues `sum_{p in S} (a_p+1) log p`, with the constant factor in coordinates not
in S. Complementation reverses each exponent coordinate. This algebra does not settle the
source form: the theta product fiber multiplying each graph is signed away from its center,
and the polar/Gamma term has not been reassembled with it. No positivity claim is made.

The signed-fiber obstruction persists after integration for one fixed graph. At `N=2`, its
energy is `log 2 * (v(u)-v(u-log 2))^2`. Choose an odd smooth bump pair supported near `+T,-T`,
with disjoint translates and T sufficiently large. All four intervals supporting that square
lie in the negative tails of `fiber 2`. Its integral is then strictly negative. This is a
paper falsification of graph-by-graph positivity, not a formalized theorem. The positive
all-prime sum in `WeilPhiDoobDivisorEnergy` uses resummation across fibers. Any next attempt
must retain that resummation and the Gamma/polar term together.

Next paper conjecture to test: apply Jacobi resummation to a complete cusp-sum index before
grouping by divisor product, retaining the Gamma and polar boundary terms exactly. Seek a
positive quadratic identity for that joint expression with its literal coefficients. No such
identity has been derived; this is a proposed mechanism, not a new premise or a proof claim.

## Checkpoint

No new Lean declaration has been written for the global task. No global theorem, source
contraction, or RH proof has been obtained. The active research goal remains open. Next
conjectures must address an exact nonlocal arithmetic cancellation, rather than reuse a
positive completion, a local residue landing, or a conditional source criterion.

## Verification at checkpoint

- Foreground `lake --old env lean GaloisForLFunctions/RHTower/XiWardGlobalCapRightZeroSum.lean`
  passed. This rechecks an existing frontier theorem; it is not a new global contraction.
- Temporary import audit of `ae_forall_xiWardGlobalCap_re_nonneg`,
  `ae_xiWardGlobalCap_eq_zero_iff`, and
  `riemannHypothesis_iff_norm_xiRightWardBoundarySourcePhaseCrossRatio_eq_one` passed.
  Their printed axioms were only `propext`, `Classical.choice`, `Quot.sound`.
- `scripts/formal_tools.py lint` reported two unrelated unreachable modules in concurrent
  workspace work: `RHTower.CHMDStage16GrowthPositivityCollapseAndTwoPointCriterion` and
  `HTGeometry.LogCurvatureEndpointRigidity`. No new Lean modules or umbrella changes belong
  to this global-contraction attempt.

## Open core

[OPEN CORE] The global signed arithmetic pairing and its residue trace must be related
with the required orientation, retaining the polar/Gamma/prime coupling.

## Resumed source audit, 2026-10-24

The requested endpoint remains an unconditional Lean proof of RH through WD. Neither
another receiver nor an improved finite constant meets that endpoint. Current worktree
source was read; the following conclusions are source audits, not fresh kernel audits.

### Actual parabolic source, before an infinite-packet interchange

Write `L = logDeriv xi`, `z_h = z + i h²`, and let `W` be the actual homogeneous
cubic mask. `xiWardParabolicSourceAverage_eq_incrementIntegral` gives exactly

```
A_h(z) = integral_(0<=u<=1)
  i h² (L(z_h) - L(z_h-hu)) W(z_h,hu) du.
```

`tendsto_xiWardCubicParabolicDirectionalSource` proves its pointwise limit is
`ord_z(xi)` on the strict right half-strip and zero on the left and critical line.
Its finite-packet version uses only a finite sum of these pointwise limits. In the
proof, continuity is obtained from `completedFluxGermAt_analyticAt_zero z` at each
fixed center. It provides no common radius or majorant as the center ranges over
all zeros. Other zeros may approach either `z_h` or the moving segment `z_h-hu`.
Consequently an infinite-packet dominated-convergence step still requires an actual
source bound; summability of the *limiting* Stieltjes weights does not provide it.
No uniform zero separation is being asserted or assumed.

This does not disprove a suitably weighted infinite-packet landing. Such a landing,
even if established, would still need a signed source estimate to prove cap vanishing.
Replacing this average with a different circular or area average would require a new
comparison with the literal WD current; it cannot be silently substituted.

### Joint theta form already retains the continuous source

The resummation proposal above must start from, rather than recreate,
`ThetaFullArithmeticGroundForm.thetaFullArithmeticQuadratic_eq_energy_difference`:

```
thetaFullArithmeticQuadratic chi
  = thetaPrimeScalingEnergy ... chi
    - thetaGammaPolarScalingEnergy ... chi.
```

Its left side retains the compensated Gamma quadratic, both polar translations,
the archimedean constant and prime cross pairing. Both continuous integrals are
proved integrable. `WeilPhiDoobDivisorEnergy.primeEnergy_eq_tsum_divisorEnergy`
separately retains every theta index and prime power, with absolute convergence.
Its positivity theorem concerns the prime term alone, not this energy difference.
Thus merely changing the order of those already justified sums is not a new sign
mechanism. The missing comparison must pay the continuous energy with the full
prime energy on the relevant source class.

The later `CCMThetaGroundRHCriterion` already proves the exact comparison with
the full restricted Weil form, despite the earlier ground-form module's comment
leaving that comparison open. In particular,
`ccmRestrictedWeilSourceQuadratic_eq_thetaEnergyDifference` and
`riemannHypothesis_iff_thetaGroundEnergyComparison` must be reused rather than
recreated. `ThetaPositiveScalingEnergies` further gives

```
E_continuous = E_polar - E_Gamma,
Q_full = E_prime + E_Gamma - E_polar.
```

All three displayed energies are convergent and individually nonnegative.
The exact unsolved inequality is `E_polar <= E_prime + E_Gamma` for every
`ccmThetaGroundProfile u`, at every positive aperture. Thus the continuous term
must not be described as itself a positive energy. Its kernel
`2 cosh(t/2) - exp(-t/2)/(1-exp(-2t))` changes sign.
`CCMThetaThreeEnergyComparison` already states this exact three-energy identity
and its RH equivalence; it also proves a uniform strict gap on a nonempty
small-aperture range. These are existing results, not a new contribution here.

### Finite cubic cancellation: exact scope of the available source law

`PrimeBurnolThetaCubicTraceCancellation` gives finite density-weighted commutator
identities. The stronger existing `PrimeBurnolThetaQuarterTurn` even allows an
arbitrary prime-mixing reporter that is scalar in the two theta coordinates:
the full cubic anticommutes with the common quarter turn, so each theta block is
traceless. This finite cancellation is real, but no source-to-WD trace comparison
follows from it. The separate `PrimeBurnolFourierJetThetaClosure` classification
shows why assuming an ordinary closed common theta action is not permissible.
The complete mixed-prime cubic, rather than its separate factors, must be analyzed
on its actual source domain if this candidate is pursued.

### Current conjecture and proof obligation

Attack the literal inequality `E_polar(chi) <= E_prime(chi) + E_Gamma(chi)` for
every compact smooth theta ground profile `chi`, with no aperture restriction.
The proposed mechanism is a *joint* prime--Gamma cancellation identity which
retains all mixed-prime terms before applying the directed Ward readout.
An adequate identity must prove the inequality with its native coefficients;
neither a positive completion nor a scalar theta trace is sufficient. The
inequality is the existing endpoint, not an input to any proposed theorem.

[OPEN CORE] No such identity or source estimate has been derived. No new Lean
theorem is claimed, no route is retired, and no progress in the closing sign is
claimed from these audits. Next work must attack that joint arithmetic difference
directly, rather than reprove cap convergence or finite multiplicity extraction.

Verification: direct foreground `lake --old env lean
GaloisForLFunctions/RHTower/CCM/CCMThetaGroundRHCriterion.lean` passed. A separate
import audit checked the types and transitive axioms of the energy-difference
identity, the ground-energy RH equivalence, and the polar-minus-Gamma identity;
only `propext`, `Classical.choice`, and `Quot.sound` occurred. These checks verify
existing results, not the missing source inequality.

## Follow-up after the route-progress clarification

The Gaussian-background paper theorem is deferred: it supplies model coefficient
signs, not a premise of the actual global contraction. No new criterion, numerical
improvement, or no-go theorem is being substituted for the requested source bound.

Further corpus searches and source inspection checked three possible inputs:

1. `PrimeBurnolThetaQuarterTurn` cancels every theta-neutral prime-mixing trace,
   including off-diagonal prime entries. Its exact general-reporter formula retains
   the theta diagonal difference and off-diagonal sum. Thus the missing comparison
   is not repaired by allowing a larger neutral reporter class. No identification
   of the WD signed reporter with that neutral class has been proved.
2. `PrimeBurnolCompactCalculus.primeBurnolCompactWordSpan_closure_eq` already
   generates every compact correction from the literal prime operator. This is
   source generation, not a norm bound for a correction to the completed cubic or
   a proof that the actual signed WD readout is trace-class. Reusing compact
   generation alone would leave the same mathematical estimate unpaid.
3. `ThetaPrimeGammaCutEnergy.thetaPrimeGammaCutEnergy_eq_tail` and
   `thetaPrimeGammaCutEnergy_pos` already prove the literal single-cut difference
   is the positive tail `integral_(x,infinity) 2*t*Phi(t)^2 dt`. This is stronger
   than positivity of the individual prime links. It still gives only diagonal
   cut data; the mixed-cut pairings needed for arbitrary smooth profiles have
   not acquired a source-derived quadratic bound. The existing continuous-kernel
   orientation theorem also prevents treating the whole coupling as pointwise
   nonpositive. No inference from these cut signs to full form positivity is made.

These are exact source audits, not new formal results. The target remains the
literal all-aperture inequality `E_polar <= E_prime + E_Gamma` on the existing
CCM theta profiles, with all mixed terms retained. No closing input has been
proved in this batch, no mathematical frontier movement is claimed, and the
RH goal remains open. No Lean source or umbrella was changed in this batch;
unchanged existing modules were not compiled again.
