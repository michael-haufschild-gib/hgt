**Astra — critical review of Fable and the research frontier**

Companion: [hostile audit of both reports on routes without Weil positivity, and without positivity or spectral theory](astra-routes-review.md). It checks every proposed route, identifies omitted corpus mechanisms, and gives separate priorities under both exclusions.

Follow-up: [three research programmes and proposed mathematical fields](astra-research-programmes.md) for signed quadrature, sparse arithmetic histories and adaptive factorization transport.

Fable contains a useful catalogue, but its recommendation to concentrate the programme on the odd unit window is not supported by its arguments. Its proposed induction uses a theorem that assumes the positivity being proved. Its two-site optimization claim does not follow from two-site detection. Its prohibition on losing constants contradicts existing RH receivers. These defects affect the proposed route, not merely its presentation.

The strongest research direction exposed by this audit is **extending the complete form's established small critical band to arbitrarily large critical multiples, or removing the surviving aliasing compensation on each window profile**. The source now contains whole-space positivity and a quantitative floor on one fixed critical band, with a horizon threshold uniform over all coefficient vectors and profile families. Joint control at that scale is therefore already constructed. The remaining arithmetic losses must be studied in their dependence on the critical multiple, retaining charges that disappear in input-energy limits. Uniform signed theta-jet positivity remains an independent lane. The odd unit window is a useful local problem; the corpus does not establish it as the uniquely privileged entrance to RH.

Evidence below comes from local Lean statements, definitions and proofs. `[L]` means source inspected, not a fresh kernel or transitive-axiom audit; `[D]` marks an elementary deduction in this review; `[P]` marks a research proposal. No Lean was executed. Research priorities are judgments about the available mechanisms, not theorems excluding every other possible proof.

**Fable's central induction assumes its conclusion.** In §§2.2 and 5.1, Fable uses `collar_antisymmetric_of_frozen_negative_even` and its odd counterpart to restrict possible failures of window growth. Their hypothesis is literally:

```lean
(hpos : ∀ G : ℝ → ℝ, IsWindowTest A G → 0 ≤ weilQuad G)
```

Here `windowLevel A = N + 1`: this is positivity on the current, enlarged window. Positivity on earlier, shorter windows does not supply it. The proof starts by applying `hpos` to the test under consideration. These are consequences of successful positivity, not an independent mechanism for establishing it. [Source: TheKickIsTheCollarReflection.lean](../../../formal/GaloisForLFunctions/GrowingWindowsOfSpecZ/TheKickIsTheCollarReflection.lean), the two `collar_*_of_frozen_negative_*` theorems. `[L]`

There is a second overstatement. The even theorem concludes

\[
\int_L(H+H\circ R)^2<\int_L(H-H\circ R)^2.
\]

It does **not** conclude `H∘R = −H`. Dominance of antisymmetric mass is not membership in a pure antisymmetric sector. The source proves orthogonal splitting by the global window involution `σ_A`; it does not thereby prove four-sector orthogonality of the frozen form under the additional collar reflection. Positivity on pure collar sectors would still leave mixed pairings. Moreover, a favorable kick can have insufficient magnitude to repair a negative frozen form. `[L/D]`

The valid replacement already exists:

\[
\mathcal Q\ge0\text{ on }W_{\ell+\varepsilon}
\iff
\mathcal Q\ge0\text{ on }W_\ell
\quad\text{and}\quad
|\mathcal W(u(\cdot+\varepsilon),v)|^2
\le\mathcal Q(u)\mathcal Q(v)
\]

for every pair of shorter-window tests, with `0<ε<ℓ`. This is `window_nonneg_iff_contraction` in [WindowGrowthIsATranslationContraction.lean](../../../formal/GaloisForLFunctions/CanonicalSystemOfTheWindowTower/WindowGrowthIsATranslationContraction.lean). The missing step is an independent arithmetic bound for that mixed pairing. Renaming it sector coercivity does not discharge it. `[L/D]`

Positive salvage: retain the exact collar identities, global parity decomposition, and contraction criterion. Retire the claimed inductive inference. A future window proof must supply its cross-term estimate without current-window positivity in its premises.

**Sharp constants are not compulsory for every route.** Fable repeatedly requires “never an estimate losing a factor.” The corpus has a fixed cubic spline whose transform misses no off-line zero and proves

\[
\mathrm{RH}\iff
\forall\varepsilon>0\ \exists C_\varepsilon\ \forall t\ge0,
\quad |c_B(t)|\le C_\varepsilon e^{\varepsilon t}.
\]

This is `riemannHypothesis_iff_splineOrbit_subexponential` in [TheSplineOrbitDecidesTheCriticalLine.lean](../../../formal/GaloisForLFunctions/ArithmeticOrientationGeometry/TheSplineOrbitDecidesTheCriticalLine.lean). It needs one fixed spline and a zero exponential growth rate, not the sharp two-site constant for every bump. `[L]`

More strongly, [TheBaseIsAFixedLoss.lean](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/TheBaseIsAFixedLoss.lean) proves `riemannHypothesis_of_sublinear_tensor_loss`: bounds

\[
|c_B(t)|^k\le C_k e^{L_k t},\qquad L_k/k\longrightarrow0,
\]

imply RH. Its `riemannHypothesis_iff_fixed_tensor_loss` even permits one fixed finite exponent loss for all tensor orders. Constants `C_k` may depend on order. A loss proportional to `k` is insufficient; a sublinear loss is sufficient. `[L]`

These receivers do not supply the missing arithmetic estimate. They do refute Fable's claim that collapsing lattice margins force every proof to maintain exact sharp constants throughout. A promising estimate should be assessed by how its loss enters a proved receiver. Multiplicative constants, exponential rates, and rank-dependent losses are different quantities. `[D]`

**Two-site detection does not solve the critical-multiple optimization.** `riemannHypothesis_iff_two_site_posDef` quantifies over every nonzero compact test and every positive translation. Under failure of RH, `exists_abs_weilOrbitCorr_eq` produces some test and some separation with equality. Neither theorem identifies a minimizing test at a prescribed aperture, nor proves that a weighted Rayleigh infimum is attained by two translates. Fable §4.5(b) therefore introduces an additional conjecture while presenting it as a consequence of GWZ. [Source: RHIsDecidedOnTwoSites.lean](../../../formal/GaloisForLFunctions/GrowingWindowsOfSpecZ/RHIsDecidedOnTwoSites.lean). `[L/D]`

The proposed first-jump function also has the wrong strategic interpretation. Keep the two critical parameters distinct. Put

\[
R=\lim_N c_N^8/\log N,\qquad
a_\varphi=(\int\varphi)^2/\int\varphi^2.
\]

The source limit is

\[
a_\varphi\mathcal Q(H)+\frac{7J(1)}R\|H\|_{-8}^2,
\qquad \|H\|_{-8}^2=\int e^{-8y}H(y)^2\,dy.
\]

For a negative test, its leading threshold is

\[
R_*(H)=\frac{7J(1)\|H\|_{-8}^2}{a_\varphi(-\mathcal Q(H))}.
\]

The overlap convention `c_N=2K(log N)^(1/8)` instead gives `R=(2K)^8`. The corresponding amplitude threshold is `K_*(H)=R_*(H)^(1/8)/2`. Fable uses these parameters interchangeably. [Source: `horizon_layer_criticalCurve_exact`, TheAliasingConstantOfTheTiltedSpline.lean](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/TheAliasingConstantOfTheTiltedSpline.lean). `[L/D]`

**The small critical band and its window consequences are already constructed in source.** [CompleteWeilCriticalMultipleAndWindowCorollaries.lean](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CompleteWeilCriticalMultipleAndWindowCorollaries.lean) supplies a common `K₀>0`, with `2K₀≤1`, such that eventually in N the complete matrix is positive definite for **every** `1≤c≤2K₀(log N)^(1/8)` on the whole horizon space. Its `exists_universal_horizonGram_nonneg_and_zero_negIndex_at_critical_multiple` puts the eventual N threshold **before** the quantifiers over dimension and profile family. This is stronger than eventual positivity separately for each fixed family. The imported producer even gives `completeWeilEnergy ≥ κ₀‖x‖²/(2c⁷)` on the whole space, not just the pole-orthogonal subspace. These are premise-free source statements; the WIP and its transitive axioms have not been freshly checked by executing Lean. `[L]`

For every window length, the resulting limit is nevertheless the **compensated** form

\[
a_\varphi\mathcal Q(H)+\frac{7J(1)}R\|H\|_{-8}^2\ge0,
\qquad 0<R\le(2K_0)^8.
\]

The vanishing index is that of `pencilGram`, not the index of the unweighted Weil window form. Strict pencil positivity holds for independent families; the stated strict mixed untwisted/Ramanujan-twisted corollary is eventual for each chosen family and critical schedule. It does not assert a common strict-positivity threshold for arbitrarily varying mixed families. `[L]`

The all-window weighted floor itself has an independent proof in [OneCriticalMultiplePaysEveryWindow.lean](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/OneCriticalMultiplePaysEveryWindow.lean): `Q(H)≥−C₈‖H‖²_{−8}` with C₈ independent of aperture. A sufficiently large coefficient `7J(1)/R` makes the pencil positive regardless of whether `Q(H)` is negative. Thus all-window compensated positivity does not remove the RH obstruction. For each fixed H, extending the compensated inequality to an unbounded sequence `R→∞` would remove that term and give `Q(H)≥0`; this is an elementary deduction, not a construction supplied by the WIP. `[L/D]`

Define `R₁(A)` as the infimum over negative tests supported in `[-A,0]`, with empty infimum `∞`. Then **`R₁(A)` is nonincreasing**: the admissible class grows with `A`. Once one negative test exists, it supplies a finite upper bound for every larger aperture. A lower bound tending to infinity with `A` would therefore prove RH; it is not a sub-RH milestone. A bounded increasing lower bound is a different, much weaker statement. Attainment requires its own compactness and form-domain argument. `[D]`

Nor is continuation from one positive multiple an innocuous continuity problem. `canonicalCriticalClock_energy_negative` proves that a nonzero test on the equality face of the leading pencil has **eventually negative** finite-horizon energy on the canonical critical clock. `canonicalCriticalClock_phase_diagram` puts equality on the negative side. This is a concrete obstruction to passing through a zero margin without a new source argument. It does not assert that such a test exists for zeta. [Source: TheCanonicalCriticalClockEntersFromTheNegativeSide.lean](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/TheCanonicalCriticalClockEntersFromTheNegativeSide.lean). `[L]`

**Several global unifications suppress essential qualifications.** These corrections matter because the suppressed information is often precisely the open problem.

| Fable's claim | What the evidence permits |
|---|---|
| Everything reads “one even integer.” | The global index takes values in `ℕ∞`. Its equality with twice a sector count does not prove finiteness. Local window indices exhaust the global index by a supremum; each window is not already that global invariant. |
| The obstruction is one trivial direction, all others manifestly positive. | Particular pole terms, fixed-packet limits and the odd unit-window estimate have small exceptional sectors. This does not give a globally positive complement with paid mixed interactions. A global index bound `≤1` for the fixed spline would already prove RH. |
| Positive Euler twins force every proof to use precisely the strict Selberg Euler bound. | The twins rule out the tested weaker axiom package. Their completion has conductor `p²`, not zeta's conductor one. Exact source data or exact completion can distinguish these examples too. No uniqueness theorem for admissible proof inputs follows. |
| Off RH, the Bochner measure has mass off the gauge torus. | The positive Bochner representation is obtained after positive definiteness. A measure on that torus cannot literally have mass outside it. A generalized nonunitary spectral representation needs its own hypotheses; finite-index theory cannot silently supply unconditional finite index. |
| `−ζ′/ζ` is Herglotz on `Re s>1` because its Dirichlet coefficients are positive. | Positive Dirichlet coefficients do not imply a positive real part. The proposed starting point of §2.3 is false. |

For the index statements, see `negIndex_zetaKernel`, `zetaKernel_finiteIndex_tfae` and the separate implication `lindelof_of_negIndex_zetaKernel_lt_top` in [TheFiniteIndexStratumOfZetaIsLindelofDeep.lean](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/TheFiniteIndexStratumOfZetaIsLindelofDeep.lean), and `iSup_windowIndex` in [TheWindowIndex.lean](../../../formal/GaloisForLFunctions/CohomologyOfWindowsOfSpecZ/TheWindowIndex.lean). Finite index means finitely many off-line zeros, equivalently an on-line tail; Lindelöf is a consequence, not the listed equivalence. `[L]`

The twin's exact scope is in [PositiveFiniteEulerTwins.lean](../../../formal/GaloisForLFunctions/SelbergClass/PositiveFiniteEulerTwins.lean) and its conductor in [PositiveFiniteEulerCompletion.lean](../../../formal/GaloisForLFunctions/SelbergClass/PositiveFiniteEulerCompletion.lean). These are valuable obstructions to source-insensitive arguments. They do not close whole subjects called geometry, counts or Hodge theory. `[L/D]`

The Herglotz error has an elementary check using the Dirichlet series invoked by Fable. At `t₀=π/log 2`, absolute convergence gives

\[
2^\sigma\operatorname{Re}\!\left[-\frac{\zeta'}{\zeta}(\sigma+it_0)\right]
=-\log2+\sum_{n\ge3}\Lambda(n)(2/n)^\sigma\cos(t_0\log n)
\longrightarrow-\log2.
\]

Thus its real part is negative for large `σ`. Positive Fourier weights and positive real part are different properties. Likewise, identifying the window Toeplitz algorithm with a Pick algorithm for `ξ′/ξ` requires an actual transform and domain theorem, not analogy. `[D]`

**The arithmetic frontier is sharper than “pay one scalar charge.”** Write `e_m` for the normalized Ramanujan mode, `F_a=Σ_{m≤M}a_m e_m`, and

\[
L_M(a)=\sum_{m\le M}(\log m+\tau(m))a_m^2,\qquad
G F_a(n)=\sum_{k\ge1}\frac{\Lambda(k)}k\,[F_a(kn)-F_a(n)],
\]

where `τ` is the corpus's `tameDifferent`. This is the actual convergent arithmetic generator, not an abstract replacement. On prime-supported input the corpus proves the exact decomposition

\[
GF_a=P_M(a)-\sum_{p\le M}\tau(p)a_p e_p,
\quad
P_M(a)=\sum_{p\le M}\frac{\log p}{\sqrt{p-1}}a_p.
\]

Its constant output is orthogonal to the prime-supported input in complete-period averaging. After removing that output,

\[
\operatorname{mean}|GF_a-P_M(a)|^2
\le \frac{\log2}{2}L_M(a).
\]

This is a positive survivor with a sharp cutoff-independent constant, not merely a no-go. See `arithmeticPrimeGenerator_primeOnly_decomposition`, `arithmeticPrimeGenerator_primeOnly_self_pairing`, and `primeCenteredGenerator_period_sq_le` in [PrimeGeneratorOrthogonalRows.lean](../../../formal/GaloisForLFunctions/CriticalScaleArithmeticRigidity/PrimeGeneratorOrthogonalRows.lean). `[L]`

The exceptional output cannot be controlled by a uniform multiple of input energy. Put `B_M=Σ_{p≤M}log p/p`. The explicit coefficients

\[
a_p=\frac{t}{B_M}\frac{\sqrt{p-1}}p
\]

have output charge `P_M(a)=t` and energy `L_M(a)=t²/B_M→0`. Literal harmonic pole projection changes the constant input coefficient while preserving both generator and adjunction energy. [Source: `normalizedPrimeCharge_response_and_energy` and `exists_harmonic_neutral_arbitrarily_small_energy_charge`, VanishingEnergyCharge.lean](../../../formal/GaloisForLFunctions/CriticalScaleArithmeticRigidity/VanishingEnergyCharge.lean). `[L]`

This survives physical sampling. `exists_harmonic_neutral_physical_vanishing_charge` states: for any prescribed `t`, any `ε>0`, and any lower conductor cutoff, some larger `M` works for every `N≥M`; there is an actual harmonic-pole-neutral packet with

\[
L_M(a)<\varepsilon,\qquad
\frac1{\log N}\sum_{n\le N}\frac{F_a(n)^2}{n}<\varepsilon,
\qquad
\frac1{\log N}\sum_{n\le N}\frac{(GF_a(n)-t)^2}{n}<\varepsilon,
\]

and complete-period generator mean exactly `t`. [Source: PhysicalHorizonCharges.lean](../../../formal/GaloisForLFunctions/CriticalScaleArithmeticRigidity/PhysicalHorizonCharges.lean). `[L]`

Consequently, convergence in these energy and physical-input norms can erase a nonzero arithmetic receiving charge. Removing the input pole does not remove it. Any argument passing to a limit must retain that charge or prove its cancellation inside the complete form. Conversely, a large generator norm does not establish a negative Weil direction: the exact self-pairing above already shows why norms and signed quadratic forms must be distinguished. `[D]`

There is also a sharp limit to improving residual norms. `exists_primeResidual_packet_relative_log_sq_le` separates scalar coefficient mass from a quadratic logarithmic cost multiplying adjunction energy. `eventually_coherentPrimeResidual_logarithmic_lower` exhibits actual prime coefficients attaining that logarithmic scale. An indiscriminate smaller norm bound is therefore the wrong target. [Sources: RelativePrimeResidual.lean](../../../formal/GaloisForLFunctions/CriticalScaleArithmeticRigidity/RelativePrimeResidual.lean), [SharpPrimeResidualScale.lean](../../../formal/GaloisForLFunctions/CriticalScaleArithmeticRigidity/SharpPrimeResidualScale.lean). `[L]`

The corpus supplies more than a scalar example. `normalizedPrimeModeSource_mul_of_coprime` proves

\[
G(e_{ab})=e_bG(e_a)+e_aG(e_b)\qquad((a,b)=1),
\]

and the adjunction weights add under the same product. [Source: CoprimeModeTransport.lean](../../../formal/GaloisForLFunctions/CriticalScaleArithmeticRigidity/CoprimeModeTransport.lean). This is an exact arithmetic transport law available for studying nonconstant receiving channels. Proving this product rule again would not advance the frontier. Classifying its consequences for growing-conductor limits would. `[L/P]`

**There is already positive arithmetic structure to connect to the full form.** `divisorJetEnergy_eq` completes the divisor jet to

\[
\sum_{m\mid D}\sum_{k\mid m}\Lambda(m/k)\varphi(k)(f(m)-f(k))^2\ge0,
\]

with zero energy exactly on constant divisor profiles when `D>0`. This is an exact completion with incoming and outgoing arithmetic charges. It is not yet identification with the full finite-horizon Weil block. [Source: DivisorJetGroundState.lean](../../../formal/GaloisForLFunctions/SuccessorShellArithmetic/Conductor/DivisorJetGroundState.lean). `[L]`

`completeWeilEnergy_packetVector_at_every_overlap` gives the literal complete energy as prime jump energy, affine edge energy, diagonal terms, negative shell degree, center, far cross, pole error and archimedean overlap. For the nonnegative tilted-spline profile the affine weights are nonnegative. The identity retains the terms that a standalone sum of squares does not pay. [Source: TheCompleteFormAtEveryOverlap.lean](../../../formal/GaloisForLFunctions/ArithmeticCouplingTheory/TheCompleteFormAtEveryOverlap.lean). `[L]`

There is a concrete additive–multiplicative reserve: `prime_successor_edges_control_nonconstant_packets` uses actual edges `(n,pn+1)` to bound nonconstant packet mass by affine energy, with factor

\[
\frac1{64}\left[B_{\lfloor N/(16M^2)\rfloor}-B_M\right].
\]

Its usefulness depends on the conductor/horizon range; it does not pay every remaining signed term. [Source: ThePrimeSuccessorEdgesControlNonconstantPackets.lean](../../../formal/GaloisForLFunctions/ArithmeticCouplingTheory/ThePrimeSuccessorEdgesControlNonconstantPackets.lean). `[L]`

Joint shell–pole cancellation is also beyond the single witness stage: arbitrary bounded base profiles and mean-zero periodic perturbations have source-level identities and uniform estimates. [Sources: WeightedBaseCollapse.lean](../../../formal/GaloisForLFunctions/SuccessorShellArithmetic/TopBand/WeightedBaseCollapse.lean), [NonpolarJointCancellation.lean](../../../formal/GaloisForLFunctions/SuccessorShellArithmetic/TopBand/NonpolarJointCancellation.lean). At a small fixed critical multiple, the growing-packet/complement comparison is now assembled in [CriticalMultipleCompleteWeilPositivity.lean](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/CriticalMultipleCompleteWeilPositivity.lean). It splits low conductors, two intermediate bands and the far complement, and pays their mixed pairings with separate prefix and weighted-collar reserves. It would understate the frontier to call this comparison wholly missing. `[L]`

The decisive inputs are concrete arithmetic estimates. [LogarithmFreeCriticalConductorResiduals.lean](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/LogarithmFreeCriticalConductorResiduals.lean) removes logarithmic losses using exact near-Gamma/center cancellation, zero-mean Ramanujan periodicity, and the adjoint downward-divisor identity for upward prime pairings. [TheTopCollarHasADyadicSeventhPowerReserve.lean](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/TheTopCollarHasADyadicSeventhPowerReserve.lean) supplies the collar mass `Σ(N/n)⁷x_n²`; its dual residual weight is `(n/N)⁷`. This is an implemented instance of retaining the complete arithmetic interaction. Extending its usable critical-multiple range remains open in these sources. `[L/P]`

**The relevant frontiers have different missing quantifiers.** Collapsing them to one scalar hides what must be proved.

| Route | Actual established reach | Missing RH-strength step |
|---|---|---|
| Complete arithmetic matrices | Whole-space positivity and a `κ₀/(2c⁷)` floor throughout one fixed small critical band, with a threshold uniform in vectors and profiles; source proof inspected, no fresh Lean execution. | Extend to every required critical multiple. Full complementary interaction is already paid within the small band. |
| Critical window pencils | One small range of `R=c⁸/log N` gives compensated positivity and zero pencil index at every aperture; strict positivity for independent families. | Remove the `7J(1)/R` weighted aliasing term, for example through unbounded R. All apertures at bounded R do not do this. |
| Unweighted local windows | Strict short-window floors; exact global parity and translation-contraction laws; strong moment-zero subspaces of the odd unit window. | Independent mixed-pairing control through all lengths. The compensated pencil result does not establish this induction. |
| Theta signed jets | Actual signed Hankel matrix of size eight is positive definite for every `0<a<1/2`. | All ranks for the prescribed source moments, with uniform signed-flux payment. |
| Fixed spline orbit | One fixed spline detects every off-line zero; subexponential growth and sublinear tensor-loss receivers are exact. | A source-derived zero growth rate or sublinear tensor loss. |
| Prime-blind cone | Full aggregate prime-blind positivity is unconditionally equivalent to RH. A restricted nonnegative-test reduction is available. | Positivity on the full cone of aggregate cancellations among complex tests. |
| Index / two-prime coupling | Exact index receivers and strong obstruction models. | An actual arithmetic input excluding infinite or escaping off-line configurations; generic divisor geometry is insufficient. |

The first row now rests on the explicit producer `exists_tiltedUnitSpline_spectralFloorWeilMatrix_posDef_at_critical_multiple` and its complete-form corollaries in `CriticalMultipleCompleteWeilPositivity.lean`, then the WIP's window synthesis. The aggregate file is not the source of the arithmetic estimates. An older frontier-map verification flag does not establish that those estimates or their assembly are absent; equally, source text and appended `#print axioms` commands are not evidence that a fresh kernel audit has run.

The exact receiver is `riemannHypothesis_iff_conductorGram_nonneg_eighthRoot`: **for every `K>0`, eventually in `N`, for every coefficient vector over all conductors `e≤N`**, the full conductor Gram at `2K(log N)^(1/8)` is nonnegative. Fixed-conductor diagonals, a non-effectively growing positive packet, and one small `K` do not supply these quantifiers. [Source: TheCrossConductorPairings.lean](../../../formal/GaloisForLFunctions/HodgeTheoryWithoutVarieties/TheCrossConductorPairings.lean). `[L]`

For theta, [StrictEighthSection.lean](../../../formal/GaloisForLFunctions/ThetaCuspSections/StrictEighthSection.lean) proves `thetaCuspCenterMixedSignedHankel_eight_posDef`. [ThetaCuspCenterMixedSignedJetCompleteness.lean](../../../formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspCenterMixedSignedJetCompleteness.lean) proves that the complete signed-jet cone is equivalent to RH, with the analytic and moment-determinacy inputs derived from the actual source. This is substantive source positivity which Fable relegates to an appendix. A generic positive moment extension is insufficient: its next moment must equal the prescribed signed theta derivative. `[L/D]`

For prime-blind positivity, `PrimeBlindPositive` quantifies over finite nonnegative combinations of autocorrelations of **complex smooth tests**, whose combined symmetric samples vanish at every `log n`, `n≥2`. Individual tests need not be blind or pointwise nonnegative. See [WeilFullConeOneSidedCriterion.lean](../../../formal/GaloisForLFunctions/RHTower/WeilFullConeOneSidedCriterion.lean) and `riemannHypothesis_iff_primeBlindPositive_unconditional` in [TwistedArcMinimumPrincipleProof.lean](../../../formal/GaloisForLFunctions/RHTower/TwistedArcMinimumPrincipleProof.lean). The rearrangement result in [PrimeBlindNonnegativeConeReduction.lean](../../../formal/GaloisForLFunctions/RHTower/PrimeBlindNonnegativeConeReduction.lean) is conditional on its stated short-window inequality and applies to nonnegative, individually blind tests. It does not close the signed aggregate cone. Fable's dimension-counting heuristic does not supply this missing positivity. `[L/D]`

For coupling, the corpus constructs a simple sign/conjugation-symmetric divisor with exact spline weights, absolutely convergent real Laplace sums, bounded natural two-prime cone coupling, positive unattained width, and the full two-term Riemann–von Mangoldt count with `O(log T)` remainder. See `exists_two_prime_rvm_prescribed_spline_divisor` in [RVMCompletedSplineDivisor.lean](../../../formal/GaloisForLFunctions/ArithmeticCouplingTheory/ConeMoments/RVMCompletedSplineDivisor.lean). This is an abstract divisor, not an Euler-product realization of zeta. Its positive lesson is precise: even correct spline weights and zero counts do not replace the missing source arithmetic. It rules out that upgrade, not every arithmetic coupling route. `[L/D]`

**The next attacks should produce mechanisms that survive increasing complexity.** My priority order is:

1. **Remove the small-critical-multiple restriction in the existing joint estimate.** Start from its low-packet, intermediate-band and far-collar assembly. The low-packet proof chooses K small to absorb bilinear and dual-collar residuals; the far reserve imposes an additional smallness condition. Its normalized losses include

   \[
   \frac{c^8}{\log N}=(2K)^8=R,
   \qquad \frac{c^{16}}{(\log N)^2}=(2K)^{16}=R^2.
   \]

   Increasing N at fixed K does not make these losses vanish. The concrete next question is which leading signed interaction the current absolute residual bounds discard, and whether retaining it can extend the allowed R. Derive that interaction as a function of R, in the same prefix/collar norms that already pay the Schur coupling. Establishing a larger finite range is a partial advance; an unbounded range or a source-derived vanishing compensation is the RH-strength target. Repeating the small-band assembly is not the next task. `[L/P]`

   There are two distinct landing choices: whole-space positivity for every K via the conductor-Gram receiver, or compensated positivity at unbounded R separately for each fixed window profile, sufficient to let the aliasing term vanish. The latter does not require a universal threshold over all profiles. Use the coherent prime-charge families and the existing coprime product rule to test proposed improvements, including whether `mp` packets can retain a nonconstant receiving charge at vanishing input energy. Those classifications remain possible diagnostic work; they no longer replace the already constructed small-band comparison. `[D/P]`

2. **A rank-uniform theta source law.** Extract from the established low-rank signed-flux payment a recurrence, factorization or comparison for the actual next Schur complement at arbitrary rank and every `0<a<1/2`. Rank nine is useful if it reveals that law or a new obstruction; a sequence of unrelated rank calculations is not a route to the missing universal quantifier. Do not assume a positive representing measure or choose replacement moments: either would evade the source sign being sought. `[P]`

3. **The full prime-blind cancellation cone as an independent route.** Study finite aggregate blind combinations with signed or complex source tests, keeping their Gram positivity and all shared blind constraints. Seek an archimedean/pole inequality stable under passage to the full cone. Nonnegative-test rearrangement is a foothold, not the required signed theorem. This lane has different immediate inputs from estimating each von Mangoldt sum, although its receiver remains RH-equivalent. `[P]`

Use the fixed-spline growth and tensor-loss theorems throughout as alternative landing criteria. An arithmetic estimate that cannot preserve a sharp window margin may still be decisive if it controls exponential rate. No new tensor estimate has been supplied here.

**Retain the odd unit window as a diagnostic, with a precise question.** Let `L(F)=∫xF(x)dx`, `b=3203/320`, and `R(F)=𝒬(F)+bL(F)²` on odd unit-window tests. The existing floor `R(F)≥‖F‖²/1000` makes the remaining question exactly

\[
b\sup_{F\ne0}\frac{L(F)^2}{R(F)}\le1.
\]

This formulation distinguishes the known positive reference form from the unproved capacity bound. It does not assume a maximizing vector exists. The source anchor for this constant is `weilQuad_add_reduced_first_moment_ge_mass` in [TheThirdOddMomentIsPaidByTheFirstFold.lean](../../../formal/GaloisForLFunctions/WindowTowerOfSpecZ/TheThirdOddMomentIsPaidByTheFirstFold.lean); the unreduced theorem cited by Fable has constant `5123/320`. The exact Gamma remainder and signed prime-two term must survive in any proposed certificate. `[L/D]` Solving the capacity bound would be a real bounded-window advance. To elevate it to the principal RH programme, the solution must also produce an independent estimate stable under further window growth; the currently cited sector lemmas do not do that.

The highest-priority question is therefore: **which retained arithmetic interaction removes the dimensionless critical-multiple losses, so that the established complete-form control survives as the aliasing compensation tends to zero?** The corpus now supplies a small-band construction, exact cancellation mechanisms and explicit stress-test families. The remaining gap is sharper than constructing joint control for the first time. The WIP does not repair Fable's circular window induction, prove unweighted window positivity, or exclude the independent routes in the companion reports.
