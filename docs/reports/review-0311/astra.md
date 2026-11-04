**Astra — critical review of Fable and the research frontier**

Companion: [hostile audit of both reports on routes without Weil positivity, and without positivity or spectral theory](astra-routes-review.md). It checks every proposed route, identifies omitted corpus mechanisms, and gives separate priorities under both exclusions.

Follow-up: [three research programmes and proposed mathematical fields](astra-research-programmes.md) for signed quadrature, sparse arithmetic histories and adaptive factorization transport.

Fable contains a useful catalogue, but its recommendation to concentrate the programme on the odd unit window is not supported by its arguments. Its proposed induction uses a theorem that assumes the positivity being proved. Its two-site optimization claim does not follow from two-site detection. Its prohibition on losing constants contradicts existing RH receivers. These defects affect the proposed route, not merely its presentation.

The strongest research direction exposed by this audit is **extending the complete form's established small critical band to arbitrarily large critical multiples, or removing the surviving aliasing compensation on each window profile**. The source now contains whole-space positivity and a quantitative floor on one fixed critical band, with a horizon threshold uniform over all coefficient vectors and profile families. Joint control at that scale is therefore already constructed. The remaining arithmetic losses must be studied in their dependence on the critical multiple, retaining charges that disappear in input-energy limits. Uniform signed theta-jet positivity remains an independent lane. The odd unit window is a useful local problem; the corpus does not establish it as the uniquely privileged entrance to RH.

The continuation now excludes one tempting shortcut: the current absolute pole-collar cost has a proved lower bound κR² at the cutoff used in the small-band proof. Improving constants in that norm cannot yield all-R continuation. The checked nonzero signed pole–window response instead directs the attack toward exact mixed payment or a different decomposition; the all-R low packet alone does not settle its complement. `[K]`

Evidence below comes from local Lean statements, definitions and proofs. `[L]` means source inspected, not a fresh kernel or transitive-axiom audit; `[D]` marks an elementary deduction; `[P]` marks a research proposal; `[K]` marks a subsequent kernel-checked continuation result. The original review was source-only. Research priorities are judgments about the available mechanisms, not theorems excluding every other possible proof.

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

The window infimum is now formalized as `windowThreshold A`. It decreases with aperture; it is infinite exactly when the unweighted window form is nonnegative. Below it every nonzero fixed window test has a positive pencil and eventually positive horizon energy; above it some test has eventually negative horizon energy. The source does not supply a threshold uniform over those tests or an attained minimizer. RH is equivalent to this threshold being infinite at every aperture. This confirms the continuation target without proving continuation. [Source: TheCriticalThresholdOfAWindow.lean](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/TheCriticalThresholdOfAWindow.lean); its [formalization card](../../drafts/pipeline/3-formalized/the-critical-threshold-of-a-window.md) records checks with the standard three axioms. `[L]`

**The small critical band and its window consequences are already constructed in source.** [CompleteWeilCriticalMultipleAndWindowCorollaries.lean](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CompleteWeilCriticalMultipleAndWindowCorollaries.lean) supplies a common `K₀>0`, with `2K₀≤1`, such that eventually in N the complete matrix is positive definite for **every** `1≤c≤2K₀(log N)^(1/8)` on the whole horizon space. Its `exists_universal_horizonGram_nonneg_and_zero_negIndex_at_critical_multiple` puts the eventual N threshold **before** the quantifiers over dimension and profile family. This is stronger than eventual positivity separately for each fixed family. The imported producer even gives `completeWeilEnergy ≥ κ₀‖x‖²/(2c⁷)` on the whole space, not just the pole-orthogonal subspace. These are premise-free source statements; the WIP and its transitive axioms have not been freshly checked by executing Lean. `[L]`

For every window length, the resulting limit is nevertheless the **compensated** form

\[
a_\varphi\mathcal Q(H)+\frac{7J(1)}R\|H\|_{-8}^2\ge0,
\qquad 0<R\le(2K_0)^8.
\]

The vanishing index is that of `pencilGram`, not the index of the unweighted Weil window form. Strict pencil positivity holds for independent families; strict mixed untwisted/Ramanujan-twisted positivity is eventual for each chosen family, fixed finite Ramanujan combination and critical schedule. Its eventual threshold follows those choices, unlike the universal nonnegative horizon-Gram threshold. `[L]`

The all-window weighted floor itself has an independent proof in [OneCriticalMultiplePaysEveryWindow.lean](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/OneCriticalMultiplePaysEveryWindow.lean): `Q(H)≥−C₈‖H‖²_{−8}` with C₈ independent of aperture. The WIP's joint theorem explicitly shrinks K₀ to satisfy this bound, invokes `pencilGram_posDef_below_apertureIndependentMultiple`, then transfers strictness through `mixed_inherit_of_pencil_pos`. These strict corollaries therefore supply no additional continuation in R. A sufficiently large coefficient `7J(1)/R` makes the pencil positive even when `Q(H)` is negative. For each fixed H, extending the compensated inequality to an unbounded sequence `R→∞` would give `Q(H)≥0`; the WIP does not construct that extension. `[L/D]`

A bounded extension is now verified in [JointPolePaymentExtendsTheCriticalRatio.lean](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/JointPolePaymentExtendsTheCriticalRatio.lean). Keeping the two pole moments correlated replaces their separate cost `1/(p+1)+1/(p−1)` by `d(p)=1/(sqrt(p+1)sqrt(p−1))−1/p`. With `Cjoint(p)=|gammaBracket(0)|+2 exponentialPrimeMass(p)+d(p)`, the certified window-pencil interval reaches `Rjoint=7J(1)/(aφ Cjoint(8))`, strictly beyond the old natural weighted-floor threshold. Scalar nonnegativity includes its endpoint; independent finite pencils and their eventual horizon Grams are strict below it. Audited declarations use only `[propext, Classical.choice, Quot.sound]`. This does **not** enlarge the proved whole-space band or remove compensation; no comparison with that band's independent threshold is claimed. [Exact scope and proof](../../drafts/pipeline/3-formalized/joint-pole-payment-extends-the-critical-ratio.md). `[K]`

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

The gauge programme now has a sharper obstruction to explaining the half-power law through the pole alone. For every `0<b<1` and `a<b`, some gauge point agrees with the trivial prime source to `O(N^b)` but fails the pole-subtracted `O(N^a)` law. Thus information shared by all points with that coarse pole agreement cannot force the finer exponent. Its positive survivor is an exact classification: the pole-subtracted exponents fill `[Θ,1]`, where Θ is the zeta-zero abscissa, and the trivial point attains the minimum. Identifying that minimum with `1/2` remains RH. [Obstruction](../../../formal/GaloisForLFunctions/ArithmeticGaugeTheory/ThePoleDoesNotDecideTheHalfPowerLaw.lean), [classification](../../../formal/GaloisForLFunctions/ArithmeticGaugeTheory/ThePoleSubtractedSpectrumIsAnInterval.lean). Their formalization card records successful individual checks and standard transitive axioms; source proofs were inspected here. `[L/D]`

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

The complete-form test is now stronger: for coherent harmonic-neutral prime charge `t`, cutoffs `Q=X^a`, horizons `N=X^d`, and fixed integers `0<a≤d`, the raw complete energy tends to `t²(d/a−1/2)` at **every** fixed critical multiple `K>0`. Its logarithmically normalized physical energy tends to zero. This applies to nonnegative admissible profiles, including the tilted spline; at `Q=N` the raw limit is `t²/2`. [Source: PrimeChargeCompleteEnergy.lean](../../../formal/GaloisForLFunctions/CriticalScaleArithmeticRigidity/ReceivingCharges/PrimeChargeCompleteEnergy.lean); its [research card](../../drafts/pipeline/1-in-progress/critical-overlap-receiving-charge.md) records successful individual checks with the standard three axioms. `[L]`

The signed complementary pairing is now established too: at `Q=X²`, `N=X⁴⁰`, the physical charge vector v has a literal receiver r in the exact conductor complement with `‖r‖²→1/20` and `⟨Bv,r⟩→t/80`, although v's physical energy tends to zero. But the receiver's energy grows: `⟨Br,r⟩/log N→1/20`. The corpus now proves the **positive** Schur determinant limit `6239t²/6400` and eventual positivity on the entire two-dimensional span for `t≠0`. Nonzero receiving charge defeats control by vanishing input energy alone; it does not defeat Schur control retaining the receiver's cost. [Signed pairing](../../../formal/GaloisForLFunctions/CriticalScaleArithmeticRigidity/ReceivingCharges/PrimeChargeSignedReceiver.lean), [complete Schur theorem](../../../formal/GaloisForLFunctions/CriticalScaleArithmeticRigidity/ReceivingCharges/PrimeChargeSchur.lean). Their card records successful individual checks. `[L]`

**The obstruction now reaches raw complete energy.** Finite prime-scale distributions have an exact positive limiting form `Σ_(k<d)(d−k−1/2)f_k²`. Dividing charge t among M terminal dyadic bands gives raw complete energy tending to `3t²/(2M)`. Consequently, at every fixed critical multiple and arbitrarily large horizons, exact charge t survives arbitrarily small adjunction mass, raw input square and absolute raw complete energy simultaneously. No horizon-independent constant can bound charge squared by their sum. [Scale form](../../../formal/GaloisForLFunctions/CriticalScaleArithmeticRigidity/ReceivingCharges/PrimeChargeScaleForm.lean), [raw-cost obstruction](../../../formal/GaloisForLFunctions/CriticalScaleArithmeticRigidity/ReceivingCharges/PrimeChargeRawObstruction.lean). These are stronger source theorems than the single-prefix example; their card records completed checks. `[L]`

The positive survivor is an exact capacity: for prime coordinates P below N, `C(P,N)=Σ_(p∈P)(log p/p)/H_(floor(N/p))`, and minimum dilation energy at charge t is `t²/C(P,N)`, attained uniquely by `b_p=t/[C(P,N)H_(floor(N/p))]`. [Source: PrimeIncidenceReceivingCapacity.lean](../../../formal/GaloisForLFunctions/ArithmeticCouplingTheory/ReceivingCharges/PrimeIncidenceReceivingCapacity.lean). The missing issue is joint growth of capacity, complete energy and mixed window pairing on the critical clock. The dyadic theorem fixes M before taking the horizon limit; it supplies no bound at a prescribed rate such as `1/c_N`. Its construction uses `N=X^(2^(M+1))`, so complexity and physical scale cannot be treated as independent. Uniform growing-complexity transport, including conductor fibres, remains open. At a fixed conductor cutoff, the checked centered raw energy is asymptotic to `c_N Σ_(m≠1)J(m)a_m²/R` and diverges for every nonzero nonpolar packet, despite vanishing normalized output. Thus fixing a large cutoff first cannot supply a cheap raw corrector on all later horizons. [Source: FixedChargeJordanLimit.lean](../../../formal/GaloisForLFunctions/CriticalScaleArithmeticRigidity/ReceivingCharges/FixedChargeJordanLimit.lean); its receiving-charge card records the successful individual audit. `[L/D/P]`

**The common-fibre WIP carries arbitrary finite receiving vectors.** With mode bound J, cutoff `J!X²` and horizon `X⁴⁰`, its statements give prescribed coordinates `t₁,…,t_J`, raw complete energy tending to `(39/2)Σt_m²`, vanishing physical energy, and signed complementary pairings tending to `t_l/80`. Its receivers are projected contrasts on `[X³⁸,X⁴⁰]`: their logarithmic length grows as `2log X`. They lie outside the fixed compact terminal-profile problem below. This exposes a larger arithmetic receiving space; its uniform joint energy payment remains open. [Simultaneous assembly](../../../formal/GaloisForLFunctions/CriticalScaleArithmeticRigidity/ReceivingCharges/SimultaneousCompleteReceivingLaw.lean), [receiver definition](../../../formal/GaloisForLFunctions/CriticalScaleArithmeticRigidity/ReceivingCharges/CoprimePrimeChargeWindowScales.lean). The common-coordinate inputs are recorded as checked; the complete simultaneous assembly remains unchecked on its [programme card](../../drafts/pipeline/1-in-progress/critical-overlap-receiving-charge.md). `[L/P]`

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

**The complete fixed-conductor sign is now resolved at every positive critical ratio.** For fixed positive conductors m,l, an admissible compact C² profile φ, and c_N≥1 with c_N⁸/log N→R>0,

\[
\frac{\log N}{c_N}
\left\langle B_{\varphi,c_N,N}v_m-E_m(c_N)v_m,v_l\right\rangle
\longrightarrow
 a_\varphi\bigl(2+\gamma-\log(4\pi)\bigr)\,[m=1][l=1].
\]

Here B is the literal complete Weil matrix and E_m the completed conductor energy. The constant `2+γ−log(4π)` is positive by the existing `poleSharpConstant_pos`. The result holds more generally when c→∞ and c⁴(log N)²/N→0. Its seven-channel assembly passes the actual-path no-olean audit with `[propext, Classical.choice, Quot.sound]`. [Source: TheCompleteCriticalResidueIsSupportedAtThePole.lean](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/TheCompleteCriticalResidueIsSupportedAtThePole.lean). This determines the signed contribution of all seven channels. `[K]`

The cancellation retains arithmetic receiving terms. The upward-prime residue is `−aφ(γ+1)δₘ₁δₗ₁` and enters with a minus sign; the joint Gamma–center residue is `aφ(1−log(4π))δₘ₁δₗ₁`. Nonpolar diagonal terms and the divisor-jet receiving column cancel. Ratio-prime, self and pole replacement errors vanish. [Upward source](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/TheCriticalUpwardResidueIsSupportedAtThePole.lean), [joint Gamma–center source](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/TheGrowingGammaCenterResidueIsSupportedAtThePole.lean). `[K]`

**The specified growing low packet now stays positive at every fixed R>0.** For the tilted spline, put `Q_N=floor((log N)^(13/32))`, `y=Σ_(1≤m≤Q_N)b_m v_m` and `g=2+γ−log(4π)`. For every ε>0, eventually in N and uniformly over all real coefficients b,

\[
\left|\langle B_Ny,y\rangle-\sum_{1\le m\le Q_N}E_m(c_N)b_m^2
       -a_\varphi g\frac{c_N}{\log N}b_1^2\right|
\le\varepsilon\sum_{1\le m\le Q_N}E_m(c_N)b_m^2.
\]

Thus `⟨B_Ny,y⟩≥(1/2)ΣE_m b_m²` eventually at every fixed positive critical ratio. The proof uses the summable relative square envelope `C_R/(m³l³)` below overlap, a separate decaying estimate above overlap, and a vanishing energy-weighted Gram discrepancy. This is uniformity on a prescribed growing packet, beyond fixed-pair convergence. The main transfer and its transitive axioms pass the actual-path Lean check with `[propext, Classical.choice, Quot.sound]`. [Source: TheCriticalLowPacketRetainsItsSignedPolarPart.lean](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/TheCriticalLowPacketRetainsItsSignedPolarPart.lean). `[K]`

The threshold may depend on R. The theorem neither controls the entire horizon space nor pays its mixed pairing with the low packet. The dual collar budget, far reserve and prefix/window coupling remain separate obligations with surviving R and R² losses. Those are now the relevant places to seek signed cancellation; low-packet self-positivity itself is no longer the missing all-R theorem. `[D/P]`

**Every fixed critical window survives removal of this whole low packet.** Let P_N be its actual orthogonal projection and x_N the horizon vector of a bounded profile supported in a fixed interval. At every R>0, `‖B_N P_N x_N‖→0` and `⟨B_N(x_N−P_Nx_N),x_N−P_Nx_N⟩−⟨B_Nx_N,x_N⟩→0`. For compact C² profiles, the complement therefore carries the same compensated window limit, including `7J(1)/R`. This localizes any negative compensated window in the complement; it does not assert one exists. The four endpoints pass their actual-path check with the standard three axioms. [Source: CriticalWindowsSurviveLowConductorRemoval.lean](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CriticalWindowsSurviveLowConductorRemoval.lean). Orthogonal removal is not energy minimization: growing corrector coefficients require a separate inverse-energy mixed estimate. `[K/D]`

**The relevant frontiers have different missing quantifiers.** Collapsing them to one scalar hides what must be proved.

| Route | Actual established reach | Missing RH-strength step |
|---|---|---|
| Complete arithmetic matrices | Whole-space positivity and a `κ₀/(2c⁷)` floor throughout one fixed small critical band, with a threshold uniform in vectors and profiles; source proof inspected, no fresh Lean execution. | Extend to every required critical multiple. Full complementary interaction is already paid within the small band. |
| Growing conductor packet | At every fixed R>0, the full packet through `(log N)^(13/32)` retains its positive polar term and half its conductor energy, uniformly over coefficients. | Control its mixed pairing with the horizon complement and the complement's signed energy. The checked packet theorem supplies neither. |
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

1. **Remove the small-critical-multiple restriction in the existing joint estimate.** Retain the checked all-R low-packet approximation, including its positive polar term. The original assembly also chooses K small for the dual-collar residual and far reserve; these bounds remain to improve. Their normalized losses include

   \[
   \frac{c^8}{\log N}=(2K)^8=R,
   \qquad \frac{c^{16}}{(\log N)^2}=(2K)^{16}=R^2.
   \]

   Increasing N at fixed K does not make these losses vanish. The concrete next question is which leading signed interaction the current absolute residual bounds discard, and whether retaining it can extend the allowed R. Derive that interaction as a function of R, in the same prefix/collar norms that already pay the Schur coupling. Establishing a larger finite range is a partial advance; an unbounded range or a source-derived vanishing compensation is the RH-strength target. Repeating the small-band assembly is not the next task. `[L/P]`

   There are two distinct landing choices: whole-space positivity for every K via the conductor-Gram receiver, or compensated positivity at unbounded R separately for each fixed window profile, sufficient to let the aliasing term vanish. The latter does not require a universal threshold over all profiles. The prime-charge corpus supplies finite scale distributions and arbitrarily small raw complete costs, but their fixed-complexity limits do not pay a critical window. Its exact dilation capacity now satisfies `C_N=log log N+O(1)`: for every nonzero fixed charge t, the minimum dilation cost `t²/C_N` obeys `c_N t²/C_N→∞` at every positive critical ratio. Thus this cost is too large at the reciprocal-overlap scale. This is a proved boundary for the dilation model, not a lower bound for the complete signed energy. The surviving question is whether complete arithmetic interactions change that rate while preserving the mixed receiving response. [Capacity and critical-scale corollary](../../drafts/pipeline/3-formalized/critical-receiving-capacity-growth.md). `[K/D/P]`

   A concrete signed test is the [critical pole–window transport conjecture](../../drafts/pipeline/1-in-progress/critical-pole-window-signed-transport.md): determine `sqrt(log N)/c` times the complete pairing of the normalized pole vector with a terminal window. The corpus's exact continuous pole action supplies a candidate boundary–Chebyshev functional. Discrete aliasing and possible nonpolar boundary sources remain explicit open problems. This would identify the benefit of growing arithmetic correctors; it must not be inferred from ordinary orthogonal projection. `[P]`

   **The complete polar source is now checked on interior terminal windows.** For `F(x)=h(log x)` supported in a fixed interval `(δ,η)⊂(1/2,1)`, every critical clock with `c_N⁸/log N→R>0` satisfies

   \[
   \frac{\sqrt{\log N}}{c_N}\langle B_Nv_1,x_N\rangle
   \longrightarrow a_\varphi\int_0^1F(x)
     \left[\frac1x-\frac12\log(1-x^2)-\log(2\pi)\right]dx.
   \]

   This is the literal complete-matrix pairing, independent of R, with no surviving aliasing cross term on this support. Both prime boundary channels vanish exactly. The signed Gamma and near-center terms cancel Euler's constant and `∫F log x`; the four remaining errors vanish. The proof retains log c times the **actual** near Gram before taking limits. [Exact assembly and limit](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/TerminalPolarSourceAboveHalf.lean), actual-path audit with `[propext, Classical.choice, Quot.sound]`. `[K]`

   **Every fixed nonpolar conductor has zero complete source on this same support.** The full-center charge `−Λ(m)∫F` cancels the opposite divisor-jet charge, including prime-power conductors; the remaining channels vanish. Thus the fixed-conductor response is exactly polar for every R>0. [Complete nonpolar assembly](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/TerminalNonpolarSourceAboveHalf.lean) passes its actual-path audit with the standard three axioms. General terminal support and uniformity through a growing packet remain separate obligations. `[K/P]`

   The local source is nonzero: `F(x)=tiltedUnitSpline(256x−254)` is nonnegative, supported in `[127/128,255/256]`, and has strictly positive source mean. The proof uses `(2π)²(1−x²)<1` on its support, with no numerical experiment. [Checked witness and complete mixed limit](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/TerminalPolarSourceIsNonzero.lean), with the standard three axioms. `[K]`

   **A growing pole corrector gives an exact, checked improvement.** Write S(h) for that polar source, `a=(∫φ)²/∫φ²`, `g=2+γ−log(4π)` and `D(R)=J(1)/R+ag>0`. For every R>0, the complete energy of `x_N+t√(log N)v₁`, divided by c_N, tends to

   \[
   a\mathcal Q(H)+\frac{7J(1)}R M_8(H)+2tS(h)+t^2D(R).
   \]

   Within the established positive band, choosing `t=−S(h)/D(R)` proves `a𝒬(H)+7J(1)M₈(H)/R≥S(h)²/D(R)`. The aliasing term remains; the correction vanishes on the kernel of S. This supplies the precise signed payment that the absolute collar estimate loses, without establishing all-R positivity. [Complete limit and optimized inequality](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/ThePoleCorrectorRetainsItsSignedWindowBenefit.lean) pass their actual-path audits with the standard three axioms. `[K/D]`

   **The existing absolute collar cost is intrinsically quadratic in R.** Put `r₁=B_Nv₁−E₁v₁` and `M_N=N/linearDefectCutoff(c_N)`. One fixed κ>0, independent of R and its critical clock, satisfies eventually

   \[
   \frac{c_N^7}{\log N}\frac{\operatorname{DualCollar}_7(M_N,N,r_1)}{E_1(c_N)}
   \ge \kappa R^2.
   \]

   Thus every fixed absolute budget is exceeded at some positive critical ratio, already by the pole residual alone. The source witness, weighted Cauchy–Schwarz and `E₁≤C/c⁷` prove this at the literal cutoff used in the small-band assembly. Refining this same absolute norm cannot remove its R² growth. The survivor is the nonzero signed terminal response: continuation must retain its interaction, change the payment, or use another decomposition. This does not exclude signed continuation or establish failure of whole-space positivity. [Checked lower bound and arbitrary-budget counterfamily](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/TheCriticalPoleHasAnIntrinsicCollarCost.lean), with the standard three axioms; [precise retired mechanism](../../drafts/pipeline/5-failed/critical-absolute-collar-budget-continuation.md). `[K]`

   **The below-overlap source envelope is now checked.** For residual `r_m=B_Nv_m−E_m v_m`, weighted collar Cauchy–Schwarz and the actual floor `E_m≥κm⁷/c⁷` give `|⟨r_m,x_N⟩|²/(c E_m)≤C_(h,R)/m⁵` for every `m≤c` at one eventual horizon. Restoring `E_m v_m` preserves this summable envelope for the complete pairing. [Both envelope theorems](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/TerminalConductorSourcesAreSummableBelowOverlap.lean) pass their actual-path audits with the standard three axioms. `[K]`

   Above overlap, the common positive energy floor and quadratic residual estimate give a closed paper reduction of the sum through `(log N)^(13/32)` to zero. The reference diagonal also has vanishing total contribution. Those transfers and the square-sum assembly await audits. The full signed packet form needed for optimization is already checked: its relative error is uniformly arbitrarily small after retaining the polar term. The remaining steps are square-sum convergence and finite quadratic optimization; no new uniform prime-distribution or packet-Gram input is exposed by this reduction. [Precise reduction and source declarations](../../drafts/pipeline/1-in-progress/critical-pole-window-signed-transport.md#uniformity-exposed-by-the-existing-conductor-bounds). `[L/P]`

   If optimized corrections are exhausted by that one pole functional, their subtraction has rank one and leaves compensation intact on its kernel. Such a classification would sharpen the obstruction; it would still require further growing arithmetic charges or direct control of the complementary window form. `[D/P]`

2. **A rank-uniform theta source law.** Extract from the established low-rank signed-flux payment a recurrence, factorization or comparison for the actual next Schur complement at arbitrary rank and every `0<a<1/2`. Rank nine is useful if it reveals that law or a new obstruction; a sequence of unrelated rank calculations is not a route to the missing universal quantifier. Do not assume a positive representing measure or choose replacement moments: either would evade the source sign being sought. `[P]`

3. **The full prime-blind cancellation cone as an independent route.** Study finite aggregate blind combinations with signed or complex source tests, keeping their Gram positivity and all shared blind constraints. Seek an archimedean/pole inequality stable under passage to the full cone. Nonnegative-test rearrangement is a foothold, not the required signed theorem. This lane has different immediate inputs from estimating each von Mangoldt sum, although its receiver remains RH-equivalent. `[P]`

Use the fixed-spline growth and tensor-loss theorems throughout as alternative landing criteria. An arithmetic estimate that cannot preserve a sharp window margin may still be decisive if it controls exponential rate. No new tensor estimate has been supplied here.

**Retain the odd unit window as a diagnostic, with a precise question.** Let `L(F)=∫xF(x)dx`, `b=3203/320`, and `R(F)=𝒬(F)+bL(F)²` on odd unit-window tests. The existing floor `R(F)≥‖F‖²/1000` makes the remaining question exactly

\[
b\sup_{F\ne0}\frac{L(F)^2}{R(F)}\le1.
\]

This formulation distinguishes the known positive reference form from the unproved capacity bound. It does not assume a maximizing vector exists. The source anchor for this constant is `weilQuad_add_reduced_first_moment_ge_mass` in [TheThirdOddMomentIsPaidByTheFirstFold.lean](../../../formal/GaloisForLFunctions/WindowTowerOfSpecZ/TheThirdOddMomentIsPaidByTheFirstFold.lean); the unreduced theorem cited by Fable has constant `5123/320`. The exact Gamma remainder and signed prime-two term must survive in any proposed certificate. `[L/D]` Solving the capacity bound would be a real bounded-window advance. To elevate it to the principal RH programme, the solution must also produce an independent estimate stable under further window growth; the currently cited sector lemmas do not do that.

The highest-priority question is therefore: **which retained arithmetic interaction removes the dimensionless critical-multiple losses, so that the established complete-form control survives as the aliasing compensation tends to zero?** The corpus now supplies a small-band construction, exact cancellation mechanisms and explicit stress-test families. The remaining gap is sharper than constructing joint control for the first time. The WIP does not repair Fable's circular window induction, prove unweighted window positivity, or exclude the independent routes in the companion reports.
