# Arithmetic Compensation Theory (`GaloisForLFunctions.ArithmeticCompensationTheory`)

**One question.** When several exact arithmetic descriptions belong to the same source, what
signed critical-norm estimates do their compatibility conditions force that none of the
descriptions forces separately?

Arithmetic Compensation Theory — *arithmetic compatibility and compensated coercivity* (ACCC) —
studies cancellation between descriptions of the same arithmetic source. Separately divergent
pieces can cancel to leading order while their sum still exceeds the critical norm. The task is to
identify the coherent part, retain its mixed terms, and estimate the absolute remainder with
constants independent of the cutoff. Relative cancellation is the starting point, not admission.

## Place in the research

The programme connects exact source decompositions to estimates. Its model examples explain both
sides of this distinction: the prime comb has exponentially large energy because it translates a
profile to the horizon, while that translated profile has little overlap with the original test;
the large-prime Möbius–Ramanujan sector cancels against its literal complement, but the known
relative cancellation gives no cutoff-independent bound for their sum.

The governing example of this programme is the actual centred receiver

`A_ε(n) = Σ_{d ≤ n} μ(d) d^{−ε} ⌊n/d⌋ − n/ζ(1+ε)`,   `E_T(ε) = Σ_{n ≤ T} |A_ε(n)|²/(n(n+1))`,

with **admission** `∃ B_ε ∀ T, E_T(ε) ≤ B_ε`. RH is admission at positive dampings arbitrarily
close to `0` (`RHTower.riemannHypothesis_iff_cofinal_budget`), the constants allowed to deteriorate,
and the infimum of the admitted dampings at which they accumulate is `Θ − ½`
(`RHTower.receiverDampingRate_eq_zetaZeroAbscissa_sub_half`). The cofinal quantifier and the
accumulation qualifier are part of every target below.

### This programme's role

ACCC is the **compensation layer**. Where the faces produce exact identities and the finite
programmes produce leading-order cancellation, ACCC asks for the quantitative remainder and keeps
the bookkeeping that every remainder estimate needs:

* the coherent piece of a source is subtracted before any absolute value is taken;
* the mixed Gram terms, the poles, the even parts and the boundary terms stay attached until the
  cancellation they carry has been used;
* every change of representation — of norm, cutoff, gauge, scale or origin — is paid for with an
  explicit transfer term.

In the shared units its contribution is a rate: a residual exponent, a logarithmic saving, an
aperture decay, a resolution threshold. Identities and equivalent criteria count as zero.

### Connections and reading route

- **[Arithmetic Incidence Positivity](../ArithmeticIncidencePositivity/README.md).** AIP reduced the exponential obstruction of its cost side to
  one scalar, the cross-prime aggregate of the prime comb, and asked for its size (topic 8). ACCC
  answers: the aggregate is `∼ 4e^{2r}` on a smooth odd family of unit mass, the universal bound
  is attained, and on every fixed nonzero continuous compact test the comb energy is asymptotic to `4J(F)e^{2r}` with an explicit
  horizon energy `J`. The comb is a translation on slowly varying tests and an exponential
  resolvent on fixed ones; its first-power charge is `o(e^r)` on the slowly varying compact family. Shared objects: the pairing
  calculus, `primeComb`, `combEnergy`.
- **[Arithmetic Continuation and Critical Energy](../ArithmeticContinuationAndCriticalEnergy/README.md).** ACCE owns admission, the averaged budget and its
  equivalence with admission, the signed work and its prime-harmonic core. ACCC adds the rung
  between them — the positive-part budget, strictly stronger than the signed one even on monotone
  families — the exact limit of the core debt on positive intervals, the adverse first-cell work,
  and the adapted-energy (corrector) criterion with its exact equivalence. Shared objects:
  `Admits`, `relativeLoss`, `AveragedContinuation`, `signedDampingWork`, `workCore`.
- **[Arithmetic Criticality Theory](../ArithmeticCriticalityTheory/README.md).** ACT owns the Gaussian ceiling of the restricted Weil ground
  energy. ACCC reads it as a forced loss rate: any positive aperture floor must decay doubly
  exponentially, the half-summable transport premise is impossible along unbounded apertures, and
  even the harmonic product is too large along linear ones. Shared object:
  `ccmRestrictedWeilGroundEnergy`.
- **[Bézout–Valuation Incidence](../BezoutValuationIncidence/README.md).** BVI owns the actual-row estimate for the centred prime row on
  unbalanced scales, with Huxley's exponent. ACCC transfers the corpus's Guth–Maynard exponent into
  it, widening the range from `Q ≤ P^{12/7−δ}` to `Q ≤ P^{30/17−δ}` with every side condition kept.
  Shared objects: `centredPrimeRow`, `rowBilinear`.
- **RHTower.** The large-prime sector of the damped Möbius–Ramanujan expansion and its literal
  complement cancel to leading order (`PMRamanujanComplementaryCancellation`). ACCC writes that
  cancellation in compensation coordinates and proves the Pythagorean law that ties both
  coordinates to the complete receiver energy. RHTower also supplies the prime number theorem
  through Abel summation and the `17/30` short-window theorem.
- **[Square-Root Threshold](../SquareRootThreshold/README.md).** SRT owns the graded floor in both directions: a floor at rate `2σ` is
  the strip `½ + σ`, and the width bounds the floor in the energy normalisation. ACCC uses the
  dictionary as its scoring rule and does not reprove it.
- **[Bi-Scale Uncertainty](../BiScaleUncertainty/README.md).** Its finite-filter Schur residuals are the abstract projection algebra
  of the compensation coordinates; its test models are the selectivity audit every ACCC estimate
  must pass.
- **[Trans-Horizon Incidence Mechanics](../TransHorizonIncidenceMechanics/README.md) and
  [Scale-Signed Incidence Criticality](../ScaleSignedIncidenceCriticality/README.md).** They own readings,
  fibres and origin loss. ACCC inherits their rule that recovery is worth something only with a
  stability estimate in the receiver's norm, and its defect profiles are readings with retained
  arithmetic constraints.

- **[Arithmetic Positivity Theory](../arithmetic-positivity-theory/README.md).** Supplies the full
  Weil–Markov–pole target and multiscale Schur estimates to which a compensated remainder must return.
- **[Arithmetic Castelnuovo–Severi](../ArithmeticCastelnuovoSeveri/README.md).** Asks whether
  source-compatible effectivity can force the sign that compensation alone does not determine.
- **[Signed Arithmetic Energy Incidence](../SignedArithmeticEnergyIncidence/README.md).** Keeps
  Möbius coefficients, residue incidence and signed Gram interactions attached to the source.
- **[Arithmetic Orientation Theory](../ArithmeticOrientationTheory/README.md).** Its selectivity
  battery requires every positive floor to respect the doubly exponential decay of mechanism 25,
  and its unit hygiene applies to the corrector criterion of mechanism 26: until the corrector is
  built from source terms, an adapted energy is one more reading of the damping unit.

Read the comb mechanisms first as a worked example of a failed majorant with a useful survivor;
then the compensation coordinates, signed budgets and correctors. The short-window transfer shows
how an existing analytic theorem yields a genuine gain once the receiving estimate's quantifiers
are matched. `RHTower` supplies the underlying analytic and arithmetic identities.

---

## 1. Why: motivation

**The walls are failures of particular estimates.** They do not say that every proof must use one
prescribed set of tools. Source realization without orientation asks for orientation derived from
arithmetic; sharp arbitrary-row majorants ask which joint constraints distinguish the actual rows;
blind readings ask for anchored, stable reconstruction; the critical norm asks for quantitative
transfer with boundary and moving-projection terms; finite positivity asks for cofinal transport;
exact identities with no gain ask for a strict estimate not obtained by substituting the unknown
energy back into itself. Each is a missing *rate*.

**Compensation is the right object.** Two facts make this concrete.

* The actual source already realizes leading-order cancellation of separately divergent pieces:
  the large-prime sector `L` of the damped Möbius–Ramanujan expansion and its literal complement
  `C` have `‖C‖²/‖L‖² → 1` and `⟪L, C⟫/‖L‖² → −1` (`RHTower.PMRamanujanComplementaryCancellation`).
  The pieces diverge; their sum does not grow at their rate. But the remainder can still grow with
  a positive power: relative cancellation is not critical admission.
* A majorant can be exponentially larger than the signed quantity it majorizes. The raw prime-comb
  energy is `∼ 4e^{2r}` on unit-mass odd tests while the first-power charge it was meant to control
  is `o(e^r)` there (`ThePrimeCombIsATranslation`). Cauchy–Schwarz discarded exactly the geometry —
  a translation to the horizon — that kills the charge.

The strongest opportunity is therefore specific: turn the proved leading cancellation into a
stable quantitative law by exploiting the compatibility between different decompositions of the
same source, and do the accounting that keeps every compensating term in view.

---

## 2. What: objects and language

| Object | Required data | Purpose | Lean |
|---|---|---|---|
| Anchored arithmetic source | actual coefficients, convolution relations, successor incidence, centring, boundary normalization | forbid replacing the source by a broad class whose extremizers need not be arithmetic | `RHTower.pmPowerDampedCenteredDivisorPrefix`, `dampedMobiusEnergy` |
| Finite critical states | prefixes, damping, aperture, scale, with the exact pronic or Weil normalization | state estimates before limits; expose every uniformity | `ArithmeticContinuationAndCriticalEnergy.Admits`, `relativeLoss` |
| Compensated decomposition | coherent piece, its mixed Gram terms, a residual | treat cancellation as data | `compensationAmplitude`, `transverseRemainder`, `gramAmplitude`, `gramTransverse` |
| Scale transition | refinement maps, moving projections, boundary and connection terms | decide whether local gains survive a growing family | `combShellMass`, `combTail`, `tileSeq` |
| Reading with a fibre | observable data and the compatible sources | state what information is lost | `ScaleSignedIncidenceCriticality` |
| Critical defect profile | where the unit energy of a normalized family goes | turn the failure of a bound into a classification | `normalizedComb`, `horizonEnergy` |
| Graded estimate | an explicit growth rate, source class, norm, parameter dependence | measure progress before the RH endpoint | `apertureCeilingExponent`, `SquareRootThreshold` dictionaries |

**The prime comb at aperture `r`.** `C_r F = Σ_{p ≤ e^{2r}} w_p F(· + log p)` with the Euler
weights `w_p = √p log p/(p − 1)` (`combWeight`, `combPrimes`), comb mass `S_r = Σ w_p` (`combMass`),
raw energy `E_r(F) = ‖C_r F‖² = Σ_{p,q} w_p w_q A_F(log q − log p)` (`combEnergy`), cross-prime
aggregate (`combCross`), diagonal `Σ w_p²` (`combDiagonal`) and first-power charge
`Σ_p w_p A_F(log p)` (`combCharge`). The **depth** of a comb prime is `u_p = 2r − log p`
(`combDepth`); the **comb tail** `D_r(u) = S_{r−u/2}/S_r` is the fraction of the mass at depth at
least `u` (`combTail`); the **horizon law** is the density `½e^{−u/2}` on `(0, ∞)`
(`horizonDensity`, `horizonIntegral`); the **horizon energy** of a test is
`J(F) = ∫∫_{u,v>0} A_F(u − v) ½e^{−u/2} ½e^{−v/2}` (`horizonEnergy`). The slowly varying test of
profile `f` is `F_r(x) = r^{−1/2} f(x/r)` (`rescaledTest`), and the normalized comb read at scale `r`
is `S_r^{−1} Σ_p w_p f(· + log p/r)` (`normalizedComb`).

**Compensation coordinates.** For a coherent sector `L` and its complement `C`, the **amplitude**
`α = −⟪L, C⟫/‖L‖²` and the **transverse remainder** `R = C + αL` (`compensationAmplitude`,
`transverseRemainder`), with `L ≠ 0`; in scalar Gram data `a = ‖L‖²`, `b = ‖C‖²`, `m = ⟪L, C⟫` they are
`−m/a` and `b − m²/a` (`gramAmplitude`, `gramTransverse`), with `a > 0`.

**Budgets.** The signed averaged budget (`AveragedContinuation`), the positive-part budget
(`PositivePartContinuation`), the pointwise budget (`LinearContinuation`), and the adapted energy
(`AdaptedEnergy`): a family comparable to `1 + E_T` with horizon-free constants whose signed
relative loss has a horizon-free integral bound.

**Words.** *Coherent subtraction*: removing a named leading piece before estimating.
*Signed pairing*: a bilinear quantity estimated with its sign, not through its absolute value.
*Anchored restriction*: a statement about the actual source, not a class containing it.
*Refinement*: a change of scale with its boundary terms. *Compensated transport*: propagation of a
bound along a parameter in which losses at one parameter may be repaid at another. *Defect
extraction*: identification of where the energy of a normalized family goes.

**The four qualifiers.** "The correction is bounded" is not a statement until it says **which
norm**, **uniform in which cutoff**, **on which source class**, and **with which dependence on the
damping or the aperture**. A dense image, a vanishing relative error and a bounded critical error
are three different statements and remain visibly different here.

---

## 3. How: mechanisms

### The prime comb at the horizon

1. **The comb mass is `2e^r`** (`tendsto_combMass_div_exp`). The main part `Σ p^{−1/2} log p` is
   the prime number theorem through Abel summation (`RHTower.tendsto_primeRpowLogSumIoc` at
   exponent `½`); the correction `w_p − p^{−1/2} log p = log p/(√p(p − 1)) ≤ 2p^{−3/2} log p` has a
   bounded sum (`combCorrectionMass_le`).
2. **Concentration at the horizon.** The primes `p ≤ e^{(2−δ)r}` carry the mass `S_{(1−δ/2)r}`, a
   vanishing fraction of `S_r` (`tendsto_tailMass_div_combMass`). Hence the rescaled shifts
   `log p/r` concentrate at `2` and their differences at `0`: for bounded `g` continuous at the
   point, `S_r^{−1} Σ w_p g(log p/r) → g(2)` and `S_r^{−2} Σ w_p w_q g((log q − log p)/r) → g(0)`
   (`tendsto_combAverage`, `tendsto_combPairAverage`).
3. **The universal bound** `E_r(F) ≤ S_r² A_F(0)` (`combEnergy_le_combMass_sq_mul`), from
   `|A_F| ≤ A_F(0)` and nonnegative weights.
4. **The sharp exponential rate.** For the slowly varying family `A_{F_r}(t) = A_f(t/r)`
   (`autoCorr_rescaledTest`), so the pair concentration gives `E_r(F_r)/S_r² → A_f(0)` and
   `E_r(F_r) ∼ 4e^{2r} A_f(0)` (`tendsto_combEnergy_rescaledTest_div_exp`). The diagonal is
   `≤ 16r²(1 + 2r)` (`combDiagonal_le`), so the cross-prime aggregate alone is `∼ 4e^{2r} A_f(0)`
   (`tendsto_combCross_rescaledTest_div_exp`). The rate `2` of the raw energy is sharp from both
   sides, and AIP's polynomial target for the aggregate fails.
5. **The translation survivor.** `‖(√r/S_r)(C_r F_r)(r ·) − f(· + 2)‖² → 0`
   (`tendsto_testPairing_normalizedComb_sub_translate`, with `normalizedComb_eq` identifying the
   normalized comb with the actual one). Expanding the square leaves `E/S²`, the cross pairing
   `S_r^{−1} Σ w_p A_f(log p/r − 2)` and `A_f(0)`, all controlled by mechanism 2.
6. **No adverse charge.** `S_r^{−1} Σ_p w_p A_{F_r}(log p) → A_f(2)`, and `A_f(2) = 0` for `f` in
   `[−1, 1]`, since the translate `f(· + 2)` lives in `[−3, −1]`
   (`tendsto_combCharge_rescaledTest_div_combMass_zero`). Enormous energy is not an enormous signed
   charge, and certainly not a negative Weil form.
7. **The compensated prime–polar residual has the de la Vallée Poussin saving, and the full
   ledger remainder is governed by the zero-free strip dictionary.** Before any
   square, the prime atoms and the polar density cancel exactly up to the two-pole defect
   `E(s) = e^s + s − 1 − ψ(e^s)` tested against `h′` (AIP's
   `sum_vonMangoldt_sub_polar_eq_chebyshev`, `primeShift_sub_polarDensity_eq_chebyshev`). The
   defect, weighted by `e^{−θs}`, `0 ≤ θ ≤ ½`, is at most `Ke^{(1−θ)S}exp(−c√S)` on `[0, S]`
   (`exists_abs_chebyshevTwoPoleDefect_mul_exp_le`), so every lag weight of aperture `S` has
   residual at most `Ke^S exp(−c√S)∫_0^S|h′|` (`exists_abs_sum_vonMangoldt_sub_polar_le`), and
   every translate `x` of a `C¹` test in `[−r, r]` has ledger residual at most
   `Ke^{S/2}exp(−c√S)(2‖F′‖₁ + ‖F‖₁)`, `S = 2r + |x|` (`exists_abs_primeShift_sub_polar_le`), with
   universal constants. Retaining the even parts and the archimedean gamma factor, the **full
   compensated ledger remainder** `fullLedgerCompensatedRemainder F` equals the bilateral prime–polar
   residual minus `archimedeanShift F` (`fullLedgerCompensatedRemainder_eq_primePolar_sub_archimedean`),
   whose even autocorrelation kills every odd part (`fullLedgerCompensatedRemainder_odd_eq_zero`),
   whose archimedean piece is `O(‖F‖₁ + ‖F′‖₁)` uniformly in the aperture
   (`abs_archimedeanLedgerRemainder_le_norm`), and whose full remainder has the unconditional
   de la Vallée Poussin bound `K e^r exp(−c√(2r)) ‖F′‖₁ + (2π + 2)(‖F‖₁ + ‖F′‖₁)` on `C¹` tests in
   `[−r, r]` (`exists_abs_fullLedgerCompensatedRemainder_le_deLaValleePoussin`), while every single
   prime-power atom `p^m` contributes `O(p^{−m/2} log p · ‖F‖₂²)` (`abs_primePowerShift_le_l2`).
   An exponent `θ ∈ (0, ½)` for `primePolarLedgerRemainder` or `fullLedgerCompensatedRemainder` on
   the smooth test class is **equivalent** to the quantitative Chebyshev bound
   `|E(s)| ≤ C e^{(1/2+θ)s}` (`fullLedger_sub_half_exponent_iff_chebyshev_bound`), which implies the
   zero-free strip `Re ρ ≤ ½ + θ` via the Mellin transform
   (`zeta_zeroFree_strip_of_fullLedger_sub_half_exponent`) and follows from `Θ < ½ + θ`
   (`fullLedger_sub_half_exponent_of_zetaZeroAbscissa_lt`), so the infimum of admissible ledger
   exponents is `max(0, Θ − ½)` and the `θ → 0⁺` limit is RH
   (`riemannHypothesis_iff_forall_pos_fullLedger_exponent`).
8. **The ledger's own test class.** The profile `oddBump(x) = x e^{−1/(1−x²)}` normalized to unit
   mass gives smooth odd tests supported in `[−r, r]` on which all of the above hold at once
   (`exists_odd_smooth_family_sharp_comb_rate`).
9. **The depth law.** The comb tail tends to `e^{−u/2}` uniformly in `u ≥ 0`
   (`eventually_abs_combTail_sub_le`): a near range where both `S_y/e^y` are within `δ` of `2`, and
   a far range controlled by monotonicity.
10. **Depth statistics converge to the horizon law, uniformly over translates**
   (`eventually_abs_combAverage_sub_horizonIntegral_le`). Shells of depth `[kh, (k + 1)h)` carry the
   comb mass `S_{r−kh/2} − S_{r−(k+1)h/2}` (`combShellMass`); comparing the discrete shell sum
   (`abs_combDepthSum_sub_shells_le`) and the continuous one (`abs_horizonIntegral_sub_shells_le`)
   costs the modulus of continuity, the tail at the cutoff and `2KMη` from the uniform depth law.
11. **The comb resolvent law.** Since `log q − log p = u_p − u_q` (`combDepth_sub_combDepth`), the
    comb energy is a double depth statistic (`combEnergy_eq_depthSum`), and the uniform version of
    mechanism 10 applied twice gives, for every continuous compactly supported test,
    `E_r(F)/S_r² → J(F)` and `E_r(F) ∼ 4J(F)e^{2r}`
    (`tendsto_combEnergy_div_combMass_sq_horizonEnergy`,
    `tendsto_combEnergy_div_exp_horizonEnergy`), with `0 ≤ J(F) ≤ A_F(0)`
    (`horizonEnergy_nonneg`, `horizonEnergy_le`). In operator language
    `S_r^{−1} C_r ≈ τ_{2r} ∘ Ψ`, `ΨF = ∫_{u>0} ½e^{−u/2} F(· − u) du`, the resolvent of `1 + 2∂`, and
    `J(F) = ‖ΨF‖²`. For every nonzero continuous compactly supported `F`, **`J(F) > 0`**
    (`horizonEnergy_pos`): vanishing horizon energy forces all exponentially weighted tails of
    the autocorrelation to vanish, hence `A_F(0) = 0`. Thus every such fixed test has exponential
    comb energy (`exists_pos_tendsto_combEnergy_div_exp`). This is pointwise positivity in `F`,
    not a uniform coercive constant over all test profiles. On slowly varying tests `Ψ ≈ id`
    and mechanism 5 is recovered.
12. **The horizon law at the de la Vallée Poussin rate.** Abel summation of `p^{−1/2} log p`
    against `θ` writes `S_r − 2e^r` exactly as a bounded correction, a constant, the boundary error
    `e^r(θ(x)/x − 1)` and half the integrated error `∫_2^x (θ(t)/t − 1)t^{−1/2} dt`, `x = e^{2r}`
    (`combMass_sub_eq`); cutting the integral at `√x` gives `|S_r − 2e^r| ≤ Ke^r exp(−c√r)`
    (`exists_abs_combMass_sub_le`). The depth law follows at the same rate,
    `sup_{u≥0}|S_{r−u/2}/S_r − e^{−u/2}| ≤ K exp(−c√r)` (`exists_abs_combTail_sub_le`), and with
    shells of width `e^{−s}` down to depth `2s`, `s ≍ √r`, every `L`-Lipschitz test bounded by `M`
    has depth statistics within `K(L + M) exp(−c√r)` of the horizon law, uniformly in the
    translate (`exists_abs_combAverage_sub_horizonIntegral_le`). Since the autocorrelation of a
    `Λ`-Lipschitz test is `Λ‖F‖₁`-Lipschitz (`abs_autoCorr_sub_le`), the resolvent law holds at
    the same rate, `|E_r(F)/S_r² − J(F)| ≤ K(Λ‖F‖₁ + A_F(0)) exp(−c√r)`, and
    `E_r(F) = 4J(F)e^{2r} + O(e^{2r} exp(−c√r))` (`exists_abs_combEnergy_div_sub_horizonEnergy_le`,
    `exists_abs_combEnergy_sub_le`); `c` and `K` are universal, independent of the test. The rate
    is the prime number theorem's: an error `O(e^{θr})`, `θ < 1`, in `S_r − 2e^r` would be a
    statement about the zeros of `ζ`.
13. **The horizon energy is one horizon average, the resolvent identity is exact, and the first and
    second corrections are quadratic and quartic.**
    The double average collapses: `J(F) = ∫_{u>0} A_F(u) ½e^{−u/2} du`
    (`horizonEnergy_eq_horizonIntegral_autoCorr`), by integrating `−¼e^{−v}Φ(−v)`,
    `Φ(w) = ∫_{s>w} A_F(s)e^{−s/2} ds`, along the half-line with `A_F` even. A `Λ`-Lipschitz test
    supported in `[−R, R]` has `A(0) − A(s) = ½∫(F(x) − F(x+s))² ≤ Λ²s²(R + |s|)`
    (`autoCorr_zero_sub_le`), and the horizon moments are `∫u^k dμ = 2^k k!`
    (`integral_pow_mul_horizonDensity`). Hence `J(F) ≥ A_F(0) − Λ²(8R + 48)` for every such test
    (`horizonEnergy_ge_of_lipschitz`): uniform coercivity on the class of unit tests with
    `Λ²(8R + 48) < 1`. On the slowly varying family this gives
    `A_f(0) − Λ²(8/r² + 48/r³) ≤ J(F_r) ≤ A_f(0)` (`horizonEnergy_rescaledTest_ge`), and since the
    rate of mechanism 12 has test-independent constants, the comb itself satisfies
    `0 ≤ A_f(0) − E_r(F_r)/S_r² ≤ C/r²` (`exists_combEnergy_rescaledTest_deficit_le`). For a `C¹`
    profile the first correction is exact: `(A_f(0) − A_f(s))/s² → ½‖f′‖²`
    (`tendsto_autoCorr_deficit_div_sq`), so `r²(A_f(0) − E_r(F_r)/S_r²) → 4‖f′‖²`
    (`tendsto_sq_mul_horizonEnergy_rescaledTest_deficit`,
    `tendsto_sq_mul_combEnergy_rescaledTest_deficit`). On every compactly supported `C¹` test the
    resolvent `ΨF = ∫_{u>0} ½e^{−u/2} F(· − u) du` satisfies the exact differential equation
    `ΨF + 2(ΨF)′ = F` (`horizonResolvent_add_two_deriv`), which squares and integrates to the
    **exact resolvent energy identity** `J(F) + 4 J(F′) = A_F(0)`
    (`horizonEnergy_add_four_deriv_eq`) and the `m`-step Taylor tower
    `A_F(0) − J(F) = Σ_{k=1}^{m−1} (−1)^{k−1} 4^k A_{F^{(k)}}(0) + (−1)^{m−1} 4^m J(F^{(m)})`. At
    `m = 2` this gives the exact second-order identity
    `A_F(0) − J(F) − 4 A_{F′}(0) = −16 J(F″)` (`horizonEnergy_second_order_identity`), the universal
    positivity of the second correction (`horizonEnergy_ge_first_order`), and on slowly varying `C²`
    tests the exact **quartic second horizon and comb correction** `−16‖f″‖²/r⁴`
    (`tendsto_pow_four_mul_horizonEnergy_rescaledTest_second_correction`,
    `tendsto_pow_four_mul_combEnergy_rescaledTest_second_correction`). At any fixed aperture `R > 0`,
    whereas the unrestricted coercive constant over all odd `C¹` tests in `[−R, R]` is `0`
    (`not_exists_pos_odd_horizonEnergy_coercive`), restricting the `H¹` seminorm `‖F′‖² ≤ γ‖F‖²` gives
    the explicit coercive constant `max(1/(1 + 4γ), 1 − 4γ)` (`odd_horizonEnergy_ge_inv_add_four`),
    and the first Dirichlet odd mode `sin(πx/R)𝟙_{[−R,R]}` gives the upper bound `1/(1 + π²/R²)` on
    the optimal fixed-aperture Poincaré constant (`odd_poincare_mode_horizonEnergy_lt`).
14. **No uniform coercivity over the integers; uniform coercivity on a curve.** The concentrated
    tests `F_λ(x) = √λ φ(λx)` keep their mass and have `A_{F_λ}(u) = A_φ(λu)`, so
    `J(F_λ) ≤ (2λ)^{−1}∫_{v>0}|A_φ|` (`horizonEnergy_concentratedTest_le`): no `c > 0` has
    `J(F) ≥ c∫F²` for all tests (`not_exists_horizonEnergy_ge`), and for every `c` some unit test
    has `E_r(F) ≤ cS_r²` at all large apertures (`exists_combEnergy_le_mul`). The integer comb
    shifts by the dense set `{log p}`, its horizon law is the resolvent of the unbounded `1 + 2∂`,
    and a narrow bump defeats it. A curve comb shifts by the lattice `ℕ log q` and the geometric
    weights invert the bounded shift: `‖C_D F‖² ≥ (q^D/12)∫F²` for every test at all large `D`
    (`curveCombEnergy_ge`, `exists_curveCombEnergy_ge`). The curve comb has its own resolvent law:
    the share of the comb at depth `k` tends to `w_k = (1 − q^{−1/2})q^{−k/2}`
    (`tendsto_curveCombWeight_div_mass`), and for every test
    `‖C_D F‖²/S_D² → J_q(F) = Σ_{k,k'} w_k w_{k'} A_F((k − k') log q)`, independently of the
    eigenvalues (`tendsto_curveCombEnergy_div_sq`), with `J_q(F) ≥ ((1 − q^{−1/2})²/12)∫F²`
    (`curveHorizonEnergy_ge`): the discrete horizon energy is uniformly coercive, the continuous
    one is not. Uniform coercivity must therefore come from a restricted test class or from the
    arithmetic of the pairing, never from the integer comb alone.

15. **The horizon law of a curve is geometric.** For a curve model over `F_q` with Frobenius
    eigenvalues of modulus at most `λ√q`, the comb built from the point counts
    `N(n) = qⁿ + 1 − Re Σαᵢⁿ`, with weight `N(n)q^{−n/2}` at degree `n`, has mass
    `Σ_{n≤D} q^{n/2}` up to `D + 2gΣ_{n≤D}λⁿ` (`abs_curveCombMass_sub_geometricMass_le`), hence up to
    `(2g + 1)D` on the Weil circle (`abs_curveCombMass_sub_geometricMass_le_of_weil`); and the
    fraction of the mass at depth `k` below the horizon is `q^{−k/2}` up to
    `16(2g + 1)(D + 1)/q^{D/2}` (`abs_curveCombTail_sub_le_of_weil`). What replaces `e^{−u/2}` is
    its exact discretization at `u = k log q`, and the error of the law is the width of the zero
    set: square-root small on the circle, growing like `λ^D` off it. Weil's bound is the defining
    property of the model class, not a claim about actual curves.
    The receiver of the curve model is the prefix of `Z(u)(1/Z)(q^{−ε}u)` centred by the density
    `δ_ε = Σ_k μ_ε(k)q^{−k}`, with `Z = P/((1−u)(1−qu))` and `Z·(1/Z) = 1` (`curveZ_mul_curveZinv`),
    and its energy weights degree `n` by the norm weight `q^{−n}`. The centring removes the pole at
    `u = 1/q` exactly — the coefficients of `(1−qu)^{−1}(R − δ)` are `−qⁿΣ_{j>n}b_jq^{−j}`
    (`coeff_geomSeries_mul_eq_neg_tail`) — so only the zeros remain, and **the receiver is admitted
    at every damping above the zero width**: eigenvalues of modulus at most `λ√q` and `λ < q^ε`
    give a horizon-free energy bound (`exists_curveReceiverEnergy_le`), on the Weil circle at every
    `ε > 0` (`exists_curveReceiverEnergy_le_of_weil`). Conversely, for any number `m` of complex
    eigenvalues, multiplying the centred prefix series by the polynomial filter
    `Q_i(u) = (1 − u)²(1 − qu)Π_{j≠i}(1 − α_j q^{−ε}u)` of degree `m + 2` annihilates all other
    Frobenius modes, the poles at `1` and `1/q`, and the polynomial density term above degree
    `2m + 1`, isolating the pure geometric mode `curveEigenvalueResidue q α ε i · (α_i q^{−ε})ᴺ` at
    every degree `N ≥ 2m + 2` (`coeff_curveAnnihilatorFilter_mul_curveCentredSeries`), whose
    amplitude vanishes iff `α_i` is shadowed by some `α_j = α_i q^{−ε}` or `α_i ∈ {1, q}`
    (`curveEigenvalueResidue_eq_zero_iff`, `coeff_curveAnnihilatorFilter_mul_eq_zero_of_shadow`).
    Oscillating modes therefore cannot cancel across a block of length `m + 3`: any unshadowed
    eigenvalue with `√q q^ε < ‖α_i‖` (`α_i ≠ 1, q`) forces exponential growth
    `curveReceiverEnergy q α ε D ≥ c(‖α_i‖q^{−ε}/√q)^{2D}` (`exists_pos_mul_pow_le_curveReceiverEnergy`,
    `not_exists_curveReceiverEnergy_le`), so equimodular families `‖α_j‖ = λ√q` are admitted at `ε`
    iff `λ < q^ε` (`curveReceiverEnergy_admitted_iff_of_equimodular`), and for any tuple `α_i ≠ q`
    **cofinal admission as `ε ↓ 0` is equivalent to the Weil bound `∀ i, ‖α_i‖ ≤ √q`**
    (`weil_iff_cofinal_curveReceiverEnergy`) — the function-field form of
    `riemannHypothesis_iff_cofinal_adaptedEnergy`.

### Compensation coordinates

16. **The Pythagorean compensation law.** `‖L + C‖² = (1 − α)²‖L‖² + ‖R‖²` for `L ≠ 0`, with `⟪L, R⟫ = 0`
    (`norm_add_sq_eq_compensation`, `inner_transverseRemainder`), hence
    `(1 − α)² + ‖R‖²/‖L‖² = ‖L + C‖²/‖L‖²` (`compensationDefect_eq_relativeEnergy`). The same law
    holds for scalar Gram data, with `‖R‖² ≥ 0` from Cauchy–Schwarz (`gram_add_eq_compensation`,
    `gramTransverse_nonneg`, `gram_coordinates_le`).
17. **The actual instance.** For `0 < ε < ½` the large-prime sector of the damped
    Möbius–Ramanujan expansion at cutoff `P²` has `α_P → 1` and `‖R_P‖²/‖L_P‖² → 0`
    (`tendsto_pmCompensationAmplitude_one`, `tendsto_pmTransverseEnergy_div_sectorEnergy_zero`),
    and the complete head energy is exactly `(1 − α_P)²‖L_P‖² + ‖R_P‖²`
    (`pmCompleteHeadEnergy_eq_compensation`, from the energy split
    `pmCompleteHeadEnergy_eq_sum` and the Cauchy–Schwarz bound `pmMixedEnergy_sq_le`).
18. **The compensation rate on the actual source, and the two-scale cutoff transition rate.** The
    defect is the relative complete head energy for all large `P`
    (`eventually_compensationDefect_eq_relative`); the sector energy is at least `cP^{1−2ε}/log²P`
    (`sectorEnergy_eventually_lower`), the complete energy at most twice the divisor-remainder
    energy plus the Ramanujan truncation cost `2T⁴P^{1−3ε}` (`prefixEnergy_le`), and the
    remainder energy is `O(P^{(1−2ε)/2}) + O(1) + O(P^{1−2ε}/log⁸P)` (`remainderEnergy_le`).
    Hence `(1 − α_P)² + ‖R_P‖²/‖L_P‖² ≤ K/log⁶P` for all large `P`
    (`exists_compensationDefect_le_inv_log_pow_six`): an explicit logarithmic rate of compensation,
    with an absolute complete energy `O(P^{1−2ε}/log⁸P)` that still grows with the cutoff.
    The logarithmic power is not a limit of the method: feeding the Möbius harmonic saving of
    every logarithmic power through the signed hyperbola split gives
    `|R_ε(N)| ≤ 1 + C_m N^{1−ε}/log^m N` (`exists_norm_pmPowerDampedDivisorRemainder_le_log_pow`),
    hence **`(1 − α_P)² + ‖R_P‖²/‖L_P‖² ≤ K_m/log^m P` for every `m`**
    (`exists_compensationDefect_le_inv_log_pow`) and `|1 − α_P| = O(log^{−m}P)`
    (`exists_abs_one_sub_pmCompensationAmplitude_le_log_pow`): the compensation is faster than
    every power of the logarithm.
    The rate iterates over scales: the defects at `P = 2^k` are summable
    (`summable_compensationDefect_dyadic`), while the absolute energies are not. The moving
    projection pays a summable connection term: `|1 − α_P| ≤ K/log³P`
    (`exists_abs_one_sub_pmCompensationAmplitude_le`), so the amplitude has bounded variation
    over the dyadic scales (`summable_abs_pmCompensationAmplitude_dyadic_sub`), and the relative
    transverse energies are summable (`summable_pmTransverseEnergy_div_sectorEnergy_dyadic`).
    Comparing the overlapping decompositions at cutoffs `P²` and `Q²` (`Q ≥ P`, in particular
    `Q = 2P`) on their common head `1 ≤ N ≤ P − 1` cancels the cutoff-independent divisor remainder
    `R_ε(N)` identically (`norm_twoScale_completePrefix_sub_le`), giving the **power-saving
    two-scale cutoff shift** `twoScaleCompleteShiftEnergy ε P Q P ≤ C P^{1−3ε}`
    (`exists_twoScaleCompleteShiftEnergy_le_pow_saving`), the **polynomial** relative decay
    `O(P^{−ε} log² P)` against `‖L_P‖²` (`exists_twoScaleCompleteShiftEnergy_div_sectorEnergy_le_rpow`),
    and absolute polynomial decay to `0` for `ε > 1/3`
    (`tendsto_twoScaleCompleteShiftEnergy_zero_of_one_third_lt`). The moving projection between
    scales obeys the exact connection identity
    `R_Q − R_P = (S_Q − S_P) − (1 − α_Q)(L_Q − L_P) + (α_Q − α_P) L_P`
    (`transverseRemainder_sub_eq_complete_sub_connection`,
    `pmTransverseRemainderSeq_sub_eq_connection`,
    `twoScale_transverseRemainder_diff_energy_le`), with two-scale coordinate mismatch
    `|α_Q − α_P| ≤ K_m/log^m P` and polynomial-weight dyadic summability
    `Σ_k k^m |α_{2^{k+1}} − α_{2^k}| < ∞` (`exists_abs_pmCompensationAmplitude_sub_le_log_pow_of_le`,
    `summable_mul_pow_abs_pmCompensationAmplitude_dyadic_sub`).

### Where a blow-up of the receiver goes

19. **A blow-up escapes to the horizon, and the normalized receiver profile retains its arithmetic
    laws.** The damped divisor remainder read at the integers gives
    the source bound `|A_ε(n)| ≤ Cn^{1−ε}` for `0 < ε < ½` (`exists_abs_centredPrefix_le`), so each
    cell carries at most `C²n^{−2ε}` and the receiver grows at most at the trivial rate,
    `E_N(ε) ≤ D(1 + N^{1−2ε})` (`exists_dampedMobiusEnergy_le`). Hence the blow-up dichotomy
    (`admits_or_escapesToHorizon`): either the receiver is admitted at `ε`, or for every `θ < 1`
    the energy below the scale `E_T^{θ/(1−2ε)}` is a vanishing fraction of `E_T`; and at every
    damping, either admission holds or every fixed window and every cell carries a vanishing
    fraction (`admits_or_fixedWindowEnergy_vanishes`). Normalizing by the critical norm,
    `u_{ε,T}(n) = A_ε(n)/√E_T(ε)` (`normalizedReceiverProfile`) has exact unit pronic energy for
    `ε > 0`, `T ≥ 1` (`pronicEnergy_normalizedReceiverProfile`), concentrates `1 − o(1)` of its
    energy in the horizon shell `(⌊E_T^{θ/(1−2ε)}⌋, T]` under blow-up
    (`admits_or_normalizedReceiverProfile_shell_tendsto_one`), obeys the two-sided horizon-dilation
    sandwich `(1/j) pronicEnergy v (T/j − 1) ≤ pronicEnergy (rowDilate j v) T ≤ (1/j) pronicEnergy v (T/j)`
    (`pronicEnergy_rowDilate_sandwich`, `pronicEnergy_rowDilate_normalizedReceiverProfile_sandwich`)
    so deep cofactors `T/j_T ≤ ⌊E_T^{θ/(1−2ε)}⌋` carry `o(1/j_T)` energy
    (`admits_or_deepCofactor_normalizedReceiverProfile_vanishes`), and satisfies the normalized
    inversion law `u_{ε,T}(n) + Σ_{j=2}^n j^{−ε} u_{ε,T}(⌊n/j⌋) = ρ_ε(n)/√E_T(ε)`
    (`normalizedReceiverProfile_add_properUnitDilation_eq`, converging to the homogeneous cofactor
    relation on `n = o(√E_T(ε))`), the self-improving energy identity
    (`normalizedReceiverProfile_selfImproving_identity`), and the Möbius-factored tangent law
    (`normalizedTangentProfile_eq_moebiusDilation`). The drifted `n^{1/4}` family, the sign-blind
    majorant source (strictly negative, violating the inversion sign law), the cofactor aliasing
    eigenmodes `ω = 2πk/log j` (`cofactorAliasingWave_alias_eigenmode`), and the half-damped
    oscillating probes (whose normalized energy splits into the spectral shares
    `α_t²|ζ(½+it)|²/(2|½+it|² V(J,α))`, `tendsto_normalizedHalfProbeCombination_energy_share`) all
    embed in the normalized defect space.

### The price of a change of origin

20. **A finite change of origin costs exactly `(k+1)(k+2)/2`.** Shifting a sequence by `k` cells
    multiplies its pronic energy by at most `(k+1)(k+2)/2` (`pronicEnergy_shift_le`, from the weight
    comparison `pronicWeight_shift_le`), the factor is attained by the indicator of the cell `k + 1`
    (`pronicEnergy_shift_indicator`), and the shift loses only the first `k` cells in the other
    direction (`pronicEnergy_le_head_add_shift`). Admission is therefore invariant under every
    finite change of origin (`bddAbove_pronicEnergy_shift_iff`), in particular for the damped Möbius
    receiver (`admits_dampedMobiusEnergy_iff_shift`). Finite origin information is recovered stably
    in the critical norm.
21. **A drifting origin is priced by the tail beyond it.** The translate `a(· + k)` on `[1, T]`
    carries between the tail `E(T+k) − E(k)` and `(k+1)(k+2)/2` times that tail
    (`pronicTail_le_pronicEnergy_shift`, `pronicEnergy_shift_le_tail`). Every admitted sequence
    stays admitted along a drift `k(T)` if and only if the drift is bounded
    (`forall_admitted_drift_admitted_iff`), and the single admitted sequence `n^{1/4}` has drifted
    energy tending to infinity along every drift tending to infinity
    (`tendsto_pronicEnergy_quarterPower_drift`): control of a drifting origin is never a norm fact
    and must use the tail decay of the source. For the receiver the source bound gives the trivial
    drift budget `D(k+1)^{2−2ε}(1 + T^{1−2ε})` (`exists_dampedMobius_drift_le`).

### Quantifier corrections of the continuation problem

22. **The signed budget is strictly weaker than its positive part.** The positive-part budget
    implies the averaged one (`averagedContinuation_of_positivePart`), and the lacunary family
    `E_T(ε) = Σ_{1 ≤ k ≤ T} 2^{−k}(2 + sin(16^k ε))` — nonnegative, nondecreasing in the horizon,
    bounded by `3`, hence admitted everywhere with averaged budgets on every interval — has
    `∫_a^c (r_T)_+ → ∞` on every nondegenerate interval
    (`exists_admitted_monotone_not_positivePartContinuation`). The mechanism is lacunary
    near-orthogonality: `∫_a^c E'_T cos(16^T ε) ≥ 8^T(c − a)/2 − 2`
    (`integral_lacunaryEnergyDeriv_mul_cos_ge`).
23. **The core debt on a positive interval is a zeta-log ratio.**
    `lim_T ∫_η^ε core_x(T) dx = log ζ(1+η) − log ζ(1+ε)` for `η, ε > 0`
    (`tendsto_integral_workCore_logZeta`), by dominated convergence against the Euler logarithm,
    with the horizon-free bound `∫_η^ε core ≤ log ζ(1+η) − log ζ(1+ε)` for `η ≤ ε`
    (`integral_workCore_le_logZeta`). The divergence of `exists_horizon_integral_workCore_ge` is an
    endpoint effect at zero damping.
24. **The first cell carries adverse work.** `W_1(ε) = −(1 − 1/ζ(1+ε)) m(ε)/2 → −½`
    (`tendsto_signedDampingWork_one`), so global nonnegative work fails on the actual source
    (`not_forall_signedDampingWork_nonneg`).
25. **The aperture floor must decay doubly exponentially.** From the Gaussian ceiling
    `μ(A) ≤ K e^{(11/2)A − πe^{2(A−2)}}`: no fixed positive floor along any unbounded aperture sequence
    (`not_exists_positive_floor_along`); the half-summable relative transport, whose conclusion is
    the floor `1/10000`, is impossible there (`not_relative_step_transport`); every floor
    `m₀e^{−B(A)}` has `B(A) ≥ πe^{2(A−2)} − (11/2)A + log(m₀/K)` (`exists_le_floorLoss_of_floor`);
    transported products lie below the ceiling (`prod_le_ceiling_of_relative_step`); and the
    harmonic transport fails along linearly growing apertures
    (`exists_groundEnergy_lt_harmonic_transport`).
26. **An adapted energy is exactly admission, and the Bézout unit-boundary corrector discharges
    comparability and the first-cell obstruction.** With the right end admitted, an adapted energy
    on `[a, c]` exists iff the receiver is admitted at `a`, for every nonnegative differentiable
    family with integrable relative loss (`adaptedEnergy_iff_admits`); for the damped Möbius
    receiver on `[a, ½]` all of these inputs are proved (`adaptedEnergy_dampedMobiusEnergy_iff_admits`);
    a pointwise corrector budget produces one (`adaptedEnergy_of_pointwise`); and cofinal adapted
    energies on `[a, ½]` for the damped Möbius receiver are RH
    (`riemannHypothesis_iff_cofinal_adaptedEnergy`). The **Bézout unit-boundary corrector**
    `bezoutUnitCorrector ε T = Σ_{n ≤ T}(1 − 2A_ε(n))/(n(n+1))` completes the square
    `bezoutCorrectedEnergy ε T = 1 + pmPowerDampedDualResidual ε T`
    (`bezoutCorrectedEnergy_eq_one_add_residual`), satisfies unconditional horizon-free and
    damping-free comparability `(1/3)(1 + E_T(ε)) ≤ bezoutCorrectedEnergy ε T ≤ 3(1 + E_T(ε))`
    (`bezoutCorrectedEnergy_comparison`), has a uniformly bounded derivative on `[a, ∞)`
    (`exists_abs_bezoutUnitCorrectorDeriv_le`), and replaces the adverse first-cell work
    `W_1(ε) → −½` by `residualDampingWork ε 1 = Re(1/ζ(1+ε))m(ε)/2 > 0`
    (`residualDampingWork_one`, `eventually_residualDampingWork_one_pos`). The normalized mixed
    large-prime/complement cross term `pmNormalizedMixedCross ε P` is bounded by `1` at every
    cutoff and tends to `−1` for `0 < ε < ½` (`abs_pmNormalizedMixedCross_le_one`,
    `tendsto_pmNormalizedMixedCross_neg_one`), and any composite corrector bounded by
    `θ · bezoutCorrectedEnergy` (`0 ≤ θ < 1`) preserves comparability `((1−θ)/3, 3(1+θ))` and
    changes the integrated relative loss by at most `log((1+θ)/(1−θ))`
    (`compositeCorrectedEnergy_comparison`, `integral_compositeCorrectedRelativeLoss_le`). A
    boundary-accumulating family of Bézout-corrected relative-loss bounds on `(a₀, c]` yields the
    zero-free strip `Θ ≤ ½ + a₀` (`zetaZeroAbscissa_le_half_add_of_bezoutCorrected_family`), and
    cofinal bounds on `[a, ½]` as `a ↓ 0` are equivalent to RH
    (`riemannHypothesis_iff_cofinal_bezoutCorrected_loss`).

### An internal transfer

27. **Huxley's uniform window at the Guth–Maynard exponent.** For every `α > 17/30`,
    `|ψ(x + h) − ψ(x) − h| ≤ εh` uniformly for `x^α ≤ h ≤ x/2`
    (`eventually_abs_psi_window_sub_le_seventeenThirtieths`): tile `[x, x + h]` by windows
    `[y, y + y^β]`, `17/30 < β < α` (`tileSeq`); the errors add, and the last partial window costs
    `(1 + ε/2)y^β = o(x^α)` by monotonicity of `ψ`.
28. **The centred prime row on the wider range and in the balanced regime.** The BVI actual-row
    estimate holds at every block exponent `α > 17/30`
    (`exists_abs_rowBilinear_centredPrimeRow_le_seventeenThirtieths`), hence on
    `P^{1+δ} ≤ Q ≤ P^{30/17−δ}` for horizons `N ≤ Q^C` at `α = 17/30 + δ/4`
    (`exists_abs_rowBilinear_centredPrimeRow_le_of_range`). Feeding the uniform `17/30` window into
    the short-window mean-square transfer widens `CentredPrimeBlockBeatsTheLargeSieve` and
    `DualNormOfTheActualRowsBeatsTheLargeSieve` to `17/30 < α < 1`, bounds the block-mass terms of
    both the centred prime and Möbius blocks by `√2 ε / Q` via Cauchy–Schwarz on the sum-preserving
    window average (`abs_sum_Icc_div_sq_le_of_shortWindowAverage`), and discharges the small-prime
    threshold throughout the balanced regime `P ≤ Q ≤ B P`
    (`exists_balanced_centredPrimeBlock_rowBilinear_le`,
    `exists_balanced_centredPrimeBlock_dualNorm_le`). Centring `Λ` by `1` kills the rank-one
    block mass while preserving 100% of the single-modulus omitted-residue-class main term,
    `Q · Λ_p((Λ − 1)𝟙_{(Q,2Q]}) → −π²(p² − 1)²/(144 p²(p − 1))`
    (`tendsto_mul_kernelStatistic_centredPrimeBlock`), which is cancelled to `o(1/Q)` by adding the
    zero-mean periodic sieve corrector `omittedClassCorrector p Q`
    (`tendsto_mul_kernelStatistic_centredPrimeBlock_add_corrector`). Upgrading the qualitative
    short-window mean-square saving to a power saving is equivalent to crossing below half damping
    for the complete coupled receiver (`primePowerWindowSaving_iff_receiverDampingRate_lt_half`,
    `moebiusPowerWindowSaving_iff_receiverDampingRate_lt_half`).

---

## 4. Traps

| Trap | What is true instead |
|---|---|
| Expecting the raw comb energy, or its cross-prime aggregate, to be polynomial in the aperture | Both are `∼ 4e^{2r}` on unit-mass smooth odd tests, and `∼ 4J(F)e^{2r}` on every fixed nonzero continuous compact test; the universal bound `S_r²A(0)` is attained. |
| Reading large comb energy as a large adverse charge | The first-power charge is `o(S_r)` on the extremal family; Cauchy–Schwarz discards the translation geometry that kills it. |
| Treating the comb as a rank-one object | It is a translation on slowly varying profiles and an exponential resolvent on fixed ones. |
| Reading relative cancellation `‖L + C‖ = o(‖L‖)` as a bounded remainder | The two compensation coordinates add up exactly to the relative complete energy; relative smallness of either coordinate does not bound the complete energy. |
| Paying every local loss separately | The positive-part budget is strictly stronger than the signed one, even on smooth horizon-monotone families. Keep signed recovery. |
| Asking for nonnegative signed work | The first cell has `W_1(ε) → −½`. |
| Reading the core divergence on `[0, ε]` as a divergence on positive intervals | On `[η, ε]`, `η > 0`, the core converges to `log ζ(1+η) − log ζ(1+ε)`. |
| Transporting a fixed positive aperture floor | Impossible along unbounded apertures; any positive floor loses at least `πe^{2(A−2)}`. A graded negative floor is the target. |
| Choosing a corrector from the desired bound | The adapted-energy criterion is exactly admission; without comparability the constant family has zero loss for every receiver. Its content is the construction. |
| Citing a short-window theorem at a fixed length as a uniform one | The length-uniform version needs the tiling argument and the monotonicity of `ψ`; the side conditions of the block estimate stay. |
| Taking the `30/17` block-equidistribution range for a balanced-scale result | The block-equidistribution transfer covers `Q ≥ P^{1+δ}` only; reaching `Q ≍ P` requires the short-window mean-square transfer (`exists_balanced_centredPrimeBlock_rowBilinear_le`), where the cubic/quartic Taylor tails remain `O(|S|(P/Q)²)`. |
| Subtracting a smooth prime main term and calling the remainder estimated | The remainder after the polar/PNT main term is the zero-width problem relocated; a power saving there is a zero-free strip. |

---

## 5. The research questions and what is settled

Each question is narrower than RH, though the strongest endpoint of several implies it.

| Question | Answer proved here | What remains |
|---|---|---|
| Can adjacent decompositions force a rate of compensation? | For one split the amplitude mismatch and the transverse remainder add up *exactly* to the relative complete energy (mechanism 16); on the actual large-prime sector the defect is `O(log^{−m}P)` for every `m` and summable over dyadic scales, the moving projection's connection term is summable against every polynomial weight `k^m`, and comparing cutoffs `P²` and `Q²` on `[1, P−1]` cancels `R_ε(N)` identically to give the power-saving cutoff shift `O(P^{1−3ε})` and polynomial relative decay `O(P^{−ε}log²P)` (mechanism 18). | Unconditional horizon-free control of the single-scale divisor remainder below `ε = ½`. |
| Can compatible constraints exclude critical blow-up profiles? | For the receiver: profiles living below the scale `E_T^{θ/(1−2ε)}`, `θ < 1`, are excluded, so a blow-up escapes to the horizon, and the normalized profile `u_{ε,T} = A_ε/√E_T` obeys the two-sided cofactor sandwich, the homogeneous cofactor limit `u + D^{ζ_ε,≥2}u = 0` on `n = o(√E_T)`, and the Möbius-factored tangent law while embedding the drifted, majorant, aliasing and oscillating-probe defect profiles (mechanism 19). For the raw comb the profile is classified completely through the resolvent energy identity `J(F) + 4J(F′) = A_F(0)`, the quartic second correction `−16‖f″‖²/r⁴`, and fixed-aperture `H¹` coercivity (mechanisms 5, 11–13). | Excluding horizon-shell oscillating defect profiles below `ε = ½`. |
| Can prime–polar coherence be handled before squaring? | The comb's coherent part is identified before the square, and on the extremal family it contributes nothing to the first-power charge (mechanism 6); the full compensated ledger remainder (retaining even parts and the archimedean gamma factor) has the unconditional de la Vallée Poussin bound `Ke^r exp(−c√(2r))‖F′‖₁ + O(‖F‖_{W^{1,1}})`, and an exponent `θ ∈ (0, ½)` on the smooth test class is equivalent to the Chebyshev bound `|E(s)| ≤ Ce^{(1/2+θ)s}` and to the zero-free strip `Re ρ ≤ ½ + θ` (mechanism 7). | Unconditional proof of an exponent `θ < ½`, which is a zero-free strip. |
| Can origin information be recovered stably at the threshold? | In the anchored pronic norm a change of origin by `k` cells costs exactly `(k+1)(k+2)/2`, so admission never sees finite origin information (mechanism 20); a drifting origin is priced by the tail beyond it, and uniform drift tolerance holds exactly for bounded drifts (mechanism 21); the comb's coherent part is anchored at the horizon `2r` (mechanism 5). | A tail-decay rate for the actual receiver beyond the origin, which is what a drifting origin needs. |
| Can arithmetic cross terms create a useful adapted energy? | An adapted energy is exactly admission, and cofinally RH; `bezoutUnitCorrector` gives unconditional `(1/3, 3)` comparability for all `ε, T`, eliminates the adverse first-cell work (`residualDampingWork ε 1 > 0`), extends to composite correctors with relative-loss stability `log((1+θ)/(1−θ))`, is unconditionally an adapted energy on `[a, c]` for `a ≥ ½`, and yields `Θ ≤ ½ + a₀` from any boundary-accumulating family on `(a₀, c]` (mechanism 26). | A horizon-free bound on `∫_a^c bezoutCorrectedRelativeLoss` for some `a < ½`. |
| Can positivity be replaced by the right graded floor? | Positive aperture floors cannot be transported and must lose at least `πe^{2(A−2)}` (mechanism 25); SRT's graded floor at rate `2σ` is the strip `½ + σ`. | Any fixed `σ < ½`. |
| What is the balanced-scale structure for actual rows? | The unbalanced block-equidistribution range reaches `30/17`, and the short-window mean-square transfer at `α > 17/30` reaches the balanced regime `P ≤ Q ≤ B P` with the block mass bounded by `√2 ε / Q` while `centredPrimeBlock Q` retains the exact omitted-residue-class limit `−π²(p²−1)²/(144p²(p−1))` (cancelled by `omittedClassCorrector`); a power saving in the short-window mean square is equivalent to `receiverDampingRate < ½` (mechanism 28). | Unconditional power saving in the short-window mean square, which is a zero-free strip. |

---

## 6. What compatibility must contribute

One decomposition gives a Pythagorean identity, not an extra inequality. A useful second
representation must constrain the same residual in a different way: shared divisor coefficients,
overlapping prime/cofactor cuts, a common successor boundary, or a pole term fixed by the source.
The new estimate must survive the change of representation, including the motion of its projection.

Three distinctions organize this work:

- **Relative and absolute compensation.** `α → 1` and `‖R‖/‖L‖ → 0` permit an unbounded complete
  energy. Admission needs bounds on `(1−α)²‖L‖² + ‖R‖²`, in the original normalization.
- **Large energy and adverse signed charge.** Translation and the resolvent explain the comb's
  energy. Its overlap with the test, and then its signed pairing with the poles, are different
  quantities. The exact two-pole defect identity in AIP is the appropriate bridge.
- **A criterion and its arithmetic producer.** Adapted energies are equivalent to admission.
  Their value lies in a corrector built from independently estimated source terms, with uniform
  comparability and signed recovery retained. Defining the corrector from the desired bound is
  circular.

These distinctions also specify useful partial results: a remainder exponent, a stable transfer
between decompositions, or a classification of limiting receiver profiles. None requires claiming
that every successful route must use the same mechanism.

---

## 7. Tools

- **Horizon concentration** (`tendsto_combAverage`, `tendsto_combPairAverage`): any bounded
  statistic of the rescaled comb shifts continuous at the horizon, in one or two variables.
- **The horizon law** (`eventually_abs_combTail_sub_le`,
  `eventually_abs_combAverage_sub_horizonIntegral_le`): any bounded uniformly continuous statistic
  of the comb depths, uniformly over translates; the shell comparisons on both sides are separate
  lemmas and can be reused with other weights.
- **The comb resolvent law** (`tendsto_combEnergy_div_combMass_sq_horizonEnergy`): the leading
  term of every comb Gram form.
- **Compensated prime–polar and full-ledger residuals** (`exists_abs_chebyshevTwoPoleDefect_mul_exp_le`,
  `exists_abs_sum_vonMangoldt_sub_polar_le`, `exists_abs_primeShift_sub_polar_le`,
  `fullLedgerCompensatedRemainder`, `exists_abs_fullLedgerCompensatedRemainder_le_deLaValleePoussin`,
  `fullLedger_sub_half_exponent_iff_chebyshev_bound`,
  `zeta_zeroFree_strip_of_fullLedger_sub_half_exponent`): the
  exponentially weighted two-pole defect, the residual of every lag weight and every ledger
  translate, and the full compensated ledger remainder with its archimedean bound and zero-free
  strip equivalence.
- **Curve-model combs and receivers** (`curvePointCount`, `curveCombMass`, `curveCombTail`,
  `curveComb`, `curveCombEnergy`, `curveHorizonWeight`, `curveHorizonEnergy`,
  `curveZ`, `curveDampedZinv`, `curveCentredPrefix`, `curveReceiverEnergy`,
  `curveAnnihilatorFilter`, `curveEigenvalueResidue`): the comb and the receiver of a
  function-field model built from its eigenvalues, with mass, depth and admission laws for every
  eigenvalue configuration; `norm_coeff_prod_le`, `coeff_geomSeries_mul_eq_neg_tail` and
  `coeff_curveAnnihilatorFilter_mul_curveCentredSeries` are the coefficient calculus behind them.
- **The single-average formula, the resolvent differential identity, and the moment calculus**
  (`horizonEnergy_eq_horizonIntegral_autoCorr`, `horizonResolvent_add_two_deriv`,
  `horizonEnergy_add_four_deriv_eq`, `horizonEnergy_second_order_identity`,
  `integral_pow_mul_horizonDensity`, `autoCorr_zero_sub_le`,
  `odd_horizonEnergy_ge_inv_add_four`): `J` as an expectation of `A_F` under the horizon law and
  as `‖ΨF‖²` with `J(F) + 4J(F′) = A_F(0)`, exact quadratic and quartic Taylor corrections, and
  fixed-aperture `H¹` coercivity.
- **Quantitative horizon law** (`exists_abs_combMass_sub_le`, `exists_abs_combTail_sub_le`,
  `exists_abs_combAverage_sub_horizonIntegral_le`, `exists_abs_combEnergy_sub_le`): the same laws
  with the explicit error `exp(−c√r)` and universal constants, for Lipschitz statistics and
  Lipschitz tests; `abs_autoCorr_sub_le` transfers a test's Lipschitz constant to its
  autocorrelation.
- **Compensation coordinates and two-scale transition calculus** (`compensationAmplitude`,
  `transverseRemainder`, `twoScaleCompleteShiftEnergy`, `pmTransverseRemainderSeq`,
  `exists_twoScaleCompleteShiftEnergy_le_pow_saving`,
  `exists_twoScaleCompleteShiftEnergy_div_sectorEnergy_le_rpow`,
  `twoScale_transverseRemainder_diff_energy_le`): single-scale and two-scale moving-projection
  identities, all-logarithmic-power defect and amplitude bounds, and the power-saving cutoff shift
  on `[1, P−1]`.
- **Budget hierarchy**: pointwise control implies a positive-part budget, which implies a signed
  budget; with an admitted right endpoint, the signed budget is equivalent to admission.
  The lacunary countermodel proves that the positive-part requirement is strictly stronger
  (`exists_admitted_monotone_not_positivePartContinuation`); admission also need not yield a
  pointwise budget (`exists_admits_everywhere_not_linearContinuation`).
- **Adapted-energy criterion and Bézout arithmetic correctors** (`AdaptedEnergy`,
  `bezoutUnitCorrector`, `bezoutCorrectedEnergy`, `bezoutCorrectedRelativeLoss`,
  `compositeArithmeticCorrector`, `bezoutCorrectedEnergy_comparison`,
  `integral_compositeCorrectedRelativeLoss_le`,
  `zetaZeroAbscissa_le_half_add_of_bezoutCorrected_family`,
  `riemannHypothesis_iff_cofinal_bezoutCorrected_loss`).
- **Aperture loss-rate calculus**: the ceiling exponent, its monotonicity, forced loss rates for
  floors and products.
- **Origin calculus** for the pronic norm: the exact shift constant and the head loss
  (`pronicEnergy_shift_le`, `pronicEnergy_le_head_add_shift`), the exact split at the origin
  (`pronicEnergy_add_eq`) and the two-sided tail price of a translate
  (`pronicTail_le_pronicEnergy_shift`, `pronicEnergy_shift_le_tail`).
- **Source growth bounds and normalized blow-up profiles** (`exists_abs_centredPrefix_le`,
  `exists_dampedMobiusEnergy_le`, `exists_dampedMobius_drift_le`, `admits_or_tendsto_atTop`,
  `normalizedReceiverProfile`, `pronicEnergy_rowDilate_sandwich`,
  `normalizedReceiverProfile_add_properUnitDilation_eq`,
  `cofactorAliasingWave_alias_eigenmode`,
  `tendsto_normalizedHalfProbeCombination_energy_share`): unit-energy normalization, horizon-shell
  concentration, exact horizon-dilation cofactor bounds, surviving inversion and tangent laws, and
  explicit escape/aliasing/spectral defect profiles.
- **The compatibility identities of the source**, owned by ACCE and BVI and used here as the
  constraints a second decomposition must respect: the tangent law `∂_ε A_ε(n) = E_ε(n)`
  (`BezoutValuationIncidence.hasDerivAt_pmPowerDampedCenteredDivisorPrefix`), its prime-dilation
  form `E_ε(n) = Σ_{j≤n} Λ(j)j^{−ε}A_ε(⌊n/j⌋) + m₀(ε)Ψ_ε(n) − n m(ε)`
  (`ArithmeticContinuationAndCriticalEnergy.dampedChebyshevError_eq_dilation`), the inversion law
  `Σ_{j≤n} j^{−ε}A_ε(⌊n/j⌋) = n − m₀(ε)Σ_{j≤n} j^{−ε}⌊n/j⌋`
  (`ArithmeticContinuationAndCriticalEnergy.sum_rpow_mul_centeredPrefix_eq`), the exact
  composition `D^f D^g = D^{f*g}` of prefix dilations
  (`ArithmeticContinuationAndCriticalEnergy.prefixDilation_comp`), and its consequence
  `Λ_ε = μ_ε * (log)_ε`: the tangent is the Möbius dilation of one explicit Möbius-free row
  (`ArithmeticContinuationAndCriticalEnergy.dampedChebyshevError_eq_moebiusDilation`). The prime
  dilation form and the Möbius dilation form are two decompositions of the same tangent, and
  their compatibility is the kind of second constraint §6 asks for. In the accounting of the
  work the only unpaid term is quadratic in the deviation `A_ε − 1`, bounded by
  `Σ_{j≤T}Λ(j)j^{−(ε+1/2)}` times the Báez–Duarte residual
  (`ArithmeticContinuationAndCriticalEnergy.abs_workQuadratic_le_energy`).
- **Length-uniform short windows and balanced-regime transfer** (`tileSeq`,
  `abs_sum_Icc_div_sq_le_of_shortWindowAverage`, `omittedClassCorrector`): length-uniform short
  windows from fixed-length ones, Cauchy–Schwarz block-mass elimination from the short-window
  average, and the zero-mean periodic sieve corrector for the omitted residue class.

---

## 8. Open research topics

1. **A two-scale compensation rate.** Comparing the overlapping large-prime decompositions at
   cutoffs `P²` and `Q²` (`Q ≥ P`, in particular `Q = 2P`) on their common head `1 ≤ N ≤ P − 1`
   cancels the cutoff-independent divisor remainder `R_ε(N)` identically and gives the power-saving
   cutoff shift `twoScaleCompleteShiftEnergy ε P Q P ≤ C P^{1−3ε}`
   (`exists_twoScaleCompleteShiftEnergy_le_pow_saving`) and the polynomial relative decay
   `O(P^{−ε} log² P)` against `‖L_P‖²`
   (`exists_twoScaleCompleteShiftEnergy_div_sectorEnergy_le_rpow`, with absolute decay to `0` for
   `ε > 1/3`), while the moving projection obeys
   `R_Q − R_P = (S_Q − S_P) − (1 − α_Q)(L_Q − L_P) + (α_Q − α_P) L_P`
   (`pmTransverseRemainderSeq_sub_eq_connection`, `twoScale_transverseRemainder_diff_energy_le`)
   with `|α_Q − α_P| ≤ K_m/log^m P` and `Σ_k k^m |α_{2^{k+1}} − α_{2^k}| < ∞` (mechanism 18).
2. **Constructing an arithmetic corrector.** The Bézout unit-boundary corrector
   `bezoutUnitCorrector ε T = Σ_{n ≤ T}(1 − 2A_ε(n))/(n(n+1))` completes the square
   `1 + pmPowerDampedDualResidual ε T`, satisfies unconditional `(1/3, 3)` comparability for all
   `ε, T` (`bezoutCorrectedEnergy_comparison`), has a uniformly bounded derivative on `[a, ∞)`
   (`exists_abs_bezoutUnitCorrectorDeriv_le`), eliminates the adverse first-cell work
   (`eventually_residualDampingWork_one_pos`), extends to composite correctors with relative-loss
   stability `log((1+θ)/(1−θ))` (`integral_compositeCorrectedRelativeLoss_le`), is unconditionally
   an adapted energy on `[a, c]` for `a ≥ ½` (`bezoutCorrected_adaptedEnergy_of_half_le`), yields
   the strip `Θ ≤ ½ + a₀` from any boundary-accumulating family on `(a₀, c]`
   (`zetaZeroAbscissa_le_half_add_of_bezoutCorrected_family`), and is cofinally equivalent to RH
   (`riemannHypothesis_iff_cofinal_bezoutCorrected_loss`, mechanism 26).
3. **Receiver blow-up profiles.** The critical-energy normalization
   `u_{ε,T}(n) = A_ε(n)/√E_T(ε)` (`normalizedReceiverProfile`) has exact unit pronic energy for
   `ε > 0`, `T ≥ 1`, concentrates `1 − o(1)` of its energy in `(⌊E_T^{θ/(1−2ε)}⌋, T]` under
   blow-up (`admits_or_normalizedReceiverProfile_shell_tendsto_one`), obeys the two-sided
   horizon-dilation cofactor sandwich (`pronicEnergy_rowDilate_sandwich`) so deep cofactors vanish,
   satisfies the normalized inversion law converging to `u + D^{ζ_ε,≥2}u = 0` on `n = o(√E_T)`
   (`admits_or_tendsto_normalizedReceiverProfile_add_properUnitDilation_zero`), the self-improving
   identity, and the Möbius-factored tangent law, and embeds the drifted `n^{1/4}`, negative
   majorant, cofactor aliasing (`ω = 2πk/log j`) and spectral oscillating-probe defect families
   (mechanism 19).
4. **Quantitative horizon asymptotics.** The resolvent `ΨF` satisfies `ΨF + 2(ΨF)′ = F`
   (`horizonResolvent_add_two_deriv`) and the exact energy identity `J(F) + 4J(F′) = A_F(0)`
   (`horizonEnergy_add_four_deriv_eq`), giving `A_F(0) − J(F) − 4A_{F′}(0) = −16J(F″)`
   (`horizonEnergy_second_order_identity`) and the exact quartic second correction `−16‖f″‖²/r⁴`
   for both `J(F_r)` and `E_r(F_r)/S_r²` on slowly varying `C²` tests
   (`tendsto_pow_four_mul_combEnergy_rescaledTest_second_correction`); at a fixed aperture `R > 0`,
   the unrestricted odd coercive constant is `0` (`not_exists_pos_odd_horizonEnergy_coercive`), the
   `H¹`-restricted class `‖F′‖² ≤ γ‖F‖²` has coercive constant `max(1/(1 + 4γ), 1 − 4γ)`
   (`odd_horizonEnergy_ge_inv_add_four`), and the optimal Poincaré constant is bounded above by
   `1/(1 + π²/R²)` (`odd_poincare_mode_horizonEnergy_lt`, mechanism 13).
5. **The compensated remainder of the full ledger.** Retaining the even parts and the archimedean
   gamma factor, `fullLedgerCompensatedRemainder F` vanishes on odd tests, has archimedean part
   `O(‖F‖₁ + ‖F′‖₁)` uniformly in the aperture, and satisfies the unconditional de la Vallée
   Poussin bound `Ke^r exp(−c√(2r))‖F′‖₁ + (2π + 2)(‖F‖₁ + ‖F′‖₁)` on `C¹` tests in `[−r, r]`
   (`exists_abs_fullLedgerCompensatedRemainder_le_deLaValleePoussin`); an exponent `θ ∈ (0, ½)` on
   the smooth test class is equivalent to `|E(s)| ≤ Ce^{(1/2+θ)s}`
   (`fullLedger_sub_half_exponent_iff_chebyshev_bound`) and to the zero-free strip `Re ρ ≤ ½ + θ`
   (`zeta_zeroFree_strip_of_fullLedger_sub_half_exponent`,
   `riemannHypothesis_iff_forall_pos_fullLedger_exponent`, mechanism 7).
6. **The balanced regime.** For the actual centred prime and Möbius blocks at `Q ≍ P`, the
   short-window mean-square transfer at `α > 17/30` gives unconditional `o(1)` savings over the
   large-sieve barrier across `P ≤ Q ≤ B P` with the block-mass term bounded by `√2 ε / Q`, while
   `centredPrimeBlock Q` retains the exact omitted-residue-class limit
   `−π²(p² − 1)²/(144 p²(p − 1))` (cancelled by `omittedClassCorrector p Q`), and upgrading the
   short-window mean square to a power saving is equivalent to `receiverDampingRate < ½` for the
   complete coupled receiver (mechanism 28).
7. **Function-field calibration.** In the curve model the horizon law is geometric with
   square-root error, the curve comb obeys the discrete resolvent law and is uniformly coercive
   (mechanism 14), and the receiver is admitted above the zero width and fails below it for any
   number of eigenvalues via the polynomial annihilator filter, so cofinal admission is equivalent
   to the Weil bound (`weil_iff_cofinal_curveReceiverEnergy`, mechanism 15).

---

## 9. Foundational pillar theorems

1. `exists_odd_smooth_family_sharp_comb_rate` — the sharp exponential comb family, the translation
   survivor, and the vanishing charge, on the ledger's test class.
2. `tendsto_combEnergy_div_combMass_sq_horizonEnergy` and `horizonEnergy_pos` — the comb resolvent
   law and strict positivity on nonzero continuous compact tests.
3. `norm_add_sq_eq_compensation` with `pmCompleteHeadEnergy_eq_compensation`,
   `exists_compensationDefect_le_inv_log_pow`, and
   `exists_twoScaleCompleteShiftEnergy_div_sectorEnergy_le_rpow` — the Pythagorean compensation
   law, its actual instance, its all-logarithmic-power single-scale rate, and its polynomial
   two-scale cutoff shift rate.
4. `exists_admitted_monotone_not_positivePartContinuation` — signed recovery is strictly weaker
   than paying every loss.
5. `tendsto_integral_workCore_logZeta` — the core debt on positive intervals.
6. `not_relative_step_transport` and `exists_le_floorLoss_of_floor` — the forced aperture loss.
7. `adaptedEnergy_dampedMobiusEnergy_iff_admits`, `bezoutCorrectedEnergy_comparison`,
   `zetaZeroAbscissa_le_half_add_of_bezoutCorrected_family`, and
   `riemannHypothesis_iff_cofinal_bezoutCorrected_loss` — the corrector criterion, the unconditional
   Bézout unit-boundary corrector, its zero-free strip transport, and its RH equivalence;
   `weil_iff_cofinal_curveReceiverEnergy` and `not_exists_curveReceiverEnergy_le` — its
   multi-eigenvalue function-field calibration.
8. `exists_abs_rowBilinear_centredPrimeRow_le_of_range`,
   `exists_balanced_centredPrimeBlock_rowBilinear_le`, and
   `tendsto_mul_kernelStatistic_centredPrimeBlock` — the `30/17` unbalanced range, the balanced
   regime `P ≤ Q ≤ B P` with block-mass elimination, the omitted-residue-class law of the centred
   prime block, and `primePowerWindowSaving_iff_receiverDampingRate_lt_half`.
9. `pronicEnergy_shift_le` with `admits_dampedMobiusEnergy_iff_shift` — the exact price of a change
   of origin, and the invariance of admission under it; `forall_admitted_drift_admitted_iff` — a
   drifting origin is tolerated uniformly exactly when it is bounded.
10. `admits_or_escapesToHorizon`, `pronicEnergy_rowDilate_sandwich`, and
    `admits_or_tendsto_normalizedReceiverProfile_add_properUnitDilation_zero` — horizon escape of a
    receiver blow-up, the two-sided horizon-dilation cofactor sandwich, and the homogeneous cofactor
    law of the normalized receiver profile.
11. `exists_abs_combEnergy_div_sub_horizonEnergy_le` with `exists_abs_combMass_sub_le`,
    `horizonEnergy_add_four_deriv_eq`, and
    `tendsto_pow_four_mul_combEnergy_rescaledTest_second_correction` — the horizon and resolvent
    laws at the de la Vallée Poussin rate, the exact resolvent energy identity, and the quadratic
    and quartic corrections `4‖f′‖²/r² − 16‖f″‖²/r⁴` of the translation law.
12. `exists_abs_primeShift_sub_polar_le`,
    `exists_abs_fullLedgerCompensatedRemainder_le_deLaValleePoussin`, and
    `zeta_zeroFree_strip_of_fullLedger_sub_half_exponent` — the compensated prime–polar and
    full-ledger residuals at the de la Vallée Poussin rate and their zero-free strip equivalence.

---

## 10. Success criteria and what a contribution must be

The programme succeeds in degrees, each measured in the corpus's units:

- a **two-scale rate**: a bound on a compensation coordinate of the actual source stronger than
  relative cancellation, with all transfer terms included;
- a **corrector on one interval**: an adapted energy built from arithmetic cross terms on some
  `[a, c]`, `a > 0`, transferring admission from `c` to `a`; a boundary-accumulating family
  then yields a zero-free strip;
- a **classified defect family** for the receiver, excluding a nontrivial class of profiles;
- the **endpoint**: cofinal admission, which is RH.

A contribution to ACCC must

- be unconditional, on the anchored source or on an honestly quantified class containing it, with
  the relation the adversarial models violate named;
- keep the mixed terms, poles, even parts and boundary terms until their cancellation is used;
- pay for every change of norm, cutoff, gauge, scale or origin with an explicit term;
- state its uniformity: which constants depend on the damping or the aperture, and that none
  depends on the horizon;
- come with its stability estimate if it recovers or separates;
- report a rate — a residual exponent, a logarithmic saving, an aperture decay, a resolution
  threshold — and never call an identity or an equivalent criterion a bound;
- keep failure constructive: an obstruction comes with its strongest positive law, as the
  translation and resolvent laws come with the exponential comb family;
- hide no analytic input in an interface: an assumed coercivity, budget or positive realization is
  an open obligation, not a theorem.

---

## 11. Principles

1. **Exact source before estimates.** Derive the finite identities from the actual arithmetic laws.
2. **Compensate before taking absolute values.** The separate pieces may be unbounded.
3. **Pay for changes of representation.** Moving projections have connection terms; changes of
   origin are not free.
4. **Uniformity is part of the theorem.** A constant depending on a positive damping is acceptable
   for admission; a constant secretly depending on the horizon is not.
5. **Recovery requires stability.**
6. **Measure partial progress by a rate.**
7. **Keep failure constructive.**
8. **No analytic input hidden in an interface.**
9. **Search the corpus before proving:** `scripts/formal_tools.py research "<query>"` (from the repository root); the comb,
   the pairing calculus, the receiver and its dictionaries already exist and are not redefined.
