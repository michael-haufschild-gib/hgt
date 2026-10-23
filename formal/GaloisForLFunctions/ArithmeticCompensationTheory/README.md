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
7. **The ledger's own test class.** The profile `oddBump(x) = x e^{−1/(1−x²)}` normalized to unit
   mass gives smooth odd tests supported in `[−r, r]` on which all of the above hold at once
   (`exists_odd_smooth_family_sharp_comb_rate`).
8. **The depth law.** The comb tail tends to `e^{−u/2}` uniformly in `u ≥ 0`
   (`eventually_abs_combTail_sub_le`): a near range where both `S_y/e^y` are within `δ` of `2`, and
   a far range controlled by monotonicity.
9. **Depth statistics converge to the horizon law, uniformly over translates**
   (`eventually_abs_combAverage_sub_horizonIntegral_le`). Shells of depth `[kh, (k + 1)h)` carry the
   comb mass `S_{r−kh/2} − S_{r−(k+1)h/2}` (`combShellMass`); comparing the discrete shell sum
   (`abs_combDepthSum_sub_shells_le`) and the continuous one (`abs_horizonIntegral_sub_shells_le`)
   costs the modulus of continuity, the tail at the cutoff and `2KMη` from the uniform depth law.
10. **The comb resolvent law.** Since `log q − log p = u_p − u_q` (`combDepth_sub_combDepth`), the
    comb energy is a double depth statistic (`combEnergy_eq_depthSum`), and the uniform version of
    mechanism 9 applied twice gives, for every continuous compactly supported test,
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
10′. **The horizon law at the de la Vallée Poussin rate.** Abel summation of `p^{−1/2} log p`
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
10″. **The horizon energy is one horizon average, and the translation deficit is inverse-square.**
    The double average collapses: `J(F) = ∫_{u>0} A_F(u) ½e^{−u/2} du`
    (`horizonEnergy_eq_horizonIntegral_autoCorr`), by integrating `−¼e^{−v}Φ(−v)`,
    `Φ(w) = ∫_{s>w} A_F(s)e^{−s/2} ds`, along the half-line with `A_F` even. A `Λ`-Lipschitz test
    supported in `[−R, R]` has `A(0) − A(s) = ½∫(F(x) − F(x+s))² ≤ Λ²s²(R + |s|)`
    (`autoCorr_zero_sub_le`), and the horizon moments are `∫u^k dμ = 2^k k!`
    (`integral_pow_mul_horizonDensity`). On the slowly varying family this gives
    `A_f(0) − Λ²(8/r² + 48/r³) ≤ J(F_r) ≤ A_f(0)` (`horizonEnergy_rescaledTest_ge`), and since the
    rate of mechanism 10′ has test-independent constants, the comb itself satisfies
    `0 ≤ A_f(0) − E_r(F_r)/S_r² ≤ C/r²` (`exists_combEnergy_rescaledTest_deficit_le`). The deficit
    is of the order of the resolvent's first correction `−4‖f′‖²/r²`, not of the prime error.

### Compensation coordinates

11. **The Pythagorean compensation law.** `‖L + C‖² = (1 − α)²‖L‖² + ‖R‖²` for `L ≠ 0`, with `⟪L, R⟫ = 0`
    (`norm_add_sq_eq_compensation`, `inner_transverseRemainder`), hence
    `(1 − α)² + ‖R‖²/‖L‖² = ‖L + C‖²/‖L‖²` (`compensationDefect_eq_relativeEnergy`). The same law
    holds for scalar Gram data, with `‖R‖² ≥ 0` from Cauchy–Schwarz (`gram_add_eq_compensation`,
    `gramTransverse_nonneg`, `gram_coordinates_le`).
12. **The actual instance.** For `0 < ε < ½` the large-prime sector of the damped
    Möbius–Ramanujan expansion at cutoff `P²` has `α_P → 1` and `‖R_P‖²/‖L_P‖² → 0`
    (`tendsto_pmCompensationAmplitude_one`, `tendsto_pmTransverseEnergy_div_sectorEnergy_zero`),
    and the complete head energy is exactly `(1 − α_P)²‖L_P‖² + ‖R_P‖²`
    (`pmCompleteHeadEnergy_eq_compensation`, from the energy split
    `pmCompleteHeadEnergy_eq_sum` and the Cauchy–Schwarz bound `pmMixedEnergy_sq_le`).
12′. **The compensation rate on the actual source.** The defect is the relative complete head
    energy for all large `P` (`eventually_compensationDefect_eq_relative`); the sector energy is at least `cP^{1−2ε}/log²P`
    (`sectorEnergy_eventually_lower`), the complete energy at most twice the divisor-remainder
    energy plus the Ramanujan truncation cost `2T⁴P^{1−3ε}` (`prefixEnergy_le`), and the
    remainder energy is `O(P^{(1−2ε)/2}) + O(1) + O(P^{1−2ε}/log⁸P)` (`remainderEnergy_le`).
    Hence `(1 − α_P)² + ‖R_P‖²/‖L_P‖² ≤ K/log⁶P` for all large `P`
    (`exists_compensationDefect_le_inv_log_pow_six`): an explicit logarithmic rate of compensation,
    with an absolute complete energy `O(P^{1−2ε}/log⁸P)` that still grows with the cutoff.
    The rate iterates over scales: the defects at `P = 2^k` are summable
    (`summable_compensationDefect_dyadic`), while the absolute energies are not. The moving
    projection pays a summable connection term: `|1 − α_P| ≤ K/log³P`
    (`exists_abs_one_sub_pmCompensationAmplitude_le`), so the amplitude has bounded variation
    over the dyadic scales (`summable_abs_pmCompensationAmplitude_dyadic_sub`), and the relative
    transverse energies are summable (`summable_pmTransverseEnergy_div_sectorEnergy_dyadic`).

### Where a blow-up of the receiver goes

12‴. **A blow-up escapes to the horizon.** The damped divisor remainder read at the integers gives
    the source bound `|A_ε(n)| ≤ Cn^{1−ε}` for `0 < ε < ½` (`exists_abs_centredPrefix_le`), so each
    cell carries at most `C²n^{−2ε}` and the receiver grows at most at the trivial rate,
    `E_N(ε) ≤ D(1 + N^{1−2ε})` (`exists_dampedMobiusEnergy_le`). Hence the blow-up dichotomy
    (`admits_or_escapesToHorizon`): either the receiver is admitted at `ε`, or for every `θ < 1`
    the energy below the scale `E_T^{θ/(1−2ε)}` is a vanishing fraction of `E_T`; and at every
    damping, either admission holds or every fixed window and every cell carries a vanishing
    fraction (`admits_or_fixedWindowEnergy_vanishes`). Profiles concentrating at
    bounded scales, or at scales polynomially below `E_T^{1/(1−2ε)}`, are excluded.

### The price of a change of origin

12″. **A finite change of origin costs exactly `(k+1)(k+2)/2`.** Shifting a sequence by `k` cells
    multiplies its pronic energy by at most `(k+1)(k+2)/2` (`pronicEnergy_shift_le`, from the weight
    comparison `pronicWeight_shift_le`), the factor is attained by the indicator of the cell `k + 1`
    (`pronicEnergy_shift_indicator`), and the shift loses only the first `k` cells in the other
    direction (`pronicEnergy_le_head_add_shift`). Admission is therefore invariant under every
    finite change of origin (`bddAbove_pronicEnergy_shift_iff`), in particular for the damped Möbius
    receiver (`admits_dampedMobiusEnergy_iff_shift`). Finite origin information is recovered stably
    in the critical norm.
12⁗. **A drifting origin is priced by the tail beyond it.** The translate `a(· + k)` on `[1, T]`
    carries between the tail `E(T+k) − E(k)` and `(k+1)(k+2)/2` times that tail
    (`pronicTail_le_pronicEnergy_shift`, `pronicEnergy_shift_le_tail`). Every admitted sequence
    stays admitted along a drift `k(T)` if and only if the drift is bounded
    (`forall_admitted_drift_admitted_iff`), and the single admitted sequence `n^{1/4}` has drifted
    energy tending to infinity along every drift tending to infinity
    (`tendsto_pronicEnergy_quarterPower_drift`): control of a drifting origin is never a norm fact
    and must use the tail decay of the source. For the receiver the source bound gives the trivial
    drift budget `D(k+1)^{2−2ε}(1 + T^{1−2ε})` (`exists_dampedMobius_drift_le`).

### Quantifier corrections of the continuation problem

13. **The signed budget is strictly weaker than its positive part.** The positive-part budget
    implies the averaged one (`averagedContinuation_of_positivePart`), and the lacunary family
    `E_T(ε) = Σ_{1 ≤ k ≤ T} 2^{−k}(2 + sin(16^k ε))` — nonnegative, nondecreasing in the horizon,
    bounded by `3`, hence admitted everywhere with averaged budgets on every interval — has
    `∫_a^c (r_T)_+ → ∞` on every nondegenerate interval
    (`exists_admitted_monotone_not_positivePartContinuation`). The mechanism is lacunary
    near-orthogonality: `∫_a^c E'_T cos(16^T ε) ≥ 8^T(c − a)/2 − 2`
    (`integral_lacunaryEnergyDeriv_mul_cos_ge`).
14. **The core debt on a positive interval is a zeta-log ratio.**
    `lim_T ∫_η^ε core_x(T) dx = log ζ(1+η) − log ζ(1+ε)` for `η, ε > 0`
    (`tendsto_integral_workCore_logZeta`), by dominated convergence against the Euler logarithm,
    with the horizon-free bound `∫_η^ε core ≤ log ζ(1+η) − log ζ(1+ε)` for `η ≤ ε`
    (`integral_workCore_le_logZeta`). The divergence of `exists_horizon_integral_workCore_ge` is an
    endpoint effect at zero damping.
15. **The first cell carries adverse work.** `W_1(ε) = −(1 − 1/ζ(1+ε)) m(ε)/2 → −½`
    (`tendsto_signedDampingWork_one`), so global nonnegative work fails on the actual source
    (`not_forall_signedDampingWork_nonneg`).
16. **The aperture floor must decay doubly exponentially.** From the Gaussian ceiling
    `μ(A) ≤ K e^{(11/2)A − πe^{2(A−2)}}`: no fixed positive floor along any unbounded aperture sequence
    (`not_exists_positive_floor_along`); the half-summable relative transport, whose conclusion is
    the floor `1/10000`, is impossible there (`not_relative_step_transport`); every floor
    `m₀e^{−B(A)}` has `B(A) ≥ πe^{2(A−2)} − (11/2)A + log(m₀/K)` (`exists_le_floorLoss_of_floor`);
    transported products lie below the ceiling (`prod_le_ceiling_of_relative_step`); and the
    harmonic transport fails along linearly growing apertures
    (`exists_groundEnergy_lt_harmonic_transport`).
17. **An adapted energy is exactly admission.** With the right end admitted, an adapted energy on
    `[a, c]` exists iff the receiver is admitted at `a`, for every nonnegative differentiable family
    with integrable relative loss (`adaptedEnergy_iff_admits`); for the damped Möbius receiver on
    `[a, ½]` all of these inputs are proved (`adaptedEnergy_dampedMobiusEnergy_iff_admits`); a pointwise
    corrector budget produces one (`adaptedEnergy_of_pointwise`); and cofinal adapted energies on
    `[a, ½]` for the damped Möbius receiver are RH (`riemannHypothesis_iff_cofinal_adaptedEnergy`).

### An internal transfer

18. **Huxley's uniform window at the Guth–Maynard exponent.** For every `α > 17/30`,
    `|ψ(x + h) − ψ(x) − h| ≤ εh` uniformly for `x^α ≤ h ≤ x/2`
    (`eventually_abs_psi_window_sub_le_seventeenThirtieths`): tile `[x, x + h]` by windows
    `[y, y + y^β]`, `17/30 < β < α` (`tileSeq`); the errors add, and the last partial window costs
    `(1 + ε/2)y^β = o(x^α)` by monotonicity of `ψ`.
19. **The centred prime row on the wider range.** The BVI actual-row estimate holds at every block
    exponent `α > 17/30` (`exists_abs_rowBilinear_centredPrimeRow_le_seventeenThirtieths`), hence
    on `P^{1+δ} ≤ Q ≤ P^{30/17−δ}` for horizons `N ≤ Q^C` at `α = 17/30 + δ/4`
    (`exists_abs_rowBilinear_centredPrimeRow_le_of_range`).

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
| Taking the `30/17` range for a balanced-scale result | The transfer covers `Q ≥ P^{1+δ}` only; the regime `Q ≍ P` is untouched. |
| Subtracting a smooth prime main term and calling the remainder estimated | The remainder after the polar/PNT main term is the zero-width problem relocated; a power saving there is a zero-free strip. |

---

## 5. The research questions and what is settled

Each question is narrower than RH, though the strongest endpoint of several implies it.

| Question | Answer proved here | What remains |
|---|---|---|
| Can adjacent decompositions force a rate of compensation? | For one split the amplitude mismatch and the transverse remainder add up *exactly* to the relative complete energy (mechanism 11); on the actual large-prime sector the defect is `O(log⁻⁶P)` and summable over dyadic scales, and the moving projection's connection term is summable (mechanism 12′). | A rate from a second, compatible decomposition that bounds the absolute remainder. |
| Can compatible constraints exclude critical blow-up profiles? | For the receiver: profiles living below the scale `E_T^{θ/(1−2ε)}`, `θ < 1`, are excluded, so a blow-up escapes to the horizon (mechanism 12‴). For the raw comb the profile is classified completely: translation on slowly varying tests, exponential resolvent on fixed tests, `J(F) > 0` on every nonzero test (mechanisms 5, 10), and on Lipschitz tests the resolvent law holds at the rate `exp(−c√r)` with universal constants (mechanism 10′). | The classification of the receiver's profiles at the horizon itself. |
| Can prime–polar coherence be handled before squaring? | The comb's coherent part is identified before the square, and on the extremal family it contributes nothing to the first-power charge (mechanism 6); the exact prime–polar pairing is AIP's two-pole defect identity. | A remainder exponent below the trivial one, which is a zero-free strip. |
| Can origin information be recovered stably at the threshold? | In the anchored pronic norm a change of origin by `k` cells costs exactly `(k+1)(k+2)/2`, so admission never sees finite origin information (mechanism 12″); a drifting origin is priced by the tail beyond it, and uniform drift tolerance holds exactly for bounded drifts (mechanism 12⁗); the comb's coherent part is anchored at the horizon `2r` (mechanism 5). | A tail-decay rate for the actual receiver beyond the origin, which is what a drifting origin needs. |
| Can arithmetic cross terms create a useful adapted energy? | An adapted energy is exactly admission, and cofinally RH (mechanism 17); a pointwise corrector budget is one producer. | The construction of `C_T` from source terms with independent constants. |
| Can positivity be replaced by the right graded floor? | Positive aperture floors cannot be transported and must lose at least `πe^{2(A−2)}` (mechanism 16); SRT's graded floor at rate `2σ` is the strip `½ + σ`. | Any fixed `σ < ½`. |
| What is the balanced-scale obstruction for actual rows? | The unbalanced range of the centred prime row reaches `30/17` (mechanism 19); the method stops at `Q ≍ P`, where `3P ≤ 2εQ` fails. | A saving at `Q ≍ P` keeping the omitted-residue-class main term. |

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
- **The single-average formula and the moment calculus** (`horizonEnergy_eq_horizonIntegral_autoCorr`,
  `integral_pow_mul_horizonDensity`, `autoCorr_zero_sub_le`): `J` as an expectation of `A_F`
  under the horizon law, with explicit moments and a quadratic deficit at the origin.
- **Quantitative horizon law** (`exists_abs_combMass_sub_le`, `exists_abs_combTail_sub_le`,
  `exists_abs_combAverage_sub_horizonIntegral_le`, `exists_abs_combEnergy_sub_le`): the same laws
  with the explicit error `exp(−c√r)` and universal constants, for Lipschitz statistics and
  Lipschitz tests; `abs_autoCorr_sub_le` transfers a test's Lipschitz constant to its
  autocorrelation.
- **Compensation coordinates** (abstract and scalar), with the actual PM-Ramanujan instance and its
  explicit logarithmic rate.
- **Budget hierarchy**: pointwise control implies a positive-part budget, which implies a signed
  budget; with an admitted right endpoint, the signed budget is equivalent to admission.
  The lacunary countermodel proves that the positive-part requirement is strictly stronger
  (`exists_admitted_monotone_not_positivePartContinuation`); admission also need not yield a
  pointwise budget (`exists_admits_everywhere_not_linearContinuation`).
- **Adapted-energy criterion** and its arithmetic dictionary.
- **Aperture loss-rate calculus**: the ceiling exponent, its monotonicity, forced loss rates for
  floors and products.
- **Origin calculus** for the pronic norm: the exact shift constant and the head loss
  (`pronicEnergy_shift_le`, `pronicEnergy_le_head_add_shift`), the exact split at the origin
  (`pronicEnergy_add_eq`) and the two-sided tail price of a translate
  (`pronicTail_le_pronicEnergy_shift`, `pronicEnergy_shift_le_tail`).
- **Source growth bounds**: `|A_ε(n)| ≤ Cn^{1−ε}` (`exists_abs_centredPrefix_le`), the trivial
  energy rate (`exists_dampedMobiusEnergy_le`) and its drifted form
  (`exists_dampedMobius_drift_le`); the admitted-or-unbounded dichotomy
  (`admits_or_tendsto_atTop`) turns any of them into an escape statement for a blow-up.
- **The compatibility identities of the source**, owned by ACCE and BVI and used here as the
  constraints a second decomposition must respect: the tangent law `∂_ε A_ε(n) = E_ε(n)`
  (`BezoutValuationIncidence.hasDerivAt_pmPowerDampedCenteredDivisorPrefix`), its prime-dilation
  form `E_ε(n) = Σ_{j≤n} Λ(j)j^{−ε}A_ε(⌊n/j⌋) + m₀(ε)Ψ_ε(n) − n m(ε)`
  (`ArithmeticContinuationAndCriticalEnergy.dampedChebyshevError_eq_dilation`), the inversion law
  `Σ_{j≤n} j^{−ε}A_ε(⌊n/j⌋) = n − m₀(ε)Σ_{j≤n} j^{−ε}⌊n/j⌋`
  (`ArithmeticContinuationAndCriticalEnergy.sum_rpow_mul_centeredPrefix_eq`) and the exact
  composition `D^f D^g = D^{f*g}` of prefix dilations
  (`ArithmeticContinuationAndCriticalEnergy.prefixDilation_comp`).
- **Length-uniform short windows** from fixed-length ones (`tileSeq`), reusable for any exponent
  at which the corpus owns a fixed-length theorem.

---

## 8. Open research topics

1. **A two-scale compensation rate.** Choose one actual-source pair of overlapping decompositions —
   the large-prime sector at cutoffs `P²` and `(2P)²`, or adjacent prime/cofactor splits of the same
   integers with their common successor boundary — and prove a bound on the mismatch of their
   compensation coordinates stronger than the relative cancellation, with the connection term of
   the moving projection included. State the intended gain first: a better residual rate, a stable
   corrector, or a classified defect family.
2. **Constructing an arithmetic corrector.** On one compact interval `[a, c]`, `a > 0`, build
   `C_T` from the mixed large-prime/complement terms and the Bézout boundary corrections, with
   `m(1+E_T) ≤ 1+E_T+C_T ≤ M(1+E_T)` and a signed loss bound proved independently.
   An admitted right endpoint gives admission at the left endpoint. A strip conclusion needs
   a family of admitted dampings accumulating at the desired boundary, not one isolated
   admitted damping; adapted energies on `[a, ½]` cofinally as `a ↓ 0` are RH.
3. **Receiver blow-up profiles.** Normalize an actual receiver sequence by its critical energy,
   retain scale, cofactor, origin and frequency data, and derive the arithmetic identities that
   survive in the limit; the escape and aliasing examples of the corpus must appear in the defect
   space. The comb resolvent law is the model case.
4. **Quantitative horizon asymptotics.** Strict positivity of `J` is proved; on Lipschitz tests the
   comb converges to its resolvent at the rate `exp(−c√r)` with universal constants (mechanism
   10′); `J(F)` is the single horizon average of `A_F`, and on slowly varying tests the deficit is
   `O(r^{−2})` (mechanism 10″). Open: the exact first correction `−4‖f′‖²/r²` for `C¹` profiles,
   and lower bounds on `J` over specified profile classes uniform in the profile.
5. **The compensated remainder of the full ledger.** Pair the comb's coherent part with the pole
   charge before squaring, on an expanding test class, and bound the remainder with an explicit
   aperture exponent; any exponent below the trivial one is a strip.
6. **The balanced regime.** Classify or save for the actual centred prime/Möbius incidence at
   `Q ≍ P`, keeping the omitted-residue-class main term. BVI's block mean-square estimates already
   give balanced-scale control for the stated centred rows; distinguish that result from a
   uniform bound for the complete coupled receiver.
7. **Function-field calibration.** Reproduce the comb laws over a nontrivial curve, where the
   rational zeta function does not make the cancellation degenerate, and identify what replaces
   the horizon law.

---

## 9. Foundational pillar theorems

1. `exists_odd_smooth_family_sharp_comb_rate` — the sharp exponential comb family, the translation
   survivor, and the vanishing charge, on the ledger's test class.
2. `tendsto_combEnergy_div_combMass_sq_horizonEnergy` and `horizonEnergy_pos` — the comb resolvent
   law and strict positivity on nonzero continuous compact tests.
3. `norm_add_sq_eq_compensation` with `pmCompleteHeadEnergy_eq_compensation` and
   `exists_compensationDefect_le_inv_log_pow_six` — the Pythagorean compensation law, its actual
   instance, and its logarithmic rate.
4. `exists_admitted_monotone_not_positivePartContinuation` — signed recovery is strictly weaker
   than paying every loss.
5. `tendsto_integral_workCore_logZeta` — the core debt on positive intervals.
6. `not_relative_step_transport` and `exists_le_floorLoss_of_floor` — the forced aperture loss.
7. `adaptedEnergy_dampedMobiusEnergy_iff_admits` and `riemannHypothesis_iff_cofinal_adaptedEnergy` — the corrector
   criterion and its arithmetic dictionary.
8. `exists_abs_rowBilinear_centredPrimeRow_le_of_range` — the `30/17` range.
9. `pronicEnergy_shift_le` with `admits_dampedMobiusEnergy_iff_shift` — the exact price of a change
   of origin, and the invariance of admission under it; `forall_admitted_drift_admitted_iff` — a
   drifting origin is tolerated uniformly exactly when it is bounded.
10. `admits_or_escapesToHorizon` — a blow-up of the receiver escapes to the horizon.
11. `exists_abs_combEnergy_div_sub_horizonEnergy_le` with `exists_abs_combMass_sub_le` — the
    horizon law and the resolvent law at the de la Vallée Poussin rate.

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
