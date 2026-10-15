import GaloisForLFunctions.RHTower.EvenSectorTwistedArcNull
import GaloisForLFunctions.RHTower.CHMDStage2KleinGordonTransmutationAndTContourBochner

/-!
# CHMD Stage 3: Unconditional 1D Sech-Representation and Twisted-Arc Annihilation

This module establishes **Stage 3** of the Causal Hyperbolic–Modular Duality (CHMD) route by
removing the Bochner measure hypothesis `hν` from the kernel and multiplier representations of
`EvenSectorSpectralConsistency` and `EvenSectorSechRepresentation`, and proving the unconditional
1D sech-integral representation and twisted-arc annihilation equations:

1. **Unconditional Exponential Bound on `evenPrimePart` and Chebyshev Bound for `Λ`
   (`abs_vonMangoldt_le_sqrt_mul_one_add_log`, `abs_evenPrimePart_cos_mul_le`,
   `integrable_mul_evenPrimePart_cos_mul`)**:
   - In `EvenSectorSpectralConsistency.evenWeilDensity_specSq_mul_kernel`, a Bochner measure `ν`
     was assumed in order to deduce `Integrable (fun t => κ t * Q t)` via `|cosineShiftFn| ≤ ν(ℝ)`.
   - Here we bound `|Q(t)| = |evenPrimePart lam (cos(t ρ(z)) K(z))|` directly from the strip decay
     of `K` by `C_Q * exp(5/4 * |t|)`. Together with continuity of `cosineShiftFn lam Φ`, this gives
     `Integrable (fun t => κ t * Q t)` and `Integrable (fun t => κ t * cosineShiftFn lam Φ t)` for
     every `κ` with `|κ(t)| ≤ C_κ * exp(-b |t|)` (`b > 5/4`), **without any measure or positivity
     assumption**.
   - For the von Mangoldt function `Λ`, we prove the unconditional elementary bound
     `|(Λ n : ℝ)| ≤ 1 * √n * (1 + log n)` for all `n ≥ 2`.

2. **Unconditional Kernel, Multiplier, and 1D Sech-Representation Theorems
   (`evenWeilDensity_specSq_mul_kernel_unconditional`,
   `evenWeilDensity_specSq_mul_multiplier_unconditional`,
   `evenWeilDensity_specSq_eq_integral_sechKernel_unconditional`,
   `cosineShiftFn_mul_eq_integral_cosShiftKernel_unconditional`)**:
   - For every `Φ` with `EvenStrip Φ` and every `Multiplier T`,
     `evenWeilDensity lam (specSq Φ * T) = ∫ t : ℝ, stripTest (rhoLift T) t * cosineShiftFn lam Φ t`.
   - Specializing to the reference strip function `sechHalf z = (cosh(z/2))⁻¹` and
     `sechKernel Ψ := stripTest (rhoLift (sechWeight Ψ))`, we obtain the **unconditional 1D
     sech-representation** for every `Ψ` such that `Multiplier (sechWeight Ψ)`:
     `evenWeilDensity lam (specSq Ψ) = ∫ t : ℝ, sechKernel Ψ t * cosineShiftFn lam sechHalf t`.
   - For every multiplier `h`, the shifted cosine function `cosineShiftFn lam (Φ * h) y` is the
     even convolution of `cosineShiftFn lam Φ` with `stripTest (specSq (rhoLift h))`:
     `cosineShiftFn lam (Φ * h) y = ∫ t : ℝ, cosShiftKernel (stripTest (specSq (rhoLift h))) y t * cosineShiftFn lam Φ t`.

3. **Standalone Zero-Side Identity for `xiShiftedGammaTest` and Unconditional Twisted-Arc
   Sech-Integral Annihilation (`archPoleEnergy_xiShiftedGammaTest_eq_abelPrimePairing`,
   `tsum_mul_integral_sechKernel_xiShiftedGamma_eq_zero`,
   `exists_twistedArc_weights_tsum_integral_sechKernel_vonMangoldt_eq_zero`)**:
   - Because `paperFT (xiShiftedGammaTest j)` vanishes at every nontrivial zero of `ζ` (on or off
     the critical line), its archimedean + pole energy equals its Abel prime pairing unconditionally.
   - Combining `tsum_mul_evenWeilDensity_xiShiftedGamma_eq_zero` with the unconditional 1D
     sech-representation proves that the twisted-arc combination of sech-kernels annihilates the
     1D sech-function `cosineShiftFn Λ sechHalf` unconditionally.
-/

open Complex MeasureTheory Set Filter Topology Zeta23
open scoped ComplexConjugate Nat

noncomputable section

namespace RHTower.CHMDStage3

open WeilOneSided WeilSpectral RHTower.EvenSector GaloisForLFunctions.HTGeometry

/-! ## Section 1: Unconditional Growth Bounds for `Λ` and `evenPrimePart` -/

/-- **Unconditional Growth Bound for `Λ`**:
For every `n ≥ 2`, `|(ArithmeticFunction.vonMangoldt n : ℝ)| ≤ 1 * Real.sqrt n * (1 + Real.log n)`. -/
theorem abs_vonMangoldt_le_sqrt_mul_one_add_log (n : ℕ) (hn : 2 ≤ n) :
    |(ArithmeticFunction.vonMangoldt n : ℝ)| ≤ 1 * Real.sqrt n * (1 + Real.log n) := by
  rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, one_mul]
  have hlog : ArithmeticFunction.vonMangoldt n ≤ Real.log (n : ℝ) :=
    ArithmeticFunction.vonMangoldt_le_log
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hsqrt : 1 ≤ Real.sqrt (n : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hn1
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  calc (ArithmeticFunction.vonMangoldt n : ℝ)
      ≤ Real.log (n : ℝ) := hlog
    _ ≤ 1 * (1 + Real.log (n : ℝ)) := by linarith
    _ ≤ Real.sqrt (n : ℝ) * (1 + Real.log (n : ℝ)) :=
        mul_le_mul_of_nonneg_right hsqrt (by positivity)

/-- **Unconditional Exponential Bound on `evenPrimePart` of a Cosine-Shifted Good Density**:
For every `K` with `GoodDensity K` and `StripDecay K (5 / 4) ε C`, the prime part of
`z ↦ cos(t * rhoC z) * K z` grows at most as `O(exp(5 / 4 * |t|))` for all `t ∈ ℝ`. -/
theorem abs_evenPrimePart_cos_mul_le {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) {K : ℂ → ℂ}
    (hK : GoodDensity K) {ε C : ℝ} (hε : 0 < ε) (hs : StripDecay K (5 / 4) ε C) (t : ℝ) :
    |evenPrimePart lam (fun z => Complex.cos (t * rhoC z) * K z)| ≤
      Cg * (2 * (C * (∫ r : ℝ, Real.exp (-(ε * |r|))) / (2 * Real.pi))) *
        (∑' n : ℕ, (1 + Real.log n) * (n : ℝ) ^ (-(5 / 4 : ℝ))) * Real.exp (5 / 4 * |t|) := by
  have hCg := growthConst_nonneg hg
  have hC := hs.const_nonneg (by norm_num)
  set D := 2 * (C * (∫ r : ℝ, Real.exp (-(ε * |r|))) / (2 * Real.pi))
  have hD0 : 0 ≤ D := by
    have : 0 ≤ ∫ r : ℝ, Real.exp (-(ε * |r|)) := integral_nonneg fun _ => (Real.exp_pos _).le
    positivity
  set u : ℕ → ℝ := fun n => (1 + Real.log n) * (n : ℝ) ^ (-(5 / 4 : ℝ))
  have husum : Summable u := summable_one_add_log_mul_rpow (b₁ := 5 / 4) (by norm_num)
  set term : ℕ → ℝ := fun n => (if 2 ≤ n then lam n / Real.sqrt n else 0) *
    (1 / Real.pi * ∫ r : ℝ, (Complex.cos (t * rhoC r) * K r).re * Real.cos (r * Real.log n))
  have hterm_le : ∀ n : ℕ, |term n| ≤ Cg * D * Real.exp (5 / 4 * |t|) * u n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [term, u]
    rw [abs_mul]
    calc |(if 2 ≤ n then lam n / Real.sqrt n else 0)| *
          |1 / Real.pi * ∫ r : ℝ, (Complex.cos (t * rhoC r) * K r).re * Real.cos (r * Real.log n)|
        ≤ (Cg * (1 + Real.log n)) * (D * ((n : ℝ) ^ (-(5 / 4 : ℝ)) * Real.exp (5 / 4 * |t|))) :=
          mul_le_mul (abs_weight_le hg n) (abs_primeTerm_cos_mul_le hK hε hs t hn)
            (abs_nonneg _) (by have := Real.log_natCast_nonneg n; positivity)
      _ = Cg * D * Real.exp (5 / 4 * |t|) * u n := by simp only [u]; ring
  have hterm_sum : Summable fun n => ‖term n‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => by rw [Real.norm_eq_abs]; exact hterm_le n)
      (husum.mul_left (Cg * D * Real.exp (5 / 4 * |t|)))
  change |∑' n : ℕ, term n| ≤ _
  calc |∑' n : ℕ, term n|
      = ‖∑' n : ℕ, term n‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' n : ℕ, ‖term n‖ := norm_tsum_le_tsum_norm hterm_sum
    _ ≤ ∑' n : ℕ, Cg * D * Real.exp (5 / 4 * |t|) * u n :=
        hterm_sum.tsum_le_tsum (fun n => by rw [Real.norm_eq_abs]; exact hterm_le n)
          (husum.mul_left _)
    _ = Cg * D * Real.exp (5 / 4 * |t|) * ∑' n : ℕ, u n := tsum_mul_left
    _ = Cg * D * (∑' n : ℕ, u n) * Real.exp (5 / 4 * |t|) := by ring

/-- Continuity of `t ↦ evenPrimePart lam (fun z => Complex.cos (t * rhoC z) * specSq Φ z)` for
any `EvenStrip Φ`. -/
theorem continuous_evenPrimePart_cosShift {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) {Φ : ℂ → ℂ}
    (hΦ : EvenStrip Φ) :
    Continuous fun t : ℝ =>
      evenPrimePart lam (fun z => Complex.cos (t * rhoC z) * specSq Φ z) := by
  have hK := goodDensity_specSq hΦ
  have hP : Continuous fun t : ℝ =>
      evenPolePart (fun z => Complex.cos (t * rhoC z) * specSq Φ z) := by
    have hPe : ∀ t : ℝ, evenPolePart (fun z => Complex.cos (t * rhoC z) * specSq Φ z) =
        Real.cos (t * Real.sqrt (7 / 4)) * (specSq Φ (I / 2) + specSq Φ (-I / 2)).re := fun t => by
      simp only [evenPolePart, rhoC_I_div_two, rhoC_neg_I_div_two]
      rw [← mul_add, ← Complex.ofReal_mul, ← Complex.ofReal_cos, Complex.re_ofReal_mul]
    simp_rw [hPe]
    fun_prop
  have hA : Continuous fun t : ℝ =>
      evenArchPart (fun z => Complex.cos (t * rhoC z) * specSq Φ z) := by
    obtain ⟨ε, C, hε, hs⟩ := hΦ.strip
    have hint : Integrable fun r : ℝ => ‖Φ r‖ ^ 2 * |EF.gammaBracket r| := by
      have := hK.integrable_mul continuous_abs_gammaBracket (M := |gammaLogConst| + 2)
        abs_abs_gammaBracket_le_linear
      simpa [specSq_re_ofReal] using this
    have hcΦ : Continuous fun r : ℝ => ‖Φ r‖ ^ 2 :=
      ((continuous_ofReal_comp_of_stripDecay hs (by norm_num)).norm).pow 2
    have hAe : ∀ t : ℝ, evenArchPart (fun z => Complex.cos (t * rhoC z) * specSq Φ z) =
        ∫ r : ℝ, Real.cos (t * Real.sqrt (r ^ 2 + 2)) * ‖Φ r‖ ^ 2 * EF.gammaBracket r := fun t => by
      unfold evenArchPart
      congr 1; funext r
      rw [re_cos_mul_ofReal, specSq_re_ofReal]
    simp_rw [hAe]
    refine continuous_of_dominated (bound := fun r => ‖Φ r‖ ^ 2 * |EF.gammaBracket r|)
      (fun t => ?_) (fun t => Filter.Eventually.of_forall fun r => ?_) hint
      (Filter.Eventually.of_forall fun r => ?_)
    · exact (((by fun_prop : Continuous fun r : ℝ => Real.cos (t * Real.sqrt (r ^ 2 + 2)))).mul
        hcΦ |>.mul WeilHerglotz.continuous_gammaBracket).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg ‖Φ r‖)]
      have hcos := Real.abs_cos_le_one (t * Real.sqrt (r ^ 2 + 2))
      calc |Real.cos (t * Real.sqrt (r ^ 2 + 2))| * ‖Φ r‖ ^ 2 * |EF.gammaBracket r|
          ≤ 1 * ‖Φ r‖ ^ 2 * |EF.gammaBracket r| := by gcongr
        _ = ‖Φ r‖ ^ 2 * |EF.gammaBracket r| := by ring
    · fun_prop
  have hφ := continuous_cosineShiftFn hg hΦ
  have hQeq : (fun t : ℝ => evenPrimePart lam (fun z => Complex.cos (t * rhoC z) * specSq Φ z)) =
      fun t : ℝ => evenPolePart (fun z => Complex.cos (t * rhoC z) * specSq Φ z) +
        1 / (2 * Real.pi) * evenArchPart (fun z => Complex.cos (t * rhoC z) * specSq Φ z) -
        cosineShiftFn lam Φ t := by
    funext t
    have hdef : cosineShiftFn lam Φ t =
        evenPolePart (fun z => Complex.cos (t * rhoC z) * specSq Φ z) +
          1 / (2 * Real.pi) * evenArchPart (fun z => Complex.cos (t * rhoC z) * specSq Φ z) -
          evenPrimePart lam (fun z => Complex.cos (t * rhoC z) * specSq Φ z) := rfl
    linarith
  rw [hQeq]
  exact (hP.add (continuous_const.mul hA)).sub hφ

/-- **Unconditional Integrability of `t ↦ κ t * evenPrimePart ...` without a Bochner Measure**:
For every `EvenStrip Φ` and continuous `κ` with `|κ t| ≤ Cκ * exp(-b |t|)` (`b > 5/4`),
`t ↦ κ t * evenPrimePart lam (fun z => Complex.cos (t * rhoC z) * specSq Φ z)` is integrable on `ℝ`. -/
theorem integrable_mul_evenPrimePart_cosShift {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) {Φ : ℂ → ℂ}
    (hΦ : EvenStrip Φ) {κ : ℝ → ℝ} (hκc : Continuous κ) {Cκ b : ℝ} (hb : 5 / 4 < b)
    (hκb : ∀ t, |κ t| ≤ Cκ * Real.exp (-(b * |t|))) :
    Integrable fun t : ℝ =>
      κ t * evenPrimePart lam (fun z => Complex.cos (t * rhoC z) * specSq Φ z) := by
  have hK := goodDensity_specSq hΦ
  obtain ⟨ε, C, hε, hs⟩ := hK.strip
  have hCκ := nonneg_of_abs_le_exp hκb
  set CQ := Cg * (2 * (C * (∫ r : ℝ, Real.exp (-(ε * |r|))) / (2 * Real.pi))) *
    (∑' n : ℕ, (1 + Real.log n) * (n : ℝ) ^ (-(5 / 4 : ℝ)))
  have hQc := continuous_evenPrimePart_cosShift hg hΦ
  have hQb : ∀ t : ℝ,
      |κ t * evenPrimePart lam (fun z => Complex.cos (t * rhoC z) * specSq Φ z)| ≤
        (Cκ * CQ) * Real.exp (-((b - 5 / 4) * |t|)) := fun t => by
    rw [abs_mul]
    calc |κ t| * |evenPrimePart lam (fun z => Complex.cos (t * rhoC z) * specSq Φ z)|
        ≤ (Cκ * Real.exp (-(b * |t|))) * (CQ * Real.exp (5 / 4 * |t|)) :=
          mul_le_mul (hκb t) (abs_evenPrimePart_cos_mul_le hg hK hε hs t) (abs_nonneg _)
            (mul_nonneg hCκ (Real.exp_pos _).le)
      _ = Cκ * CQ * (Real.exp (-(b * |t|)) * Real.exp (5 / 4 * |t|)) := by ring
      _ = (Cκ * CQ) * Real.exp (-((b - 5 / 4) * |t|)) := by rw [← Real.exp_add]; ring_nf
  exact integrable_of_exp_bound (hκc.mul hQc) (by linarith : 0 < b - 5 / 4) hQb

/-! ## Section 2: Unconditional Kernel, Multiplier, and 1D Sech-Representation Identities -/

/-- **Unconditional Kernel Identity (Measure-Free Form)**:
For every `lam` with `|lam n| ≤ Cg * √n * (1 + log n)`, every `Φ` with `EvenStrip Φ`, and every
continuous `κ` with `|κ t| ≤ Cκ * exp(-b |t|)` (`b > 5/4`),
`evenWeilDensity lam (fun z => specSq Φ z * ∫ t : ℝ, (κ t : ℂ) * Complex.cos (t * rhoC z)) =
  ∫ t : ℝ, κ t * cosineShiftFn lam Φ t`.
No Bochner measure `ν` or Weil positivity hypothesis is required. -/
theorem evenWeilDensity_specSq_mul_kernel_unconditional {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) {Φ : ℂ → ℂ}
    (hΦ : EvenStrip Φ) {κ : ℝ → ℝ} (hκc : Continuous κ) {Cκ b : ℝ} (hb : 5 / 4 < b)
    (hκb : ∀ t, |κ t| ≤ Cκ * Real.exp (-(b * |t|))) :
    evenWeilDensity lam (fun z => specSq Φ z * ∫ t : ℝ, (κ t : ℂ) * Complex.cos (t * rhoC z)) =
      ∫ t : ℝ, κ t * cosineShiftFn lam Φ t := by
  have hK := goodDensity_specSq hΦ
  have hκ : Integrable κ := integrable_of_exp_bound hκc (by linarith) hκb
  set P : ℝ → ℝ := fun t => evenPolePart (fun z => Complex.cos (t * rhoC z) * specSq Φ z) with hP
  set A : ℝ → ℝ := fun t => evenArchPart (fun z => Complex.cos (t * rhoC z) * specSq Φ z) with hA
  set Q : ℝ → ℝ := fun t => evenPrimePart lam (fun z => Complex.cos (t * rhoC z) * specSq Φ z)
    with hQ
  have hsplit : ∀ t, cosineShiftFn lam Φ t = P t + 1 / (2 * Real.pi) * A t - Q t :=
    fun _ => rfl
  have hPe : ∀ t, P t = Real.cos (t * Real.sqrt (7 / 4)) *
      (specSq Φ (I / 2) + specSq Φ (-I / 2)).re := fun t => by
    simp only [hP, evenPolePart, rhoC_I_div_two, rhoC_neg_I_div_two]
    rw [← mul_add, ← Complex.ofReal_mul, ← Complex.ofReal_cos, Complex.re_ofReal_mul]
  have hPi : Integrable fun t => κ t * P t := by
    simp_rw [hPe, ← mul_assoc]
    exact (integrable_mul_cos_of_integrable hκc hκ _ (by fun_prop)).mul_const _
  have hAi : Integrable fun t => κ t * A t := by
    have hint := integrable_prod_bound hK hκc hκ WeilHerglotz.continuous_gammaBracket
      (M := |gammaLogConst| + 2) (fun r => by
        have := abs_abs_gammaBracket_le_linear r; rwa [abs_abs] at this)
      (fun r t => Real.cos (t * Real.sqrt (r ^ 2 + 2))) (by fun_prop)
      (fun r t => Real.abs_cos_le_one _)
    refine hint.integral_prod_right.congr (Eventually.of_forall fun t => ?_)
    simp only [Function.uncurry_apply_pair, hA, evenArchPart]
    rw [← integral_const_mul]
    congr 1; funext r
    rw [re_cos_mul_ofReal]
  have hQi : Integrable fun t => κ t * Q t :=
    integrable_mul_evenPrimePart_cosShift hg hΦ hκc hb hκb
  rw [evenWeilDensity_eq_parts, evenPolePart_mul_integral,
    evenArchPart_mul_integral hK hκc hκ, evenPrimePart_mul_integral hg hK hκc hb hκb]
  simp_rw [hsplit]
  have e : ∀ t, κ t * (P t + 1 / (2 * Real.pi) * A t - Q t) =
      κ t * P t + 1 / (2 * Real.pi) * (κ t * A t) - κ t * Q t := fun _ => by ring
  simp_rw [e]
  have h1 : Integrable fun t => κ t * P t + 1 / (2 * Real.pi) * (κ t * A t) :=
    hPi.add (hAi.const_mul _)
  rw [integral_sub h1 hQi, integral_add hPi (hAi.const_mul _), integral_const_mul]

/-- **Unconditional Multiplier Identity (Measure-Free Form)**:
For every `lam` with `|lam n| ≤ Cg * √n * (1 + log n)`, every `Φ` with `EvenStrip Φ`, and every
multiplier `T`,
`evenWeilDensity lam (fun z => specSq Φ z * T z) =
  ∫ t : ℝ, stripTest (rhoLift T) t * cosineShiftFn lam Φ t`. -/
theorem evenWeilDensity_specSq_mul_multiplier_unconditional {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) {Φ : ℂ → ℂ}
    (hΦ : EvenStrip Φ) {T : ℂ → ℂ} (hT : Multiplier T) :
    evenWeilDensity lam (fun z => specSq Φ z * T z) =
      ∫ t : ℝ, stripTest (rhoLift T) t * cosineShiftFn lam Φ t := by
  obtain ⟨ε, C, hε, hs⟩ := stripDecay_rhoLift hT
  set κ := stripTest (rhoLift T)
  have hκc : Continuous κ := continuous_stripTest (by norm_num) hε hs
  have hκb : ∀ t, |κ t| ≤ C * (∫ r : ℝ, Real.exp (-(ε * |r|))) / (2 * Real.pi) *
      Real.exp (-(3 / 2 * |t|)) := abs_stripTest_le (by norm_num) hε hs
  have hκs : ∀ s : ℝ, ∫ t : ℝ, κ t * Real.cos (t * s) = (rhoLift T s).re := fun s =>
    integral_stripTest_mul_cos (by norm_num) hε hs (rhoLift_neg T) (rhoLift_im_ofReal hT) s
  rw [evenWeilDensity_congr (K₂ := fun z => specSq Φ z * ∫ t : ℝ, (κ t : ℂ) *
      Complex.cos (t * rhoC z))
    (by rw [multiplier_eq_kernel_integral hT hκs rhoC_I_div_two])
    (by rw [multiplier_eq_kernel_integral hT hκs rhoC_neg_I_div_two])
    (fun r => by rw [multiplier_eq_kernel_integral hT hκs (rhoC_ofReal r)]),
    evenWeilDensity_specSq_mul_kernel_unconditional hg hΦ hκc (by norm_num : (5 / 4 : ℝ) < 3 / 2)
      hκb]

/-- The 1D sech-kernel `κ_Ψ(t) = stripTest (rhoLift (sechWeight Ψ)) t` associated to a strip
function `Ψ`. -/
def sechKernel (Ψ : ℂ → ℂ) (t : ℝ) : ℝ :=
  stripTest (rhoLift (sechWeight Ψ)) t

/-- **Unconditional 1D Sech-Representation**:
For every `lam` with `|lam n| ≤ Cg * √n * (1 + log n)` and every `Ψ` such that
`Multiplier (sechWeight Ψ)`, the even Weil density of `specSq Ψ` is represented directly as a 1D
integral against the single reference function `cosineShiftFn lam sechHalf`:
`evenWeilDensity lam (specSq Ψ) = ∫ t : ℝ, sechKernel Ψ t * cosineShiftFn lam sechHalf t`.
No Bochner measure `ν` or Weil positivity hypothesis is needed. -/
theorem evenWeilDensity_specSq_eq_integral_sechKernel_unconditional {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) {Ψ : ℂ → ℂ}
    (hT : Multiplier (sechWeight Ψ)) :
    evenWeilDensity lam (specSq Ψ) =
      ∫ t : ℝ, sechKernel Ψ t * cosineShiftFn lam sechHalf t := by
  have e : ∀ z : ℂ, |z.im| ≤ 9 / 4 → specSq Ψ z = specSq sechHalf z * sechWeight Ψ z := by
    intro z hz
    unfold sechWeight
    rw [show specSq sechHalf z * (specSq Ψ z * Complex.cosh (z / 2) ^ 2) =
      specSq Ψ z * (specSq sechHalf z * Complex.cosh (z / 2) ^ 2) by ring,
      specSq_sechHalf_mul_cosh_sq hz, mul_one]
  rw [evenWeilDensity_congr (K₂ := fun z => specSq sechHalf z * sechWeight Ψ z)
    (e _ (by norm_num)) (e _ (by norm_num)) (fun r => e _ (by norm_num)),
    evenWeilDensity_specSq_mul_multiplier_unconditional hg evenStrip_sechHalf hT]
  rfl

/-- **Unconditional 1D Sech-Representation for `Λ`**:
For every `Ψ` such that `Multiplier (sechWeight Ψ)`,
`evenWeilDensity Λ (specSq Ψ) = ∫ t : ℝ, sechKernel Ψ t * cosineShiftFn Λ sechHalf t`
with **zero hypotheses**. -/
theorem evenWeilDensity_specSq_vonMangoldt_eq_integral_sechKernel {Ψ : ℂ → ℂ}
    (hT : Multiplier (sechWeight Ψ)) :
    evenWeilDensity (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) (specSq Ψ) =
      ∫ t : ℝ, sechKernel Ψ t *
        cosineShiftFn (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) sechHalf t :=
  evenWeilDensity_specSq_eq_integral_sechKernel_unconditional
    abs_vonMangoldt_le_sqrt_mul_one_add_log hT

/-- **Unconditional Shifted-Cosine Convolution Identity**:
For every `lam` with `|lam n| ≤ Cg * √n * (1 + log n)`, every `Φ` with `EvenStrip Φ`, and every
multiplier `h`, the cosine-shift function of `Φ * h` is the shifted-kernel integral of
`cosineShiftFn lam Φ` against `stripTest (specSq (rhoLift h))`. -/
theorem cosineShiftFn_mul_eq_integral_cosShiftKernel_unconditional {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) {Φ h : ℂ → ℂ}
    (hΦ : EvenStrip Φ) (hh : Multiplier h) (y : ℝ) :
    cosineShiftFn lam (fun z => Φ z * h z) y =
      ∫ t : ℝ, cosShiftKernel (stripTest (specSq (rhoLift h))) y t * cosineShiftFn lam Φ t := by
  obtain ⟨ε, C, hε, hs⟩ := stripDecay_specSq_rhoLift hh
  have hτe : ∀ z, specSq (rhoLift h) (-z) = specSq (rhoLift h) z :=
    specSq_neg_of_even (rhoLift_neg h)
  set κ := stripTest (specSq (rhoLift h))
  have hκc : Continuous κ := continuous_stripTest (by norm_num) hε hs
  set Cκ := C * (∫ r : ℝ, Real.exp (-(ε * |r|))) / (2 * Real.pi)
  have hκb : ∀ t, |κ t| ≤ Cκ * Real.exp (-(3 / 2 * |t|)) := abs_stripTest_le (by norm_num) hε hs
  have hκ : Integrable κ := integrable_of_exp_bound hκc (by norm_num) hκb
  have hκs : ∀ s : ℝ, ∫ t : ℝ, κ t * Real.cos (t * s) = ‖rhoLift h s‖ ^ 2 := fun s => by
    rw [integral_stripTest_mul_cos (by norm_num) hε hs hτe (fun r => specSq_im_ofReal r),
      specSq_rhoLift_re]
  change evenWeilDensity lam (rhoCosShift y (fun z => Φ z * h z)) = _
  rw [evenWeilDensity_congr (K₂ := fun z => specSq Φ z * ∫ t : ℝ, (cosShiftKernel κ y t : ℂ) *
      Complex.cos (t * rhoC z))
    (rhoCosShift_mul_eq_kernel hh hκc hκ hκs y rhoC_I_div_two (specSq_I_div_two_eq hh.even))
    (rhoCosShift_mul_eq_kernel hh hκc hκ hκs y rhoC_neg_I_div_two
      (specSq_neg_I_div_two_eq hh.even))
    (fun r => rhoCosShift_mul_eq_kernel hh hκc hκ hκs y (rhoC_ofReal r) (specSq_ofReal_eq h r)),
    evenWeilDensity_specSq_mul_kernel_unconditional hg hΦ (continuous_cosShiftKernel hκc y)
      (by norm_num : (5 / 4 : ℝ) < 3 / 2) (abs_cosShiftKernel_le (by norm_num) hκb y)]

/-! ## Section 3: Standalone Zero-Side Ground State and Unconditional Sech-Integral Annihilation -/

/-- **Unconditional Zero-Side Vanishing and Exact Prime Pairing of `xiShiftedGammaTest j`**:
Because `paperFT (xiShiftedGammaTest j)` vanishes at every nontrivial zero of `ζ` (on or off the
critical line), its zero-side sum `zetaZeroConfig.W` vanishes identically and its archimedean + pole
energy equals its Abel prime pairing `abelPrimePairing Λ (xiShiftedGammaTest j)` unconditionally. -/
theorem archPoleEnergy_xiShiftedGammaTest_eq_abelPrimePairing (j : ℕ) :
    archPoleEnergy (xiShiftedGammaTest j) =
      abelPrimePairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (xiShiftedGammaTest j) := by
  obtain ⟨C', _, hF⟩ := exists_decayBound_xiShiftedGammaTest
  rw [archPoleEnergy_eq_re_W_add_abelPrimePairing ((hF j).expDecayTest (by norm_num))]
  have hW : zetaZeroConfig.W (fun u => (xiShiftedGammaTest j u : ℂ))
      (fun u => (xiShiftedGammaTest j u : ℂ)) = 0 := by
    unfold Zeta23.ZeroConfig.W Zeta23.ZeroConfig.Wsummand
    simp [paperFT_xiShiftedGammaTest_gammaOf]
  rw [hW, Complex.zero_re, zero_add]

/-- For each `j : ℕ`, `evenWeilDensity lam (specSq (xiShiftedGamma j))` equals the 1D sech-integral
`∫ t : ℝ, sechKernel (xiShiftedGamma j) t * cosineShiftFn lam sechHalf t` unconditionally. -/
theorem evenWeilDensity_xiShiftedGamma_eq_integral_sechKernel {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) (j : ℕ) :
    evenWeilDensity lam (specSq (xiShiftedGamma j)) =
      ∫ t : ℝ, sechKernel (xiShiftedGamma j) t * cosineShiftFn lam sechHalf t :=
  evenWeilDensity_specSq_eq_integral_sechKernel_unconditional hg
    (multiplier_sechWeight_xiShiftedGamma j)

/-- **Unconditional Twisted-Arc Sech-Integral Annihilation Law**:
For any `lam` with `|lam n| ≤ Cg * √n * (1 + log n)` and any prime-blind twisted-arc weight
sequence `w : ℕ → ℝ`, the weighted sum of the 1D sech-kernel pairings against
`cosineShiftFn lam sechHalf` vanishes identically:
`∑' j, w j * ∫ t : ℝ, sechKernel (xiShiftedGamma j) t * cosineShiftFn lam sechHalf t = 0`. -/
theorem tsum_mul_integral_sechKernel_xiShiftedGamma_eq_zero {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) {w : ℕ → ℝ}
    (hw : ∀ j, 0 ≤ w j) (hsum : Summable fun j => w j * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) ^ 2)
    (hblind : ∀ n : ℕ, 2 ≤ n →
      ∑' j, w j * ∫ r : ℝ, ‖xiShiftedGamma j r‖ ^ 2 * Real.cos (r * Real.log n) = 0) :
    Summable (fun j => w j *
      ∫ t : ℝ, sechKernel (xiShiftedGamma j) t * cosineShiftFn lam sechHalf t) ∧
      ∑' j, w j *
        (∫ t : ℝ, sechKernel (xiShiftedGamma j) t * cosineShiftFn lam sechHalf t) = 0 := by
  have h := tsum_mul_evenWeilDensity_xiShiftedGamma_eq_zero hg hw hsum hblind
  simp_rw [evenWeilDensity_xiShiftedGamma_eq_integral_sechKernel hg] at h
  exact h

/-- **Unconditional Existence of Nonnegative Twisted-Arc Weights Annihilating `cosineShiftFn Λ sechHalf`**:
With **zero hypotheses**, there exists a sequence of nonnegative weights `w : ℕ → ℝ` with `w 0 > 0`
such that:
1. `∀ y : ℝ, |y| ≤ 3 / 2 → 0 < ∑' j, w j * shiftedGammaLaplaceFactor j y` (strict Laplace
   positivity across the entire critical strip `|y| ≤ 3 / 2`), and
2. `∑' j, w j * ∫ t : ℝ, sechKernel (xiShiftedGamma j) t * cosineShiftFn Λ sechHalf t = 0`
   (unconditional 1D sech-integral annihilation for the von Mangoldt function `Λ`). -/
theorem exists_twistedArc_weights_tsum_integral_sechKernel_vonMangoldt_eq_zero :
    ∃ w : ℕ → ℝ, (∀ j, 0 ≤ w j) ∧ 0 < w 0 ∧
      Summable (fun j => w j * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) ^ 2) ∧
      (∀ y : ℝ, |y| ≤ 3 / 2 → 0 < ∑' j, w j * shiftedGammaLaplaceFactor j y) ∧
      Summable (fun j => w j *
        ∫ t : ℝ, sechKernel (xiShiftedGamma j) t *
          cosineShiftFn (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) sechHalf t) ∧
      ∑' j, w j *
        (∫ t : ℝ, sechKernel (xiShiftedGamma j) t *
          cosineShiftFn (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) sechHalf t) = 0 := by
  obtain ⟨μ, hμ⟩ := exists_probabilityMeasure_twArc_annihilating twistedArcMinimumPrinciple_holds
  set ν₀ : Measure ArcParam := (μ : Measure ArcParam)
  have hmom : ∀ j, 0 ≤ twArcEvenMoment ν₀ (fun _ => 1) j := twArcEvenMoment_one_nonneg μ
  have hblind0 : ∀ n : ℕ, ∫ u, (fun _ : ArcParam => (1 : ℝ)) u * twArcMoment n u ∂ν₀ = 0 :=
    fun n => by simpa using hμ n
  set w : ℕ → ℝ := fun j => arcGammaWeight (twArcEvenMoment ν₀ (fun _ => 1) j) j with hw_def
  have hw : ∀ j, 0 ≤ w j := fun j => arcGammaWeight_nonneg (hmom j) j
  have hw0 : 0 < w 0 := by
    simp only [hw_def, arcGammaWeight]
    exact div_pos (mul_pos (by positivity) (twArcEvenMoment_one_zero_pos μ))
      (by exact_mod_cast Nat.factorial_pos _)
  have hsum : Summable fun j => w j * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) ^ 2 :=
    summable_arcGammaWeight hmom
      (twArcEvenMoment_le (ν := ν₀) (g := fun _ => 1) (B := 1) fun _ => by norm_num)
  have hblind := shiftedGamma_blind_of_twistedArc (B := 1) measurable_const
    (fun _ => by norm_num) hblind0 hmom
  have hpos : ∀ y : ℝ, |y| ≤ 3 / 2 → 0 < ∑' j, w j * shiftedGammaLaplaceFactor j y := by
    intro y hy
    have h1 := sqrt_two_mul_le_tsum_arcGammaWeight_mul_prod ν₀ hy
    have h2 := twArcEvenMoment_one_zero_pos μ
    exact lt_of_lt_of_le (by positivity) h1
  obtain ⟨hS, hZ⟩ := tsum_mul_integral_sechKernel_xiShiftedGamma_eq_zero
    abs_vonMangoldt_le_sqrt_mul_one_add_log hw hsum hblind
  exact ⟨w, hw, hw0, hsum, hpos, hS, hZ⟩

end RHTower.CHMDStage3

end
