import GaloisForLFunctions.RHTower.XiCenteredOrdersFifteenSixteenSourcePositivity
import GaloisForLFunctions.RHTower.XiEndpointSchwarzPairHeightGap
import GaloisForLFunctions.RHTower.RiemannKernelSpectralLocalization
import GaloisForLFunctions.RHTower.XiThermalSourceRelativeGapBound

/-!
# Modulated radical tests on the first zero-free window of `Ξ`

With `X(ξ) = Ξ(2πξ)` and `K = Φ⋆Φ̃` (`𝓕K = X²`), a full-cone Weil-positive `lam` pairs nonnegatively
with every radical test `K ⋆ (g ⋆ g̃)`. This module builds tests whose spectral weight `X²|𝓕g|²` is an
arbitrary window inside the zero-free interval around `0`.

**Zero-free window** (`phiFourierReal_ne_zero_of_abs_le`). `X(ξ) ≠ 0` for `|ξ| ≤ 1633/1000`, i.e.
`Ξ(t) ≠ 0` for `|t| ≤ 10.26`. Each critical zero `½ + iγ` and its conjugate put `2/γ⁴` into the fourth
reciprocal trace, which is below `9/50000`, so `γ⁴ > 100000/9`.

**Deviations of logarithmic size** (`normDeficit_pairing_nonneg_of_log_bound`,
`normDeficit_pairing_nonneg_of_decay_log`). The near-null pairing inequality holds for
`|v(n)| ≤ A(1 + |log n|)`, the size of the universal box, not only for bounded `v`.

**Modulated localized tests** (`modTest`, `riemannPairForm_modTest_add_neg`). With the profile
`φ((ξ − ξ₀)/η)(1 + σe^{2πiξa})/X(ξ)` the pairing at lag `y` is `2η` times
`(1 + σ²)cos(2πξ₀y)B(ηy) + σ(cos(2πξ₀(y+a))B(η(y+a)) + cos(2πξ₀(y−a))B(η(y−a)))`, where
`B = 𝓕(φ²)` (`modulated_localized_deviation_nonneg`).

**Superposition** (`superposed_deviation_nonneg`). Integrating the centre `ξ₀` over `(−L, L]` against
`cos²(πξ₀/(2L))` replaces `cos(2πξ₀ z)` by the window transform
`W(z) = ∫_{−L}^{L} cos²(πξ/(2L)) cos(2πξz) dξ = L sin(πu)/(πu(1 − u²))`, `u = 2Lz`
(`cosSqWindowTransform_eq`, `cosSqWindowTransform_zero`). The result: for `L + η ≤ 1633/1000`,
`Σ_n v(n)[(1 + σ²)B(η log n)W(log n) + σ(B(η(log n + a))W(log n + a) + B(η(log n − a))W(log n − a))] ≥ 0`.
Since `|B| ≤ B(0)`, the kernel seen by the deviation is the explicit window transform
`|W(z)| ≤ L/(π|u|(u² − 1))` (`abs_cosSqWindowTransform_le`), whose resolution is set by the width of
the zero-free window rather than by the width of `K`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate Convolution FourierTransform
open Zeta23

namespace RHTower

noncomputable section



/-- On-line zeros: `2/γ⁴ < 9/50000`. -/
theorem hundredThousand_div_nine_lt_im_pow_four_of_onLine (q : XiZeroCopy)
    (hre : (q.1 : ℂ).re = 1 / 2) :
    (100000 / 9 : ℝ) < (q.1 : ℂ).im ^ 4 := by
  have hsum : Summable
      (fun r : XiZeroCopy => (xiZeroCopyReciprocalSquare r ^ (2 : ℕ)).re) :=
    (summable_xiZeroCopyReciprocalSquare_pow 1).mapL Complex.reCLM
  have hle := two_mul_le_tsum_of_conj_invariant xiFourthReciprocalTraceAtom_nonneg hsum
    xiFourthReciprocalTraceAtom_conj q
  rw [tsum_xiFourthReciprocalTraceAtom_eq_source] at hle
  have hup := normalizedPrimeArchMoment_one_lt_nine_over_fiftyThousand
  have hγ : (q.1 : ℂ).im ≠ 0 := xi_divisor_support_im_ne_zero q.1
  set γ := (q.1 : ℂ).im with hγdef
  have hre' := xiZeroCopyReciprocalSquare_re_formula q
  have him' := xiZeroCopyReciprocalSquare_im_formula q
  rw [hre, sub_self] at hre' him'
  rw [← hγdef] at hre' him'
  have hγ2 : 0 < γ ^ 2 := by positivity
  have hRe : (xiZeroCopyReciprocalSquare q).re = 1 / γ ^ 2 := by
    rw [hre']; field_simp; ring
  have hIm : (xiZeroCopyReciprocalSquare q).im = 0 := by
    rw [him']; simp
  have hatom : (xiZeroCopyReciprocalSquare q ^ (2 : ℕ)).re = 1 / γ ^ 4 := by
    rw [pow_two, Complex.mul_re, hRe, hIm]; field_simp; ring
  rw [hatom] at hle
  have hγ4 : 0 < γ ^ 4 := by positivity
  have h2 : 2 / γ ^ 4 < 9 / 50000 := by
    have := lt_of_le_of_lt hle hup
    rwa [mul_one_div] at this
  rw [div_lt_div_iff₀ hγ4 (by norm_num)] at h2
  rw [div_lt_iff₀ (by norm_num : (0:ℝ) < 9)]
  linarith

/-- `X = Ξ(2π·)` has no zero on `|ξ| ≤ 1633/1000` (i.e. `|t| ≤ 10.26`). -/
theorem phiFourierReal_ne_zero_of_abs_le {ξ : ℝ} (hξ : |ξ| ≤ 1633 / 1000) :
    phiFourierReal ξ ≠ 0 := by
  intro h0
  have hXi : Xi (2 * π * ξ) = 0 := h0
  have hz : xi (1 / 2 + ((2 * π * ξ : ℝ) : ℂ) * I) = 0 := by
    have := XiC_ofReal (2 * π * ξ)
    rw [hXi, Complex.ofReal_zero] at this
    exact this
  set ρ : ℂ := 1 / 2 + ((2 * π * ξ : ℝ) : ℂ) * I with hρ
  let q : XiZeroCopy := by
    have hmem := mem_xi_divisor_support_of_eq_zero hz
    let r : XiDivisorSupport := ⟨ρ, hmem⟩
    have hpos := xi_divisor_pos_on_support r
    have hn : 0 < Int.toNat ((MeromorphicOn.divisor xi Set.univ) (r : ℂ)) := by omega
    exact ⟨r, ⟨0, hn⟩⟩
  have hq1 : (q.1 : ℂ) = ρ := rfl
  have hre : (q.1 : ℂ).re = 1 / 2 := by rw [hq1, hρ]; simp
  have him : (q.1 : ℂ).im = 2 * π * ξ := by rw [hq1, hρ]; simp
  have hbig := hundredThousand_div_nine_lt_im_pow_four_of_onLine q hre
  rw [him] at hbig
  have hpi := Real.pi_lt_d4
  have hpi0 := Real.pi_pos
  have habs : |2 * π * ξ| ≤ 2 * 3.1416 * (1633 / 1000) := by
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * π)]
    exact mul_le_mul (by linarith) hξ (abs_nonneg _) (by norm_num)
  have h4 : (2 * π * ξ) ^ 4 = |2 * π * ξ| ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
  rw [h4] at hbig
  have hmono : |2 * π * ξ| ^ 4 ≤ (2 * 3.1416 * (1633 / 1000)) ^ 4 :=
    pow_le_pow_left₀ (abs_nonneg _) habs 4
  have hnum : (2 * 3.1416 * (1633 / 1000) : ℝ) ^ 4 < 100000 / 9 := by norm_num
  linarith



theorem one_add_abs_log_le_three_mul_sqrt (n : ℕ) :
    1 + |Real.log n| ≤ 3 * Real.sqrt ((n : ℝ) + 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hl : 0 ≤ Real.log n := Real.log_nonneg hn1
    rw [abs_of_nonneg hl]
    have h := Real.log_le_rpow_div (x := (n : ℝ)) (by linarith) (by norm_num : (0 : ℝ) < 1 / 2)
    rw [← Real.sqrt_eq_rpow] at h
    have hs : Real.sqrt n ≤ Real.sqrt ((n : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
    have h1 : (1 : ℝ) ≤ Real.sqrt ((n : ℝ) + 1) := by
      rw [Real.one_le_sqrt]; linarith
    linarith

theorem summable_one_add_abs_log_mul_four_div_succ_sq :
    Summable fun n : ℕ => (1 + |Real.log n|) * (4 / ((n : ℝ) + 1) ^ 2) := by
  have h := (Real.summable_one_div_nat_rpow (p := 3 / 2)).mpr (by norm_num)
  have h2 := ((summable_nat_add_iff 1).mpr h).mul_left 12
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) h2
  have hb := one_add_abs_log_le_three_mul_sqrt n
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hsq : Real.sqrt ((n : ℝ) + 1) ^ 2 = (n : ℝ) + 1 := Real.sq_sqrt hpos.le
  have hrp : ((n + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ) = ((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1) := by
    push_cast
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hpos, Real.rpow_one,
      Real.sqrt_eq_rpow]
  simp only [one_div]
  rw [hrp]
  have hs0 : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr hpos
  rw [show (1 + |Real.log n|) * (4 / ((n : ℝ) + 1) ^ 2) =
      (1 + |Real.log n|) * 4 / ((n : ℝ) + 1) ^ 2 by ring,
    div_le_iff₀ (by positivity)]
  have : 12 * (((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1))⁻¹ * ((n : ℝ) + 1) ^ 2 =
      12 * Real.sqrt ((n : ℝ) + 1) := by
    field_simp
    nlinarith [hsq]
  rw [this]
  nlinarith

/-- **Near-null positivity for deviations of logarithmic size**, compactly supported tests. -/
theorem normDeficit_pairing_nonneg_of_log_bound {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {A : ℝ}
    (hA : ∀ n, |normDeficit lam n| ≤ A * (1 + |Real.log n|)) {g : ℝ → ℂ} (hg : Continuous g)
    (hgc : HasCompactSupport g) :
    0 ≤ (∑' n : ℕ, ((normDeficit lam n : ℝ) : ℂ) *
      (riemannPairForm riemannAutocorr g (Real.log n) + riemannPairForm riemannAutocorr g (-Real.log n))).re := by
  obtain ⟨Λ, -, hΛ⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  obtain ⟨R, hR0, hR⟩ := exists_radius_vanishing_complex hgc
  obtain ⟨C, hC0, hC⟩ := exists_truncatedRiemannAutocorr_le
  have hA0 : 0 ≤ A := by
    have h := (abs_nonneg _).trans (hA 0)
    simpa using h
  set B := C * Real.exp (4 * R) * (∫ u, ‖g u‖) ^ 2 with hB
  have hB0 : 0 ≤ B := by positivity
  have hκ : ∀ L z, |truncatedRiemannAutocorr L z| ≤ C * Real.exp (-(2 * |z|)) := fun L z => by
    rw [abs_of_nonneg (truncatedRiemannAutocorr_nonneg L z)]; exact hC L z
  have hbd : ∀ L (n : ℕ), ‖((normDeficit lam n : ℝ) : ℂ) *
      (riemannPairForm (truncatedRiemannAutocorr L) g (Real.log n) +
        riemannPairForm (truncatedRiemannAutocorr L) g (-Real.log n))‖ ≤
      A * (2 * B) * ((1 + |Real.log n|) * (4 / ((n : ℝ) + 1) ^ 2)) := by
    intro L n
    have h1 := norm_riemannPairForm_le hC0 (hκ L) hg hgc hR (Real.log n)
    have h2 := norm_riemannPairForm_le hC0 (hκ L) hg hgc hR (-Real.log n)
    rw [abs_neg] at h2
    have he := exp_neg_two_abs_log_le n
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hsum : ‖riemannPairForm (truncatedRiemannAutocorr L) g (Real.log n) +
        riemannPairForm (truncatedRiemannAutocorr L) g (-Real.log n)‖ ≤
        2 * B * (4 / ((n : ℝ) + 1) ^ 2) := by
      refine (norm_add_le _ _).trans ?_
      have : C * Real.exp (4 * R) * Real.exp (-(2 * |Real.log n|)) * (∫ u, ‖g u‖) ^ 2 =
          B * Real.exp (-(2 * |Real.log n|)) := by rw [hB]; ring
      rw [this] at h1 h2
      nlinarith [mul_le_mul_of_nonneg_left he hB0]
    have hl0 : 0 ≤ 1 + |Real.log n| := by positivity
    calc |normDeficit lam n| * ‖riemannPairForm (truncatedRiemannAutocorr L) g (Real.log n) +
          riemannPairForm (truncatedRiemannAutocorr L) g (-Real.log n)‖
        ≤ (A * (1 + |Real.log n|)) * (2 * B * (4 / ((n : ℝ) + 1) ^ 2)) :=
          mul_le_mul (hA n) hsum (norm_nonneg _) (by positivity)
      _ = A * (2 * B) * ((1 + |Real.log n|) * (4 / ((n : ℝ) + 1) ^ 2)) := by ring
  have hlim : Tendsto (fun L => ∑' n : ℕ, ((normDeficit lam n : ℝ) : ℂ) *
      (riemannPairForm (truncatedRiemannAutocorr L) g (Real.log n) +
        riemannPairForm (truncatedRiemannAutocorr L) g (-Real.log n))) atTop
      (𝓝 (∑' n : ℕ, ((normDeficit lam n : ℝ) : ℂ) *
        (riemannPairForm riemannAutocorr g (Real.log n) + riemannPairForm riemannAutocorr g (-Real.log n)))) :=
    tendsto_tsum_of_dominated_convergence (summable_one_add_abs_log_mul_four_div_succ_sq.mul_left _)
      (fun n => tendsto_const_nhds.mul ((tendsto_riemannPairForm_truncated hg hgc _).add
        (tendsto_riemannPairForm_truncated hg hgc _)))
      (Eventually.of_forall fun L n => hbd L n)
  have hre := (Complex.continuous_re.tendsto _).comp hlim
  set M2 := (∫ u, ‖g u‖ * Real.exp (1 / 2 * |u|)) ^ 2 with hM2
  have hM0 : 0 ≤ M2 := sq_nonneg _
  have key : ∀ ε > 0, -(M2 * ε) ≤ (∑' n : ℕ, ((normDeficit lam n : ℝ) : ℂ) *
      (riemannPairForm riemannAutocorr g (Real.log n) + riemannPairForm riemannAutocorr g (-Real.log n))).re := by
    intro ε hε
    obtain ⟨L₀, hL₀⟩ := exists_nearRadicalEnergy_le hε
    refine ge_of_tendsto hre ?_
    filter_upwards [eventually_ge_atTop L₀] with L hL
    have h1 := normDeficit_pairing_ge_of_truncation hW L hg hgc hΛ
    have h2 := mul_le_mul_of_nonneg_left (hL₀ L hL) hM0
    simp only [Function.comp]
    rw [← hM2] at h1
    linarith
  by_contra hneg
  push Not at hneg
  set x := (∑' n : ℕ, ((normDeficit lam n : ℝ) : ℂ) *
      (riemannPairForm riemannAutocorr g (Real.log n) + riemannPairForm riemannAutocorr g (-Real.log n))).re
  have hε : 0 < -x / (2 * (M2 + 1)) := div_pos (by linarith) (by positivity)
  have h := key _ hε
  have e : M2 * (-x / (2 * (M2 + 1))) = -x * (M2 / (2 * (M2 + 1))) := by ring
  have hq : M2 / (2 * (M2 + 1)) < 1 := by
    rw [div_lt_one (by positivity)]; linarith
  rw [e] at h
  nlinarith


/-- **Near-null positivity for rapidly decaying tests and deviations of logarithmic size.** -/
theorem normDeficit_pairing_nonneg_of_decay_log {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {A : ℝ}
    (hA : ∀ n, |normDeficit lam n| ≤ A * (1 + |Real.log n|)) {k : ℕ}
    (hZ : Summable fun n : ℕ => |normDeficit lam n| * ((1 + |Real.log n|) ^ k)⁻¹)
    {g : ℝ → ℂ} (hg : Continuous g) {D : ℝ} (hD : ∀ x, ‖g x‖ ≤ D * ((1 + |x|) ^ (k + 2))⁻¹) :
    0 ≤ (∑' n : ℕ, ((normDeficit lam n : ℝ) : ℂ) *
      (riemannPairForm riemannAutocorr g (Real.log n) + riemannPairForm riemannAutocorr g (-Real.log n))).re := by
  obtain ⟨B, hB0, hB⟩ := exists_riemannAutocorr_mul_pow_le k
  have hD0 : 0 ≤ D := by
    have := (norm_nonneg _).trans (hD 0); simp at this; exact this
  have hgi : Integrable fun x => ‖g x‖ := by
    refine (integrable_inv_one_add_abs_sq.const_mul D).mono' hg.norm.aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    refine (hD x).trans (mul_le_mul_of_nonneg_left ?_ hD0)
    have h1 : (1 : ℝ) ≤ 1 + |x| := by linarith [abs_nonneg x]
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ h1 (by omega))
  set c := D ^ 2 * B * (∫ x : ℝ, ((1 + |x|) ^ 2)⁻¹) ^ 2 with hc
  have hc0 : 0 ≤ c := by
    have : 0 ≤ ∫ x : ℝ, ((1 + |x|) ^ 2)⁻¹ := integral_nonneg fun _ => by positivity
    positivity
  have hDM : ∀ M x, ‖cutoffTest M g x‖ ≤ D * ((1 + |x|) ^ (k + 2))⁻¹ := fun M x =>
    (norm_cutoffTest_le M g x).trans (hD x)
  have hbd : ∀ M (n : ℕ), ‖((normDeficit lam n : ℝ) : ℂ) *
      (riemannPairForm riemannAutocorr (cutoffTest M g) (Real.log n) +
        riemannPairForm riemannAutocorr (cutoffTest M g) (-Real.log n))‖ ≤
      2 * c * (|normDeficit lam n| * ((1 + |Real.log n|) ^ k)⁻¹) := by
    intro M n
    have h1 := norm_riemannPairForm_le_of_decay hB (hDM M) (Real.log n)
    have h2 := norm_riemannPairForm_le_of_decay hB (hDM M) (-Real.log n)
    rw [abs_neg] at h2
    rw [← hc] at h1 h2
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h3 := norm_add_le (riemannPairForm riemannAutocorr (cutoffTest M g) (Real.log n))
      (riemannPairForm riemannAutocorr (cutoffTest M g) (-Real.log n))
    have ha := abs_nonneg (normDeficit lam n)
    calc |normDeficit lam n| * ‖riemannPairForm riemannAutocorr (cutoffTest M g) (Real.log n) +
          riemannPairForm riemannAutocorr (cutoffTest M g) (-Real.log n)‖
        ≤ |normDeficit lam n| * (2 * (c * ((1 + |Real.log n|) ^ k)⁻¹)) :=
          mul_le_mul_of_nonneg_left (by linarith) ha
      _ = _ := by ring
  have hlim := tendsto_tsum_of_dominated_convergence (hZ.mul_left (2 * c))
    (fun n => tendsto_const_nhds.mul ((tendsto_riemannPairForm_cutoff hg hgi _).add
      (tendsto_riemannPairForm_cutoff hg hgi _)))
    (Eventually.of_forall fun M n => hbd M n)
  refine ge_of_tendsto ((Complex.continuous_re.tendsto _).comp hlim)
    (Eventually.of_forall fun M => ?_)
  exact normDeficit_pairing_nonneg_of_log_bound hW hA (continuous_cutoffTest M hg)
    (hasCompactSupport_cutoffTest M g)

/-! ## Modulated localized tests -/

/-- The modulated profile `φ((ξ − ξ₀)/η) (1 + σ e^{2πiξa}) / X(ξ)`. -/
def modProfileC (η ξ₀ a σ : ℝ) (ξ : ℝ) : ℂ :=
  localProfileC η ξ₀ ξ * (1 + (σ : ℂ) * spectralChar ξ a)

theorem contDiff_spectralChar_left (a : ℝ) : ContDiff ℝ (⊤ : ℕ∞) fun ξ => spectralChar ξ a := by
  unfold spectralChar
  refine Complex.contDiff_exp.comp ?_
  refine ContDiff.mul ?_ contDiff_const
  exact Complex.ofRealCLM.contDiff.comp ((contDiff_const.mul contDiff_id).mul contDiff_const)

theorem contDiff_modProfileC {η ξ₀ : ℝ} (hη : 0 < η)
    (hfree : ∀ ξ, |ξ - ξ₀| < η → phiFourierReal ξ ≠ 0) (a σ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (modProfileC η ξ₀ a σ) :=
  (contDiff_localProfileC hη hfree).mul (contDiff_const.add
    (contDiff_const.mul (contDiff_spectralChar_left a)))

theorem hasCompactSupport_modProfileC {η : ℝ} (hη : 0 < η) (ξ₀ a σ : ℝ) :
    HasCompactSupport (modProfileC η ξ₀ a σ) :=
  (hasCompactSupport_localProfileC hη ξ₀).mul_right

/-- The modulated test `g = 𝓕⁻u` as a Schwartz function. -/
def modTest {η ξ₀ : ℝ} (hη : 0 < η) (hfree : ∀ ξ, |ξ - ξ₀| < η → phiFourierReal ξ ≠ 0)
    (a σ : ℝ) : SchwartzMap ℝ ℂ :=
  𝓕⁻ ((hasCompactSupport_modProfileC hη ξ₀ a σ).toSchwartzMap (contDiff_modProfileC hη hfree a σ))

theorem fourier_modTest {η ξ₀ : ℝ} (hη : 0 < η)
    (hfree : ∀ ξ, |ξ - ξ₀| < η → phiFourierReal ξ ≠ 0) (a σ : ℝ) :
    𝓕 (modTest hη hfree a σ : ℝ → ℂ) = modProfileC η ξ₀ a σ := by
  rw [← SchwartzMap.fourier_coe, modTest, FourierInvPair.fourier_fourierInv_eq]
  rfl

theorem exists_modTest_decay {η ξ₀ : ℝ} (hη : 0 < η)
    (hfree : ∀ ξ, |ξ - ξ₀| < η → phiFourierReal ξ ≠ 0) (a σ : ℝ) (m : ℕ) :
    ∃ D : ℝ, ∀ x, ‖modTest hη hfree a σ x‖ ≤ D * ((1 + |x|) ^ m)⁻¹ := by
  set f := modTest hη hfree a σ
  refine ⟨2 ^ m * ((Finset.Iic (m, 0)).sup fun p => SchwartzMap.seminorm ℝ p.1 p.2) f,
    fun x => ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (m, 0)) (k := m) (n := 0)
    le_rfl le_rfl f x
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
  rw [le_mul_inv_iff₀ (by positivity), mul_comm]
  exact h

theorem conj_spectralChar (ξ a : ℝ) : conj (spectralChar ξ a) = spectralChar ξ (-a) := by
  unfold spectralChar
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast; ring

theorem spectralChar_mul_neg (ξ a : ℝ) : spectralChar ξ a * spectralChar ξ (-a) = 1 := by
  rw [← spectralChar_add, add_neg_cancel]
  unfold spectralChar; simp

/-- `X² |u|² = φ((ξ − ξ₀)/η)² ((1 + σ²) + σ(e_a + e_{−a}))`. -/
theorem phiFourier_sq_mul_modProfileC {η ξ₀ : ℝ} (hη : 0 < η)
    (hfree : ∀ ξ, |ξ - ξ₀| < η → phiFourierReal ξ ≠ 0) (a σ ξ : ℝ) :
    phiFourier ξ ^ 2 * (modProfileC η ξ₀ a σ ξ * conj (modProfileC η ξ₀ a σ ξ)) =
      ((localBump ((ξ - ξ₀) / η) ^ 2 : ℝ) : ℂ) *
        ((1 + σ ^ 2 : ℝ) + (σ : ℂ) * (spectralChar ξ a + spectralChar ξ (-a))) := by
  have h := phiFourier_sq_mul_localProfileC hη hfree ξ
  unfold modProfileC
  rw [map_mul, map_add, map_one, map_mul, Complex.conj_ofReal, conj_spectralChar]
  have e : phiFourier ξ ^ 2 * (localProfileC η ξ₀ ξ * (1 + (σ : ℂ) * spectralChar ξ a) *
      (conj (localProfileC η ξ₀ ξ) * (1 + (σ : ℂ) * spectralChar ξ (-a)))) =
      (phiFourier ξ ^ 2 * (localProfileC η ξ₀ ξ * conj (localProfileC η ξ₀ ξ))) *
        ((1 + (σ : ℂ) * spectralChar ξ a) * (1 + (σ : ℂ) * spectralChar ξ (-a))) := by ring
  rw [e, h]
  congr 1
  have hm := spectralChar_mul_neg ξ a
  push_cast
  linear_combination (σ : ℂ) ^ 2 * hm

/-- The value of the modulated localized pairing at lag `y` (divided by `2η`). -/
def modValue (η ξ₀ a σ y : ℝ) : ℝ :=
  (1 + σ ^ 2) * (Real.cos (2 * π * ξ₀ * y) * bumpCos (η * y)) +
    σ * (Real.cos (2 * π * ξ₀ * (y + a)) * bumpCos (η * (y + a)) +
      Real.cos (2 * π * ξ₀ * (y - a)) * bumpCos (η * (y - a)))

theorem integrable_localBump_localize_sq_mul_spectralChar {η : ℝ} (hη : 0 < η) (ξ₀ y : ℝ) :
    Integrable fun ξ => ((localBump ((ξ - ξ₀) / η) ^ 2 : ℝ) : ℂ) * spectralChar ξ y := by
  have hbc : Continuous fun ξ => ((localBump ((ξ - ξ₀) / η) ^ 2 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp ((continuous_localBump.comp
      ((continuous_id.sub continuous_const).div_const η)).pow 2)
  have hbs : HasCompactSupport fun ξ => ((localBump ((ξ - ξ₀) / η) ^ 2 : ℝ) : ℂ) :=
    (hasCompactSupport_localBump_localize_sq hη ξ₀).comp_left Complex.ofReal_zero
  exact (hbc.mul (continuous_spectralChar.comp (continuous_id.prodMk continuous_const)))
    |>.integrable_of_hasCompactSupport hbs.mul_right

/-- The modulated pairing identity. -/
theorem riemannPairForm_modTest_add_neg {η ξ₀ : ℝ} (hη : 0 < η)
    (hfree : ∀ ξ, |ξ - ξ₀| < η → phiFourierReal ξ ≠ 0) (a σ y : ℝ) :
    riemannPairForm riemannAutocorr (modTest hη hfree a σ) y +
        riemannPairForm riemannAutocorr (modTest hη hfree a σ) (-y) =
      ((2 * η * modValue η ξ₀ a σ y : ℝ) : ℂ) := by
  set g := (modTest hη hfree a σ : ℝ → ℂ) with hgdef
  have hg : Continuous g := SchwartzMap.continuous _
  have hgi : Integrable g := SchwartzMap.integrable _
  set b : ℝ → ℂ := fun ξ => ((localBump ((ξ - ξ₀) / η) ^ 2 : ℝ) : ℂ) with hb
  have hI := integrable_localBump_localize_sq_mul_spectralChar hη ξ₀
  have hpf : ∀ z, riemannPairForm riemannAutocorr g z =
      ∫ ξ, b ξ * ((1 + σ ^ 2 : ℝ) + (σ : ℂ) * (spectralChar ξ a + spectralChar ξ (-a))) *
        spectralChar ξ z := by
    intro z
    rw [riemannPairForm_eq_integral_fourier hg hgi, hgdef, fourier_modTest]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only
    rw [phiFourier_sq_mul_modProfileC hη hfree]
  -- expand the integrand
  have hexp : ∀ ξ, b ξ * ((1 + σ ^ 2 : ℝ) + (σ : ℂ) * (spectralChar ξ a + spectralChar ξ (-a))) *
      spectralChar ξ y + b ξ * ((1 + σ ^ 2 : ℝ) + (σ : ℂ) * (spectralChar ξ a +
        spectralChar ξ (-a))) * spectralChar ξ (-y) =
      ((1 + σ ^ 2 : ℝ) : ℂ) * (b ξ * (spectralChar ξ y + spectralChar ξ (-y))) +
        (σ : ℂ) * (b ξ * (spectralChar ξ (y + a) + spectralChar ξ (-(y + a))) +
          b ξ * (spectralChar ξ (y - a) + spectralChar ξ (-(y - a)))) := by
    intro ξ
    have e1 : spectralChar ξ a * spectralChar ξ y = spectralChar ξ (y + a) := by
      rw [← spectralChar_add, add_comm]
    have e2 : spectralChar ξ a * spectralChar ξ (-y) = spectralChar ξ (-(y - a)) := by
      rw [← spectralChar_add]; congr 1; ring
    have e3 : spectralChar ξ (-a) * spectralChar ξ y = spectralChar ξ (y - a) := by
      rw [← spectralChar_add]; congr 1; ring
    have e4 : spectralChar ξ (-a) * spectralChar ξ (-y) = spectralChar ξ (-(y + a)) := by
      rw [← spectralChar_add]; congr 1; ring
    linear_combination (σ : ℂ) * b ξ * (e1 + e2 + e3 + e4)
  have hB := fun z => integral_localBump_spectralChar hη ξ₀ z
  have hIpair : ∀ z, Integrable fun ξ => b ξ * (spectralChar ξ z + spectralChar ξ (-z)) := by
    intro z
    have := (hI z).add (hI (-z))
    refine this.congr (Eventually.of_forall fun ξ => ?_)
    simp only [Pi.add_apply, hb]; ring
  rw [hpf, hpf]
  have hint1 : Integrable fun ξ => b ξ * ((1 + σ ^ 2 : ℝ) + (σ : ℂ) *
      (spectralChar ξ a + spectralChar ξ (-a))) * spectralChar ξ y := by
    have := (((hI y).const_mul ((1 + σ ^ 2 : ℝ) : ℂ)).add
      (((hI (y + a)).add (hI (y - a))).const_mul (σ : ℂ)))
    refine this.congr (Eventually.of_forall fun ξ => ?_)
    have e1 : spectralChar ξ a * spectralChar ξ y = spectralChar ξ (y + a) := by
      rw [← spectralChar_add, add_comm]
    have e3 : spectralChar ξ (-a) * spectralChar ξ y = spectralChar ξ (y - a) := by
      rw [← spectralChar_add]; congr 1; ring
    simp only [Pi.add_apply, hb]
    linear_combination (-(σ : ℂ)) * ((localBump ((ξ - ξ₀) / η) ^ 2 : ℝ) : ℂ) * (e1 + e3)
  have hint2 : Integrable fun ξ => b ξ * ((1 + σ ^ 2 : ℝ) + (σ : ℂ) *
      (spectralChar ξ a + spectralChar ξ (-a))) * spectralChar ξ (-y) := by
    have := (((hI (-y)).const_mul ((1 + σ ^ 2 : ℝ) : ℂ)).add
      (((hI (-(y - a))).add (hI (-(y + a)))).const_mul (σ : ℂ)))
    refine this.congr (Eventually.of_forall fun ξ => ?_)
    have e2 : spectralChar ξ a * spectralChar ξ (-y) = spectralChar ξ (-(y - a)) := by
      rw [← spectralChar_add]; congr 1; ring
    have e4 : spectralChar ξ (-a) * spectralChar ξ (-y) = spectralChar ξ (-(y + a)) := by
      rw [← spectralChar_add]; congr 1; ring
    simp only [Pi.add_apply, hb]
    linear_combination (-(σ : ℂ)) * ((localBump ((ξ - ξ₀) / η) ^ 2 : ℝ) : ℂ) * (e2 + e4)
  rw [← integral_add hint1 hint2]
  simp_rw [hexp]
  have hP : ∀ z, Integrable fun ξ => b ξ * (spectralChar ξ z + spectralChar ξ (-z)) := hIpair
  have hsplit : ∫ ξ, (((1 + σ ^ 2 : ℝ) : ℂ) * (b ξ * (spectralChar ξ y + spectralChar ξ (-y))) +
      (σ : ℂ) * (b ξ * (spectralChar ξ (y + a) + spectralChar ξ (-(y + a))) +
        b ξ * (spectralChar ξ (y - a) + spectralChar ξ (-(y - a))))) =
      ((1 + σ ^ 2 : ℝ) : ℂ) * (∫ ξ, b ξ * (spectralChar ξ y + spectralChar ξ (-y))) +
        (σ : ℂ) * ((∫ ξ, b ξ * (spectralChar ξ (y + a) + spectralChar ξ (-(y + a)))) +
          ∫ ξ, b ξ * (spectralChar ξ (y - a) + spectralChar ξ (-(y - a)))) := by
    have h1 : Integrable fun ξ => ((1 + σ ^ 2 : ℝ) : ℂ) *
        (b ξ * (spectralChar ξ y + spectralChar ξ (-y))) := (hP y).const_mul _
    have h2 : Integrable fun ξ => (σ : ℂ) * (b ξ * (spectralChar ξ (y + a) +
        spectralChar ξ (-(y + a))) + b ξ * (spectralChar ξ (y - a) + spectralChar ξ (-(y - a)))) :=
      ((hP (y + a)).add (hP (y - a))).const_mul _
    rw [integral_add h1 h2, integral_const_mul, integral_const_mul, integral_add (hP _) (hP _)]
  rw [hsplit]
  simp only [hb]
  rw [hB y, hB (y + a), hB (y - a)]
  unfold modValue
  push_cast
  ring

/-- **Positivity of the modulated localized pairing.** -/
theorem modulated_localized_deviation_nonneg {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {A : ℝ}
    (hA : ∀ n, |normDeficit lam n| ≤ A * (1 + |Real.log n|)) {k : ℕ}
    (hZ : Summable fun n : ℕ => |normDeficit lam n| * ((1 + |Real.log n|) ^ k)⁻¹)
    {η ξ₀ : ℝ} (hη : 0 < η) (hfree : ∀ ξ, |ξ - ξ₀| < η → phiFourierReal ξ ≠ 0) (a σ : ℝ) :
    0 ≤ ∑' n : ℕ, normDeficit lam n * modValue η ξ₀ a σ (Real.log n) := by
  obtain ⟨D, hD⟩ := exists_modTest_decay hη hfree a σ (k + 2)
  have hg : Continuous (modTest hη hfree a σ : ℝ → ℂ) := SchwartzMap.continuous _
  have h := normDeficit_pairing_nonneg_of_decay_log hW hA hZ hg hD
  simp_rw [riemannPairForm_modTest_add_neg hη hfree a σ] at h
  have e : (∑' n : ℕ, ((normDeficit lam n : ℝ) : ℂ) *
      ((2 * η * modValue η ξ₀ a σ (Real.log n) : ℝ) : ℂ)) =
      ((2 * η * ∑' n : ℕ, normDeficit lam n * modValue η ξ₀ a σ (Real.log n) : ℝ) : ℂ) := by
    rw [← tsum_mul_left, Complex.ofReal_tsum]
    refine tsum_congr fun n => ?_
    push_cast; ring
  rw [e, Complex.ofReal_re] at h
  have h2η : 0 < 2 * η := by linarith
  by_contra hneg
  push Not at hneg
  nlinarith

/-! ## Superposition over the window -/

/-- The window weight `cos²(πξ/(2L))`. -/
def cosSqWindow (L ξ : ℝ) : ℝ := Real.cos (π * ξ / (2 * L)) ^ 2

/-- Its cosine transform `W(z) = ∫_{−L}^{L} cos²(πξ/(2L)) cos(2πξz) dξ`. -/
def cosSqWindowTransform (L z : ℝ) : ℝ := ∫ ξ in (-L)..L, cosSqWindow L ξ * Real.cos (2 * π * ξ * z)

/-- The superposed value at `y`. -/
def modSuperValue (L η a σ y : ℝ) : ℝ :=
  (1 + σ ^ 2) * (bumpCos (η * y) * cosSqWindowTransform L y) +
    σ * (bumpCos (η * (y + a)) * cosSqWindowTransform L (y + a) +
      bumpCos (η * (y - a)) * cosSqWindowTransform L (y - a))

theorem continuous_cosSqWindow (L : ℝ) : Continuous (cosSqWindow L) := by
  unfold cosSqWindow; fun_prop

theorem cosSqWindow_nonneg (L ξ : ℝ) : 0 ≤ cosSqWindow L ξ := sq_nonneg _

theorem cosSqWindow_le_one (L ξ : ℝ) : cosSqWindow L ξ ≤ 1 := by
  unfold cosSqWindow
  have := Real.cos_sq_le_one (π * ξ / (2 * L))
  exact this

theorem continuous_modValue (η a σ y : ℝ) : Continuous fun ξ₀ => modValue η ξ₀ a σ y := by
  unfold modValue; fun_prop

theorem abs_modValue_le (η ξ₀ a σ y : ℝ) :
    |modValue η ξ₀ a σ y| ≤ (1 + σ ^ 2) * |bumpCos (η * y)| +
      |σ| * (|bumpCos (η * (y + a))| + |bumpCos (η * (y - a))|) := by
  unfold modValue
  have h1 := Real.abs_cos_le_one (2 * π * ξ₀ * y)
  have h2 := Real.abs_cos_le_one (2 * π * ξ₀ * (y + a))
  have h3 := Real.abs_cos_le_one (2 * π * ξ₀ * (y - a))
  have hs : 0 ≤ 1 + σ ^ 2 := by positivity
  calc |(1 + σ ^ 2) * (Real.cos (2 * π * ξ₀ * y) * bumpCos (η * y)) +
        σ * (Real.cos (2 * π * ξ₀ * (y + a)) * bumpCos (η * (y + a)) +
          Real.cos (2 * π * ξ₀ * (y - a)) * bumpCos (η * (y - a)))|
      ≤ |(1 + σ ^ 2) * (Real.cos (2 * π * ξ₀ * y) * bumpCos (η * y))| +
        |σ * (Real.cos (2 * π * ξ₀ * (y + a)) * bumpCos (η * (y + a)) +
          Real.cos (2 * π * ξ₀ * (y - a)) * bumpCos (η * (y - a)))| := abs_add_le _ _
    _ ≤ (1 + σ ^ 2) * |bumpCos (η * y)| +
        |σ| * (|bumpCos (η * (y + a))| + |bumpCos (η * (y - a))|) := by
      gcongr
      · rw [abs_mul, abs_of_nonneg hs, abs_mul]
        exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (abs_nonneg _) h1) hs
      · rw [abs_mul]
        refine mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans ?_) (abs_nonneg _)
        rw [abs_mul, abs_mul]
        exact add_le_add (mul_le_of_le_one_left (abs_nonneg _) h2)
          (mul_le_of_le_one_left (abs_nonneg _) h3)

/-- Peetre-type transfer of polynomial decay under dilation and shift. -/
theorem one_add_abs_le_mul_one_add_abs_dilate {η : ℝ} (hη : 0 < η) (a t : ℝ) :
    1 + |t| ≤ ((1 + |a|) * max 1 η⁻¹) * (1 + |η * (t + a)|) := by
  have hm1 : (1 : ℝ) ≤ max 1 η⁻¹ := le_max_left _ _
  have hm2 : η⁻¹ ≤ max 1 η⁻¹ := le_max_right _ _
  have hta : |t| ≤ |t + a| + |a| := by
    have := abs_sub_abs_le_abs_sub t (-a)
    rw [abs_neg, sub_neg_eq_add] at this; linarith
  have hηabs : |η * (t + a)| = η * |t + a| := by rw [abs_mul, abs_of_pos hη]
  rw [hηabs]
  have hk : |t + a| ≤ max 1 η⁻¹ * (η * |t + a|) := by
    calc |t + a| = η⁻¹ * (η * |t + a|) := by field_simp
      _ ≤ max 1 η⁻¹ * (η * |t + a|) := by gcongr
  have h0 : 0 ≤ η * |t + a| := by positivity
  nlinarith [abs_nonneg a, abs_nonneg (t + a)]

theorem abs_bumpCos_dilate_le {η : ℝ} (hη : 0 < η) (J : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a t, |bumpCos (η * (t + a))| ≤
      K * ((1 + |a|) * max 1 η⁻¹) ^ J * ((1 + |t|) ^ J)⁻¹ := by
  obtain ⟨K, hK0, hK⟩ := exists_abs_bumpCos_le J
  refine ⟨K, hK0, fun a t => ?_⟩
  refine (hK _).trans ?_
  have hp := one_add_abs_le_mul_one_add_abs_dilate hη a t
  have hpos : 0 < 1 + |η * (t + a)| := by positivity
  have hpos2 : 0 < 1 + |t| := by positivity
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hK0
  have hq : (1 + |t|) ^ J ≤ ((1 + |a|) * max 1 η⁻¹) ^ J * (1 + |η * (t + a)|) ^ J := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hp J
  rw [inv_eq_one_div, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

theorem integral_cosSqWindow_mul_modValue {L : ℝ} (hL : 0 < L) (η a σ y : ℝ) :
    ∫ ξ₀ in Ioc (-L) L, cosSqWindow L ξ₀ * modValue η ξ₀ a σ y =
      (1 + σ ^ 2) * (bumpCos (η * y) * cosSqWindowTransform L y) +
        σ * (bumpCos (η * (y + a)) * cosSqWindowTransform L (y + a) +
          bumpCos (η * (y - a)) * cosSqWindowTransform L (y - a)) := by
  have hLle : -L ≤ L := by linarith
  have hT : ∀ z, cosSqWindowTransform L z =
      ∫ ξ₀ in Ioc (-L) L, cosSqWindow L ξ₀ * Real.cos (2 * π * ξ₀ * z) := fun z => by
    unfold cosSqWindowTransform; rw [intervalIntegral.integral_of_le hLle]
  have hi : ∀ z, IntegrableOn (fun ξ₀ => cosSqWindow L ξ₀ * Real.cos (2 * π * ξ₀ * z))
      (Ioc (-L) L) := fun z =>
    ((continuous_cosSqWindow L).mul (by fun_prop)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have e : ∀ ξ₀, cosSqWindow L ξ₀ * modValue η ξ₀ a σ y =
      ((1 + σ ^ 2) * bumpCos (η * y)) * (cosSqWindow L ξ₀ * Real.cos (2 * π * ξ₀ * y)) +
        ((σ * bumpCos (η * (y + a))) * (cosSqWindow L ξ₀ * Real.cos (2 * π * ξ₀ * (y + a))) +
          (σ * bumpCos (η * (y - a))) * (cosSqWindow L ξ₀ * Real.cos (2 * π * ξ₀ * (y - a)))) := by
    intro ξ₀; unfold modValue; ring
  simp_rw [e]
  set c₁ := (1 + σ ^ 2) * bumpCos (η * y)
  set c₂ := σ * bumpCos (η * (y + a))
  set c₃ := σ * bumpCos (η * (y - a))
  have h1 : Integrable (fun ξ₀ => c₁ * (cosSqWindow L ξ₀ * Real.cos (2 * π * ξ₀ * y)))
      (volume.restrict (Ioc (-L) L)) := (hi y).const_mul c₁
  have h2 : Integrable (fun ξ₀ => c₂ * (cosSqWindow L ξ₀ * Real.cos (2 * π * ξ₀ * (y + a))) +
      c₃ * (cosSqWindow L ξ₀ * Real.cos (2 * π * ξ₀ * (y - a))))
      (volume.restrict (Ioc (-L) L)) := ((hi (y + a)).const_mul c₂).add ((hi (y - a)).const_mul c₃)
  have h3 : Integrable (fun ξ₀ => c₂ * (cosSqWindow L ξ₀ * Real.cos (2 * π * ξ₀ * (y + a))))
      (volume.restrict (Ioc (-L) L)) := (hi (y + a)).const_mul c₂
  have h4 : Integrable (fun ξ₀ => c₃ * (cosSqWindow L ξ₀ * Real.cos (2 * π * ξ₀ * (y - a))))
      (volume.restrict (Ioc (-L) L)) := (hi (y - a)).const_mul c₃
  rw [integral_add h1 h2, integral_add h3 h4, integral_const_mul, integral_const_mul,
    integral_const_mul, ← hT, ← hT, ← hT]
  ring

/-- **Positivity against the window transform.** -/
theorem superposed_deviation_nonneg {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {A : ℝ}
    (hA : ∀ n, |normDeficit lam n| ≤ A * (1 + |Real.log n|)) {k : ℕ}
    (hZ : Summable fun n : ℕ => |normDeficit lam n| * ((1 + |Real.log n|) ^ k)⁻¹)
    {L η : ℝ} (hL : 0 < L) (hη : 0 < η) (hwin : L + η ≤ 1633 / 1000) (a σ : ℝ) :
    0 ≤ ∑' n : ℕ, normDeficit lam n * modSuperValue L η a σ (Real.log n) := by
  set μ := volume.restrict (Ioc (-L) L) with hμ
  set F : ℕ → ℝ → ℝ := fun n ξ₀ => cosSqWindow L ξ₀ *
    (normDeficit lam n * modValue η ξ₀ a σ (Real.log n)) with hF
  have hcont : ∀ n, Continuous (F n) := fun n =>
    (continuous_cosSqWindow L).mul (continuous_const.mul (continuous_modValue η a σ _))
  have hInt : ∀ n, Integrable (F n) μ := fun n =>
    (hcont n).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  -- decay of the bump factors
  obtain ⟨K, hK0, hK⟩ := abs_bumpCos_dilate_le hη k
  set Cp : ℝ → ℝ := fun b => K * ((1 + |b|) * max 1 η⁻¹) ^ k with hCp
  have hCp0 : ∀ b, 0 ≤ Cp b := fun b => by simp only [hCp]; positivity
  set Mc : ℝ := (1 + σ ^ 2) * Cp 0 + |σ| * (Cp a + Cp (-a)) with hMc
  have hMc0 : 0 ≤ Mc := by rw [hMc]; have := hCp0 0; have := hCp0 a; have := hCp0 (-a); positivity
  have hmod : ∀ ξ₀ (n : ℕ), |modValue η ξ₀ a σ (Real.log n)| ≤ Mc * ((1 + |Real.log n|) ^ k)⁻¹ := by
    intro ξ₀ n
    refine (abs_modValue_le η ξ₀ a σ _).trans ?_
    have h0 := hK 0 (Real.log n)
    have h1 := hK a (Real.log n)
    have h2 := hK (-a) (Real.log n)
    rw [add_zero] at h0
    rw [← sub_eq_add_neg] at h2
    have hs : 0 ≤ 1 + σ ^ 2 := by positivity
    rw [hMc]
    simp only [hCp] at h0 h1 h2 ⊢
    have hσ := abs_nonneg σ
    nlinarith [mul_le_mul_of_nonneg_left h0 hs, mul_le_mul_of_nonneg_left (add_le_add h1 h2) hσ]
  have hμfin : μ.real univ = 2 * L := by
    rw [hμ, measureReal_restrict_apply_univ, Real.volume_real_Ioc_of_le (by linarith)]; ring
  have hbound : ∀ n, ∫ ξ₀, ‖F n ξ₀‖ ∂μ ≤ 2 * L * Mc * (|normDeficit lam n| * ((1 + |Real.log n|) ^ k)⁻¹) := by
    intro n
    have hc : Integrable (fun _ : ℝ => Mc * (|normDeficit lam n| * ((1 + |Real.log n|) ^ k)⁻¹)) μ :=
      integrable_const _
    refine (integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hc
      (Eventually.of_forall fun ξ₀ => ?_)).trans ?_
    · simp only [hF, Real.norm_eq_abs, abs_mul]
      have hw : |cosSqWindow L ξ₀| ≤ 1 := by
        rw [abs_of_nonneg (cosSqWindow_nonneg L ξ₀)]; exact cosSqWindow_le_one L ξ₀
      have hm := hmod ξ₀ n
      have hw0 : 0 ≤ |cosSqWindow L ξ₀| := abs_nonneg _
      calc |cosSqWindow L ξ₀| * (|normDeficit lam n| * |modValue η ξ₀ a σ (Real.log n)|)
          ≤ 1 * (|normDeficit lam n| * (Mc * ((1 + |Real.log n|) ^ k)⁻¹)) :=
            mul_le_mul hw (mul_le_mul_of_nonneg_left hm (abs_nonneg _)) (by positivity) zero_le_one
        _ = Mc * (|normDeficit lam n| * ((1 + |Real.log n|) ^ k)⁻¹) := by ring
    · rw [integral_const, smul_eq_mul, hμfin]; ring_nf; exact le_refl _
  have hSum : Summable fun n => ∫ ξ₀, ‖F n ξ₀‖ ∂μ :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _) hbound
      (hZ.mul_left (2 * L * Mc))
  have hswap := integral_tsum_of_summable_integral_norm hInt hSum
  have hpt : ∀ n, ∫ ξ₀, F n ξ₀ ∂μ = normDeficit lam n * modSuperValue L η a σ (Real.log n) := by
    intro n
    have e : (fun ξ₀ => F n ξ₀) = fun ξ₀ => normDeficit lam n *
        (cosSqWindow L ξ₀ * modValue η ξ₀ a σ (Real.log n)) := by
      funext ξ₀; simp only [hF]; ring
    rw [e, integral_const_mul, hμ, integral_cosSqWindow_mul_modValue hL]
    rfl
  simp_rw [hpt] at hswap
  rw [hswap]
  refine setIntegral_nonneg measurableSet_Ioc fun ξ₀ hξ₀ => ?_
  have hfree : ∀ ξ, |ξ - ξ₀| < η → phiFourierReal ξ ≠ 0 := by
    intro ξ hξ
    refine phiFourierReal_ne_zero_of_abs_le ?_
    have h1 : |ξ₀| ≤ L := by
      rw [abs_le]; exact ⟨by linarith [hξ₀.1], hξ₀.2⟩
    have h2 : |ξ| ≤ |ξ - ξ₀| + |ξ₀| := by
      have := abs_add_le (ξ - ξ₀) ξ₀; rwa [sub_add_cancel] at this
    linarith
  have hP := modulated_localized_deviation_nonneg hW hA hZ hη hfree a σ
  have e2 : (∑' n, F n ξ₀) = cosSqWindow L ξ₀ *
      ∑' n : ℕ, normDeficit lam n * modValue η ξ₀ a σ (Real.log n) := by
    rw [← tsum_mul_left]
  rw [e2]
  exact mul_nonneg (cosSqWindow_nonneg L ξ₀) hP

/-! ## The window transform in closed form -/

theorem hasDerivAt_sin_pi_mul_div (k L x : ℝ) :
    HasDerivAt (fun ξ => Real.sin (π * k * ξ / L)) (Real.cos (π * k * x / L) * (π * k / L)) x := by
  have h := ((hasDerivAt_id x).const_mul (π * k)).div_const L
  simpa using h.sin

theorem cosSqWindow_mul_cos_eq (L u ξ : ℝ) (hL : L ≠ 0) :
    cosSqWindow L ξ * Real.cos (2 * π * ξ * (u / (2 * L))) =
      1 / 2 * Real.cos (π * u * ξ / L) + 1 / 4 * Real.cos (π * (u + 1) * ξ / L) +
        1 / 4 * Real.cos (π * (u - 1) * ξ / L) := by
  unfold cosSqWindow
  have e1 : 2 * π * ξ * (u / (2 * L)) = π * u * ξ / L := by field_simp
  have e2 : π * (u + 1) * ξ / L = π * u * ξ / L + 2 * (π * ξ / (2 * L)) := by field_simp
  have e3 : π * (u - 1) * ξ / L = π * u * ξ / L - 2 * (π * ξ / (2 * L)) := by field_simp
  rw [e1, e2, e3, Real.cos_add, Real.cos_sub, Real.cos_sq (π * ξ / (2 * L))]
  ring

theorem cosSqWindowTransform_eq {L u : ℝ} (hL : 0 < L) (hu0 : u ≠ 0) (hu1 : u + 1 ≠ 0)
    (hu2 : u - 1 ≠ 0) :
    cosSqWindowTransform L (u / (2 * L)) = L * Real.sin (π * u) / (π * u * (1 - u ^ 2)) := by
  have hLne : L ≠ 0 := hL.ne'
  have hπ : π ≠ 0 := Real.pi_ne_zero
  unfold cosSqWindowTransform
  simp_rw [cosSqWindow_mul_cos_eq L u _ hLne]
  set F : ℝ → ℝ := fun ξ => L / (2 * π * u) * Real.sin (π * u * ξ / L) +
    L / (4 * π * (u + 1)) * Real.sin (π * (u + 1) * ξ / L) +
      L / (4 * π * (u - 1)) * Real.sin (π * (u - 1) * ξ / L) with hF
  have hderiv : ∀ x ∈ uIcc (-L) L, HasDerivAt F (1 / 2 * Real.cos (π * u * x / L) +
      1 / 4 * Real.cos (π * (u + 1) * x / L) + 1 / 4 * Real.cos (π * (u - 1) * x / L)) x := by
    intro x _
    have := (((hasDerivAt_sin_pi_mul_div u L x).const_mul (L / (2 * π * u))).add
      ((hasDerivAt_sin_pi_mul_div (u + 1) L x).const_mul (L / (4 * π * (u + 1))))).add
      ((hasDerivAt_sin_pi_mul_div (u - 1) L x).const_mul (L / (4 * π * (u - 1))))
    refine this.congr_deriv ?_
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (by
    apply Continuous.intervalIntegrable; fun_prop)]
  simp only [hF]
  have e1 : π * u * L / L = π * u := by field_simp
  have e2 : π * u * -L / L = -(π * u) := by field_simp
  have e3 : π * (u + 1) * L / L = π * u + π := by field_simp
  have e4 : π * (u + 1) * -L / L = -(π * u + π) := by field_simp
  have e5 : π * (u - 1) * L / L = π * u - π := by field_simp
  have e6 : π * (u - 1) * -L / L = -(π * u - π) := by field_simp
  rw [e1, e2, e3, e4, e5, e6, Real.sin_neg, Real.sin_neg, Real.sin_neg, Real.sin_add_pi,
    Real.sin_sub_pi]
  have hu3 : 1 - u ^ 2 ≠ 0 := by
    have : 1 - u ^ 2 = -((u + 1) * (u - 1)) := by ring
    rw [this]; exact neg_ne_zero.mpr (mul_ne_zero hu1 hu2)
  field_simp
  ring

theorem cosSqWindowTransform_zero {L : ℝ} (hL : 0 < L) : cosSqWindowTransform L 0 = L := by
  have hLne : L ≠ 0 := hL.ne'
  have hπ : π ≠ 0 := Real.pi_ne_zero
  unfold cosSqWindowTransform cosSqWindow
  simp only [mul_zero, Real.cos_zero, mul_one]
  have e : ∀ ξ, Real.cos (π * ξ / (2 * L)) ^ 2 = 1 / 2 + 1 / 2 * Real.cos (π * 1 * ξ / L) := by
    intro ξ
    rw [Real.cos_sq]; congr 2; field_simp
  simp_rw [e]
  have hderiv : ∀ x ∈ uIcc (-L) L, HasDerivAt (fun ξ => 1 / 2 * ξ + L / (2 * π) *
      Real.sin (π * 1 * ξ / L)) (1 / 2 + 1 / 2 * Real.cos (π * 1 * x / L)) x := by
    intro x _
    have := ((hasDerivAt_id x).const_mul (1 / 2)).add
      ((hasDerivAt_sin_pi_mul_div 1 L x).const_mul (L / (2 * π)))
    refine this.congr_deriv ?_
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (by
    apply Continuous.intervalIntegrable; fun_prop)]
  have e1 : π * 1 * L / L = π := by field_simp
  have e2 : π * 1 * -L / L = -π := by field_simp
  simp only [e1, e2, Real.sin_pi, Real.sin_neg]
  ring

/-- `|W(z)| ≤ L/(π|u|(u² − 1))` for `u = 2Lz`, `|u| > 1`. -/
theorem abs_cosSqWindowTransform_le {L z : ℝ} (hL : 0 < L) (hu : 1 < |2 * L * z|) :
    |cosSqWindowTransform L z| ≤ L / (π * |2 * L * z| * ((2 * L * z) ^ 2 - 1)) := by
  set u := 2 * L * z with hu_def
  have hz : z = u / (2 * L) := by rw [hu_def]; field_simp
  have hu0 : u ≠ 0 := by intro h; rw [h, abs_zero] at hu; linarith
  have hsq : 1 < u ^ 2 := by
    have := sq_abs u; nlinarith [abs_nonneg u]
  have hu1 : u + 1 ≠ 0 := by
    intro h
    have h' : u = -1 := by linarith
    rw [h'] at hsq; norm_num at hsq
  have hu2 : u - 1 ≠ 0 := by
    intro h
    have h' : u = 1 := by linarith
    rw [h'] at hsq; norm_num at hsq
  rw [hz, cosSqWindowTransform_eq hL hu0 hu1 hu2]
  have hπ := Real.pi_pos
  have hden : 0 < π * |u| * (u ^ 2 - 1) := by
    have h1 := abs_pos.mpr hu0
    have h2 : 0 < u ^ 2 - 1 := by linarith
    positivity
  rw [abs_div, abs_mul, abs_of_pos hL, abs_mul, abs_mul, abs_of_pos hπ,
    show |1 - u ^ 2| = u ^ 2 - 1 by rw [abs_of_neg (by linarith)]; ring]
  rw [div_le_div_iff₀ (by positivity) hden]
  have hs := Real.abs_sin_le_one (π * u)
  have hk : 0 ≤ L * (π * |u| * (u ^ 2 - 1)) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hs hk]

end

end RHTower
