import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEisensteinLineEigenEquation
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEisensteinLineInvariance

/-!
# Vertical bounds for the Eisenstein tail

The Whittaker tail of the completed Eisenstein series is bounded uniformly along vertical lines of
the parameter. The source of the uniformity is `|cosh(νt)| ≤ cosh(Re ν · t)`, which gives
`‖K_s(ν)‖ ≤ ‖K_s(Re ν)‖` in the Schläfli integral. The arithmetic coefficient obeys
`‖c_n(u)‖ ≤ n^{3|Re u|+1}`, which also ignores `Im u`.

Hence for `|Re u| ≤ R` and `Y` in a window, the tail and its jets `∂_x`, `∂_x²`, `∂_Y` are bounded by a
constant, and the eigen-equation bounds `∂_Y²` by a constant times `1 + ‖u‖²`.

Each tail, as a function of the parameter along a vertical line, is measurable. These facts are what
is needed to differentiate under the spectral integral of a wave packet.
-/

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open _root_.RHTower HTGeometry

/-! ### The Bessel function along a vertical line -/

theorem norm_cosh_ofReal_mul_le (ν : ℂ) (t : ℝ) :
    ‖Complex.cosh (ν * (t : ℂ))‖ ≤ Real.cosh (ν.re * t) := by
  have hre : (ν * (t : ℂ)).re = ν.re * t := by simp
  rw [Complex.cosh, Real.cosh_eq, norm_div]
  simp only [Complex.norm_ofNat]
  refine div_le_div_of_nonneg_right ?_ (by norm_num)
  refine (norm_add_le _ _).trans ?_
  rw [Complex.norm_exp, Complex.norm_exp, Complex.neg_re, hre]

theorem besselOrderKernel_ofReal (s η t : ℝ) :
    besselOrderKernel s (η : ℂ) t =
      ((Real.exp (-s * Real.cosh t) * Real.cosh (η * t) : ℝ) : ℂ) := by
  rw [besselOrderKernel]
  push_cast
  rfl

theorem norm_besselOrderKernel_le_re (s : ℝ) (ν : ℂ) (t : ℝ) :
    ‖besselOrderKernel s ν t‖ ≤ Real.exp (-s * Real.cosh t) * Real.cosh (ν.re * t) := by
  rw [besselOrderKernel, norm_mul, Complex.norm_exp]
  have hre : (-(s : ℂ) * Complex.cosh (t : ℂ)).re = -s * Real.cosh t := by
    rw [← Complex.ofReal_cosh]
    simp
  rw [hre]
  exact mul_le_mul_of_nonneg_left (norm_cosh_ofReal_mul_le ν t) (Real.exp_pos _).le

/-- **The Bessel function along a vertical line** is dominated by its value at the real part. -/
theorem norm_modifiedBesselKOrder_le_re {s : ℝ} (hs : 0 < s) (ν : ℂ) :
    ‖modifiedBesselKOrder s ν‖ ≤ ‖modifiedBesselKOrder s (ν.re : ℂ)‖ := by
  set kernel : ℝ → ℝ := fun t => Real.exp (-s * Real.cosh t) * Real.cosh (ν.re * t) with hkernel
  have hreal : IntegrableOn kernel (Ioi 0) := by
    have h := (integrableOn_besselOrderKernel hs (ν.re : ℂ)).re
    refine h.congr (Eventually.of_forall fun t => ?_)
    simp only [RCLike.re_to_complex]
    rw [besselOrderKernel_ofReal, Complex.ofReal_re]
  have hval : modifiedBesselKOrder s (ν.re : ℂ) = ((∫ t in Ioi (0 : ℝ), kernel t : ℝ) : ℂ) := by
    have hco : (∫ t in Ioi (0 : ℝ), ((kernel t : ℝ) : ℂ)) = ((∫ t in Ioi (0 : ℝ), kernel t : ℝ) : ℂ) :=
      integral_ofReal
    rw [← hco, modifiedBesselKOrder]
    exact setIntegral_congr_fun measurableSet_Ioi fun t _ => besselOrderKernel_ofReal s ν.re t
  have hnn : 0 ≤ ∫ t in Ioi (0 : ℝ), kernel t :=
    setIntegral_nonneg measurableSet_Ioi fun t _ => by
      rw [hkernel]
      exact mul_nonneg (Real.exp_pos _).le (Real.cosh_pos _).le
  rw [hval, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn, modifiedBesselKOrder]
  refine (norm_integral_le_integral_norm _).trans ?_
  exact setIntegral_mono_on (integrableOn_besselOrderKernel hs ν).norm hreal measurableSet_Ioi
    fun t _ => norm_besselOrderKernel_le_re s ν t

theorem scale_mul_window_pos {Y₀ Y : ℝ} (hY₀ : 0 < Y₀) (hY : Y ∈ Icc (Y₀ / 2) (2 * Y₀)) (N : ℕ) :
    0 < (d4BMPositiveFourierScale N : ℝ) * Y :=
  mul_pos (d4BMPositiveFourierScale N).2 (window_pos hY₀ hY)

/-- **The window bound depends only on the real part of the order.** -/
theorem norm_besselOrder_window_re_le {Y₀ Y : ℝ} (hY₀ : 0 < Y₀) (hY : Y ∈ Icc (Y₀ / 2) (2 * Y₀))
    {R : ℝ} {ν : ℂ} (hν : |ν.re| ≤ R) (N : ℕ) :
    ‖modifiedBesselKOrder ((d4BMPositiveFourierScale N : ℝ) * Y) ν‖ ≤
      besselModeMajorant Y₀ R N := by
  refine (norm_modifiedBesselKOrder_le_re (scale_mul_window_pos hY₀ hY N) ν).trans ?_
  refine norm_modifiedBesselKOrder_window_le hY₀ hY ?_ N
  rwa [Complex.norm_real, Real.norm_eq_abs]

/-! ### The Whittaker functions -/

section Modes

variable {Y₀ Y R : ℝ}

theorem norm_mode_le (hY₀ : 0 < Y₀) (hY : Y ∈ Icc (Y₀ / 2) (2 * Y₀)) {ν : ℂ} (hν : |ν.re| ≤ R)
    (negative : Bool) (N : ℕ) (x : ℝ) :
    ‖d4BMSignedWhittakerMode negative N ν x Y‖ ≤
      Real.sqrt (2 * Y₀) * besselModeMajorant Y₀ R N := by
  rw [d4BMSignedWhittakerMode, norm_mul, norm_fourierPhase, one_mul, d4BMWhittakerP0, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul (window_sqrt_le hY) (norm_besselOrder_window_re_le hY₀ hY hν N) (norm_nonneg _)
    (Real.sqrt_nonneg _)

theorem norm_firstJet_le (hY₀ : 0 < Y₀) (hY : Y ∈ Icc (Y₀ / 2) (2 * Y₀)) {ν : ℂ}
    (hν : |ν.re| ≤ R) (N : ℕ) :
    ‖d4BMWhittakerP0FirstJet (d4BMPositiveFourierScale N) ν Y‖ ≤
      (1 / (2 * Real.sqrt (Y₀ / 2)) + Real.sqrt (2 * Y₀) * (2 * Real.pi)) * ((N : ℝ) + 1) *
        besselModeMajorant Y₀ (R + 1) N := by
  have hB := besselModeMajorant_nonneg Y₀ (R + 1) N
  have hYpos := window_pos hY₀ hY
  have hK0 := norm_besselOrder_window_re_le hY₀ hY (R := R + 1) (ν := ν) (by linarith) N
  have hK1 := norm_besselOrder_window_re_le hY₀ hY (R := R + 1) (ν := ν + 1) (by
    have : (ν + 1).re = ν.re + 1 := by simp
    rw [this]
    have := abs_add_le ν.re 1
    rw [abs_one] at this
    linarith) N
  have hK2 := norm_besselOrder_window_re_le hY₀ hY (R := R + 1) (ν := ν - 1) (by
    have : (ν - 1).re = ν.re - 1 := by simp
    rw [this]
    have := abs_sub ν.re 1
    rw [abs_one] at this
    linarith) N
  have hc : ‖((d4BMPositiveFourierScale N : ℝ) : ℂ)‖ = 2 * Real.pi * ((N : ℝ) + 1) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (d4BMPositiveFourierScale N).2.le]
    rfl
  have hN1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hinv : ‖((1 / (2 * Real.sqrt Y) : ℝ) : ℂ)‖ ≤ 1 / (2 * Real.sqrt (Y₀ / 2)) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact window_inv_sqrt_le hY₀ hY
  have hsq : ‖(Real.sqrt Y : ℂ)‖ ≤ Real.sqrt (2 * Y₀) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact window_sqrt_le hY
  rw [d4BMWhittakerP0FirstJet]
  refine (norm_add_le _ _).trans ?_
  have hA : ‖((1 / (2 * Real.sqrt Y) : ℝ) : ℂ) *
        modifiedBesselKOrder ((d4BMPositiveFourierScale N : ℝ) * Y) ν‖ ≤
      1 / (2 * Real.sqrt (Y₀ / 2)) * ((N : ℝ) + 1) * besselModeMajorant Y₀ (R + 1) N := by
    rw [norm_mul]
    calc _ ≤ 1 / (2 * Real.sqrt (Y₀ / 2)) * besselModeMajorant Y₀ (R + 1) N :=
          mul_le_mul hinv hK0 (norm_nonneg _) (by positivity)
      _ ≤ _ := by
          have : 0 ≤ 1 / (2 * Real.sqrt (Y₀ / 2)) * besselModeMajorant Y₀ (R + 1) N := by positivity
          nlinarith
  have hB' : ‖(Real.sqrt Y : ℂ) * ((d4BMPositiveFourierScale N : ℝ) : ℂ) * (-(1 / 2 : ℂ)) *
        (modifiedBesselKOrder ((d4BMPositiveFourierScale N : ℝ) * Y) (ν + 1) +
          modifiedBesselKOrder ((d4BMPositiveFourierScale N : ℝ) * Y) (ν - 1))‖ ≤
      Real.sqrt (2 * Y₀) * (2 * Real.pi) * ((N : ℝ) + 1) * besselModeMajorant Y₀ (R + 1) N := by
    rw [norm_mul, norm_mul, norm_mul, hc, norm_neg]
    have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
    rw [hhalf]
    have hsum : ‖modifiedBesselKOrder ((d4BMPositiveFourierScale N : ℝ) * Y) (ν + 1) +
        modifiedBesselKOrder ((d4BMPositiveFourierScale N : ℝ) * Y) (ν - 1)‖ ≤
        2 * besselModeMajorant Y₀ (R + 1) N := by
      refine (norm_add_le _ _).trans ?_
      linarith
    have hpre : ‖(Real.sqrt Y : ℂ)‖ * (2 * Real.pi * ((N : ℝ) + 1)) * (1 / 2) ≤
        Real.sqrt (2 * Y₀) * (2 * Real.pi * ((N : ℝ) + 1)) * (1 / 2) := by
      gcongr
    calc _ ≤ Real.sqrt (2 * Y₀) * (2 * Real.pi * ((N : ℝ) + 1)) * (1 / 2) *
          (2 * besselModeMajorant Y₀ (R + 1) N) :=
          mul_le_mul hpre hsum (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hgoal := add_le_add hA hB'
  refine hgoal.trans (le_of_eq ?_)
  ring

end Modes

/-! ### Summing the modes -/

/-- The arithmetic coefficient is bounded along vertical lines. -/
theorem norm_modeCoefficient_le {R : ℝ} {u : ℂ} (hu : |u.re| ≤ R) (N : ℕ) :
    ‖modeCoefficient u N‖ ≤ ((N : ℝ) + 1) ^ (⌈3 * R + 1⌉₊) := by
  refine (d4BM_norm_completedEisensteinWhittakerCoefficient_le u ⟨N + 1, by omega⟩).trans ?_
  have hN1 : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
  calc ((N + 1 : ℕ) : ℝ) ^ (3 * |u.re| + 1) ≤ ((N + 1 : ℕ) : ℝ) ^ (⌈3 * R + 1⌉₊ : ℝ) := by
        refine Real.rpow_le_rpow_of_exponent_le hN1 ?_
        have := Nat.le_ceil (3 * R + 1)
        linarith
    _ = ((N : ℝ) + 1) ^ (⌈3 * R + 1⌉₊) := by
        rw [Real.rpow_natCast]
        push_cast
        rfl

/-- A family of modes dominated by `K (N+1)^d B_N` sums to a uniformly bounded tail. -/
theorem exists_norm_tsum_modeCoefficient_le {Y₀ R : ℝ} (hY₀ : 0 < Y₀) {d : ℕ} {K : ℝ} (hK : 0 ≤ K)
    {f : ℕ → ℂ → ℝ → ℝ → ℂ}
    (hf : ∀ (N : ℕ) (u : ℂ) (x Y : ℝ), |u.re| ≤ R → Y ∈ Icc (Y₀ / 2) (2 * Y₀) →
      ‖f N u x Y‖ ≤ K * ((N : ℝ) + 1) ^ d * besselModeMajorant Y₀ (R + 1) N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ℂ) (x Y : ℝ), |u.re| ≤ R → Y ∈ Icc (Y₀ / 2) (2 * Y₀) →
      ‖∑' N : ℕ, modeCoefficient u N * f N u x Y‖ ≤ C := by
  have hsum := summable_pow_mul_besselModeMajorant hY₀ (R + 1) (d + ⌈3 * R + 1⌉₊)
  refine ⟨K * ∑' N : ℕ, ((N : ℝ) + 1) ^ (d + ⌈3 * R + 1⌉₊) * besselModeMajorant Y₀ (R + 1) N,
    mul_nonneg hK (tsum_nonneg fun N => mul_nonneg (by positivity)
      (besselModeMajorant_nonneg _ _ _)), fun u x Y hu hY => ?_⟩
  refine tsum_of_norm_bounded (hsum.hasSum.mul_left K) fun N => ?_
  rw [norm_mul]
  have h1 := norm_modeCoefficient_le hu N
  have h2 := hf N u x Y hu hY
  have hB := besselModeMajorant_nonneg Y₀ (R + 1) N
  calc ‖modeCoefficient u N‖ * ‖f N u x Y‖
      ≤ ((N : ℝ) + 1) ^ (⌈3 * R + 1⌉₊) *
          (K * ((N : ℝ) + 1) ^ d * besselModeMajorant Y₀ (R + 1) N) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = K * (((N : ℝ) + 1) ^ (d + ⌈3 * R + 1⌉₊) * besselModeMajorant Y₀ (R + 1) N) := by
        rw [pow_add]
        ring

/-- **Vertical bounds for the tail and its jets.**  For `|Re u| ≤ R`, on a height window, uniformly in
`x` and in `Im u`. -/
theorem exists_weightedTail_jets_le {Y₀ R : ℝ} (hY₀ : 0 < Y₀) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ℂ) (negative : Bool) (x Y : ℝ), |u.re| ≤ R →
      Y ∈ Icc (Y₀ / 2) (2 * Y₀) →
      ‖weightedTail u negative x Y‖ ≤ C ∧ ‖weightedTailX u negative x Y‖ ≤ C ∧
        ‖weightedTailXX u negative x Y‖ ≤ C ∧ ‖weightedTailY u negative x Y‖ ≤ C := by
  have hmono : ∀ N : ℕ, besselModeMajorant Y₀ R N ≤ besselModeMajorant Y₀ (R + 1) N := by
    intro N
    unfold besselModeMajorant
    have hexp : Real.exp (R ^ 2 / (2 * Real.pi * Y₀)) ≤
        Real.exp ((R + 1) ^ 2 / (2 * Real.pi * Y₀)) := by
      refine Real.exp_le_exp.mpr ?_
      gcongr
      linarith
    gcongr
  have hmode : ∀ (negative : Bool) (N : ℕ) (u : ℂ) (x Y : ℝ), |u.re| ≤ R →
      Y ∈ Icc (Y₀ / 2) (2 * Y₀) →
      ‖d4BMSignedWhittakerMode negative N u x Y‖ ≤
        Real.sqrt (2 * Y₀) * besselModeMajorant Y₀ (R + 1) N := by
    intro negative N u x Y hu hY
    refine (norm_mode_le hY₀ hY hu negative N x).trans ?_
    exact mul_le_mul_of_nonneg_left (hmono N) (Real.sqrt_nonneg _)
  have hgen : ∀ (d : ℕ) (K : ℝ), 0 ≤ K → ∀ (f : Bool → ℕ → ℂ → ℝ → ℝ → ℂ),
      (∀ negative N u x Y, |u.re| ≤ R → Y ∈ Icc (Y₀ / 2) (2 * Y₀) →
        ‖f negative N u x Y‖ ≤ K * ((N : ℝ) + 1) ^ d * besselModeMajorant Y₀ (R + 1) N) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ℂ) (negative : Bool) (x Y : ℝ), |u.re| ≤ R →
        Y ∈ Icc (Y₀ / 2) (2 * Y₀) → ‖∑' N : ℕ, modeCoefficient u N * f negative N u x Y‖ ≤ C := by
    intro d K hK f hf
    obtain ⟨C₁, hC₁, h₁⟩ := exists_norm_tsum_modeCoefficient_le hY₀ hK (f := f false)
      (fun N u x Y hu hY => hf false N u x Y hu hY)
    obtain ⟨C₂, hC₂, h₂⟩ := exists_norm_tsum_modeCoefficient_le hY₀ hK (f := f true)
      (fun N u x Y hu hY => hf true N u x Y hu hY)
    refine ⟨max C₁ C₂, le_max_of_le_left hC₁, fun u negative x Y hu hY => ?_⟩
    cases negative
    · exact (h₁ u x Y hu hY).trans (le_max_left _ _)
    · exact (h₂ u x Y hu hY).trans (le_max_right _ _)
  obtain ⟨C₀, hC₀, h₀⟩ := hgen 0 (Real.sqrt (2 * Y₀)) (Real.sqrt_nonneg _)
    (fun negative N u x Y => d4BMSignedWhittakerMode negative N u x Y)
    (fun negative N u x Y hu hY => by
      simpa using hmode negative N u x Y hu hY)
  obtain ⟨C₁, hC₁, h₁⟩ := hgen 1 (2 * Real.pi * Real.sqrt (2 * Y₀)) (by positivity)
    (fun negative N u x Y => d4BMSignedWhittakerModeHorizontalFirstJet negative N u x Y)
    (fun negative N u x Y hu hY => by
      rw [d4BMSignedWhittakerModeHorizontalFirstJet, norm_mul, norm_signedFourierRate]
      have hm := hmode negative N u x Y hu hY
      calc 2 * Real.pi * ((N : ℝ) + 1) * ‖d4BMSignedWhittakerMode negative N u x Y‖
          ≤ 2 * Real.pi * ((N : ℝ) + 1) * (Real.sqrt (2 * Y₀) * besselModeMajorant Y₀ (R + 1) N) :=
            mul_le_mul_of_nonneg_left hm (by positivity)
        _ = _ := by ring)
  obtain ⟨C₂, hC₂, h₂⟩ := hgen 2 ((2 * Real.pi) ^ 2 * Real.sqrt (2 * Y₀)) (by positivity)
    (fun negative N u x Y => d4BMSignedWhittakerModeHorizontalSecondJet negative N u x Y)
    (fun negative N u x Y hu hY => by
      rw [d4BMSignedWhittakerModeHorizontalSecondJet, norm_mul, norm_pow, norm_signedFourierRate]
      have hm := hmode negative N u x Y hu hY
      calc (2 * Real.pi * ((N : ℝ) + 1)) ^ 2 * ‖d4BMSignedWhittakerMode negative N u x Y‖
          ≤ (2 * Real.pi * ((N : ℝ) + 1)) ^ 2 *
              (Real.sqrt (2 * Y₀) * besselModeMajorant Y₀ (R + 1) N) :=
            mul_le_mul_of_nonneg_left hm (by positivity)
        _ = _ := by ring)
  obtain ⟨C₃, hC₃, h₃⟩ := hgen 1 (1 / (2 * Real.sqrt (Y₀ / 2)) + Real.sqrt (2 * Y₀) * (2 * Real.pi))
    (by positivity)
    (fun negative N u x Y => d4BMSignedWhittakerModeVerticalFirstJet negative N u x Y)
    (fun negative N u x Y hu hY => by
      rw [d4BMSignedWhittakerModeVerticalFirstJet, norm_mul, norm_fourierPhase, one_mul]
      simpa using norm_firstJet_le hY₀ hY hu N)
  refine ⟨C₀ + C₁ + C₂ + C₃, by positivity, fun u negative x Y hu hY => ⟨?_, ?_, ?_, ?_⟩⟩
  · have := h₀ u negative x Y hu hY
    rw [weightedTail]
    linarith
  · have := h₁ u negative x Y hu hY
    rw [weightedTailX]
    linarith
  · have := h₂ u negative x Y hu hY
    rw [weightedTailXX]
    linarith
  · have := h₃ u negative x Y hu hY
    rw [weightedTailY]
    linarith

/-- The eigen-equation expresses `∂_Y²` of the tail through the other jets. -/
theorem weightedTailYY_eq (u : ℂ) (negative : Bool) (x : ℝ) {Y : ℝ} (hY : 0 < Y) :
    weightedTailYY u negative x Y =
      (u ^ 2 - 1 / 4) * weightedTail u negative x Y / (Y : ℂ) ^ 2 -
        weightedTailXX u negative x Y := by
  have h := weightedTail_eigen u negative x hY
  have hYC : (Y : ℂ) ≠ 0 := by exact_mod_cast hY.ne'
  have h' : weightedTailXX u negative x Y + weightedTailYY u negative x Y =
      (u ^ 2 - 1 / 4) * weightedTail u negative x Y / (Y : ℂ) ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 hYC)]
    linear_combination h
  linear_combination h'

/-! ### Measurability along a vertical line -/

theorem continuous_modeCoefficient (N : ℕ) : Continuous fun u : ℂ => modeCoefficient u N :=
  continuous_iff_continuousAt.mpr fun u =>
    (differentiableAt_whittakerCoefficient ⟨N + 1, by omega⟩ u).continuousAt

section Measurability

variable {Y : ℝ}

theorem continuous_bessel_order (hY : 0 < Y) (N : ℕ) :
    Continuous fun ν : ℂ => modifiedBesselKOrder ((d4BMPositiveFourierScale N : ℝ) * Y) ν :=
  (differentiable_modifiedBesselKOrder (mul_pos (d4BMPositiveFourierScale N).2 hY)).continuous

theorem continuous_mode_order (hY : 0 < Y) (negative : Bool) (N : ℕ) (x : ℝ) :
    Continuous fun ν : ℂ => d4BMSignedWhittakerMode negative N ν x Y := by
  unfold d4BMSignedWhittakerMode d4BMWhittakerP0
  exact continuous_const.mul (continuous_const.mul (continuous_bessel_order hY N))

theorem continuous_firstJet_order (hY : 0 < Y) (negative : Bool) (N : ℕ) (x : ℝ) :
    Continuous fun ν : ℂ => d4BMSignedWhittakerModeVerticalFirstJet negative N ν x Y := by
  unfold d4BMSignedWhittakerModeVerticalFirstJet d4BMWhittakerP0FirstJet
  have h0 := continuous_bessel_order hY N
  have h1 := h0.comp (continuous_id.add continuous_const : Continuous fun ν : ℂ => ν + 1)
  have h2 := h0.comp (continuous_id.sub continuous_const : Continuous fun ν : ℂ => ν - 1)
  exact continuous_const.mul ((continuous_const.mul h0).add (continuous_const.mul (h1.add h2)))

theorem measurable_tsum_modeCoefficient {f : ℕ → ℂ → ℂ} (hf : ∀ N, Continuous (f N)) :
    Measurable fun ξ : ℝ => ∑' N : ℕ, modeCoefficient ((ξ : ℂ) * I) N * f N ((ξ : ℂ) * I) := by
  refine Measurable.tsum fun N => ?_
  have hline : Continuous fun ξ : ℝ => (ξ : ℂ) * I := by fun_prop
  exact (((continuous_modeCoefficient N).comp hline).mul ((hf N).comp hline)).measurable

theorem measurable_weightedTail_line (hY : 0 < Y) (negative : Bool) (x : ℝ) :
    Measurable fun ξ : ℝ => weightedTail ((ξ : ℂ) * I) negative x Y :=
  measurable_tsum_modeCoefficient fun N => continuous_mode_order hY negative N x

theorem measurable_weightedTailX_line (hY : 0 < Y) (negative : Bool) (x : ℝ) :
    Measurable fun ξ : ℝ => weightedTailX ((ξ : ℂ) * I) negative x Y :=
  measurable_tsum_modeCoefficient
    (f := fun N ν => d4BMSignedWhittakerModeHorizontalFirstJet negative N ν x Y) fun N => by
    unfold d4BMSignedWhittakerModeHorizontalFirstJet
    exact continuous_const.mul (continuous_mode_order hY negative N x)

theorem measurable_weightedTailXX_line (hY : 0 < Y) (negative : Bool) (x : ℝ) :
    Measurable fun ξ : ℝ => weightedTailXX ((ξ : ℂ) * I) negative x Y :=
  measurable_tsum_modeCoefficient
    (f := fun N ν => d4BMSignedWhittakerModeHorizontalSecondJet negative N ν x Y) fun N => by
    unfold d4BMSignedWhittakerModeHorizontalSecondJet
    exact continuous_const.mul (continuous_mode_order hY negative N x)

theorem measurable_weightedTailY_line (hY : 0 < Y) (negative : Bool) (x : ℝ) :
    Measurable fun ξ : ℝ => weightedTailY ((ξ : ℂ) * I) negative x Y :=
  measurable_tsum_modeCoefficient fun N => continuous_firstJet_order hY negative N x

theorem measurable_weightedTailYY_line (hY : 0 < Y) (negative : Bool) (x : ℝ) :
    Measurable fun ξ : ℝ => weightedTailYY ((ξ : ℂ) * I) negative x Y := by
  have hfun : (fun ξ : ℝ => weightedTailYY ((ξ : ℂ) * I) negative x Y) =
      fun ξ : ℝ => ((((ξ : ℂ) * I) ^ 2 - 1 / 4) * weightedTail ((ξ : ℂ) * I) negative x Y / (Y : ℂ) ^ 2 -
        weightedTailXX ((ξ : ℂ) * I) negative x Y) :=
    funext fun ξ => weightedTailYY_eq _ negative x hY
  rw [hfun]
  have hline : Continuous fun ξ : ℝ => (((ξ : ℂ) * I) ^ 2 - 1 / 4 : ℂ) := by fun_prop
  exact ((hline.measurable.mul (measurable_weightedTail_line hY negative x)).div_const _).sub
    (measurable_weightedTailXX_line hY negative x)

end Measurability

end GaloisForLFunctions.BlackHoleRingdown

end
