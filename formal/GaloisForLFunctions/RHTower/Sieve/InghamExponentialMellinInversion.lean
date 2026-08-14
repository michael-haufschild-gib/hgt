import GaloisForLFunctions.HTGeometry.BoundedCoefficientLaplaceMellin
import GaloisForLFunctions.HTGeometry.GammaVerticalModulus
import GaloisForLFunctions.HTGeometry.TwoSidedExponentialMoments
import GaloisForLFunctions.RHTower.MobiusLaplaceAdditiveTriangleSubpower
import GaloisForLFunctions.RHTower.Sieve.GhsStepFour
import GaloisForLFunctions.RHTower.DivisorBound
import GaloisForLFunctions.RHTower.HardyCarrier
import Mathlib.Analysis.MellinInversion
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Gamma--Mellin inversion for exponential Dirichlet profiles

Ramachandra's fourth-moment argument begins from the exact inverse-Mellin representation of an
exponentially smoothed Dirichlet series.  The existing corpus proved only the forward identity

`M[Σ f(n)e^{-nx}](s) = Γ(s)L(f,s)`.

This file closes the inverse direction at the fixed line `Re s = 2` for every coefficient sequence
bounded by one.  It supplies the exact, unconditional contour identity needed before the zeta-square
contour can be shifted and reflected.
-/

open Complex Filter Set MeasureTheory

namespace RHTower.Sieve

noncomputable section

open GaloisForLFunctions.HTGeometry
open scoped ArithmeticFunction.zeta

/-- A bounded exponential Dirichlet profile has at most the universal `x⁻¹` singularity at zero. -/
theorem coeffLaplaceProfile_isBigO_rpow_neg_one_nhdsGT
    {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) :
    coeffLaplaceProfile f =O[nhdsWithin 0 (Ioi 0)]
      (fun x : ℝ => x ^ (-(1 : ℝ))) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨1 + Real.exp 1, ?_⟩
  filter_upwards [eventually_mem_set.mpr (Ioo_mem_nhdsGT zero_lt_one)] with x hx
  have hx0 : 0 < x := hx.1
  have hx1 : x ≤ 1 := hx.2.le
  have hterms := summable_coeffLaplaceTerm hf hx0
  have hmoment := _root_.RHTower.summable_natSucc_rpow_exp_neg_and_tsum_le
    (r := (0 : ℝ)) (x := x) (by norm_num) hx0
  have hnorm : ‖coeffLaplaceProfile f x‖ ≤
      ∑' n : ℕ, Real.exp (-((n : ℝ) * x)) := by
    unfold coeffLaplaceProfile
    calc
      ‖∑' n : ℕ, f n * Complex.exp (-((n : ℝ) * x : ℝ))‖ ≤
          ∑' n : ℕ, ‖f n * Complex.exp (-((n : ℝ) * x : ℝ))‖ :=
        norm_tsum_le_tsum_norm hterms.norm
      _ ≤ ∑' n : ℕ, Real.exp (-((n : ℝ) * x)) := by
        exact hterms.norm.tsum_le_tsum (fun n => by
          rw [norm_mul, Complex.norm_exp]
          exact mul_le_of_le_one_left (Real.exp_pos _).le (hf n))
          (summable_exp_neg_nat_mul hx0)
  have hmoment' : (∑' n : ℕ, Real.exp (-((n : ℝ) * x))) ≤
      1 + Real.exp x * (1 / x) := by
    simpa using hmoment.2
  have hexp : Real.exp x ≤ Real.exp 1 := Real.exp_le_exp.mpr hx1
  have hinvOne : 1 ≤ 1 / x := (one_le_div hx0).2 hx1
  have hcoarse : (∑' n : ℕ, Real.exp (-((n : ℝ) * x))) ≤
      (1 + Real.exp 1) * (1 / x) := by
    calc
      (∑' n : ℕ, Real.exp (-((n : ℝ) * x))) ≤ 1 + Real.exp x * (1 / x) := hmoment'
      _ ≤ 1 + Real.exp 1 * (1 / x) := by
        gcongr
      _ ≤ (1 + Real.exp 1) * (1 / x) := by nlinarith [Real.exp_pos 1]
  have htarget : ‖x ^ (-(1 : ℝ))‖ = 1 / x := by
    rw [Real.norm_eq_abs, Real.rpow_neg_one, abs_of_pos (inv_pos.mpr hx0), one_div]
  rw [htarget]
  exact hnorm.trans hcoarse

/-- Mellin convergence of every bounded exponential profile on `Re s = 2`. -/
theorem coeffLaplaceProfile_mellinConvergent_two
    {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (hf0 : f 0 = 0) :
    MellinConvergent (coeffLaplaceProfile f) (2 : ℂ) := by
  apply mellinConvergent_of_isBigO_rpow_exp (a := (1 : ℝ)) (b := (1 : ℝ)) one_pos
  · exact coeffLaplaceProfile_locallyIntegrableOn hf
  · simpa only [one_mul] using coeffLaplaceProfile_isBigO_exp_neg hf hf0
  · exact coeffLaplaceProfile_isBigO_rpow_neg_one_nhdsGT hf
  · norm_num

/-- Gamma is vertically integrable on the fixed inversion line `Re s = 2`. -/
theorem Gamma_verticalIntegrable_two :
    Complex.VerticalIntegrable Complex.Gamma 2 := by
  let r : ℝ := Real.pi / 2
  let A : ℝ := 2 * Real.pi / (1 - Real.exp (-2))
  let D : ℝ := Real.exp r + 3 * (A + 1)
  have hr : 0 < r := by dsimp [r]; positivity
  have hden : 0 < 1 - Real.exp (-2 : ℝ) := by
    have := Real.exp_lt_one_iff.mpr (by norm_num : (-2 : ℝ) < 0)
    linarith
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hmajor : Integrable (fun t : ℝ =>
      D * (1 + |t|) ^ 2 * Real.exp (-r * |t|)) := by
    have h0 := HTGeometry.integrable_abs_pow_mul_exp_neg_abs 0 hr
    have h2 := HTGeometry.integrable_abs_pow_mul_exp_neg_abs 2 hr
    have hsum : Integrable (fun t : ℝ =>
        Real.exp (-r * |t|) + |t| ^ 2 * Real.exp (-r * |t|)) := by
      apply (h0.add h2).congr
      exact Filter.Eventually.of_forall fun t => by simp
    apply Integrable.mono' (hsum.const_mul (2 * D))
    · fun_prop
    · exact Filter.Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs, abs_of_nonneg]
        · have habs : 0 ≤ |t| := abs_nonneg t
          have hexp : 0 ≤ Real.exp (-r * |t|) := (Real.exp_pos _).le
          have hquad : (1 + |t|) ^ 2 ≤ 2 * (1 + |t| ^ 2) := by
            nlinarith [sq_nonneg (|t| - 1)]
          calc
            D * (1 + |t|) ^ 2 * Real.exp (-r * |t|) ≤
                D * (2 * (1 + |t| ^ 2)) * Real.exp (-r * |t|) := by gcongr
            _ = 2 * D *
                (Real.exp (-r * |t|) + |t| ^ 2 * Real.exp (-r * |t|)) := by ring
        · positivity
  apply Integrable.mono' hmajor
  · have hcont : Continuous (fun t : ℝ =>
        Complex.Gamma ((2 : ℂ) + (t : ℂ) * Complex.I)) := by
      rw [continuous_iff_continuousAt]
      intro t
      apply (Complex.continuousAt_Gamma _ ?_).comp
      · fun_prop
      · intro m hm
        have hre := congrArg Complex.re hm
        simp at hre
        have hm0 : (0 : ℝ) ≤ m := by positivity
        linarith
    exact hcont.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun t => by
      by_cases ht : 1 ≤ |t|
      · have hgamma :=
          (GaloisForLFunctions.HTGeometry.norm_Gamma_one_add_nat_bounds 1 ht).2
        have hAeq : A * |t| =
            2 * Real.pi * |t| / (1 - Real.exp (-2)) := by
          dsimp [A]
          field_simp [hden.ne']
        have hgamma0 : ‖Complex.Gamma ((2 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
            Real.sqrt (A * |t|) * (3 * |t|) *
              Real.exp (-(Real.pi * |t| / 2)) := by
          rw [hAeq]
          calc
            ‖Complex.Gamma ((2 : ℂ) + (t : ℂ) * Complex.I)‖ =
                ‖Complex.Gamma ((1 : ℂ) + (t : ℂ) * Complex.I + (1 : ℂ))‖ := by
              congr 2
              ring
            _ ≤ Real.sqrt (2 * Real.pi * |t| / (1 - Real.exp (-2))) *
                (((2 : ℝ) + (1 : ℕ)) * |t|) ^ (1 : ℕ) *
                  Real.exp (-(Real.pi * |t| / 2)) := by
              simpa only [Nat.cast_one] using hgamma
            _ = Real.sqrt (2 * Real.pi * |t| / (1 - Real.exp (-2))) *
                (3 * |t|) * Real.exp (-(Real.pi * |t| / 2)) := by norm_num
        have hz : 0 ≤ A * |t| := mul_nonneg hA (abs_nonneg t)
        have hsqrtSq := Real.sq_sqrt hz
        have hsqrt : Real.sqrt (A * |t|) ≤ A * |t| + 1 := by
          have hsqrt0 := Real.sqrt_nonneg (A * |t|)
          nlinarith [sq_nonneg (Real.sqrt (A * |t|) - 1)]
        have habsSq : |t| ≤ |t| ^ 2 := by nlinarith [abs_nonneg t]
        have hpoly : Real.sqrt (A * |t|) * (3 * |t|) ≤
            3 * (A + 1) * |t| ^ 2 := by
          calc
            Real.sqrt (A * |t|) * (3 * |t|) ≤
                (A * |t| + 1) * (3 * |t|) :=
              mul_le_mul_of_nonneg_right hsqrt (by positivity)
            _ ≤ 3 * (A + 1) * |t| ^ 2 := by
              nlinarith [mul_nonneg hA (sq_nonneg |t|)]
        have hgamma' : ‖Complex.Gamma ((2 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
            3 * (A + 1) * |t| ^ 2 * Real.exp (-r * |t|) := by
          calc
            ‖Complex.Gamma ((2 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
                Real.sqrt (A * |t|) * (3 * |t|) *
                  Real.exp (-(Real.pi * |t| / 2)) := hgamma0
            _ ≤ 3 * (A + 1) * |t| ^ 2 *
                  Real.exp (-(Real.pi * |t| / 2)) :=
              mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
            _ = 3 * (A + 1) * |t| ^ 2 * Real.exp (-r * |t|) := by
              dsimp [r]
              congr 1
              ring
        calc
          ‖Complex.Gamma ((2 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
              3 * (A + 1) * |t| ^ 2 * Real.exp (-r * |t|) := hgamma'
          _ ≤ D * (1 + |t|) ^ 2 * Real.exp (-r * |t|) := by
            have hcoef : 3 * (A + 1) ≤ D := by dsimp [D]; linarith [Real.exp_pos r]
            have hp : |t| ^ 2 ≤ (1 + |t|) ^ 2 := by nlinarith [abs_nonneg t]
            gcongr
      · have htlt : |t| < 1 := lt_of_not_ge ht
        have hgamma := GaloisForLFunctions.HTGeometry.norm_Gamma_le_Gamma_re
          (s := (2 : ℂ) + (t : ℂ) * Complex.I) (by norm_num)
        have hgammaOne : ‖Complex.Gamma ((2 : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 1 := by
          calc
            ‖Complex.Gamma ((2 : ℂ) + (t : ℂ) * Complex.I)‖ ≤ Real.Gamma 2 := by
              simpa using hgamma
            _ = 1 := by norm_num [Real.Gamma_nat_eq_factorial]
        have hexpLower : 1 ≤ Real.exp r * Real.exp (-r * |t|) := by
          rw [← Real.exp_add, ← Real.exp_zero]
          apply Real.exp_le_exp.mpr
          have : 0 ≤ |t| := abs_nonneg t
          nlinarith
        calc
          ‖Complex.Gamma ((2 : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 1 := hgammaOne
          _ ≤ Real.exp r * Real.exp (-r * |t|) := hexpLower
          _ ≤ D * (1 + |t|) ^ 2 * Real.exp (-r * |t|) := by
            have hE : Real.exp r ≤ D := by
              dsimp [D]
              have : 0 ≤ 3 * (A + 1) := by positivity
              linarith
            have hp : 1 ≤ (1 + |t|) ^ 2 := by nlinarith [abs_nonneg t]
            have hprod : Real.exp r ≤ D * (1 + |t|) ^ 2 := by
              calc
                Real.exp r = Real.exp r * 1 := by ring
                _ ≤ D * (1 + |t|) ^ 2 :=
                  mul_le_mul hE hp (by positivity) hD
            exact mul_le_mul_of_nonneg_right hprod (Real.exp_pos _).le

theorem continuous_Gamma_two_line :
    Continuous (fun t : ℝ => Complex.Gamma ((2 : ℂ) + (t : ℂ) * Complex.I)) := by
  rw [continuous_iff_continuousAt]
  intro t
  apply (Complex.continuousAt_Gamma _ ?_).comp
  · fun_prop
  · intro m hm
    have hre := congrArg Complex.re hm
    simp at hre
    have hm0 : (0 : ℝ) ≤ m := by positivity
    linarith

/-- Fixed finite majorant for all bounded Dirichlet series on `Re s = 2`. -/
noncomputable def boundedLSeriesTwoMajorant : ℝ :=
  ∑' n : ℕ, ‖LSeries.term (fun _ : ℕ => (1 : ℂ)) (2 : ℂ) n‖

theorem boundedLSeriesTwoMajorant_nonneg : 0 ≤ boundedLSeriesTwoMajorant := by
  unfold boundedLSeriesTwoMajorant
  exact tsum_nonneg fun _ => norm_nonneg _

theorem norm_LSeries_two_le_boundedLSeriesTwoMajorant
    {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (t : ℝ) :
    ‖LSeries f ((2 : ℂ) + (t : ℂ) * Complex.I)‖ ≤ boundedLSeriesTwoMajorant := by
  let u : ℕ → ℂ := fun _ => 1
  have hsre : 1 < (((2 : ℂ) + (t : ℂ) * Complex.I).re) := by norm_num
  have hfs : LSeriesSummable f ((2 : ℂ) + (t : ℂ) * Complex.I) :=
    LSeriesSummable_of_bounded_of_one_lt_re (fun n _ => hf n) hsre
  have hus : LSeriesSummable u (2 : ℂ) :=
    LSeriesSummable_of_bounded_of_one_lt_re (m := 1)
      (fun _ _ => by simp [u]) (by norm_num)
  unfold LSeries
  calc
    ‖∑' n : ℕ, LSeries.term f ((2 : ℂ) + (t : ℂ) * Complex.I) n‖ ≤
        ∑' n : ℕ, ‖LSeries.term f ((2 : ℂ) + (t : ℂ) * Complex.I) n‖ :=
      norm_tsum_le_tsum_norm hfs.norm
    _ ≤ ∑' n : ℕ, ‖LSeries.term u (2 : ℂ) n‖ := by
      exact hfs.norm.tsum_le_tsum (fun n => by
        calc
          ‖LSeries.term f ((2 : ℂ) + (t : ℂ) * Complex.I) n‖ ≤
              ‖LSeries.term u ((2 : ℂ) + (t : ℂ) * Complex.I) n‖ :=
            LSeries.norm_term_le _ (by simpa [u] using hf n)
          _ = ‖LSeries.term u (2 : ℂ) n‖ := by
            rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
            norm_num)
        hus.norm
    _ = boundedLSeriesTwoMajorant := by rfl

/-- The Gamma-completed bounded Dirichlet series is integrable on the inversion line. -/
theorem gamma_mul_LSeries_verticalIntegrable_two
    {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) :
    Complex.VerticalIntegrable (fun s => Complex.Gamma s * LSeries f s) 2 := by
  let B := boundedLSeriesTwoMajorant
  have hmajor : Integrable (fun t : ℝ =>
      B * ‖Complex.Gamma ((2 : ℂ) + (t : ℂ) * Complex.I)‖) :=
    Gamma_verticalIntegrable_two.norm.const_mul B
  apply Integrable.mono' hmajor
  · exact (continuous_Gamma_two_line.mul
      (continuous_LSeries_line_of_bounded hf (by norm_num))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun t => by
      rw [norm_mul]
      have hL := norm_LSeries_two_le_boundedLSeriesTwoMajorant hf t
      dsimp [B]
      calc
        ‖Complex.Gamma ((2 : ℂ) + (t : ℂ) * Complex.I)‖ *
            ‖LSeries f ((2 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
            ‖Complex.Gamma ((2 : ℂ) + (t : ℂ) * Complex.I)‖ *
              boundedLSeriesTwoMajorant :=
          mul_le_mul_of_nonneg_left hL (norm_nonneg _)
        _ = boundedLSeriesTwoMajorant *
              ‖Complex.Gamma ((2 : ℂ) + (t : ℂ) * Complex.I)‖ := by ring

/-- **Exact exponential Mellin inversion.**  This is Ramachandra's initial contour identity for an
arbitrary bounded coefficient sequence, before specializing the coefficients to the critical
divisor carrier. -/
theorem mellinInv_two_gamma_mul_LSeries_eq_coeffLaplaceProfile
    {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (hf0 : f 0 = 0)
    {x : ℝ} (hx : 0 < x) :
    mellinInv 2 (fun s => Complex.Gamma s * LSeries f s) x =
      coeffLaplaceProfile f x := by
  have hconv := coeffLaplaceProfile_mellinConvergent_two hf hf0
  have hvertical : Complex.VerticalIntegrable (mellin (coeffLaplaceProfile f)) 2 := by
    apply (gamma_mul_LSeries_verticalIntegrable_two hf).congr
    exact Filter.Eventually.of_forall fun t => by
      symm
      exact mellin_coeffLaplaceProfile_eq_gamma_mul_LSeries hf hf0 (by norm_num)
  have hcont : ContinuousAt (coeffLaplaceProfile f) x :=
    (continuousOn_coeffLaplaceProfile hf x hx).continuousAt (Ioi_mem_nhds hx)
  have hinv := mellinInv_mellin_eq 2 (coeffLaplaceProfile f) hx hconv hvertical hcont
  calc
    mellinInv 2 (fun s => Complex.Gamma s * LSeries f s) x =
        mellinInv 2 (mellin (coeffLaplaceProfile f)) x := by
      unfold mellinInv
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t => by
        change (x : ℂ) ^ (-((2 : ℂ) + (t : ℂ) * Complex.I)) •
            (Complex.Gamma ((2 : ℂ) + (t : ℂ) * Complex.I) *
              LSeries f ((2 : ℂ) + (t : ℂ) * Complex.I)) =
          (x : ℂ) ^ (-((2 : ℂ) + (t : ℂ) * Complex.I)) •
            mellin (coeffLaplaceProfile f) ((2 : ℂ) + (t : ℂ) * Complex.I)
        congr 1
        exact (mellin_coeffLaplaceProfile_eq_gamma_mul_LSeries
          hf hf0 (by norm_num)).symm
    _ = coeffLaplaceProfile f x := hinv

/-- Mellin inversion commutes with multiplication by a complex constant. -/
theorem mellinInv_const_mul (c : ℂ) (F : ℂ → ℂ) (x : ℝ) :
    mellinInv 2 (fun s => c * F s) x = c * mellinInv 2 F x := by
  unfold mellinInv
  simp only [smul_eq_mul, Complex.real_smul]
  have hfun :
      (fun y : ℝ => (x : ℂ) ^ (-(((2 : ℝ) : ℂ) + (y : ℂ) * I)) *
        (c * F (((2 : ℝ) : ℂ) + (y : ℂ) * I))) =
      (fun y : ℝ => c * ((x : ℂ) ^ (-(((2 : ℝ) : ℂ) + (y : ℂ) * I)) *
        F (((2 : ℝ) : ℂ) + (y : ℂ) * I))) := by
    funext y
    ring
  rw [hfun, MeasureTheory.integral_const_mul]
  ring

/-- Exponential coefficient profiles commute with complex scalar multiplication. -/
theorem coeffLaplaceProfile_smul (c : ℂ) (f : ℕ → ℂ) (x : ℝ) :
    coeffLaplaceProfile (c • f) x = c * coeffLaplaceProfile f x := by
  unfold coeffLaplaceProfile
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- Exact exponential Mellin inversion for any uniformly bounded coefficient sequence.  The
constant need not be one: normalization and scalar cancellation recover the literal coefficients. -/
theorem mellinInv_two_gamma_mul_LSeries_eq_coeffLaplaceProfile_of_bound
    {f : ℕ → ℂ} {B : ℝ} (hB : 0 < B) (hf : ∀ n, ‖f n‖ ≤ B) (hf0 : f 0 = 0)
    {x : ℝ} (hx : 0 < x) :
    mellinInv 2 (fun s => Complex.Gamma s * LSeries f s) x =
      coeffLaplaceProfile f x := by
  let g : ℕ → ℂ := (B : ℂ)⁻¹ • f
  have hg : ∀ n, ‖g n‖ ≤ 1 := by
    intro n
    have hB0 : B ≠ 0 := hB.ne'
    calc
      ‖g n‖ = B⁻¹ * ‖f n‖ := by
        simp only [g, Pi.smul_apply, norm_smul, norm_inv, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hB]
      _ ≤ B⁻¹ * B := mul_le_mul_of_nonneg_left (hf n) (inv_nonneg.mpr hB.le)
      _ = 1 := inv_mul_cancel₀ hB0
  have hg0 : g 0 = 0 := by simp [g, hf0]
  have hbase := mellinInv_two_gamma_mul_LSeries_eq_coeffLaplaceProfile hg hg0 hx
  have hL : ∀ s : ℂ, LSeries g s = (B : ℂ)⁻¹ * LSeries f s := by
    intro s
    exact LSeries_smul f (B : ℂ)⁻¹ s
  have hleft :
      mellinInv 2 (fun s => Complex.Gamma s * LSeries g s) x =
        (B : ℂ)⁻¹ * mellinInv 2 (fun s => Complex.Gamma s * LSeries f s) x := by
    calc
      mellinInv 2 (fun s => Complex.Gamma s * LSeries g s) x =
          mellinInv 2 (fun s => (B : ℂ)⁻¹ *
            (Complex.Gamma s * LSeries f s)) x := by
        congr 2
        funext s
        rw [hL]
        ring
      _ = (B : ℂ)⁻¹ * mellinInv 2
          (fun s => Complex.Gamma s * LSeries f s) x :=
        mellinInv_const_mul _ _ _
  have hright : coeffLaplaceProfile g x =
      (B : ℂ)⁻¹ * coeffLaplaceProfile f x := by
    exact coeffLaplaceProfile_smul _ _ _
  have hc : (B : ℂ)⁻¹ ≠ 0 := inv_ne_zero (Complex.ofReal_ne_zero.mpr hB.ne')
  apply mul_left_cancel₀ hc
  rw [← hleft, ← hright]
  exact hbase

/-! ## Literal critical divisor specialization -/

/-- Critical divisor coefficient `d(n)n^(-1/2-iτ)` before exponential smoothing. -/
noncomputable def inghamCriticalDivisorCoeff (tau : ℝ) (n : ℕ) : ℂ :=
  (n.divisors.card : ℂ) * (n : ℂ) ^ (-linePt tau)

@[simp]
theorem inghamCriticalDivisorCoeff_zero (tau : ℝ) :
    inghamCriticalDivisorCoeff tau 0 = 0 := by
  simp [inghamCriticalDivisorCoeff]

/-- The convolution square of the arithmetic zeta function is the divisor-counting function. -/
theorem coe_zeta_mul_zeta_apply_eq_card_divisors (n : ℕ) :
    (((ArithmeticFunction.zeta : ArithmeticFunction ℂ) *
      (ArithmeticFunction.zeta : ArithmeticFunction ℂ)) n) =
      (n.divisors.card : ℂ) := by
  rw [ArithmeticFunction.coe_zeta_mul_apply]
  by_cases hn : n = 0
  · simp [hn]
  · calc
      ∑ x ∈ n.divisors, (ArithmeticFunction.zeta : ArithmeticFunction ℂ) x =
          ∑ _x ∈ n.divisors, (1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro x hx
        have hxne : x ≠ 0 := by
          intro hx0
          subst x
          exact hn (zero_dvd_iff.mp (Nat.mem_divisors.mp hx).1)
        rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, if_neg hxne]
        norm_num
      _ = (n.divisors.card : ℂ) := by simp

/-- Exact divisor Dirichlet series identity on the half-plane of absolute convergence. -/
theorem LSeries_card_divisors_eq_riemannZeta_sq {w : ℂ} (hw : 1 < w.re) :
    LSeries (fun n : ℕ => (n.divisors.card : ℂ)) w =
      riemannZeta w ^ 2 := by
  let Z : ArithmeticFunction ℂ := ArithmeticFunction.zeta
  have hz : LSeriesHasSum (Z : ℕ → ℂ) w (riemannZeta w) := by
    dsimp [Z]
    exact ArithmeticFunction.LSeriesHasSum_zeta hw
  have hmul : LSeriesHasSum ((Z * Z : ArithmeticFunction ℂ) : ℕ → ℂ) w
      (riemannZeta w * riemannZeta w) :=
    ArithmeticFunction.LSeriesHasSum_mul hz hz
  have hcongr : ∀ {n : ℕ}, n ≠ 0 →
      ((Z * Z : ArithmeticFunction ℂ) n) = (n.divisors.card : ℂ) := by
    intro n _hn
    exact coe_zeta_mul_zeta_apply_eq_card_divisors n
  have hdiv : LSeriesHasSum (fun n : ℕ => (n.divisors.card : ℂ)) w
      (riemannZeta w * riemannZeta w) :=
    (LSeriesHasSum_congr w _ hcongr).mp hmul
  simpa [pow_two] using hdiv.LSeries_eq

/-- Twisting the divisor coefficients shifts the zeta-square argument exactly. -/
theorem LSeries_inghamCriticalDivisorCoeff_eq_riemannZeta_sq
    (tau : ℝ) {z : ℂ} (hz : 1 < (linePt tau + z).re) :
    LSeries (inghamCriticalDivisorCoeff tau) z =
      riemannZeta (linePt tau + z) ^ 2 := by
  rw [← LSeries_card_divisors_eq_riemannZeta_sq hz]
  unfold LSeries
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp [LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    unfold inghamCriticalDivisorCoeff
    have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    calc
      ((n.divisors.card : ℂ) * (n : ℂ) ^ (-linePt tau)) / (n : ℂ) ^ z =
          (n.divisors.card : ℂ) *
            ((n : ℂ) ^ (-linePt tau) * (n : ℂ) ^ (-z)) := by
        rw [div_eq_mul_inv, ← Complex.cpow_neg]
        ring
      _ = (n.divisors.card : ℂ) *
          (n : ℂ) ^ ((-linePt tau) + (-z)) := by
        rw [Complex.cpow_add _ _ hnC]
      _ = (n.divisors.card : ℂ) * (n : ℂ) ^ (-(linePt tau + z)) := by
        congr 2
        ring
      _ = (n.divisors.card : ℂ) / (n : ℂ) ^ (linePt tau + z) := by
        rw [Complex.cpow_neg]
        ring

/-- The literal critical divisor coefficients are uniformly bounded, independently of height. -/
theorem exists_inghamCriticalDivisorCoeff_uniformBound :
    ∃ B : ℝ, 0 < B ∧ ∀ tau : ℝ, ∀ n : ℕ,
      ‖inghamCriticalDivisorCoeff tau n‖ ≤ B := by
  obtain ⟨C, hC, hdiv⟩ :=
    _root_.RHTower.card_divisors_le_const_mul_rpow (ε := (1 / 4 : ℝ)) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro tau n
  by_cases hn : n = 0
  · subst n
    simp [hC.le]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hd := hdiv n hnpos
    rw [inghamCriticalDivisorCoeff, norm_mul, Complex.norm_natCast,
      Complex.norm_natCast_cpow_of_pos hnpos, Complex.neg_re, linePt_re]
    calc
      (n.divisors.card : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤
          (C * (n : ℝ) ^ (1 / 4 : ℝ)) *
            (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_right hd (Real.rpow_nonneg hnR.le _)
      _ = C * ((n : ℝ) ^ (1 / 4 : ℝ) *
          (n : ℝ) ^ (-(1 / 2 : ℝ))) := by ring
      _ = C * (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
        rw [← Real.rpow_add hnR]
        congr 2
        norm_num
      _ ≤ C * 1 := by
        gcongr
        exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hnpos) (by norm_num)
      _ = C := mul_one C

/-- **Exact Ramachandra starting identity.**  On the critical line, the exponentially smoothed
divisor series is the inverse Mellin transform of `Γ(z)ζ(1/2+iτ+z)²` on `Re z = 2`. -/
theorem ingham_exponential_mellin_identity (tau : ℝ) {x : ℝ} (hx : 0 < x) :
    mellinInv 2
        (fun z => Complex.Gamma z * riemannZeta (linePt tau + z) ^ 2) x =
      ∑' n : ℕ, inghamCriticalDivisorCoeff tau n *
        Complex.exp (-((n : ℝ) * x : ℝ)) := by
  obtain ⟨B, hB, hbound⟩ := exists_inghamCriticalDivisorCoeff_uniformBound
  have hbase := mellinInv_two_gamma_mul_LSeries_eq_coeffLaplaceProfile_of_bound
    hB (hbound tau) (inghamCriticalDivisorCoeff_zero tau) hx
  have hcontour :
      mellinInv 2
          (fun z => Complex.Gamma z * riemannZeta (linePt tau + z) ^ 2) x =
        mellinInv 2
          (fun z => Complex.Gamma z * LSeries (inghamCriticalDivisorCoeff tau) z) x := by
    unfold mellinInv
    congr 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun t : ℝ => by
      have hseries :
          LSeries (inghamCriticalDivisorCoeff tau)
              (((2 : ℝ) : ℂ) + (t : ℂ) * I) =
            riemannZeta
              (linePt tau + (((2 : ℝ) : ℂ) + (t : ℂ) * I)) ^ 2 := by
        apply LSeries_inghamCriticalDivisorCoeff_eq_riemannZeta_sq
        rw [Complex.add_re, linePt_re]
        norm_num
      change (x : ℂ) ^ (-(((2 : ℝ) : ℂ) + (t : ℂ) * I)) •
          (Complex.Gamma (((2 : ℝ) : ℂ) + (t : ℂ) * I) *
            riemannZeta
              (linePt tau + (((2 : ℝ) : ℂ) + (t : ℂ) * I)) ^ 2) =
        (x : ℂ) ^ (-(((2 : ℝ) : ℂ) + (t : ℂ) * I)) •
          (Complex.Gamma (((2 : ℝ) : ℂ) + (t : ℂ) * I) *
            LSeries (inghamCriticalDivisorCoeff tau)
              (((2 : ℝ) : ℂ) + (t : ℂ) * I))
      rw [hseries]
  rw [hcontour, hbase]
  rfl

end

end RHTower.Sieve
