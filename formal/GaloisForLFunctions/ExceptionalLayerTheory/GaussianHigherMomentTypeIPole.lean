import GaloisForLFunctions.ExceptionalLayerTheory.GaussianHigherMomentLattice
import GaloisForLFunctions.ExceptionalLayerTheory.GaussianMomentTypeIPole

/-!
# Higher-order pole subtraction in the arithmetic Vaughan convolution

The actual truncated Mangoldt–Möbius coefficient retains its signed pole
mass. Moment order `r` gives error `O((UV)^(2r)t^(2r)X^(1-σ-2r)log(UV))`.
-/

open Complex Finset Filter Topology RHTower RHTower.Sieve ArithmeticFunction
noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- The normalized higher Gaussian moment on arithmetic samples. -/
def gaussianHigherPrimeMomentWeight (r : ℕ) (σ t : ℝ) (ε : ℂ) (n : ℕ) : ℂ :=
  (ε / (t : ℂ)) ^ r *
    gaussianMellinWeight (((2 * r : ℕ) : ℂ) - ((σ : ℂ) + t * I)) ε n

private theorem higherMomentWeight_zero {r : ℕ} (hr : r ≠ 0) {σ : ℝ}
    (hσ : σ < 1) (t : ℝ) (ε : ℂ) : gaussianHigherPrimeMomentWeight r σ t ε 0 = 0 := by
  have hr' : (2 : ℝ) ≤ ((2 * r : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ 2 * r by omega)
  have hw : (((2 * r : ℕ) : ℂ) - ((σ : ℂ) + t * I)) ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.natCast_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
      zero_mul, sub_zero, add_zero, Complex.zero_re] at he
    linarith
  simp only [gaussianHigherPrimeMomentWeight, Nat.cast_zero, gaussianMellinWeight,
    Complex.ofReal_zero, Complex.zero_cpow hw, zero_mul, mul_zero]

private theorem summable_higherMomentWeight_dilate (r : ℕ) (σ t : ℝ) {ε : ℂ}
    (hε : 0 < ε.re) {b : ℕ} (hb : 1 ≤ b) :
    Summable (fun a : ℕ => gaussianHigherPrimeMomentWeight r σ t ε (a * b)) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hh := (summable_gaussianMellinWeight_lattice_all
    (w := ((2 * r : ℕ) : ℂ) - ((σ : ℂ) + t * I)) hε hbR).mul_left ((ε / (t : ℂ)) ^ r)
  apply (summable_nat_add_iff 1).mp
  refine hh.congr fun a => ?_
  unfold gaussianHigherPrimeMomentWeight
  congr 2
  push_cast
  ring

private theorem tsum_higherMomentWeight_dilate_eq {r : ℕ} (hr : r ≠ 0) {σ : ℝ}
    (hσ : σ < 1) (t : ℝ) {ε : ℂ} (hε : 0 < ε.re) {b : ℕ} (hb : 1 ≤ b) :
    (∑' a : ℕ, gaussianHigherPrimeMomentWeight r σ t ε (a * b)) =
      (ε / (t : ℂ)) ^ r * ∑' a : ℕ,
        gaussianMellinWeight (((2 * r : ℕ) : ℂ) - ((σ : ℂ) + t * I)) ε
          ((b : ℝ) * (a + 1)) := by
  have hh := (summable_higherMomentWeight_dilate r σ t hε hb).sum_add_tsum_nat_add 1
  simp only [sum_range_one, zero_mul, higherMomentWeight_zero hr hσ, zero_add] at hh
  rw [← hh, ← tsum_mul_left]
  apply tsum_congr
  intro a
  unfold gaussianHigherPrimeMomentWeight
  congr 2
  push_cast
  ring

private theorem norm_higherMomentWeight_le (r : ℕ) {σ : ℝ} (hσ : 0 ≤ σ)
    (t : ℝ) (ε : ℂ) {n : ℕ} (hn : 1 ≤ n) :
    ‖gaussianHigherPrimeMomentWeight r σ t ε n‖ ≤
      ‖(ε / (t : ℂ)) ^ r‖ * (n : ℝ) ^ (2 * r) * Real.exp (-ε.re * (n : ℝ) ^ 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  unfold gaussianHigherPrimeMomentWeight gaussianMellinWeight
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hn0, Complex.norm_exp]
  have hw : (((2 * r : ℕ) : ℂ) - ((σ : ℂ) + t * I)).re = ((2 * r : ℕ) : ℝ) - σ := by simp
  have he : (-(ε * (n : ℂ) ^ 2)).re = -ε.re * (n : ℝ) ^ 2 := by simp [pow_two]
  simp only [Complex.ofReal_natCast]
  rw [hw, he]
  have hp : (n : ℝ) ^ (((2 * r : ℕ) : ℝ) - σ) ≤ (n : ℝ) ^ (2 * r) := by
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hn1
      (show ((2 * r : ℕ) : ℝ) - σ ≤ (2 * r : ℕ) by linarith)
  calc
    _ ≤ ‖(ε / (t : ℂ)) ^ r‖ * ((n : ℝ) ^ (2 * r) * Real.exp (-ε.re * (n : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le) (norm_nonneg _)
    _ = _ := by ring

private theorem tsum_zeta_conv_higherMoment_eq {r : ℕ} (hr : r ≠ 0) {σ : ℝ}
    (hσ : 0 ≤ σ) (hσ1 : σ < 1) (t : ℝ) {ε : ℂ} (hε : 0 < ε.re)
    (c : ArithmeticFunction ℝ) (K : ℕ) (hc : ∀ b, K < b → c b = 0) :
    (∑' n : ℕ, ((((zeta : ArithmeticFunction ℝ) * c) n : ℝ) : ℂ) *
      gaussianHigherPrimeMomentWeight r σ t ε n) =
      ∑ b ∈ Icc 1 K, (c b : ℂ) * ∑' a : ℕ, gaussianHigherPrimeMomentWeight r σ t ε (a * b) := by
  let W := gaussianHigherPrimeMomentWeight r σ t ε
  have hc0 (b : ℕ) (hb : b ∉ Icc 1 K) : c b = 0 := by
    by_cases h0 : b = 0
    · simp [h0]
    · exact hc b (by simp only [mem_Icc] at hb; omega)
  have hA : Summable (fun b : ℕ => |c b| * (b : ℝ) ^ (2 * r)) :=
    summable_of_ne_finset_zero (s := Icc 1 K) fun b hb => by rw [hc0 b hb]; simp
  have hB := RHTower.summable_pow_mul_exp_neg_nat_sq (2 * r) hε
  have hmajor := (hA.mul_of_nonneg hB (fun b => by positivity)
    (fun a => by positivity)).mul_left ‖(ε / (t : ℂ)) ^ r‖
  have hprod : Summable (fun p : ℕ × ℕ => (c p.1 : ℂ) *
      (((zeta : ArithmeticFunction ℝ) p.2 : ℝ) : ℂ) * W (p.1 * p.2)) := by
    apply hmajor.of_norm_bounded
    rintro ⟨b, a⟩
    by_cases hb : b = 0
    · simp [hb]
    by_cases ha : a = 0
    · simp [ha, hr]
    have hb1 : 1 ≤ b := by omega
    have hn : 1 ≤ b * a := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hb ha)
    have haR : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb1
    have hab : (a : ℝ) ≤ (b * a : ℕ) := by push_cast; nlinarith only [hbR, haR]
    have he : Real.exp (-ε.re * ((b * a : ℕ) : ℝ) ^ 2) ≤
        Real.exp (-ε.re * (a : ℝ) ^ 2) := by
      rw [Real.exp_le_exp]
      have hs := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ haR hab 2) hε.le
      linarith only [hs]
    have hW := norm_higherMomentWeight_le r hσ t ε hn
    have hz : (((zeta : ArithmeticFunction ℝ) a : ℝ) : ℂ) = 1 := by simp [ha]
    rw [hz, mul_one, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ |c b| * (‖(ε / (t : ℂ)) ^ r‖ * ((b * a : ℕ) : ℝ) ^ (2 * r) *
          Real.exp (-ε.re * ((b * a : ℕ) : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left hW (abs_nonneg _)
      _ ≤ |c b| * (‖(ε / (t : ℂ)) ^ r‖ * ((b * a : ℕ) : ℝ) ^ (2 * r) *
          Real.exp (-ε.re * (a : ℝ) ^ 2)) := by gcongr
      _ = _ := by push_cast; rw [mul_pow]; ring
  have hh := RHTower.ExactNullDivisorTransfer.tsum_tsum_mul_comp_mul
    (a := fun b => (c b : ℂ)) (b := fun a => (((zeta : ArithmeticFunction ℝ) a : ℝ) : ℂ))
    (f := W) (by simp) (by simp) hprod
  have hconv (n : ℕ) : LSeries.convolution (fun b => (c b : ℂ))
      (fun a => (((zeta : ArithmeticFunction ℝ) a : ℝ) : ℂ)) n =
        ((((zeta : ArithmeticFunction ℝ) * c) n : ℝ) : ℂ) := by
    rw [LSeries.convolution_def, mul_comm (zeta : ArithmeticFunction ℝ) c, ArithmeticFunction.mul_apply]
    push_cast
    rfl
  simp_rw [hconv] at hh
  rw [← hh]
  have hrow (b : ℕ) : (∑' a : ℕ, (c b : ℂ) *
      (((zeta : ArithmeticFunction ℝ) a : ℝ) : ℂ) * W (b * a)) =
        (c b : ℂ) * ∑' a : ℕ, W (a * b) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro a
    by_cases ha : a = 0
    · simp [ha, W, higherMomentWeight_zero hr hσ1]
    · simp [ha, Nat.mul_comm]
  simp_rw [hrow]
  exact tsum_eq_sum fun b hb => by rw [hc0 b hb]; simp

/-- The actual arithmetic fibre has the high-order physical-scale remainder. -/
theorem norm_tsum_gaussianHigherPrimeMomentWeight_dilate_sub_pole_le (r : ℕ) (hr : r ≠ 0)
    {σ t X : ℝ} {ε : ℂ} (hσ : σ < 1) (ht : 1 ≤ t) (hε : 0 < ε.re)
    (hsector : ‖ε‖ ≤ 4 * ε.re * t) (hX : 0 < X) (hscale : ε.re * X ^ 2 = 2)
    {b : ℕ} (hb : 1 ≤ b) :
    ‖(∑' a : ℕ, gaussianHigherPrimeMomentWeight r σ t ε (a * b)) -
      (b : ℂ)⁻¹ * gaussianHigherMomentPole r ((σ : ℂ) + t * I) ε t‖ ≤
      (gaussianHigherMomentLatticeConstant r σ *
        (2 : ℝ) ^ (((2 * r : ℕ) + σ - 1) / 2)) *
        (b : ℝ) ^ (2 * r - 1) * t ^ (2 * r) * X ^ (1 - σ - (2 * r : ℕ)) := by
  rw [tsum_higherMomentWeight_dilate_eq hr hσ t hε hb]
  simpa only [Complex.ofReal_natCast] using
    norm_tsum_gaussianHigherMoment_sub_pole_physical_le r hr hσ ht hε hsector hX hscale
      (by exact_mod_cast (show 0 < b by omega) : (0 : ℝ) < b)

/-- Exact signed pole extraction for the actual truncated Mangoldt–Möbius convolution.
The remainder gains `2r` powers of the ratio of divisor support to Gaussian scale. -/
theorem norm_tsum_gaussianHigherMoment_zeta_trunc_conv_sub_pole_le (r : ℕ) (hr : r ≠ 0)
    {σ t X : ℝ} {ε : ℂ} (hσ : 0 ≤ σ) (hσ1 : σ < 1) (ht : 1 ≤ t) (hε : 0 < ε.re)
    (hsector : ‖ε‖ ≤ 4 * ε.re * t) (hX : 0 < X) (hscale : ε.re * X ^ 2 = 2)
    {U V : ℕ} (hUV : 1 ≤ U * V) :
    ‖(∑' n : ℕ,
        ((((zeta : ArithmeticFunction ℝ) * (truncAF vonMangoldt U *
          truncAF (moebius : ArithmeticFunction ℝ) V)) n : ℝ) : ℂ) *
            gaussianHigherPrimeMomentWeight r σ t ε n) -
      (∑ b ∈ Icc 1 (U * V),
        (((truncAF vonMangoldt U * truncAF (moebius : ArithmeticFunction ℝ) V) b : ℝ) : ℂ) /
          (b : ℂ)) * gaussianHigherMomentPole r ((σ : ℂ) + t * I) ε t‖ ≤
      (gaussianHigherMomentLatticeConstant r σ *
        (2 : ℝ) ^ (((2 * r : ℕ) + σ - 1) / 2)) *
        t ^ (2 * r) * X ^ (1 - σ - (2 * r : ℕ)) *
        ((U * V : ℕ) : ℝ) ^ (2 * r) * Real.log ((U * V : ℕ) : ℝ) := by
  let c := truncAF vonMangoldt U * truncAF (moebius : ArithmeticFunction ℝ) V
  have hsupp (b : ℕ) (hb : U * V < b) : c b = 0 := truncAF_conv_apply_of_gt hb
  rw [tsum_zeta_conv_higherMoment_eq hr hσ hσ1 t hε c (U * V) hsupp,
    sum_mul, ← sum_sub_distrib]
  have hlog : 0 ≤ Real.log ((U * V : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast hUV)
  have hC := gaussianHigherMomentLatticeConstant_nonneg r hσ1
  calc
    _ ≤ ∑ b ∈ Icc 1 (U * V), Real.log ((U * V : ℕ) : ℝ) *
        ((gaussianHigherMomentLatticeConstant r σ *
          (2 : ℝ) ^ (((2 * r : ℕ) + σ - 1) / 2)) *
          ((U * V : ℕ) : ℝ) ^ (2 * r - 1) * t ^ (2 * r) *
            X ^ (1 - σ - (2 * r : ℕ))) := by
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro b hb
      have hb1 := (mem_Icc.mp hb).1
      have hbK : (b : ℝ) ≤ ((U * V : ℕ) : ℝ) := by exact_mod_cast (mem_Icc.mp hb).2
      have hbc : ‖(c b : ℂ)‖ ≤ Real.log ((U * V : ℕ) : ℝ) := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact (abs_truncAF_conv_le_log U V b).trans
          (Real.log_le_log (by exact_mod_cast (show 0 < b by omega)) hbK)
      have hf := norm_tsum_gaussianHigherPrimeMomentWeight_dilate_sub_pole_le
        r hr hσ1 ht hε hsector hX hscale hb1
      have hfK : ‖(∑' a : ℕ, gaussianHigherPrimeMomentWeight r σ t ε (a * b)) -
          (b : ℂ)⁻¹ * gaussianHigherMomentPole r ((σ : ℂ) + t * I) ε t‖ ≤
          (gaussianHigherMomentLatticeConstant r σ *
            (2 : ℝ) ^ (((2 * r : ℕ) + σ - 1) / 2)) *
          ((U * V : ℕ) : ℝ) ^ (2 * r - 1) * t ^ (2 * r) *
            X ^ (1 - σ - (2 * r : ℕ)) := by
        apply hf.trans
        gcongr
      have hh := mul_le_mul hbc hfK (norm_nonneg _) hlog
      rw [← norm_mul] at hh
      convert hh using 1
      congr 1
      dsimp only [c]
      ring
    _ = _ := by
      simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      have hpow : ((U * V : ℕ) : ℝ) ^ (2 * r) =
          ((U * V : ℕ) : ℝ) ^ (2 * r - 1) * ((U * V : ℕ) : ℝ) := by
        calc
          _ = ((U * V : ℕ) : ℝ) ^ (2 * r - 1 + 1) := by
            rw [show 2 * r - 1 + 1 = 2 * r by omega]
          _ = _ := pow_succ _ _
      rw [hpow]
      ring

#print axioms norm_tsum_gaussianHigherPrimeMomentWeight_dilate_sub_pole_le
#print axioms norm_tsum_gaussianHigherMoment_zeta_trunc_conv_sub_pole_le

end GaloisForLFunctions.ExceptionalLayerTheory
