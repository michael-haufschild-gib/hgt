import GaloisForLFunctions.ExceptionalLayerTheory.GaussianSecondVariation
import GaloisForLFunctions.ExceptionalLayerTheory.GaussianMomentTypeIPole

/-!
# Second-order pole subtraction for the actual first Vaughan type-I term

Trapezoidal cancellation yields an extra factor `UV t / X` in the
pole-subtracted error when the arithmetic divisor support lies below `X/t`.
-/

open Complex Finset Filter Topology RHTower RHTower.Sieve ArithmeticFunction

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

private theorem gaussianPrimeMomentWeight_zero (σ α ξ t : ℝ) :
    gaussianPrimeMomentWeight σ α ξ t 0 = 0 := by
  simp [gaussianPrimeMomentWeight]

private theorem tsum_gaussianPrimeMomentWeight_dilate_eq {σ α : ℝ} (hσ : 0 ≤ σ)
    (hα : 0 < α) (ξ t : ℝ) {b : ℕ} (hb : 1 ≤ b) :
    (∑' a : ℕ, gaussianPrimeMomentWeight σ α ξ t (a * b)) =
      (((α : ℂ) - ξ * I) / t) * ∑' a : ℕ,
        gaussianMellinWeight (2 - ((σ : ℂ) + t * I)) ((α : ℂ) - ξ * I)
          ((b : ℝ) * (a + 1)) := by
  have hh := (summable_gaussianPrimeMomentWeight_dilate hσ hα ξ t hb).sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, zero_mul, gaussianPrimeMomentWeight_zero, zero_add] at hh
  rw [← hh, ← tsum_mul_left]
  apply tsum_congr
  intro a
  rw [gaussianPrimeMomentWeight_eq_mellin σ α ξ t (Nat.mul_pos (Nat.succ_pos a) (by omega) : 1 ≤ (a + 1) * b)]
  congr 2
  push_cast
  ring

private theorem norm_damping_le_sector {α ξ t : ℝ} (hα : 0 < α)
    (hαξ : α ≤ ξ) (hξ : ξ ≤ 2 * α * t) :
    ‖(α : ℂ) - ξ * I‖ ≤ 4 * α * t := by
  have hξ0 : 0 < ξ := hα.trans_le hαξ
  calc
    _ ≤ ‖(α : ℂ)‖ + ‖(ξ : ℂ) * I‖ := norm_sub_le _ _
    _ = α + ξ := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hα, abs_of_pos hξ0]
    _ ≤ _ := by linarith

private theorem tsum_zeta_conv_gaussianMoment_eq {σ α ξ t : ℝ}
    (hσ : 0 ≤ σ) (hα : 0 < α) (hαξ : α ≤ ξ) (ht : 0 < t)
    (hξ : ξ ≤ 2 * α * t) (c : ArithmeticFunction ℝ) (K : ℕ)
    (hc : ∀ b, K < b → c b = 0) :
    (∑' n : ℕ, ((((zeta : ArithmeticFunction ℝ) * c) n : ℝ) : ℂ) *
      gaussianPrimeMomentWeight σ α ξ t n) =
      ∑ b ∈ Icc 1 K, (c b : ℂ) *
        ∑' a : ℕ, gaussianPrimeMomentWeight σ α ξ t (a * b) := by
  let W := gaussianPrimeMomentWeight σ α ξ t
  have hc0 (b : ℕ) (hb : b ∉ Icc 1 K) : c b = 0 := by
    by_cases h0 : b = 0
    · simp [h0]
    · exact hc b (by simp only [mem_Icc] at hb; omega)
  have hA : Summable (fun b : ℕ => |c b| * (b : ℝ) ^ 2) :=
    summable_of_ne_finset_zero (s := Icc 1 K) fun b hb => by rw [hc0 b hb]; simp
  have hB := RHTower.summable_pow_mul_exp_neg_nat_sq 2 hα
  have hmajor := (hA.mul_of_nonneg hB (fun b => by positivity)
    (fun a => by positivity)).mul_left (4 * α)
  have hprod : Summable (fun p : ℕ × ℕ => (c p.1 : ℂ) *
      (((zeta : ArithmeticFunction ℝ) p.2 : ℝ) : ℂ) * W (p.1 * p.2)) := by
    apply hmajor.of_norm_bounded
    rintro ⟨b, a⟩
    by_cases hb : b = 0
    · simp [hb]
    by_cases ha : a = 0
    · simp [ha]
    have hb1 : 1 ≤ b := by omega
    have ha1 : 1 ≤ a := by omega
    have hn : 1 ≤ b * a := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hb ha)
    have hnr : (1 : ℝ) ≤ (b * a : ℕ) := by exact_mod_cast hn
    have hp : ((b * a : ℕ) : ℝ) ^ (2 - σ) ≤ ((b * a : ℕ) : ℝ) ^ (2 : ℕ) := by
      simpa only [Real.rpow_two] using
        Real.rpow_le_rpow_of_exponent_le hnr (by linarith : 2 - σ ≤ 2)
    have haR : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb1
    have hab : (a : ℝ) ≤ (b * a : ℕ) := by
      push_cast
      nlinarith
    have he : Real.exp (-α * ((b * a : ℕ) : ℝ) ^ 2) ≤
        Real.exp (-α * (a : ℝ) ^ 2) := by
      rw [Real.exp_le_exp]
      have hs := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ haR hab 2) hα.le
      linarith only [hs]
    have hW := norm_gaussianPrimeMomentWeight_le σ hα.le hαξ ht hξ hn
    have hz : (((zeta : ArithmeticFunction ℝ) a : ℝ) : ℂ) = 1 := by simp [ha]
    rw [hz, mul_one, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ |c b| * (4 * α * ((b * a : ℕ) : ℝ) ^ (2 - σ) *
          Real.exp (-α * ((b * a : ℕ) : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left hW (abs_nonneg _)
      _ ≤ |c b| * (4 * α * ((b * a : ℕ) : ℝ) ^ 2 *
          Real.exp (-α * (a : ℝ) ^ 2)) := by gcongr
      _ = _ := by push_cast; ring
  have hh := RHTower.ExactNullDivisorTransfer.tsum_tsum_mul_comp_mul
    (a := fun b => (c b : ℂ))
    (b := fun a => (((zeta : ArithmeticFunction ℝ) a : ℝ) : ℂ))
    (f := W) (by simp) (by simp) hprod
  have hconv (n : ℕ) : LSeries.convolution (fun b => (c b : ℂ))
      (fun a => (((zeta : ArithmeticFunction ℝ) a : ℝ) : ℂ)) n =
        ((((zeta : ArithmeticFunction ℝ) * c) n : ℝ) : ℂ) := by
    rw [LSeries.convolution_def, mul_comm (zeta : ArithmeticFunction ℝ) c,
      ArithmeticFunction.mul_apply]
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
    · simp [ha, W, gaussianPrimeMomentWeight_zero]
    · simp [ha, Nat.mul_comm]
  simp_rw [hrow]
  exact tsum_eq_sum fun b hb => by rw [hc0 b hb]; simp


/-- The exact arithmetic divisor fibre inherits the second-order lattice error. -/
theorem norm_tsum_gaussianPrimeMomentWeight_dilate_sub_pole_second_physical_le
    {σ α ξ t X : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ < 1) (hα : 0 < α) (hαξ : α ≤ ξ)
    (ht : 2 ≤ t) (hξ : ξ ≤ 2 * α * t) (hX : 0 < X) (hscale : α * X ^ 2 = 2)
    {b : ℕ} (hb : 1 ≤ b) :
    ‖(∑' a : ℕ, gaussianPrimeMomentWeight σ α ξ t (a * b)) -
      (b : ℂ)⁻¹ * gaussianFirstMomentPole ((σ : ℂ) + t * I) ((α : ℂ) - ξ * I) t‖ ≤
      2 * gaussianSecondMomentLatticeConstant σ * b * t ^ 2 * X ^ (-1 - σ) := by
  rw [tsum_gaussianPrimeMomentWeight_dilate_eq hσ hα ξ t hb]
  have he : ((α : ℂ) - ξ * I).re = α := by simp
  simpa only [he, Complex.ofReal_natCast] using
    norm_tsum_gaussianFirstMoment_sub_pole_second_physical_le
      (ε := (α : ℂ) - ξ * I) hσ hσ1 ht (by simpa only [he] using hα)
      (by simpa only [he] using norm_damping_le_sector hα hαξ hξ)
      hX (by simpa only [he] using hscale)
      (by exact_mod_cast (show 0 < b by omega) : (0 : ℝ) < b)

/-- For the actual truncated Mangoldt--Möbius convolution, the signed pole
coefficient is exact and the remainder gains another power of `X`. -/
theorem norm_tsum_gaussianMoment_zeta_trunc_conv_sub_pole_second_physical_le
    {σ α ξ t X : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ < 1) (hα : 0 < α) (hαξ : α ≤ ξ)
    (ht : 2 ≤ t) (hξ : ξ ≤ 2 * α * t) (hX : 0 < X) (hscale : α * X ^ 2 = 2)
    {U V : ℕ} (hUV : 1 ≤ U * V) :
    ‖(∑' n : ℕ,
        ((((zeta : ArithmeticFunction ℝ) * (truncAF vonMangoldt U *
          truncAF (moebius : ArithmeticFunction ℝ) V)) n : ℝ) : ℂ) *
            gaussianPrimeMomentWeight σ α ξ t n) -
      (∑ b ∈ Icc 1 (U * V),
        (((truncAF vonMangoldt U * truncAF (moebius : ArithmeticFunction ℝ) V) b : ℝ) : ℂ) /
          (b : ℂ)) * gaussianFirstMomentPole ((σ : ℂ) + t * I) ((α : ℂ) - ξ * I) t‖ ≤
      2 * gaussianSecondMomentLatticeConstant σ * t ^ 2 * X ^ (-1 - σ) *
        ((U * V : ℕ) : ℝ) ^ 2 * Real.log ((U * V : ℕ) : ℝ) := by
  let c := truncAF vonMangoldt U * truncAF (moebius : ArithmeticFunction ℝ) V
  have hsupp (b : ℕ) (hb : U * V < b) : c b = 0 := truncAF_conv_apply_of_gt hb
  rw [tsum_zeta_conv_gaussianMoment_eq hσ hα hαξ (by linarith) hξ c (U * V) hsupp,
    Finset.sum_mul, ← sum_sub_distrib]
  have hlog : 0 ≤ Real.log ((U * V : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast hUV)
  have hC := gaussianSecondMomentLatticeConstant_nonneg hσ1
  calc
    _ ≤ ∑ b ∈ Icc 1 (U * V), Real.log ((U * V : ℕ) : ℝ) *
        (2 * gaussianSecondMomentLatticeConstant σ * ((U * V : ℕ) : ℝ) *
          t ^ 2 * X ^ (-1 - σ)) := by
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro b hb
      have hb1 := (mem_Icc.mp hb).1
      have hbK : (b : ℝ) ≤ ((U * V : ℕ) : ℝ) := by exact_mod_cast (mem_Icc.mp hb).2
      have hbc : ‖(c b : ℂ)‖ ≤ Real.log ((U * V : ℕ) : ℝ) := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact (abs_truncAF_conv_le_log U V b).trans
          (Real.log_le_log (by exact_mod_cast (show 0 < b by omega)) hbK)
      have hf := norm_tsum_gaussianPrimeMomentWeight_dilate_sub_pole_second_physical_le
        hσ hσ1 hα hαξ ht hξ hX hscale hb1
      have hfK : ‖(∑' a : ℕ, gaussianPrimeMomentWeight σ α ξ t (a * b)) -
          (b : ℂ)⁻¹ * gaussianFirstMomentPole ((σ : ℂ) + t * I) ((α : ℂ) - ξ * I) t‖ ≤
          2 * gaussianSecondMomentLatticeConstant σ * ((U * V : ℕ) : ℝ) *
            t ^ 2 * X ^ (-1 - σ) := by
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
      ring

#print axioms norm_tsum_gaussianPrimeMomentWeight_dilate_sub_pole_second_physical_le
#print axioms norm_tsum_gaussianMoment_zeta_trunc_conv_sub_pole_second_physical_le

end GaloisForLFunctions.ExceptionalLayerTheory
