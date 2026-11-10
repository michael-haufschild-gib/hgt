import GaloisForLFunctions.ExceptionalLayerTheory.GaussianLogarithmicContinuum
import GaloisForLFunctions.ExceptionalLayerTheory.GaussianMomentTypeIPole

/-!
# The signed main terms of logarithmic Gaussian type I

The actual `log * μ_V` convolution separates into two signed reciprocal
Möbius masses times continuous Gaussian moments. Its lattice error gains
one power of the Gaussian length.
-/

open Complex Finset Filter Topology RHTower RHTower.Sieve ArithmeticFunction

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

private theorem log_gaussianPrimeMomentWeight_dilate_eq (σ α ξ t : ℝ)
    {b : ℕ} (hb : 1 ≤ b) (a : ℕ) :
    (Real.log ((a : ℝ) + 1) : ℂ) * gaussianPrimeMomentWeight σ α ξ t ((a + 1) * b) =
      (((α : ℂ) - ξ * I) / t) *
        gaussianLogMellinWeight (2 - ((σ : ℂ) + t * I)) ((α : ℂ) - ξ * I)
          b ((b : ℝ) * (a + 1)) := by
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
  rw [gaussianPrimeMomentWeight_eq_mellin σ α ξ t
    (Nat.mul_pos (Nat.succ_pos a) (by omega) : 1 ≤ (a + 1) * b)]
  unfold gaussianLogMellinWeight
  have hd : (b : ℝ) * ((a : ℝ) + 1) / b = (a : ℝ) + 1 := by field_simp
  rw [hd]
  have he : (((a + 1) * b : ℕ) : ℝ) = (b : ℝ) * (a + 1) := by push_cast; ring
  rw [he]
  ring

/-- Absolute convergence of every logarithmic divisor fibre. -/
theorem summable_log_gaussianPrimeMomentWeight_dilate {σ α : ℝ} (hσ : 0 ≤ σ)
    (hα : 0 < α) (ξ t : ℝ) {b : ℕ} (hb : 1 ≤ b) :
    Summable (fun a : ℕ => (Real.log (a : ℝ) : ℂ) *
      gaussianPrimeMomentWeight σ α ξ t (a * b)) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hw2 : (2 - ((σ : ℂ) + t * I)).re ≤ 2 := by simp; linarith
  have hε : 0 < ((α : ℂ) - ξ * I).re := by simpa using hα
  have hh := (summable_gaussianLogMellinWeight_lattice hw2 hε hbR hbR).mul_left
    (((α : ℂ) - ξ * I) / t)
  apply (summable_nat_add_iff 1).mp
  refine hh.congr fun a => ?_
  simpa only [Nat.cast_add, Nat.cast_one] using
    (log_gaussianPrimeMomentWeight_dilate_eq σ α ξ t hb a).symm

private theorem tsum_log_gaussianPrimeMomentWeight_dilate_eq {σ α : ℝ} (hσ : 0 ≤ σ)
    (hα : 0 < α) (ξ t : ℝ) {b : ℕ} (hb : 1 ≤ b) :
    (∑' a : ℕ, (Real.log (a : ℝ) : ℂ) * gaussianPrimeMomentWeight σ α ξ t (a * b)) =
      (((α : ℂ) - ξ * I) / t) * ∑' a : ℕ,
        gaussianLogMellinWeight (2 - ((σ : ℂ) + t * I)) ((α : ℂ) - ξ * I)
          b ((b : ℝ) * (a + 1)) := by
  have hh := (summable_log_gaussianPrimeMomentWeight_dilate hσ hα ξ t hb).sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, Nat.cast_zero, Real.log_zero, Complex.ofReal_zero,
    zero_mul, zero_add] at hh
  rw [← hh, ← tsum_mul_left]
  apply tsum_congr
  intro a
  simpa only [Nat.cast_add, Nat.cast_one] using
    log_gaussianPrimeMomentWeight_dilate_eq σ α ξ t hb a

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

/-- The actual logarithmic fibre has two signed continuous main terms. -/
theorem norm_tsum_log_gaussianPrimeMomentWeight_dilate_sub_poles_le {σ α ξ t X : ℝ}
    (hσ : 0 ≤ σ) (hσ1 : σ < 1) (hα : 0 < α) (hαξ : α ≤ ξ)
    (ht : 2 ≤ t) (hξ : ξ ≤ 2 * α * t) (hX : 0 < X) (hscale : α * X ^ 2 = 2)
    {b : ℕ} (hb : 1 ≤ b) :
    ‖(∑' a : ℕ, (Real.log (a : ℝ) : ℂ) * gaussianPrimeMomentWeight σ α ξ t (a * b)) -
      (b : ℂ)⁻¹ * (gaussianFirstMomentLogPole ((σ : ℂ) + t * I) ((α : ℂ) - ξ * I) t -
        (Real.log (b : ℝ) : ℂ) * gaussianFirstMomentPole ((σ : ℂ) + t * I) ((α : ℂ) - ξ * I) t)‖ ≤
      gaussianLogFirstMomentConstant σ * t * X ^ (-σ) * (1 + |Real.log (X / b)|) := by
  rw [tsum_log_gaussianPrimeMomentWeight_dilate_eq hσ hα ξ t hb]
  have he : ((α : ℂ) - ξ * I).re = α := by simp
  simpa only [he, Complex.ofReal_natCast] using
    norm_tsum_gaussianLogFirstMoment_sub_poles_physical_le (ε := (α : ℂ) - ξ * I)
      hσ hσ1 ht (by simpa only [he] using hα)
      (by simpa only [he] using norm_damping_le_sector hα hαξ hξ) hX
      (by simpa only [he] using hscale)
      (by exact_mod_cast (show 0 < b by omega) : (0 : ℝ) < b)

private theorem tsum_log_conv_gaussianMoment_eq {σ α ξ t : ℝ}
    (hσ : 0 ≤ σ) (hα : 0 < α) (hαξ : α ≤ ξ) (ht : 0 < t)
    (hξ : ξ ≤ 2 * α * t) (c : ArithmeticFunction ℝ) (K : ℕ)
    (hc : ∀ b, K < b → c b = 0) :
    (∑' n : ℕ, (((ArithmeticFunction.log * c) n : ℝ) : ℂ) *
      gaussianPrimeMomentWeight σ α ξ t n) =
      ∑ b ∈ Icc 1 K, (c b : ℂ) *
        ∑' a : ℕ, (Real.log (a : ℝ) : ℂ) * gaussianPrimeMomentWeight σ α ξ t (a * b) := by
  let W := gaussianPrimeMomentWeight σ α ξ t
  have hc0 (b : ℕ) (hb : b ∉ Icc 1 K) : c b = 0 := by
    by_cases h0 : b = 0
    · simp [h0]
    · exact hc b (by simp only [mem_Icc] at hb; omega)
  have hA : Summable (fun b : ℕ => |c b| * (b : ℝ) ^ 2) :=
    summable_of_ne_finset_zero (s := Icc 1 K) fun b hb => by rw [hc0 b hb]; simp
  have hB := RHTower.summable_pow_mul_exp_neg_nat_sq 3 hα
  have hmajor := (hA.mul_of_nonneg hB (fun b => by positivity)
    (fun a => by positivity)).mul_left (4 * α)
  have hprod : Summable (fun p : ℕ × ℕ => (c p.1 : ℂ) *
      ((ArithmeticFunction.log p.2 : ℝ) : ℂ) * W (p.1 * p.2)) := by
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
    have hlog0 := Real.log_natCast_nonneg a
    have hloga : Real.log (a : ℝ) ≤ a := by
      have hh := Real.log_le_sub_one_of_pos (show (0 : ℝ) < a by exact_mod_cast (show 0 < a by omega))
      linarith
    change ‖(c b : ℂ) * (Real.log (a : ℝ) : ℂ) * W (b * a)‖ ≤ _
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlog0]
    calc
      _ ≤ |c b| * (a : ℝ) * (4 * α * ((b * a : ℕ) : ℝ) ^ (2 - σ) *
          Real.exp (-α * ((b * a : ℕ) : ℝ) ^ 2)) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left hloga (abs_nonneg _)) hW
          (norm_nonneg _) (by positivity)
      _ ≤ |c b| * (a : ℝ) * (4 * α * ((b * a : ℕ) : ℝ) ^ 2 *
          Real.exp (-α * (a : ℝ) ^ 2)) := by gcongr
      _ = _ := by push_cast; ring
  have hh := RHTower.ExactNullDivisorTransfer.tsum_tsum_mul_comp_mul
    (a := fun b => (c b : ℂ))
    (b := fun a => ((ArithmeticFunction.log a : ℝ) : ℂ))
    (f := W) (by simp) (by simp) hprod
  have hconv (n : ℕ) : LSeries.convolution (fun b => (c b : ℂ))
      (fun a => ((ArithmeticFunction.log a : ℝ) : ℂ)) n =
        (((ArithmeticFunction.log * c) n : ℝ) : ℂ) := by
    rw [LSeries.convolution_def, mul_comm ArithmeticFunction.log c,
      ArithmeticFunction.mul_apply]
    push_cast
    rfl
  simp_rw [hconv] at hh
  rw [← hh]
  have hrow (b : ℕ) : (∑' a : ℕ, (c b : ℂ) *
      ((ArithmeticFunction.log a : ℝ) : ℂ) * W (b * a)) =
        (c b : ℂ) * ∑' a : ℕ, (Real.log (a : ℝ) : ℂ) * W (a * b) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro a
    change (c b : ℂ) * (Real.log (a : ℝ) : ℂ) * W (b * a) =
      (c b : ℂ) * ((Real.log (a : ℝ) : ℂ) * W (a * b))
    rw [Nat.mul_comm b a]
    ring
  simp_rw [hrow]
  exact tsum_eq_sum fun b hb => by rw [hc0 b hb]; simp


/-- The complete logarithmic type-I convolution, with both signed Möbius
masses exact and only the lattice remainder estimated absolutely. -/
theorem norm_tsum_gaussianMoment_log_trunc_moebius_sub_poles_le {σ α ξ t X : ℝ}
    (hσ : 0 ≤ σ) (hσ1 : σ < 1) (hα : 0 < α) (hαξ : α ≤ ξ)
    (ht : 2 ≤ t) (hξ : ξ ≤ 2 * α * t) (hX : 0 < X) (hscale : α * X ^ 2 = 2)
    {V : ℕ} (hVX : (V : ℝ) ≤ X) :
    ‖(∑' n : ℕ,
        (((ArithmeticFunction.log * truncAF (moebius : ArithmeticFunction ℝ) V) n : ℝ) : ℂ) *
          gaussianPrimeMomentWeight σ α ξ t n) -
      ((∑ b ∈ Icc 1 V, ((truncAF (moebius : ArithmeticFunction ℝ) V b : ℝ) : ℂ) / (b : ℂ)) *
          gaussianFirstMomentLogPole ((σ : ℂ) + t * I) ((α : ℂ) - ξ * I) t -
        (∑ b ∈ Icc 1 V, ((truncAF (moebius : ArithmeticFunction ℝ) V b : ℝ) : ℂ) *
          (Real.log (b : ℝ) : ℂ) / (b : ℂ)) *
          gaussianFirstMomentPole ((σ : ℂ) + t * I) ((α : ℂ) - ξ * I) t)‖ ≤
      gaussianLogFirstMomentConstant σ * t * X ^ (-σ) * (1 + Real.log X) * V := by
  let c := truncAF (moebius : ArithmeticFunction ℝ) V
  let P := gaussianFirstMomentPole ((σ : ℂ) + t * I) ((α : ℂ) - ξ * I) t
  let L := gaussianFirstMomentLogPole ((σ : ℂ) + t * I) ((α : ℂ) - ξ * I) t
  have hsupp (b : ℕ) (hb : V < b) : c b = 0 := truncAF_apply_of_gt hb
  have hm : (∑ b ∈ Icc 1 V, (c b : ℂ) / (b : ℂ)) * L -
      (∑ b ∈ Icc 1 V, (c b : ℂ) * (Real.log (b : ℝ) : ℂ) / (b : ℂ)) * P =
        ∑ b ∈ Icc 1 V, (c b : ℂ) * ((b : ℂ)⁻¹ * (L - (Real.log (b : ℝ) : ℂ) * P)) := by
    rw [sum_mul, sum_mul, ← sum_sub_distrib]
    apply sum_congr rfl
    intro b _
    ring
  rw [tsum_log_conv_gaussianMoment_eq hσ hα hαξ (by linarith) hξ c V hsupp,
    hm, ← sum_sub_distrib]
  have hC := gaussianLogFirstMomentConstant_nonneg hσ1
  calc
    _ ≤ ∑ b ∈ Icc 1 V,
        gaussianLogFirstMomentConstant σ * t * X ^ (-σ) * (1 + Real.log X) := by
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro b hb
      have hb1 := (mem_Icc.mp hb).1
      have hbR : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
      have hbR1 : (1 : ℝ) ≤ b := by exact_mod_cast hb1
      have hbX : (b : ℝ) ≤ X :=
        (by exact_mod_cast (mem_Icc.mp hb).2 : (b : ℝ) ≤ V).trans hVX
      have hlog : |Real.log (X / b)| ≤ Real.log X := by
        have hnonneg : 0 ≤ Real.log (X / b) :=
          Real.log_nonneg ((le_div_iff₀ hbR).mpr (by simpa using hbX))
        rw [abs_of_nonneg hnonneg, Real.log_div hX.ne' hbR.ne']
        linarith [Real.log_nonneg hbR1]
      have hc : ‖(c b : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact abs_truncAF_moebius_le_one V b
      have hh := mul_le_mul hc
        (norm_tsum_log_gaussianPrimeMomentWeight_dilate_sub_poles_le
          hσ hσ1 hα hαξ ht hξ hX hscale hb1)
        (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      rw [one_mul, ← norm_mul] at hh
      have he : (c b : ℂ) * (∑' a : ℕ, (Real.log (a : ℝ) : ℂ) *
          gaussianPrimeMomentWeight σ α ξ t (a * b)) -
          (c b : ℂ) * ((b : ℂ)⁻¹ * (L - (Real.log (b : ℝ) : ℂ) * P)) =
        (c b : ℂ) * ((∑' a : ℕ, (Real.log (a : ℝ) : ℂ) *
          gaussianPrimeMomentWeight σ α ξ t (a * b)) -
          (b : ℂ)⁻¹ * (L - (Real.log (b : ℝ) : ℂ) * P)) := by ring
      rw [he]
      apply hh.trans
      gcongr
    _ = _ := by
      simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      ring

#print axioms summable_log_gaussianPrimeMomentWeight_dilate
#print axioms norm_tsum_log_gaussianPrimeMomentWeight_dilate_sub_poles_le
#print axioms norm_tsum_gaussianMoment_log_trunc_moebius_sub_poles_le

end GaloisForLFunctions.ExceptionalLayerTheory
