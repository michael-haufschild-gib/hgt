import GaloisForLFunctions.ExceptionalLayerTheory.GaussianHigherLogLattice
import GaloisForLFunctions.ExceptionalLayerTheory.GaussianHigherMomentTypeIPole

/-!
# Signed logarithmic type I for higher Gaussian moments

The actual logarithm–Möbius convolution retains both signed continuum
masses. First variation bounds its remainder by `O(VtX^(-σ)(1+log X))`
for every positive moment order.
-/

open Complex Finset Filter Topology RHTower RHTower.Sieve ArithmeticFunction
noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

private theorem log_higherMomentWeight_dilate_eq (r : ℕ) (σ t : ℝ) (ε : ℂ)
    {b : ℕ} (hb : 1 ≤ b) (a : ℕ) :
    (Real.log ((a : ℝ) + 1) : ℂ) * gaussianHigherPrimeMomentWeight r σ t ε ((a + 1) * b) =
      (ε / (t : ℂ)) ^ r *
        gaussianLogMellinWeight (((2 * r : ℕ) : ℂ) - ((σ : ℂ) + t * I)) ε
          b ((b : ℝ) * (a + 1)) := by
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
  unfold gaussianHigherPrimeMomentWeight gaussianLogMellinWeight
  have hd : (b : ℝ) * ((a : ℝ) + 1) / b = (a : ℝ) + 1 := by field_simp
  rw [hd]
  have he : (((a + 1) * b : ℕ) : ℝ) = (b : ℝ) * (a + 1) := by push_cast; ring
  rw [he]
  ring

/-- Absolute convergence of every logarithmic higher-moment divisor fibre. -/
theorem summable_log_gaussianHigherMoment_dilate (r : ℕ) (σ t : ℝ) {ε : ℂ}
    (hε : 0 < ε.re) {b : ℕ} (hb : 1 ≤ b) :
    Summable (fun a : ℕ => (Real.log (a : ℝ) : ℂ) *
      gaussianHigherPrimeMomentWeight r σ t ε (a * b)) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hh := (summable_gaussianLogMellinWeight_lattice_all
    (w := ((2 * r : ℕ) : ℂ) - ((σ : ℂ) + t * I)) hε hbR hbR).mul_left ((ε / (t : ℂ)) ^ r)
  apply (summable_nat_add_iff 1).mp
  refine hh.congr fun a => ?_
  simpa only [Nat.cast_add, Nat.cast_one] using
    (log_higherMomentWeight_dilate_eq r σ t ε hb a).symm

private theorem tsum_log_higherMomentWeight_dilate_eq (r : ℕ) (σ t : ℝ) {ε : ℂ}
    (hε : 0 < ε.re) {b : ℕ} (hb : 1 ≤ b) :
    (∑' a : ℕ, (Real.log (a : ℝ) : ℂ) * gaussianHigherPrimeMomentWeight r σ t ε (a * b)) =
      (ε / (t : ℂ)) ^ r * ∑' a : ℕ,
        gaussianLogMellinWeight (((2 * r : ℕ) : ℂ) - ((σ : ℂ) + t * I)) ε
          b ((b : ℝ) * (a + 1)) := by
  have hh := (summable_log_gaussianHigherMoment_dilate r σ t hε hb).sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, Nat.cast_zero, Real.log_zero, Complex.ofReal_zero,
    zero_mul, zero_add] at hh
  rw [← hh, ← tsum_mul_left]
  apply tsum_congr
  intro a
  simpa only [Nat.cast_add, Nat.cast_one] using log_higherMomentWeight_dilate_eq r σ t ε hb a

/-- The logarithmic divisor fibre has two signed higher-moment poles. -/
theorem norm_tsum_log_gaussianHigherMoment_dilate_sub_poles_le (r : ℕ) (hr : r ≠ 0)
    {σ t X : ℝ} {ε : ℂ} (hσ : 0 ≤ σ) (hσ1 : σ < 1) (ht : 1 ≤ t)
    (hε : 0 < ε.re) (hsector : ‖ε‖ ≤ 4 * ε.re * t)
    (hX : 0 < X) (hscale : ε.re * X ^ 2 = 2) {b : ℕ} (hb : 1 ≤ b) :
    ‖(∑' a : ℕ, (Real.log (a : ℝ) : ℂ) * gaussianHigherPrimeMomentWeight r σ t ε (a * b)) -
      (b : ℂ)⁻¹ * (gaussianHigherMomentLogPole r ((σ : ℂ) + t * I) ε t -
        (Real.log (b : ℝ) : ℂ) * gaussianHigherMomentPole r ((σ : ℂ) + t * I) ε t)‖ ≤
      gaussianHigherLogMomentConstant r σ * t * X ^ (-σ) * (1 + |Real.log (X / b)|) := by
  rw [tsum_log_higherMomentWeight_dilate_eq r σ t hε hb]
  simpa only [Complex.ofReal_natCast] using
    norm_tsum_gaussianHigherLogMoment_sub_poles_le r hr hσ hσ1 ht hε hsector hX hscale
      (by exact_mod_cast (show 0 < b by omega) : (0 : ℝ) < b)

private theorem tsum_log_conv_higherMoment_eq (r : ℕ) {σ t : ℝ} {ε : ℂ}
    (hσ : 0 ≤ σ) (hε : 0 < ε.re) (c : ArithmeticFunction ℝ) (K : ℕ)
    (hc : ∀ b, K < b → c b = 0) :
    (∑' n : ℕ, (((ArithmeticFunction.log * c) n : ℝ) : ℂ) *
      gaussianHigherPrimeMomentWeight r σ t ε n) =
      ∑ b ∈ Icc 1 K, (c b : ℂ) *
        ∑' a : ℕ, (Real.log (a : ℝ) : ℂ) * gaussianHigherPrimeMomentWeight r σ t ε (a * b) := by
  let W := gaussianHigherPrimeMomentWeight r σ t ε
  have hc0 (b : ℕ) (hb : b ∉ Icc 1 K) : c b = 0 := by
    by_cases h0 : b = 0
    · simp [h0]
    · exact hc b (by simp only [mem_Icc] at hb; omega)
  have hA : Summable (fun b : ℕ => |c b| * (b : ℝ) ^ (2 * r)) :=
    summable_of_ne_finset_zero (s := Icc 1 K) fun b hb => by rw [hc0 b hb]; simp
  have hB := RHTower.summable_pow_mul_exp_neg_nat_sq (2 * r + 1) hε
  have hmajor := (hA.mul_of_nonneg hB (fun b => by positivity)
    (fun a => by positivity)).mul_left ‖(ε / (t : ℂ)) ^ r‖
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
    have haR : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb1
    have hab : (a : ℝ) ≤ (b * a : ℕ) := by
      push_cast
      nlinarith
    have he : Real.exp (-ε.re * ((b * a : ℕ) : ℝ) ^ 2) ≤
        Real.exp (-ε.re * (a : ℝ) ^ 2) := by
      rw [Real.exp_le_exp]
      have hs := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ haR hab 2) hε.le
      linarith only [hs]
    have hW := norm_gaussianHigherPrimeMomentWeight_le r hσ t ε hn
    have hlog0 := Real.log_natCast_nonneg a
    have hloga : Real.log (a : ℝ) ≤ a := by
      have hh := Real.log_le_sub_one_of_pos (show (0 : ℝ) < a by exact_mod_cast (show 0 < a by omega))
      linarith
    change ‖(c b : ℂ) * (Real.log (a : ℝ) : ℂ) * W (b * a)‖ ≤ _
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlog0]
    calc
      _ ≤ |c b| * (a : ℝ) * (‖(ε / (t : ℂ)) ^ r‖ * ((b * a : ℕ) : ℝ) ^ (2 * r) *
          Real.exp (-ε.re * ((b * a : ℕ) : ℝ) ^ 2)) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left hloga (abs_nonneg _)) hW
          (norm_nonneg _) (by positivity)
      _ ≤ |c b| * (a : ℝ) * (‖(ε / (t : ℂ)) ^ r‖ * ((b * a : ℕ) : ℝ) ^ (2 * r) *
          Real.exp (-ε.re * (a : ℝ) ^ 2)) := by gcongr
      _ = _ := by push_cast; rw [mul_pow, pow_succ]; ring
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
theorem norm_tsum_gaussianHigherMoment_log_trunc_moebius_sub_poles_le (r : ℕ) (hr : r ≠ 0)
    {σ t X : ℝ} {ε : ℂ} (hσ : 0 ≤ σ) (hσ1 : σ < 1) (ht : 1 ≤ t)
    (hε : 0 < ε.re) (hsector : ‖ε‖ ≤ 4 * ε.re * t)
    (hX : 0 < X) (hscale : ε.re * X ^ 2 = 2)
    {V : ℕ} (hVX : (V : ℝ) ≤ X) :
    ‖(∑' n : ℕ,
        (((ArithmeticFunction.log * truncAF (moebius : ArithmeticFunction ℝ) V) n : ℝ) : ℂ) *
          gaussianHigherPrimeMomentWeight r σ t ε n) -
      ((∑ b ∈ Icc 1 V, ((truncAF (moebius : ArithmeticFunction ℝ) V b : ℝ) : ℂ) / (b : ℂ)) *
          gaussianHigherMomentLogPole r ((σ : ℂ) + t * I) ε t -
        (∑ b ∈ Icc 1 V, ((truncAF (moebius : ArithmeticFunction ℝ) V b : ℝ) : ℂ) *
          (Real.log (b : ℝ) : ℂ) / (b : ℂ)) *
          gaussianHigherMomentPole r ((σ : ℂ) + t * I) ε t)‖ ≤
      gaussianHigherLogMomentConstant r σ * t * X ^ (-σ) * (1 + Real.log X) * V := by
  let c := truncAF (moebius : ArithmeticFunction ℝ) V
  let P := gaussianHigherMomentPole r ((σ : ℂ) + t * I) ε t
  let L := gaussianHigherMomentLogPole r ((σ : ℂ) + t * I) ε t
  have hsupp (b : ℕ) (hb : V < b) : c b = 0 := truncAF_apply_of_gt hb
  have hm : (∑ b ∈ Icc 1 V, (c b : ℂ) / (b : ℂ)) * L -
      (∑ b ∈ Icc 1 V, (c b : ℂ) * (Real.log (b : ℝ) : ℂ) / (b : ℂ)) * P =
        ∑ b ∈ Icc 1 V, (c b : ℂ) * ((b : ℂ)⁻¹ * (L - (Real.log (b : ℝ) : ℂ) * P)) := by
    rw [sum_mul, sum_mul, ← sum_sub_distrib]
    apply sum_congr rfl
    intro b _
    ring
  rw [tsum_log_conv_higherMoment_eq r hσ hε c V hsupp,
    hm, ← sum_sub_distrib]
  have hC := gaussianHigherLogMomentConstant_nonneg hr hσ1
  calc
    _ ≤ ∑ b ∈ Icc 1 V,
        gaussianHigherLogMomentConstant r σ * t * X ^ (-σ) * (1 + Real.log X) := by
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
        (norm_tsum_log_gaussianHigherMoment_dilate_sub_poles_le
          r hr hσ hσ1 ht hε hsector hX hscale hb1)
        (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      rw [one_mul, ← norm_mul] at hh
      have he : (c b : ℂ) * (∑' a : ℕ, (Real.log (a : ℝ) : ℂ) *
          gaussianHigherPrimeMomentWeight r σ t ε (a * b)) -
          (c b : ℂ) * ((b : ℂ)⁻¹ * (L - (Real.log (b : ℝ) : ℂ) * P)) =
        (c b : ℂ) * ((∑' a : ℕ, (Real.log (a : ℝ) : ℂ) *
          gaussianHigherPrimeMomentWeight r σ t ε (a * b)) -
          (b : ℂ)⁻¹ * (L - (Real.log (b : ℝ) : ℂ) * P)) := by ring
      rw [he]
      apply hh.trans
      gcongr
    _ = _ := by
      simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      ring

#print axioms summable_log_gaussianHigherMoment_dilate
#print axioms norm_tsum_log_gaussianHigherMoment_dilate_sub_poles_le
#print axioms norm_tsum_gaussianHigherMoment_log_trunc_moebius_sub_poles_le

end GaloisForLFunctions.ExceptionalLayerTheory
