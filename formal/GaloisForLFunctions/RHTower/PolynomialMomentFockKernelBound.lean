import GaloisForLFunctions.RHTower.PolynomialMomentFockNorm

/-!
# Explicit diagonal-kernel growth for the polynomial moment Fock carrier

The unit annulus lower bound on every radial monomial moment turns the diagonal kernel into a
geometrically dominated series.  Summing that series yields a concrete point-evaluation envelope.
-/

open Filter Topology Set MeasureTheory Complex
open scoped Real

namespace RHTower

noncomputable section

/-- Explicit geometric majorant for one diagonal kernel coefficient. -/
theorem normSq_polynomialMomentFockKernelCoeff_le_geometric
    {m : ℝ} (hm : 2 ≤ m) (z : ℂ) (n : ℕ) :
    ‖momentFockKernelCoeff (polynomialFockMoment m) z n‖ ^ (2 : ℝ) ≤
      (2 * Real.pi *
          Real.exp (-2 * polynomialFockPotential m (‖z‖ + 2)))⁻¹ *
        ((‖z‖ / (‖z‖ + 1)) ^ 2) ^ n := by
  let R : ℝ := ‖z‖ + 1
  let A : ℝ := 2 * Real.pi * Real.exp (-2 * polynomialFockPotential m (R + 1))
  let q : ℝ := (‖z‖ / R) ^ 2
  have hR : 1 ≤ R := by dsimp [R]; linarith [norm_nonneg z]
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hA : 0 < A := by dsimp [A]; positivity
  have hlower : A * R ^ (2 * n) ≤ polynomialFockMoment m n := by
    simpa [A] using polynomialFockMoment_lower_geometric hm hR n
  have hden : 0 < A * R ^ (2 * n) := mul_pos hA (pow_pos hR0 _)
  rw [norm_momentFockKernelCoeff_polynomial_sq hm]
  have hright :
      (2 * Real.pi *
          Real.exp (-2 * polynomialFockPotential m (‖z‖ + 2)))⁻¹ *
        ((‖z‖ / (‖z‖ + 1)) ^ 2) ^ n = A⁻¹ * q ^ n := by
    dsimp [A, R, q]
    rw [show ‖z‖ + 1 + 1 = ‖z‖ + 2 by ring]
  rw [hright]
  calc
    ‖z‖ ^ (2 * n) / polynomialFockMoment m n ≤
        ‖z‖ ^ (2 * n) / (A * R ^ (2 * n)) :=
      div_le_div_of_nonneg_left (by positivity) hden hlower
    _ = A⁻¹ * q ^ n := by
      dsimp [q]
      rw [← pow_mul, div_pow]
      field_simp [hA.ne', hR0.ne']

/-- Explicit geometric upper bound for the diagonal polynomial Fock kernel. -/
theorem normSq_polynomialMomentFockKernel_le
    {m : ℝ} (hm : 2 ≤ m) (z : ℂ) :
    ‖momentFockKernel (polynomialMomentFockData m hm) z‖ ^ 2 ≤
      (2 * Real.pi *
          Real.exp (-2 * polynomialFockPotential m (‖z‖ + 2)))⁻¹ *
        (1 - (‖z‖ / (‖z‖ + 1)) ^ 2)⁻¹ := by
  let A : ℝ := 2 * Real.pi *
    Real.exp (-2 * polynomialFockPotential m (‖z‖ + 2))
  let q : ℝ := (‖z‖ / (‖z‖ + 1)) ^ 2
  have hR0 : 0 < ‖z‖ + 1 := by positivity
  have hratio : ‖z‖ / (‖z‖ + 1) < 1 :=
    (div_lt_one hR0).2 (by linarith [norm_nonneg z])
  have hqnorm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [q]; positivity)]
    dsimp [q]
    nlinarith [div_nonneg (norm_nonneg z) hR0.le]
  have hactual : Summable fun n =>
      ‖momentFockKernelCoeff (polynomialFockMoment m) z n‖ ^ (2 : ℝ) :=
    (polynomialMomentFockData m hm).kernel_summable z
  have hgeom : Summable fun n : ℕ => A⁻¹ * q ^ n :=
    (summable_geometric_of_norm_lt_one hqnorm).mul_left A⁻¹
  change ‖momentFockKernel (polynomialMomentFockData m hm) z‖ ^ 2 ≤
    A⁻¹ * (1 - q)⁻¹
  calc
    ‖momentFockKernel (polynomialMomentFockData m hm) z‖ ^ 2 =
        ∑' n, ‖momentFockKernelCoeff (polynomialFockMoment m) z n‖ ^ (2 : ℝ) := by
      rw [HilbertSchmidt.lp_norm_sq_eq]
      apply tsum_congr
      intro n
      rw [Real.rpow_two]
      rfl
    _ ≤ ∑' n, A⁻¹ * q ^ n :=
      hactual.tsum_le_tsum
        (fun n => by
          simpa [A, q] using normSq_polynomialMomentFockKernelCoeff_le_geometric hm z n)
        hgeom
    _ = A⁻¹ * (1 - q)⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hqnorm]

theorem inv_one_sub_norm_ratio_sq_le
    (z : ℂ) :
    (1 - (‖z‖ / (‖z‖ + 1)) ^ 2)⁻¹ ≤ (‖z‖ + 1) ^ 2 := by
  let x : ℝ := ‖z‖
  have hx : 0 ≤ x := norm_nonneg z
  have hR : 0 < x + 1 := by positivity
  have hratio : x / (x + 1) < 1 := (div_lt_one hR).2 (by linarith)
  have hratio0 : 0 ≤ x / (x + 1) := div_nonneg hx hR.le
  have hratioSq : (x / (x + 1)) ^ 2 < 1 := by
    nlinarith [mul_self_lt_mul_self hratio0 hratio]
  have hden : 0 < 1 - (x / (x + 1)) ^ 2 := by linarith
  rw [inv_eq_one_div]
  apply (div_le_iff₀ (by simpa [x] using hden)).2
  have hid : (1 - (x / (x + 1)) ^ 2) * (x + 1) ^ 2 = 2 * x + 1 := by
    field_simp [hR.ne']
    ring
  have hid' :
      (1 - (‖z‖ / (‖z‖ + 1)) ^ 2) * (‖z‖ + 1) ^ 2 =
        2 * ‖z‖ + 1 := by
    simpa [x] using hid
  rw [mul_comm, hid']
  linarith [norm_nonneg z]

/-- Diagonal kernel bound without a small denominator. -/
theorem normSq_polynomialMomentFockKernel_le_explicit
    {m : ℝ} (hm : 2 ≤ m) (z : ℂ) :
    ‖momentFockKernel (polynomialMomentFockData m hm) z‖ ^ 2 ≤
      (2 * Real.pi *
          Real.exp (-2 * polynomialFockPotential m (‖z‖ + 2)))⁻¹ *
        (‖z‖ + 1) ^ 2 := by
  calc
    ‖momentFockKernel (polynomialMomentFockData m hm) z‖ ^ 2 ≤
        (2 * Real.pi *
            Real.exp (-2 * polynomialFockPotential m (‖z‖ + 2)))⁻¹ *
          (1 - (‖z‖ / (‖z‖ + 1)) ^ 2)⁻¹ :=
      normSq_polynomialMomentFockKernel_le hm z
    _ ≤ (2 * Real.pi *
            Real.exp (-2 * polynomialFockPotential m (‖z‖ + 2)))⁻¹ *
          (‖z‖ + 1) ^ 2 := by
      exact mul_le_mul_of_nonneg_left (inv_one_sub_norm_ratio_sq_le z) (by positivity)

/-- Explicit point-evaluation growth envelope. -/
def polynomialMomentFockEvaluationMajorant (m : ℝ) (z : ℂ) : ℝ :=
  1 +
    (2 * Real.pi *
        Real.exp (-2 * polynomialFockPotential m (‖z‖ + 2)))⁻¹ *
      (‖z‖ + 1) ^ 2

theorem norm_polynomialMomentFockFunction_le_majorant
    {m : ℝ} (hm : 2 ≤ m) (f : MomentFock) (z : ℂ) :
    ‖polynomialMomentFockFunction m hm f z‖ ≤
      polynomialMomentFockEvaluationMajorant m z * ‖f‖ := by
  rw [polynomialMomentFockFunction_eq_evaluation]
  have heval := norm_momentFockEvaluation_apply_le
    (polynomialMomentFockData m hm) z f
  have hkernelSq := normSq_polynomialMomentFockKernel_le_explicit hm z
  have hkernel :
      ‖momentFockKernel (polynomialMomentFockData m hm) z‖ ≤
        polynomialMomentFockEvaluationMajorant m z := by
    unfold polynomialMomentFockEvaluationMajorant
    have hsq :
        ‖momentFockKernel (polynomialMomentFockData m hm) z‖ ≤
          1 + ‖momentFockKernel (polynomialMomentFockData m hm) z‖ ^ 2 := by
      nlinarith [sq_nonneg
        (‖momentFockKernel (polynomialMomentFockData m hm) z‖ - 1 / 2)]
    exact hsq.trans (by simpa [add_comm] using add_le_add_left hkernelSq 1)
  exact heval.trans (mul_le_mul_of_nonneg_right hkernel (norm_nonneg f))

end

end RHTower
