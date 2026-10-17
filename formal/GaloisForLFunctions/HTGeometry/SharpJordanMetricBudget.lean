import GaloisForLFunctions.HTGeometry.NilpotentSchurEnergy
import GaloisForLFunctions.HTGeometry.GeometricJordanMetricFrame

/-!
# Exact attained energy frontier under a metric condition-number budget

For a full chain of length `n+1`, arbitrary invertible metric frames of condition
number at most `q^n` have least quadratic trace-energy defect
`2*(n+1)*(Im a)^2 + n/q^2`. Geometric positive frames attain it. The scalar
endpoint is included, so actual Xi chains need no multiplicity assumption.
-/

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder

namespace GaloisForLFunctions.HTGeometry

noncomputable section
open Matrix Finset

theorem hsNorm_le_conditionNumber_mul_conjugate {d : ℕ}
    (P : (Matrix (Fin d) (Fin d) ℂ)ˣ) (A : Matrix (Fin d) (Fin d) ℂ) :
    hsNorm A ≤ HilbertMetric.similarityConditionNumber P *
      hsNorm ((P : Matrix (Fin d) (Fin d) ℂ) * A * P.inv) := by
  have hid : (P.inv : Matrix (Fin d) (Fin d) ℂ) * (P.val * A * P.inv) * P.val = A := by
    simp [Matrix.mul_assoc]
  calc
    hsNorm A = hsNorm ((P.inv : Matrix (Fin d) (Fin d) ℂ) * (P.val * A * P.inv) * P.val) :=
      congrArg hsNorm hid.symm
    _ ≤ (‖(P.inv : Matrix (Fin d) (Fin d) ℂ)‖ * hsNorm (P.val * A * P.inv)) *
        ‖(P : Matrix (Fin d) (Fin d) ℂ)‖ :=
      (hsNorm_mul_le' _ _).trans
        (mul_le_mul_of_nonneg_right (hsNorm_mul_le _ _) (norm_nonneg _))
    _ = _ := by
      change ‖P.inv‖ * hsNorm (P.val * A * P.inv) * ‖P.val‖ =
        (‖P.val‖ * ‖P.inv‖) * hsNorm (P.val * A * P.inv)
      ring

theorem jordanSimilarity_energy_lower_bound (n : ℕ)
    (P : (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)ˣ)
    {q : ℝ} (hq : 1 ≤ q) (hP : HilbertMetric.similarityConditionNumber P ≤ q ^ n) :
    (n : ℝ) / q ^ 2 ≤
      matHSNormSq ((P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) * metricJordanShift n * P.inv) := by
  by_cases hn : n = 0
  · subst n; simpa using matHSNormSq_nonneg (P.val * metricJordanShift 0 * P.inv)
  let N : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := P.val * metricJordanShift n * P.inv
  have hp : ∀ k : ℕ, N ^ k = P.val * metricJordanShift n ^ k * P.inv :=
    fun k => matrixInversePair_conjugate_pow _ _ _ P.mul_inv P.inv_mul k
  have hN : N ^ (n + 1) = 0 := by rw [hp, metricJordanShift_nilpotent]; simp
  have hnorm : 1 ≤ q ^ n * hsNorm (N ^ n) := by
    have h := hsNorm_le_conditionNumber_mul_conjugate P (metricJordanShift n ^ n)
    rw [metricJordanShift_top_hsNorm, ← hp] at h
    exact h.trans (mul_le_mul_of_nonneg_right hP (hsNorm_nonneg _))
  have hsquare : 1 ≤ (q ^ n * hsNorm (N ^ n)) ^ 2 := by
    simpa using pow_le_pow_left₀ zero_le_one hnorm 2
  have hpower : (n : ℝ) ^ n ≤ (q ^ 2 * matHSNormSq N) ^ n := by
    calc
      (n : ℝ) ^ n = (n : ℝ) ^ n * 1 := by ring
      _ ≤ (n : ℝ) ^ n * (q ^ n * hsNorm (N ^ n)) ^ 2 :=
        mul_le_mul_of_nonneg_left hsquare (by positivity)
      _ = (q ^ 2) ^ n * ((n : ℝ) ^ n * matHSNormSq (N ^ n)) := by
        rw [mul_pow, hsNorm_sq]
        change (n : ℝ) ^ n * ((q ^ n) ^ 2 * matHSNormSq (N ^ n)) = _
        rw [← pow_mul, ← pow_mul, Nat.mul_comm n 2]
        ring
      _ ≤ (q ^ 2) ^ n * matHSNormSq N ^ n :=
        mul_le_mul_of_nonneg_left (nilpotent_sharp_power_energy_bound N hN) (by positivity)
      _ = (q ^ 2 * matHSNormSq N) ^ n := (mul_pow _ _ _).symm
  have hbase : (n : ℝ) ≤ q ^ 2 * matHSNormSq N :=
    le_of_pow_le_pow_left₀ hn (mul_nonneg (sq_nonneg q) (matHSNormSq_nonneg N)) hpower
  exact (div_le_iff₀ (by positivity : 0 < q ^ 2)).mpr (by nlinarith [hbase])

theorem jordanSimilarity_defect_lower_bound (n : ℕ) (a : ℂ)
    (P : (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)ˣ)
    {q : ℝ} (hq : 1 ≤ q) (hP : HilbertMetric.similarityConditionNumber P ≤ q ^ n) :
    2 * (n + 1 : ℝ) * a.im ^ 2 + (n : ℝ) / q ^ 2 ≤
      finiteMatrixQuadraticTraceEnergyDefect
        ((P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) * (a • 1 + metricJordanShift n) * P.inv) := by
  let N : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := P.val * metricJordanShift n * P.inv
  have hN : N ^ (n + 1) = 0 := by
    change (P.val * metricJordanShift n * P.inv) ^ (n + 1) = 0
    rw [matrixInversePair_conjugate_pow P.val P.inv _ P.val_inv P.inv_val,
      metricJordanShift_nilpotent]
    simp
  have hc : (P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) *
      (a • 1 + metricJordanShift n) * P.inv = a • 1 + N := by
    simp [Matrix.mul_add, Matrix.add_mul, N]
  rw [hc, nilpotent_scalar_add_defect N hN a]
  exact add_le_add le_rfl (jordanSimilarity_energy_lower_bound n P hq hP)

theorem geometricJordanFrame_defect (n : ℕ) (a : ℂ) {q : ℝ} (hq : 1 ≤ q) :
    let P := geometricJordanFrame n q (by linarith)
    finiteMatrixQuadraticTraceEnergyDefect
        ((P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) * (a • 1 + metricJordanShift n) * P.inv) =
      2 * (n + 1 : ℝ) * a.im ^ 2 + (n : ℝ) / q ^ 2 := by
  dsimp only
  let P := geometricJordanFrame n q (by linarith)
  let N : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := P.val * metricJordanShift n * P.inv
  have hN : N ^ (n + 1) = 0 := by
    change (P.val * metricJordanShift n * P.inv) ^ (n + 1) = 0
    rw [matrixInversePair_conjugate_pow P.val P.inv _ P.val_inv P.inv_val,
      metricJordanShift_nilpotent]
    simp
  have hc : (P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) *
      (a • 1 + metricJordanShift n) * P.inv = a • 1 + N := by
    simp [Matrix.mul_add, Matrix.add_mul, N]
  change finiteMatrixQuadraticTraceEnergyDefect (P.val * (a • 1 + metricJordanShift n) * P.inv) = _
  rw [hc, nilpotent_scalar_add_defect N hN a]
  change _ + matHSNormSq (P.val * metricJordanShift n * P.inv) = _
  have hgeom : P.val * metricJordanShift n * P.inv = (q : ℂ)⁻¹ • metricJordanShift n :=
    geometricJordanFrame_conjugate n (by linarith)
  rw [hgeom, geometricJordanFrame_scaled_energy n hq]

theorem jordanMetricBudget_isLeast (n : ℕ) (a : ℂ) {q : ℝ} (hq : 1 ≤ q) :
    IsLeast
      {x : ℝ | ∃ P : (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)ˣ,
        HilbertMetric.similarityConditionNumber P ≤ q ^ n ∧
        finiteMatrixQuadraticTraceEnergyDefect
          ((P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) * (a • 1 + metricJordanShift n) * P.inv) = x}
      (2 * (n + 1 : ℝ) * a.im ^ 2 + (n : ℝ) / q ^ 2) := by
  constructor
  · refine ⟨geometricJordanFrame n q (by linarith), ?_, geometricJordanFrame_defect n a hq⟩
    rw [geometricJordanFrame_conditionNumber n hq]
  · rintro x ⟨P, hP, rfl⟩
    exact jordanSimilarity_defect_lower_bound n a P hq hP

/-- The root parameter reaches every real condition-number budget on a nontrivial chain. -/
theorem jordanMetricBudget_isLeast_of_budget (n : ℕ) (hn : 0 < n) (a : ℂ)
    {K : ℝ} (hK : 1 ≤ K) :
    IsLeast
      {x : ℝ | ∃ P : (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)ˣ,
        HilbertMetric.similarityConditionNumber P ≤ K ∧
        finiteMatrixQuadraticTraceEnergyDefect
          ((P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) * (a • 1 + metricJordanShift n) * P.inv) = x}
      (2 * (n + 1 : ℝ) * a.im ^ 2 + (n : ℝ) / (K ^ (n : ℝ)⁻¹) ^ 2) := by
  have hq : 1 ≤ K ^ (n : ℝ)⁻¹ := Real.one_le_rpow hK (by positivity)
  have hp : (K ^ (n : ℝ)⁻¹) ^ n = K :=
    Real.rpow_inv_natCast_pow (by linarith) (Nat.ne_of_gt hn)
  simpa only [hp] using jordanMetricBudget_isLeast n a hq

theorem jordanSimilarity_defect_strict (n : ℕ) (hn : 0 < n) (a : ℂ)
    (P : (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)ˣ) :
    2 * (n + 1 : ℝ) * a.im ^ 2 < finiteMatrixQuadraticTraceEnergyDefect
      ((P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) * (a • 1 + metricJordanShift n) * P.inv) := by
  let q := max 1 (HilbertMetric.similarityConditionNumber P)
  have hq : 1 ≤ q := le_max_left _ _
  have hP : HilbertMetric.similarityConditionNumber P ≤ q ^ n := by
    have hqpow : q ≤ q ^ n := by
      simpa only [pow_one] using pow_le_pow_right₀ hq (show 1 ≤ n by omega)
    exact (le_max_right 1 (HilbertMetric.similarityConditionNumber P)).trans hqpow
  have he := jordanSimilarity_defect_lower_bound n a P hq hP
  have hpenalty : 0 < (n : ℝ) / q ^ 2 := by positivity
  linarith

theorem jordanMetric_approximate_spectral_energy (n : ℕ) (a : ℂ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P : (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)ˣ,
      finiteMatrixQuadraticTraceEnergyDefect
          ((P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) * (a • 1 + metricJordanShift n) * P.inv) <
        2 * (n + 1 : ℝ) * a.im ^ 2 + ε := by
  let q : ℝ := 1 + (n : ℝ) / ε
  have hq : 1 ≤ q := by
    dsimp [q]
    exact le_add_of_nonneg_right (div_nonneg (Nat.cast_nonneg n) hε.le)
  refine ⟨geometricJordanFrame n q (by linarith), ?_⟩
  rw [geometricJordanFrame_defect n a hq]
  have hpenalty : (n : ℝ) / q ^ 2 < ε := by
    apply (div_lt_iff₀ (by positivity : 0 < q ^ 2)).mpr
    have hq2 : q ≤ q ^ 2 := by nlinarith [sq_nonneg (q - 1)]
    have heq : ε * q = ε + n := by dsimp [q]; field_simp
    nlinarith [mul_le_mul_of_nonneg_left hq2 hε.le]
  linarith

/-- The unlimited-budget infimum is spectral energy; nontrivial chains never attain it. -/
theorem jordanMetric_spectral_isGLB (n : ℕ) (a : ℂ) :
    IsGLB
      {x : ℝ | ∃ P : (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)ˣ,
        finiteMatrixQuadraticTraceEnergyDefect
          ((P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) * (a • 1 + metricJordanShift n) * P.inv) = x}
      (2 * (n + 1 : ℝ) * a.im ^ 2) := by
  constructor
  · rintro x ⟨P, rfl⟩
    let N : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := P.val * metricJordanShift n * P.inv
    have hN : N ^ (n + 1) = 0 := by
      change (P.val * metricJordanShift n * P.inv) ^ (n + 1) = 0
      rw [matrixInversePair_conjugate_pow P.val P.inv _ P.val_inv P.inv_val,
        metricJordanShift_nilpotent]
      simp
    have hc : (P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) *
        (a • 1 + metricJordanShift n) * P.inv = a • 1 + N := by
      simp [Matrix.mul_add, Matrix.add_mul, N]
    rw [hc, nilpotent_scalar_add_defect N hN a]
    exact le_add_of_nonneg_right (matHSNormSq_nonneg N)
  · intro y hy
    by_contra h
    have hε : 0 < (y - 2 * (n + 1 : ℝ) * a.im ^ 2) / 2 := by linarith
    obtain ⟨P, hP⟩ := jordanMetric_approximate_spectral_energy n a hε
    have hlow := hy ⟨P, rfl⟩
    linarith

/-- Canonical block on the literal index type, including the scalar dimension. -/
def metricJordanBlock (d : ℕ) (a : ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => if i = j then a else if i.val + 1 = j.val then 1 else 0

theorem metricJordanBlock_succ_eq (n : ℕ) (a : ℂ) :
    metricJordanBlock (n + 1) a = a • 1 + metricJordanShift n := by
  ext i j
  by_cases hij : i = j
  · subst j; simp [metricJordanBlock, metricJordanShift]
  · simp [metricJordanBlock, metricJordanShift, hij]

theorem metricJordanBlock_budget_isLeast (d : ℕ) (hd : 0 < d) (a : ℂ)
    {q : ℝ} (hq : 1 ≤ q) :
    IsLeast
      {x : ℝ | ∃ P : (Matrix (Fin d) (Fin d) ℂ)ˣ,
        HilbertMetric.similarityConditionNumber P ≤ q ^ (d - 1) ∧
        finiteMatrixQuadraticTraceEnergyDefect
          ((P : Matrix (Fin d) (Fin d) ℂ) * metricJordanBlock d a * P.inv) = x}
      (2 * (d : ℝ) * a.im ^ 2 + ((d - 1 : ℕ) : ℝ) / q ^ 2) := by
  cases d with
  | zero => omega
  | succ n =>
    simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one,
      metricJordanBlock_succ_eq] using jordanMetricBudget_isLeast n a hq

end
end GaloisForLFunctions.HTGeometry
