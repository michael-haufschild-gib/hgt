import GaloisForLFunctions.HTGeometry.GaussianWeightedObserverTubeLaw

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem sum_log_one_add_ge_two_mul_stableHarmonic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y : ι → ℝ) (hy : ∀ i, 0 ≤ y i) :
    2 * (∑ i, y i) ^ 2 /
        ((∑ i, y i ^ 2) + 2 * ∑ i, y i) ≤
      ∑ i, Real.log (1 + y i) := by
  let s : Finset ι := Finset.univ.filter fun i => 0 < y i
  have hzero {i : ι} (hi : i ∉ s) : y i = 0 := by
    have hnot : ¬ 0 < y i := by
      simpa [s] using hi
    exact le_antisymm (le_of_not_gt hnot) (hy i)
  have hsum : ∑ i ∈ s, y i = ∑ i, y i := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hi
    rw [hzero hi]
  have hsumsq : ∑ i ∈ s, y i ^ 2 = ∑ i, y i ^ 2 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hi
    rw [hzero hi, zero_pow (by norm_num : 2 ≠ 0)]
  have hsumFrac : ∑ i ∈ s, y i / (y i + 2) =
      ∑ i, y i / (y i + 2) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hi
    rw [hzero hi]
    norm_num
  have hg : ∀ i ∈ s, 0 < y i * (y i + 2) := by
    intro i hi
    have hyi : 0 < y i := by simpa [s] using hi
    exact mul_pos hyi (by linarith)
  have htitu := Finset.sq_sum_div_le_sum_sq_div s y hg
  have hden : ∑ i ∈ s, y i * (y i + 2) =
      (∑ i ∈ s, y i ^ 2) + 2 * ∑ i ∈ s, y i := by
    calc
      ∑ i ∈ s, y i * (y i + 2) =
          ∑ i ∈ s, (y i ^ 2 + 2 * y i) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = (∑ i ∈ s, y i ^ 2) + ∑ i ∈ s, 2 * y i := by
        rw [Finset.sum_add_distrib]
      _ = (∑ i ∈ s, y i ^ 2) + 2 * ∑ i ∈ s, y i := by
        rw [Finset.mul_sum]
  have hfrac : ∑ i ∈ s, y i ^ 2 / (y i * (y i + 2)) =
      ∑ i ∈ s, y i / (y i + 2) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hyi : y i ≠ 0 := ne_of_gt (by simpa [s] using hi)
    field_simp
  rw [hden, hfrac, hsum, hsumsq, hsumFrac] at htitu
  have hlog : 2 * ∑ i, y i / (y i + 2) ≤
      ∑ i, Real.log (1 + y i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    simpa only [mul_div_assoc] using Real.le_log_one_add_of_nonneg (hy i)
  have hscaled := mul_le_mul_of_nonneg_left htitu (by norm_num : (0 : ℝ) ≤ 2)
  have heq : 2 * ((∑ i, y i) ^ 2 /
      ((∑ i, y i ^ 2) + 2 * ∑ i, y i)) =
      2 * (∑ i, y i) ^ 2 /
        ((∑ i, y i ^ 2) + 2 * ∑ i, y i) := by ring
  rw [heq] at hscaled
  exact hscaled.trans hlog

/-- Stable-rank determinant compression at arbitrary Gaussian scale.  The
bound strengthens monotonically with `tau` and saturates at the genuine
stable ratio `S² / Q`; it never uses a minimum singular value. -/
theorem scaledStableRatio_inverseSqrtProduct_le_exp
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i)
    {tau : ℝ} (htau : 0 < tau) (hS : 0 < ∑ i, x i) :
    (∏ i, (1 + 2 * tau * x i) ^ (-(1 / 2 : ℝ))) ≤
      Real.exp (-((tau * (∑ i, x i) ^ 2) /
        (tau * (∑ i, x i ^ 2) + ∑ i, x i))) := by
  let S : ℝ := ∑ i, x i
  let Q : ℝ := ∑ i, x i ^ 2
  let y : ι → ℝ := fun i => 2 * tau * x i
  have hy : ∀ i, 0 ≤ y i := fun i => by
    dsimp [y]
    exact mul_nonneg (mul_nonneg (by norm_num) htau.le) (hx i)
  have hsumY : ∑ i, y i = 2 * tau * S := by
    dsimp [y]
    rw [← Finset.mul_sum]
  have hsumYSq : ∑ i, y i ^ 2 = (2 * tau) ^ 2 * Q := by
    dsimp [y]
    simp_rw [mul_pow]
    rw [← Finset.mul_sum]
  have hlog := sum_log_one_add_ge_two_mul_stableHarmonic y hy
  have hden : 0 < tau * Q + S := by
    have hQ : 0 ≤ Q := by
      dsimp [Q]
      positivity
    have hS' : 0 < S := hS
    nlinarith [mul_nonneg htau.le hQ]
  have hratio : 2 * (∑ i, y i) ^ 2 /
        ((∑ i, y i ^ 2) + 2 * ∑ i, y i) =
      2 * tau * S ^ 2 / (tau * Q + S) := by
    rw [hsumY, hsumYSq]
    field_simp
  rw [hratio] at hlog
  change (∏ i, (1 + y i) ^ (-(1 / 2 : ℝ))) ≤
    Real.exp (-((tau * S ^ 2) / (tau * Q + S)))
  have hprodPos : 0 < ∏ i, (1 + y i) ^ (-(1 / 2 : ℝ)) := by
    apply Finset.prod_pos
    intro i _
    exact Real.rpow_pos_of_pos (by linarith [hy i]) _
  apply (Real.log_le_iff_le_exp hprodPos).mp
  rw [Real.log_prod]
  · have hlogrpow : ∀ i, Real.log ((1 + y i) ^ (-(1 / 2 : ℝ))) =
        (-(1 / 2 : ℝ)) * Real.log (1 + y i) := by
      intro i
      exact Real.log_rpow (by linarith [hy i]) _
    rw [Finset.sum_congr rfl fun i _ => hlogrpow i]
    rw [← Finset.mul_sum]
    change (-(1 / 2 : ℝ)) * (∑ i, Real.log (1 + y i)) ≤
      -((tau * S ^ 2) / (tau * Q + S))
    have htwo : 2 * ((tau * S ^ 2) / (tau * Q + S)) =
        2 * tau * S ^ 2 / (tau * Q + S) := by ring
    rw [← htwo] at hlog
    nlinarith
  · intro i _
    exact ne_of_gt (Real.rpow_pos_of_pos (by linarith [hy i]) _)

theorem normalizedGaussianLaplaceFactor_eq_inverseSqrtRpow
    {tau x : ℝ} (htau : 0 ≤ tau) (hx : 0 ≤ x) :
    (Real.sqrt (2 * Real.pi))⁻¹ *
        Real.sqrt (Real.pi / (tau * x + 1 / 2)) =
      (1 + 2 * tau * x) ^ (-(1 / 2 : ℝ)) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hden : 0 < tau * x + 1 / 2 := by positivity
  have hbase : 0 < 1 + 2 * tau * x := by positivity
  have hleft : 0 < (Real.sqrt (2 * Real.pi))⁻¹ *
      Real.sqrt (Real.pi / (tau * x + 1 / 2)) := by positivity
  have hright : 0 < (1 + 2 * tau * x) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_pos_of_pos hbase _
  rw [← Real.exp_log hleft, ← Real.exp_log hright]
  congr 1
  rw [Real.log_mul (inv_ne_zero (ne_of_gt (Real.sqrt_pos.2 (by positivity))))
      (ne_of_gt (Real.sqrt_pos.2 (div_pos hpi hden))),
    Real.log_inv, Real.log_sqrt (by positivity),
    Real.log_sqrt (div_nonneg hpi.le hden.le),
    Real.log_div hpi.ne' hden.ne', Real.log_rpow hbase]
  have hlogTwoPi : Real.log (2 * Real.pi) =
      Real.log 2 + Real.log Real.pi := by
    rw [Real.log_mul (by norm_num) hpi.ne']
  have hlogBase : Real.log (1 + 2 * tau * x) =
      Real.log 2 + Real.log (tau * x + 1 / 2) := by
    rw [show 1 + 2 * tau * x = 2 * (tau * x + 1 / 2) by ring,
      Real.log_mul (by norm_num) hden.ne']
  rw [hlogTwoPi, hlogBase]
  ring

/-- The exact Gaussian determinant factor in the quenched observer law is
exponentially controlled by total activation and stable rank. -/
theorem gaussianLaplaceProduct_le_exp_stableRatio
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i)
    {tau : ℝ} (htau : 0 < tau) (hS : 0 < ∑ i, x i) :
    (∏ i, (Real.sqrt (2 * Real.pi))⁻¹ *
        Real.sqrt (Real.pi / (tau * x i + 1 / 2))) ≤
      Real.exp (-((tau * (∑ i, x i) ^ 2) /
        (tau * (∑ i, x i ^ 2) + ∑ i, x i))) := by
  calc
    (∏ i, (Real.sqrt (2 * Real.pi))⁻¹ *
        Real.sqrt (Real.pi / (tau * x i + 1 / 2))) =
      ∏ i, (1 + 2 * tau * x i) ^ (-(1 / 2 : ℝ)) := by
        apply Finset.prod_congr rfl
        intro i _
        exact normalizedGaussianLaplaceFactor_eq_inverseSqrtRpow htau.le (hx i)
    _ ≤ _ := scaledStableRatio_inverseSqrtProduct_le_exp x hx htau hS

theorem gaussianLaplaceProduct_le_exp_stableRatio_total
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i)
    {tau : ℝ} (htau : 0 < tau) :
    (∏ i, (Real.sqrt (2 * Real.pi))⁻¹ *
        Real.sqrt (Real.pi / (tau * x i + 1 / 2))) ≤
      Real.exp (-((tau * (∑ i, x i) ^ 2) /
        (tau * (∑ i, x i ^ 2) + ∑ i, x i))) := by
  have hsum0 : 0 ≤ ∑ i, x i := Finset.sum_nonneg fun i _ => hx i
  rcases hsum0.eq_or_lt with hsum | hsum
  · have hxi : ∀ i, x i = 0 := by
      intro i
      have hle : x i ≤ ∑ j, x j :=
        Finset.single_le_sum (fun j _ => hx j) (Finset.mem_univ i)
      exact le_antisymm (by simpa [hsum] using hle) (hx i)
    have hprod : (∏ i, (Real.sqrt (2 * Real.pi))⁻¹ *
        Real.sqrt (Real.pi / (tau * x i + 1 / 2))) = 1 := by
      apply Finset.prod_eq_one
      intro i _
      rw [normalizedGaussianLaplaceFactor_eq_inverseSqrtRpow htau.le (hx i), hxi i]
      norm_num
    have hsumsq : ∑ i, x i ^ 2 = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [hxi i, zero_pow (by norm_num : 2 ≠ 0)]
    rw [hprod, ← hsum, hsumsq]
    norm_num
  · exact gaussianLaplaceProduct_le_exp_stableRatio x hx htau hsum

/-- Harmonic-mean form: effective Gaussian exponent interpolates between
replica activation `tau*S` and observer stable rank `S²/Q`. -/
theorem gaussianLaplaceProduct_le_exp_activationStableHarmonicMean
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i)
    {tau : ℝ} (htau : 0 < tau)
    (hS : 0 < ∑ i, x i) (hQ : 0 < ∑ i, x i ^ 2) :
    (∏ i, (Real.sqrt (2 * Real.pi))⁻¹ *
        Real.sqrt (Real.pi / (tau * x i + 1 / 2))) ≤
      Real.exp (-
        ((tau * ∑ i, x i) *
            ((∑ i, x i) ^ 2 / ∑ i, x i ^ 2) /
          ((tau * ∑ i, x i) +
            ((∑ i, x i) ^ 2 / ∑ i, x i ^ 2)))) := by
  have hbase := gaussianLaplaceProduct_le_exp_stableRatio x hx htau hS
  convert hbase using 1
  congr 2
  field_simp

theorem LinearMap.gaussianLaplaceSingularProduct_le_exp_stableRatio
    {n : ℕ} {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (A : E →ₗ[ℝ] F) {tau : ℝ} (htau : 0 < tau)
    (hA : 0 < ∑ i : Fin n, A.singularValues i ^ 2) :
    (∏ i : Fin n, (Real.sqrt (2 * Real.pi))⁻¹ *
        Real.sqrt (Real.pi /
          (tau * A.singularValues i ^ 2 + 1 / 2))) ≤
      Real.exp (-((tau *
          (∑ i : Fin n, A.singularValues i ^ 2) ^ 2) /
        (tau * (∑ i : Fin n, A.singularValues i ^ 4) +
          ∑ i : Fin n, A.singularValues i ^ 2))) := by
  simpa only [← pow_mul, Nat.reduceMul] using
    gaussianLaplaceProduct_le_exp_stableRatio
      (fun i : Fin n => A.singularValues i ^ 2)
      (fun i => sq_nonneg _) htau hA

theorem LinearMap.gaussianLaplaceSingularProduct_le_exp_stableRatio_total
    {n : ℕ} {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (A : E →ₗ[ℝ] F) {tau : ℝ} (htau : 0 < tau) :
    (∏ i : Fin n, (Real.sqrt (2 * Real.pi))⁻¹ *
        Real.sqrt (Real.pi /
          (tau * A.singularValues i ^ 2 + 1 / 2))) ≤
      Real.exp (-((tau *
          (∑ i : Fin n, A.singularValues i ^ 2) ^ 2) /
        (tau * (∑ i : Fin n, A.singularValues i ^ 4) +
          ∑ i : Fin n, A.singularValues i ^ 2))) := by
  simpa only [← pow_mul, Nat.reduceMul] using
    gaussianLaplaceProduct_le_exp_stableRatio_total
      (fun i : Fin n => A.singularValues i ^ 2)
      (fun i => sq_nonneg _) htau

theorem stableRatio_inverseSqrtProduct_le_exp
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hS : 0 < ∑ i, x i) (hQ : 0 < ∑ i, x i ^ 2) :
    (∏ i, (1 + ((∑ j, x j) / (∑ j, x j ^ 2)) * x i) ^
        (-(1 / 2 : ℝ))) ≤
      Real.exp (-(((∑ i, x i) ^ 2 / (∑ i, x i ^ 2)) / 3)) := by
  let S : ℝ := ∑ i, x i
  let Q : ℝ := ∑ i, x i ^ 2
  let y : ι → ℝ := fun i => (S / Q) * x i
  have hy : ∀ i, 0 ≤ y i := fun i =>
    mul_nonneg (div_nonneg hS.le hQ.le) (hx i)
  have hsumY : ∑ i, y i = S ^ 2 / Q := by
    dsimp [y]
    rw [← Finset.mul_sum]
    dsimp [S, Q]
    ring
  have hsumYSq : ∑ i, y i ^ 2 = (S ^ 2 / Q) ^ 2 / (S ^ 2 / Q) := by
    have hcalc : (∑ i, y i ^ 2) = (S / Q) ^ 2 * Q := by
      dsimp [y]
      simp_rw [mul_pow]
      rw [← Finset.mul_sum]
    rw [hcalc]
    field_simp
  have hlog := sum_log_one_add_ge_two_mul_stableHarmonic y hy
  have hratio : 2 * (∑ i, y i) ^ 2 /
        ((∑ i, y i ^ 2) + 2 * ∑ i, y i) =
      2 * (S ^ 2 / Q) / 3 := by
    rw [hsumY, hsumYSq]
    have hR : 0 < S ^ 2 / Q := by positivity
    field_simp
    ring
  rw [hratio] at hlog
  change (∏ i, (1 + y i) ^ (-(1 / 2 : ℝ))) ≤
    Real.exp (-((S ^ 2 / Q) / 3))
  have hprodPos : 0 < ∏ i, (1 + y i) ^ (-(1 / 2 : ℝ)) := by
    apply Finset.prod_pos
    intro i _
    exact Real.rpow_pos_of_pos (by linarith [hy i]) _
  apply (Real.log_le_iff_le_exp hprodPos).mp
  rw [Real.log_prod]
  · have hlogrpow : ∀ i, Real.log ((1 + y i) ^ (-(1 / 2 : ℝ))) =
        (-(1 / 2 : ℝ)) * Real.log (1 + y i) := by
      intro i
      exact Real.log_rpow (by linarith [hy i]) _
    rw [Finset.sum_congr rfl fun i _ => hlogrpow i]
    rw [← Finset.mul_sum]
    change (-(1 / 2 : ℝ)) * (∑ i, Real.log (1 + y i)) ≤
      -((S ^ 2 / Q) / 3)
    nlinarith
  · intro i _
    exact ne_of_gt (Real.rpow_pos_of_pos (by linarith [hy i]) _)

end

end GaloisForLFunctions.HTGeometry
