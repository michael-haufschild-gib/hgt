import GaloisForLFunctions.RHTower.XiCriticalGaussianNodes
import GaloisForLFunctions.RHTower.XiGaussianRealChannelEnergy
import GaloisForLFunctions.HTGeometry.VandermondeSamplingEnergy

/-!
# A strictly positive all-time coefficient floor from actual critical nodes

For each finite order, one fixed family of actual critical-line zeros supplies
a positive Vandermonde constant and a fixed exponential heat rate. Every
coefficient vector shares that floor at every positive time. The floor applies
to real-amplitude energy before the imaginary-channel debt is subtracted.
-/

open scoped Real BigOperators
open Complex GaloisForLFunctions.HTGeometry
noncomputable section

namespace RHTower

/-- The complete real channel has an independent, strictly positive coefficient-uniform floor
at every positive heat time, simultaneously for all directions at each finite order. -/
theorem exists_xiGaussianRealChannel_allTime_floor (N : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∃ L : ℝ, 32 < L ∧
      ∀ (a : ℕ → ℝ) (t : {t : ℝ // 0 < t}),
        c * Real.exp (-(L * (t : ℝ))) * (∑ j ∈ Finset.range N, a j ^ 2) ≤
          xiGaussianRealChannelEnergy
            (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) t := by
  classical
  cases N with
  | zero =>
    refine ⟨1, one_pos, 33, by linarith, ?_⟩
    intro a t
    simpa only [Finset.range_zero, Finset.sum_empty, mul_zero] using
      xiGaussianRealChannelEnergy_nonneg 0 t
  | succ n =>
    let N := n + 1
    obtain ⟨γ, q, hinj, hq, hheight⟩ := exists_xiCriticalGaussian_nodes N
    let z : Fin N → ℂ := fun i => (γ i : ℂ) ^ 2
    let C := polynomialSamplingCap z
    let A : ℝ := (N : ℝ) ^ 3 * C ^ 2
    let D : ℝ := ‖(Matrix.vandermonde z).det‖ ^ 2
    let L : ℝ := 1 + ∑ i : Fin N, γ i ^ 2
    have hN : (0 : ℝ) < N := by dsimp only [N]; positivity
    have hC : 0 < C := by
      unfold C polynomialSamplingCap
      exact mul_pos (by positivity)
        (pow_pos (pow_pos (lt_of_lt_of_le zero_lt_one (one_le_phaseFrequencyScale z)) _) _)
    have hA : 0 < A := mul_pos (pow_pos hN _) (pow_pos hC _)
    have hD : 0 < D := pow_pos
      (norm_pos_iff.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hinj)) _
    have hnode (i : Fin N) : γ i ^ 2 ≤ L := by
      have h := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => sq_nonneg (γ j))
        (Finset.mem_univ i)
      change γ i ^ 2 ≤ 1 + ∑ j : Fin N, γ j ^ 2
      linarith only [h]
    have hL : 32 < L := (hheight (⟨0, by dsimp only [N]; omega⟩ : Fin N)).trans_le (hnode _)
    refine ⟨D / A, div_pos hD hA, L, hL, ?_⟩
    intro a t
    let Q : Polynomial ℝ := ∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j
    let v : Fin N → ℂ := fun j => (a j : ℂ)
    let J := xiGaussianRealChannelEnergy Q t
    have hJ : 0 ≤ J := xiGaussianRealChannelEnergy_nonneg Q t
    have heval (i : Fin N) : evalRealPolynomial Q (z i) = polynomialSample v (z i) := by
      rw [evalRealPolynomial_rangeSum, ← Fin.sum_univ_eq_sum_range]
      rfl
    have hsamp : D * (∑ j ∈ Finset.range N, a j ^ 2) ≤
        (N : ℝ) ^ 2 * C ^ 2 * ∑ i : Fin N, ‖polynomialSample v (z i)‖ ^ 2 := by
      have h := polynomialSample_energy_bound z v
      have hcoeff : (∑ j : Fin N, ‖v j‖ ^ 2) = ∑ j ∈ Finset.range N, a j ^ 2 := by
        simp only [v, Complex.norm_real, Real.norm_eq_abs, sq_abs]
        exact Fin.sum_univ_eq_sum_range (fun j => a j ^ 2) N
      rw [hcoeff] at h
      simpa only [D, C, v, Complex.norm_real, Real.norm_eq_abs, sq_abs,
        Fin.sum_univ_eq_sum_range] using h
    have hatom (i : Fin N) : ‖polynomialSample v (z i)‖ ^ 2 ≤
        Real.exp (L * (t : ℝ)) * J := by
      have hterm := xiGaussianRealChannel_atom_at_real Q t (γ i) ⟨q i, (hq i).2⟩
      have hsum := (summable_xiGaussianRealChannel_atom Q t).sum_le_tsum {q i}
        (fun p _ => xiGaussianRealChannel_atom_nonneg Q t p)
      simp only [Finset.sum_singleton] at hsum
      rw [hterm] at hsum
      have hpoly : ‖polynomialSample v (z i)‖ ^ 2 = (Q.eval (γ i ^ 2)) ^ 2 := by
        rw [← heval]
        simp only [z, ← Complex.ofReal_pow, evalRealPolynomial_ofReal,
          Complex.norm_real, Real.norm_eq_abs, sq_abs]
      rw [hpoly]
      calc
        _ = Real.exp ((t : ℝ) * γ i ^ 2) *
            ((Q.eval (γ i ^ 2)) ^ 2 * Real.exp (-((t : ℝ) * γ i ^ 2))) := by
          rw [mul_left_comm, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
        _ ≤ Real.exp ((t : ℝ) * γ i ^ 2) * J :=
          mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le
        _ ≤ Real.exp (L * (t : ℝ)) * J := by
          apply mul_le_mul_of_nonneg_right _ hJ
          apply Real.exp_le_exp.mpr
          nlinarith only [mul_le_mul_of_nonneg_left (hnode i) t.property.le]
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hatom i)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    have h := hsamp.trans (mul_le_mul_of_nonneg_left hsum
      (show 0 ≤ (N : ℝ) ^ 2 * C ^ 2 by positivity))
    have hfinal : D * (∑ j ∈ Finset.range N, a j ^ 2) ≤ A * Real.exp (L * (t : ℝ)) * J := by
      calc
        _ ≤ _ := h
        _ = A * Real.exp (L * (t : ℝ)) * J := by dsimp only [A]; ring
    have he : Real.exp (-(L * (t : ℝ))) * Real.exp (L * (t : ℝ)) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    calc
      _ = (Real.exp (-(L * (t : ℝ))) / A) *
          (D * (∑ j ∈ Finset.range N, a j ^ 2)) := by ring
      _ ≤ (Real.exp (-(L * (t : ℝ))) / A) * (A * Real.exp (L * (t : ℝ)) * J) :=
        mul_le_mul_of_nonneg_left hfinal (div_nonneg (Real.exp_pos _).le hA.le)
      _ = J := by
        rw [div_eq_mul_inv]
        calc
          _ = (A⁻¹ * A) * (Real.exp (-(L * (t : ℝ))) * Real.exp (L * (t : ℝ))) * J := by ring
          _ = J := by rw [inv_mul_cancel₀ hA.ne', he, one_mul, one_mul]

/-- The same all-time floor holds for the complete actual positive norm energy. -/
theorem exists_xiPolynomialGaussianEnergy_allTime_floor (N : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∃ L : ℝ, 32 < L ∧
      ∀ (a : ℕ → ℝ) (t : {t : ℝ // 0 < t}),
        c * Real.exp (-(L * (t : ℝ))) * (∑ j ∈ Finset.range N, a j ^ 2) ≤
          ∑' q : XiZeroCopy, ‖xiPolynomialGaussianHeatTerm
            (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) t q‖ := by
  obtain ⟨c, hc, L, hL, hfloor⟩ := exists_xiGaussianRealChannel_allTime_floor N
  exact ⟨c, hc, L, hL, fun a t => (hfloor a t).trans (xiGaussianRealChannelEnergy_le_energy _ t)⟩

/-- The independent critical-line reserve improves the full all-time signed Hankel bound. -/
theorem exists_xiHeatHankelForm_allTime_critical_reserve (N : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∃ L : ℝ, 32 < L ∧
      ∀ (a : ℕ → ℝ) (t : {t : ℝ // 0 < t}),
        2 * c * Real.exp (-(L * (t : ℝ))) * (∑ j ∈ Finset.range N, a j ^ 2) -
          xiGaussianGapCancellationBudget (2 * N) t * routeUPolynomialGaussianMass
            (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) (xiGaussianHalfHeat t) ≤
          xiHeatHankelForm N a t := by
  classical
  obtain ⟨c, hc, L, hL, hfloor⟩ := exists_xiGaussianRealChannel_allTime_floor N
  refine ⟨c, hc, L, hL, ?_⟩
  intro a t
  let Q : Polynomial ℝ := ∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j
  have hd : Q.natDegree ≤ N := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro j hj
    exact (Polynomial.natDegree_C_mul_X_pow_le (a j) j).trans (Finset.mem_range.mp hj).le
  have hK := (tsum_norm_xiPolynomialGaussianHeatTerm_le_gap Q t).trans
    (mul_le_mul_of_nonneg_right (xiGaussianGapCancellationBudget_mono t (Nat.mul_le_mul_left 2 hd))
      (routeUPolynomialGaussianMass_nonneg Q (xiGaussianHalfHeat t)))
  have hJ := hfloor a t
  change c * Real.exp (-(L * (t : ℝ))) * (∑ j ∈ Finset.range N, a j ^ 2) ≤
    xiGaussianRealChannelEnergy Q t at hJ
  rw [xiGaussianRealChannelEnergy_eq_half_energy_add_trace] at hJ
  have htrace : xiPolynomialGaussianHeatTraceReal Q t = xiHeatHankelForm N a t :=
    xiPolynomialGaussianHeatTraceReal_rangeSum t.property N a
  rw [htrace] at hJ
  change 2 * c * Real.exp (-(L * (t : ℝ))) * (∑ j ∈ Finset.range N, a j ^ 2) -
    xiGaussianGapCancellationBudget (2 * N) t * routeUPolynomialGaussianMass Q (xiGaussianHalfHeat t) ≤ _
  linarith only [hJ, hK]

/-- In the complete three-by-three form, the real-channel coefficient floor holds for all times. -/
theorem exists_xiHeatThirdRealChannel_allTime_floor :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ L : ℝ, 32 < L ∧
      ∀ (a b c : ℝ) (t : {t : ℝ // 0 < t}),
        c₀ * Real.exp (-(L * (t : ℝ))) * (a ^ 2 + b ^ 2 + c ^ 2) ≤
          xiGaussianRealChannelEnergy (xiHeatThirdPolynomial a b c) t := by
  obtain ⟨c₀, hc₀, L, hL, hfloor⟩ := exists_xiGaussianRealChannel_allTime_floor 3
  refine ⟨c₀, hc₀, L, hL, ?_⟩
  intro a b c t
  simpa [xiHeatThirdPolynomial, Finset.sum_range_succ] using
    hfloor (fun n => if n = 0 then a else if n = 1 then b else c) t

/-- The complete three-by-three form retains a positive reserve against the degree-four debt
envelope, including all three mixed coefficient terms. -/
theorem exists_xiHeatThirdQuadratic_allTime_critical_reserve :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ L : ℝ, 32 < L ∧
      ∀ (a b c : ℝ) (t : {t : ℝ // 0 < t}),
        2 * c₀ * Real.exp (-(L * (t : ℝ))) * (a ^ 2 + b ^ 2 + c ^ 2) -
          xiGaussianGapCancellationBudget 4 t *
            routeUPolynomialGaussianMass (xiHeatThirdPolynomial a b c) (xiGaussianHalfHeat t) ≤
          xiHeatThirdQuadratic a b c t := by
  obtain ⟨c₀, hc₀, L, hL, hfloor⟩ := exists_xiHeatThirdRealChannel_allTime_floor
  refine ⟨c₀, hc₀, L, hL, ?_⟩
  intro a b c t
  have hd : (xiHeatThirdPolynomial a b c).natDegree ≤ 2 := by
    apply Polynomial.natDegree_add_le_of_degree_le
    · apply Polynomial.natDegree_add_le_of_degree_le
      · simp only [Polynomial.natDegree_C]; omega
      · have h := Polynomial.natDegree_C_mul_X_pow_le b 1
        simp only [pow_one] at h
        omega
    · exact Polynomial.natDegree_C_mul_X_pow_le c 2
  have hK := (tsum_norm_xiPolynomialGaussianHeatTerm_le_gap (xiHeatThirdPolynomial a b c) t).trans
    (mul_le_mul_of_nonneg_right (xiGaussianGapCancellationBudget_mono t
      (show 2 * (xiHeatThirdPolynomial a b c).natDegree ≤ 4 by omega))
      (routeUPolynomialGaussianMass_nonneg (xiHeatThirdPolynomial a b c) (xiGaussianHalfHeat t)))
  have hJ := hfloor a b c t
  rw [xiGaussianRealChannelEnergy_eq_half_energy_add_trace] at hJ
  have heq := xiHeatThirdQuadratic_eq_trace a b c (Real.log (t : ℝ))
  rw [Real.exp_log t.property] at heq
  rw [← heq] at hJ
  linarith only [hJ, hK]

end RHTower
