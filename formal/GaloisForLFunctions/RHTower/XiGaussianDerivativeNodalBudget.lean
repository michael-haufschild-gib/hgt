import GaloisForLFunctions.RHTower.XiGaussianDerivativeCofactorTransfer
import GaloisForLFunctions.RHTower.XiCriticalGaussianPairedSamples

/-!
# Signed-derivative phase control at every finite order and positive heat time

The node family is supplied unconditionally and fixed before coefficients,
source selections, and heat times are chosen. The complete phase is bounded
relative to the real channel without replacing nodal energy by a scalar
coefficient floor.
-/

open scoped Real BigOperators
open Complex
noncomputable section

namespace RHTower

def xiGaussianDerivativeNodalBudget {N : ℕ} (F : Finset XiZeroCopy) (x : Fin N → ℝ)
    (s : {s : ℝ // 0 < s}) (t : ℝ) : ℝ :=
  (Real.exp (-((t - (s : ℝ)) * xiCriticalResidualPhaseGap F)) *
    xiGaussianDerivativeCofactorEnvelope x s t * xiResidualOrientationBudget F) /
      (2 * (Matrix.vandermonde x).det ^ 2)

theorem xiGaussianDerivativeNodalBudget_nonneg {N : ℕ} (F : Finset XiZeroCopy) (x : Fin N → ℝ)
    (s : {s : ℝ // 0 < s}) (t : ℝ) : 0 ≤ xiGaussianDerivativeNodalBudget F x s t :=
  div_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le
    (xiGaussianDerivativeCofactorEnvelope_nonneg x s t)) (xiResidualOrientationBudget_pos F).le)
      (mul_nonneg (by positivity) (sq_nonneg _))

/-- One actual paired family controls the complete phase in every coefficient direction. -/
theorem exists_xiGaussian_derivative_relative_nodal_phase_bound (N : ℕ) :
    ∃ (γ : Fin N → ℝ) (q : Fin N → XiZeroCopy),
      Function.Injective (fun i => γ i ^ 2) ∧
      (∀ i, 0 < γ i ∧ xiSpectralPoint (q i) = (γ i : ℂ)) ∧
      ∀ (F : Finset XiZeroCopy) (a : ℕ → ℝ) (s : {s : ℝ // 0 < s})
        (t : {t : {t : ℝ // 0 < t} // (s : ℝ) ≤ (t : ℝ)}),
        (∑' r : XiZeroCopy, xiGaussianImaginaryChannelAtom
          (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) t.1 r) ≤
            xiGaussianDerivativeNodalBudget F (fun i => γ i ^ 2) s t.1 *
              xiGaussianRealChannelEnergy
                (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) t.1 ∧
        (1 - xiGaussianDerivativeNodalBudget F (fun i => γ i ^ 2) s t.1) *
          xiGaussianRealChannelEnergy
            (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) t.1 ≤
              xiHeatHankelForm N a t.1 := by
  obtain ⟨γ, q, hinj, hq, hreserve⟩ := exists_xiCriticalGaussian_paired_sampling_reserve N
  refine ⟨γ, q, hinj, hq, ?_⟩
  intro F a s t
  let x : Fin N → ℝ := fun i => γ i ^ 2
  let Q : Polynomial ℝ := ∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j
  let D := (Matrix.vandermonde x).det ^ 2
  let E := ∑ i, Q.eval (x i) ^ 2 * Real.exp (-((t.1 : ℝ) * x i))
  let J := xiGaussianRealChannelEnergy Q t.1
  let I := ∑' r : XiZeroCopy, xiGaussianImaginaryChannelAtom Q t.1 r
  let B := Real.exp (-(((t.1 : ℝ) - (s : ℝ)) * xiCriticalResidualPhaseGap F)) *
    xiGaussianDerivativeCofactorEnvelope x s t.1 * xiResidualOrientationBudget F
  have hD : 0 < D := sq_pos_of_ne_zero (Matrix.det_vandermonde_ne_zero_iff.mpr hinj)
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg (Real.exp_pos _).le
    (xiGaussianDerivativeCofactorEnvelope_nonneg x s t.1)) (xiResidualOrientationBudget_pos F).le
  have heval : (∑ j : Fin N, Polynomial.C (a j) * Polynomial.X ^ (j : ℕ)) = Q :=
    Fin.sum_univ_eq_sum_range (fun j => Polynomial.C (a j) * Polynomial.X ^ j) N
  have hphase := xiGaussianImaginaryChannel_le_derivative_cofactor_budget F x (fun j => a j) s t
  rw [heval] at hphase
  have hphase' : D * I ≤ E * B := by
    change D * I ≤ ((E * _) * _) * _ at hphase
    simpa only [B, mul_assoc] using hphase
  have hpair : 2 * E ≤ J := hreserve Q t.1
  have hb := mul_le_mul_of_nonneg_left hpair hB
  have hrelative : I ≤ xiGaussianDerivativeNodalBudget F x s t.1 * J := by
    change I ≤ (B / (2 * D)) * J
    rw [div_mul_eq_mul_div, le_div_iff₀ (mul_pos (by positivity) hD)]
    nlinarith only [hphase', hb]
  refine ⟨hrelative, ?_⟩
  have he := xiGaussianTrace_eq_realChannel_sub_imaginary Q t.1
  change xiPolynomialGaussianHeatTraceReal Q t.1 = J - I at he
  have htrace : xiPolynomialGaussianHeatTraceReal Q t.1 = xiHeatHankelForm N a t.1 :=
    xiPolynomialGaussianHeatTraceReal_rangeSum t.1.property N a
  rw [htrace] at he
  change (1 - xiGaussianDerivativeNodalBudget F x s t.1) * J ≤ _
  nlinarith only [hrelative, he]

/-- Half-time anchoring supplies a coefficient-uniform relative bound on the entire positive axis. -/
theorem exists_xiHeatHankelForm_allTime_derivative_relative_lower (N : ℕ) :
    ∃ (γ : Fin N → ℝ) (q : Fin N → XiZeroCopy),
      Function.Injective (fun i => γ i ^ 2) ∧
      (∀ i, 0 < γ i ∧ xiSpectralPoint (q i) = (γ i : ℂ)) ∧
      ∀ (F : Finset XiZeroCopy) (a : ℕ → ℝ) (t : {t : ℝ // 0 < t}),
        (1 - xiGaussianDerivativeNodalBudget F (fun i => γ i ^ 2) (xiGaussianHalfHeat t) t) *
          xiGaussianRealChannelEnergy
            (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) t ≤
              xiHeatHankelForm N a t := by
  obtain ⟨γ, q, hinj, hq, hbound⟩ := exists_xiGaussian_derivative_relative_nodal_phase_bound N
  refine ⟨γ, q, hinj, hq, ?_⟩
  intro F a t
  exact (hbound F a (xiGaussianHalfHeat t)
    ⟨t, by change (t : ℝ) / 2 ≤ (t : ℝ); linarith only [t.property]⟩).2

/-- The literal complete three-by-three form obeys the same relative estimate. -/
theorem exists_xiHeatThirdQuadratic_allTime_derivative_relative_lower :
    ∃ (γ : Fin 3 → ℝ) (q : Fin 3 → XiZeroCopy),
      Function.Injective (fun i => γ i ^ 2) ∧
      (∀ i, 0 < γ i ∧ xiSpectralPoint (q i) = (γ i : ℂ)) ∧
      ∀ (F : Finset XiZeroCopy) (a b c : ℝ) (t : {t : ℝ // 0 < t}),
        (1 - xiGaussianDerivativeNodalBudget F (fun i => γ i ^ 2) (xiGaussianHalfHeat t) t) *
          xiGaussianRealChannelEnergy (xiHeatThirdPolynomial a b c) t ≤
            xiHeatThirdQuadratic a b c t := by
  obtain ⟨γ, q, hinj, hq, hbound⟩ := exists_xiHeatHankelForm_allTime_derivative_relative_lower 3
  refine ⟨γ, q, hinj, hq, ?_⟩
  intro F a b c t
  have h := hbound F (fun n => if n = 0 then a else if n = 1 then b else c) t
  rw [xiHeatThirdQuadratic_eq_hankel]
  simpa [Finset.sum_range_succ, xiHeatThirdPolynomial] using h

end RHTower
