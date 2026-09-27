import GaloisForLFunctions.RHTower.XiGaussianFullGapDerivative
import GaloisForLFunctions.RHTower.XiGaussianDerivativeNodalBudget

/-!
# Actual Hankel control without splitting the heat time

The shifted factorial envelope transfers through the exact adjugate and the
paired critical reserve. Every finite order and positive heat time uses the
full residual rate. No positivity of the remaining relative factor is assumed.
-/

open scoped Real BigOperators
open Complex GaloisForLFunctions.HTGeometry
noncomputable section

namespace RHTower

def xiGaussianFullGapCofactorEnvelope {N : ℕ} (F : Finset XiZeroCopy)
    (x : Fin N → ℝ) (t : {t : ℝ // 0 < t}) : ℝ :=
  ∑ i, xiGaussianFullGapDerivativeEnvelope F
    (∑ j, Polynomial.C ((Matrix.vandermonde x).adjugate j i) * Polynomial.X ^ (j : ℕ)) t *
      Real.exp ((t : ℝ) * x i)

theorem xiGaussianFullGapCofactorEnvelope_nonneg {N : ℕ} (F : Finset XiZeroCopy)
    (x : Fin N → ℝ) (t : {t : ℝ // 0 < t}) : 0 ≤ xiGaussianFullGapCofactorEnvelope F x t :=
  Finset.sum_nonneg fun _ _ => mul_nonneg
    (xiGaussianFullGapDerivativeEnvelope_nonneg F _ t) (Real.exp_pos _).le

theorem xiGaussianImaginaryAtom_le_fullGap_cofactor {N : ℕ} (F : Finset XiZeroCopy)
    (x a : Fin N → ℝ) (t : {t : ℝ // 0 < t}) (q : XiZeroCopy) :
    (Matrix.vandermonde x).det ^ 2 * xiGaussianImaginaryChannelAtom
      (∑ j, Polynomial.C (a j) * Polynomial.X ^ (j : ℕ)) t q ≤
        ((∑ i, ((∑ j, Polynomial.C (a j) * Polynomial.X ^ (j : ℕ)).eval (x i)) ^ 2 *
          Real.exp (-((t : ℝ) * x i))) * Real.exp (-((t : ℝ) * xiCriticalResidualPhaseGap F)) *
            xiGaussianFullGapCofactorEnvelope F x t) * (xiZeroCopyReciprocalSquare q).im ^ 2 := by
  let M := Matrix.vandermonde x
  let h : Fin N → ℝ := fun j =>
    (heatPhaseAmplitude ((xiSpectralPoint q ^ 2) ^ (j : ℕ)) t (xiSpectralPoint q ^ 2)).im
  let E := ∑ i, (M.mulVec a i) ^ 2 * Real.exp (-((t : ℝ) * x i))
  let e := Real.exp (-((t : ℝ) * xiCriticalResidualPhaseGap F))
  let u := (xiZeroCopyReciprocalSquare q).im
  have hE : 0 ≤ E := Finset.sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have hb (i : Fin N) : (∑ j, M.adjugate j i * h j) ^ 2 ≤
      (e * xiGaussianFullGapDerivativeEnvelope F
        (∑ j, Polynomial.C (M.adjugate j i) * Polynomial.X ^ (j : ℕ)) t) * u ^ 2 := by
    have h := xiGaussianImaginaryAtom_le_fullGap_derivative F
      (∑ j, Polynomial.C (M.adjugate j i) * Polynomial.X ^ (j : ℕ)) t q
    rwa [xiGaussianImaginaryChannelAtom_finSum_eq] at h
  have hs := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    mul_le_mul_of_nonneg_right (hb i) (Real.exp_pos ((t : ℝ) * x i)).le
  have hsum : (∑ i, (∑ j, M.adjugate j i * h j) ^ 2 * Real.exp ((t : ℝ) * x i)) ≤
      e * xiGaussianFullGapCofactorEnvelope F x t * u ^ 2 := by
    refine hs.trans_eq ?_
    rw [xiGaussianFullGapCofactorEnvelope, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have htransfer := real_adjugate_heat_phase_bound M a h x t
  have hfinal := htransfer.trans (mul_le_mul_of_nonneg_left hsum hE)
  rw [xiGaussianImaginaryChannelAtom_finSum_eq]
  change M.det ^ 2 * (∑ j, a j * h j) ^ 2 ≤ _
  calc
    _ ≤ E * (e * xiGaussianFullGapCofactorEnvelope F x t * u ^ 2) := hfinal
    _ = _ := by
      dsimp only [E, M, e, u]
      simp only [real_vandermonde_mulVec_eq_eval]
      ring

theorem xiGaussianImaginaryChannel_le_fullGap_cofactor {N : ℕ} (F : Finset XiZeroCopy)
    (x a : Fin N → ℝ) (t : {t : ℝ // 0 < t}) :
    (Matrix.vandermonde x).det ^ 2 *
      (∑' q : XiZeroCopy, xiGaussianImaginaryChannelAtom
        (∑ j, Polynomial.C (a j) * Polynomial.X ^ (j : ℕ)) t q) ≤
      ((∑ i, ((∑ j, Polynomial.C (a j) * Polynomial.X ^ (j : ℕ)).eval (x i)) ^ 2 *
        Real.exp (-((t : ℝ) * x i))) * Real.exp (-((t : ℝ) * xiCriticalResidualPhaseGap F)) *
          xiGaussianFullGapCofactorEnvelope F x t) * xiResidualOrientationBudget F := by
  let Q : Polynomial ℝ := ∑ j, Polynomial.C (a j) * Polynomial.X ^ (j : ℕ)
  let C := (∑ i, Q.eval (x i) ^ 2 * Real.exp (-((t : ℝ) * x i))) *
    Real.exp (-((t : ℝ) * xiCriticalResidualPhaseGap F)) * xiGaussianFullGapCofactorEnvelope F x t
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg
    (Finset.sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
      (Real.exp_pos _).le) (xiGaussianFullGapCofactorEnvelope_nonneg F x t)
  have h := ((summable_xiGaussianImaginaryChannelAtom Q t).mul_left
    ((Matrix.vandermonde x).det ^ 2)).tsum_le_tsum
      (xiGaussianImaginaryAtom_le_fullGap_cofactor F x a t)
      (summable_xiThermalOrientationTerm.mul_left C)
  rw [tsum_mul_left, tsum_mul_left] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (xiThermalOrientationEnergy_le_residualOrientationBudget F) hC)

def xiGaussianFullGapNodalBudget {N : ℕ} (F : Finset XiZeroCopy)
    (x : Fin N → ℝ) (t : {t : ℝ // 0 < t}) : ℝ :=
  (Real.exp (-((t : ℝ) * xiCriticalResidualPhaseGap F)) *
    xiGaussianFullGapCofactorEnvelope F x t * xiResidualOrientationBudget F) /
      (2 * (Matrix.vandermonde x).det ^ 2)

theorem xiGaussianFullGapNodalBudget_nonneg {N : ℕ} (F : Finset XiZeroCopy)
    (x : Fin N → ℝ) (t : {t : ℝ // 0 < t}) : 0 ≤ xiGaussianFullGapNodalBudget F x t :=
  div_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le
    (xiGaussianFullGapCofactorEnvelope_nonneg F x t)) (xiResidualOrientationBudget_pos F).le)
      (mul_nonneg (by positivity) (sq_nonneg _))

/-- Full-rate relative phase control, all orders and all positive heat times. -/
theorem exists_xiGaussian_fullGap_relative_nodal_phase_bound (N : ℕ) :
    ∃ (γ : Fin N → ℝ) (q : Fin N → XiZeroCopy),
      Function.Injective (fun i => γ i ^ 2) ∧
      (∀ i, 0 < γ i ∧ xiSpectralPoint (q i) = (γ i : ℂ)) ∧
      ∀ (F : Finset XiZeroCopy) (a : ℕ → ℝ) (t : {t : ℝ // 0 < t}),
        (∑' r : XiZeroCopy, xiGaussianImaginaryChannelAtom
          (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) t r) ≤
            xiGaussianFullGapNodalBudget F (fun i => γ i ^ 2) t *
              xiGaussianRealChannelEnergy
                (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) t ∧
        (1 - xiGaussianFullGapNodalBudget F (fun i => γ i ^ 2) t) *
          xiGaussianRealChannelEnergy
            (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) t ≤
              xiHeatHankelForm N a t := by
  obtain ⟨γ, q, hinj, hq, hreserve⟩ := exists_xiCriticalGaussian_paired_sampling_reserve N
  refine ⟨γ, q, hinj, hq, ?_⟩
  intro F a t
  let x : Fin N → ℝ := fun i => γ i ^ 2
  let Q : Polynomial ℝ := ∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j
  let D := (Matrix.vandermonde x).det ^ 2
  let E := ∑ i, Q.eval (x i) ^ 2 * Real.exp (-((t : ℝ) * x i))
  let J := xiGaussianRealChannelEnergy Q t
  let I := ∑' r : XiZeroCopy, xiGaussianImaginaryChannelAtom Q t r
  let B := Real.exp (-((t : ℝ) * xiCriticalResidualPhaseGap F)) *
    xiGaussianFullGapCofactorEnvelope F x t * xiResidualOrientationBudget F
  have hD : 0 < D := sq_pos_of_ne_zero (Matrix.det_vandermonde_ne_zero_iff.mpr hinj)
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg (Real.exp_pos _).le
    (xiGaussianFullGapCofactorEnvelope_nonneg F x t)) (xiResidualOrientationBudget_pos F).le
  have heval : (∑ j : Fin N, Polynomial.C (a j) * Polynomial.X ^ (j : ℕ)) = Q :=
    Fin.sum_univ_eq_sum_range (fun j => Polynomial.C (a j) * Polynomial.X ^ j) N
  have hphase := xiGaussianImaginaryChannel_le_fullGap_cofactor F x (fun j => a j) t
  rw [heval] at hphase
  have hphase' : D * I ≤ E * B := by
    change D * I ≤ ((E * _) * _) * _ at hphase
    simpa only [B, mul_assoc] using hphase
  have hpair : 2 * E ≤ J := hreserve Q t
  have hb := mul_le_mul_of_nonneg_left hpair hB
  have hrelative : I ≤ xiGaussianFullGapNodalBudget F x t * J := by
    change I ≤ (B / (2 * D)) * J
    rw [div_mul_eq_mul_div, le_div_iff₀ (mul_pos (by positivity) hD)]
    nlinarith only [hphase', hb]
  refine ⟨hrelative, ?_⟩
  have he := xiGaussianTrace_eq_realChannel_sub_imaginary Q t
  change xiPolynomialGaussianHeatTraceReal Q t = J - I at he
  have htrace : xiPolynomialGaussianHeatTraceReal Q t = xiHeatHankelForm N a t :=
    xiPolynomialGaussianHeatTraceReal_rangeSum t.property N a
  rw [htrace] at he
  change (1 - xiGaussianFullGapNodalBudget F x t) * J ≤ _
  nlinarith only [hrelative, he]

theorem exists_xiHeatThirdQuadratic_fullGap_relative_lower :
    ∃ (γ : Fin 3 → ℝ) (q : Fin 3 → XiZeroCopy),
      Function.Injective (fun i => γ i ^ 2) ∧
      (∀ i, 0 < γ i ∧ xiSpectralPoint (q i) = (γ i : ℂ)) ∧
      ∀ (F : Finset XiZeroCopy) (a b c : ℝ) (t : {t : ℝ // 0 < t}),
        (1 - xiGaussianFullGapNodalBudget F (fun i => γ i ^ 2) t) *
          xiGaussianRealChannelEnergy (xiHeatThirdPolynomial a b c) t ≤
            xiHeatThirdQuadratic a b c t := by
  obtain ⟨γ, q, hinj, hq, hbound⟩ := exists_xiGaussian_fullGap_relative_nodal_phase_bound 3
  refine ⟨γ, q, hinj, hq, ?_⟩
  intro F a b c t
  have h := (hbound F (fun n => if n = 0 then a else if n = 1 then b else c) t).2
  rw [xiHeatThirdQuadratic_eq_hankel]
  simpa [Finset.sum_range_succ, xiHeatThirdPolynomial] using h

end RHTower
