import GaloisForLFunctions.OrderSixMetaplecticTheory.TheConstantTermOfTheFractionalTraceReadsTheConjugateTwist

/-!
# The fractional points of a ramified cusp are ramified

For M ∈ SL₂(O) with ramified column (colRes ≠ 0) and x of height v, A_q^{±1}Mx = M'x' with M' ramified and
height(x') ≥ v/|q| (`dilation_ramified`, `contraction_ramified`). Since T_{3t/q} = A_q⁻¹T(t)A_q and both Γ(3) and T(t)
preserve the column residue modulo 3 (`colRes_levelThree_mul`), every fractional point of a ramified point
is ramified, of height ≥ v/N(q), where θ_s is bounded (`theta_fracShift_ramified`). Hence the fractional trace
is bounded at the ramified cusps (`norm_sourceFracTrace_ramified`).
-/

noncomputable section

open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

/-- Γ(3) preserves the column residue modulo 3. -/
theorem colRes_levelThree_mul (γ : levelThree) (M : SL(2, O)) :
    colRes (((γ : SL(2, O)) * M) 0 0) (((γ : SL(2, O)) * M) 1 0) = colRes (M 0 0) (M 1 0) := by
  have h00 := levelThree_entry γ 0 0
  have h01 := levelThree_entry γ 0 1
  have h10 := levelThree_entry γ 1 0
  have h11 := levelThree_entry γ 1 1
  simp only [Fin.isValue, if_true, zero_ne_one, one_ne_zero, if_false, sub_zero] at h00 h01 h10 h11
  obtain ⟨a, ha⟩ := h00
  obtain ⟨b, hb⟩ := h01
  obtain ⟨c, hc⟩ := h10
  obtain ⟨d, hd⟩ := h11
  have e0 : ((γ : SL(2, O)) * M) 0 0 = (γ : SL(2, O)) 0 0 * M 0 0 + (γ : SL(2, O)) 0 1 * M 1 0 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have e1 : ((γ : SL(2, O)) * M) 1 0 = (γ : SL(2, O)) 1 0 * M 0 0 + (γ : SL(2, O)) 1 1 * M 1 0 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  rw [colRes, colRes, cuspResidue_congr (x := ((γ : SL(2, O)) * M) 0 0) (y := M 0 0)
      ⟨a * M 0 0 + b * M 1 0, by rw [e0]; linear_combination (M 0 0) * ha + (M 1 0) * hb⟩,
    cuspResidue_congr (x := ((γ : SL(2, O)) * M) 1 0) (y := M 1 0)
      ⟨c * M 0 0 + d * M 1 0, by rw [e1]; linear_combination (M 0 0) * hc + (M 1 0) * hd⟩]

namespace PrimaryPrime

variable (P : PrimaryPrime)

theorem dilation_ramified (M : SL(2, O)) (hcol : colRes (M 0 0) (M 1 0) ≠ 0) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    ∃ (M' : SL(2, O)) (z' : ℂ) (v' : ℝ) (hv' : 0 < v'), colRes (M' 0 0) (M' 1 0) ≠ 0 ∧ v / ‖ringComplex P.p‖ ≤ v' ∧
      P.dilation • integralComplexMatrix M • upperPoint z v hv = integralComplexMatrix M' • upperPoint z' v' hv' := by
  have hn := P.norm_pos
  obtain ⟨N', g, hg, hp, hq, U, hU10, hU00, hfac⟩ := P.dilation_factor M
  have hc : colRes (N' 0 0) (N' 1 0) ≠ 0 := by
    refine colRes_ne_zero_of_factor hp hq ?_
    rw [P.colRes_p_left]
    exact hcol
  obtain ⟨z', v', hv', hpt⟩ := upperPoint_surjective (U • upperPoint z v hv)
  have hvv : v' = v * (‖ringComplex g‖ ^ 2 / ‖ringComplex P.p‖) := by
    have h := height_upper_triangular_complex U hU10 z v hv
    rw [← hpt, hyperbolicHeight_upperPoint, hU00] at h
    exact h
  have hg1 := one_le_norm_sq_ringComplex hg
  refine ⟨N', z', v', hv', hc, ?_, ?_⟩
  · rw [hvv, mul_div_assoc']
    exact div_le_div_of_nonneg_right (by nlinarith) hn.le
  · rw [← mul_smul, hfac, mul_smul, hpt]

theorem contraction_ramified (M : SL(2, O)) (hcol : colRes (M 0 0) (M 1 0) ≠ 0) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    ∃ (M' : SL(2, O)) (z' : ℂ) (v' : ℝ) (hv' : 0 < v'), colRes (M' 0 0) (M' 1 0) ≠ 0 ∧ v / ‖ringComplex P.p‖ ≤ v' ∧
      P.contraction • integralComplexMatrix M • upperPoint z v hv = integralComplexMatrix M' • upperPoint z' v' hv' := by
  have hn := P.norm_pos
  obtain ⟨N', g, hg, hp, hq, U, hU10, hU00, hfac⟩ := P.contraction_factor M
  have hc : colRes (N' 0 0) (N' 1 0) ≠ 0 := by
    refine colRes_ne_zero_of_factor hp hq ?_
    rw [P.colRes_p_right]
    exact hcol
  obtain ⟨z', v', hv', hpt⟩ := upperPoint_surjective (U • upperPoint z v hv)
  have hvv : v' = v * (‖ringComplex g‖ ^ 2 / ‖ringComplex P.p‖) := by
    have h := height_upper_triangular_complex U hU10 z v hv
    rw [← hpt, hyperbolicHeight_upperPoint, hU00] at h
    exact h
  have hg1 := one_le_norm_sq_ringComplex hg
  refine ⟨N', z', v', hv', hc, ?_, ?_⟩
  · rw [hvv, mul_div_assoc']
    exact div_le_div_of_nonneg_right (by nlinarith) hn.le
  · rw [← mul_smul, hfac, mul_smul, hpt]

/-- θ_s is bounded at the fractional points of a ramified point. -/
theorem theta_fracShift_ramified (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : O) (M : SL(2, O)), colRes (M 0 0) (M 1 0) ≠ 0 →
      ∀ (z : ℂ) (v : ℝ) (hv : 0 < v), a ≤ v →
        ‖sourceTheta (P.fracShift t • integralComplexMatrix M • upperPoint z v hv)‖ ≤ C := by
  have hn := P.norm_pos
  obtain ⟨C, β, hC, hβ, hdec⟩ :=
    sourceTheta_ramified_decay (a / ‖ringComplex P.p‖ / ‖ringComplex P.p‖) (div_pos (div_pos ha hn) hn)
  refine ⟨C, hC, fun t M hcol z v hv hav => ?_⟩
  obtain ⟨M₁, z₁, v₁, hv₁, hc₁, hle₁, he₁⟩ := P.dilation_ramified M hcol z v hv
  have hc₁' : colRes (((transThree t : SL(2, O)) * M₁) 0 0) (((transThree t : SL(2, O)) * M₁) 1 0) ≠ 0 := by
    rw [colRes_levelThree_mul]
    exact hc₁
  obtain ⟨M₂, z₂, v₂, hv₂, hc₂, hle₂, he₂⟩ := P.contraction_ramified _ hc₁' z₁ v₁ hv₁
  have hpt : P.fracShift t • integralComplexMatrix M • upperPoint z v hv =
      integralComplexMatrix M₂ • upperPoint z₂ v₂ hv₂ := by
    rw [P.fracShift_eq, mul_smul, mul_smul, he₁, ← mul_smul (complexMatrix (transThree t)), complexMatrix_eq,
      ← map_mul, he₂]
  rw [hpt]
  have hav₂ : a / ‖ringComplex P.p‖ / ‖ringComplex P.p‖ ≤ v₂ := by
    have h1 : a / ‖ringComplex P.p‖ ≤ v₁ := le_trans (div_le_div_of_nonneg_right hav hn.le) hle₁
    exact le_trans (div_le_div_of_nonneg_right h1 hn.le) hle₂
  refine (hdec M₂ hc₂ z₂ v₂ hv₂ hav₂).trans ?_
  have : Real.exp (-β * v₂) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  nlinarith

/-- **The fractional trace is bounded at the ramified cusps.** -/
theorem norm_sourceFracTrace_ramified (a : ℝ) (ha : 0 < a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (j : Fin 3), j ≠ 0 → ∀ (z : ℂ) (v : ℝ) (hv : 0 < v), a ≤ v →
      ‖P.sourceFracTrace (integralComplexMatrix (cuspRepresentative j) • upperPoint z v hv)‖ ≤ K := by
  obtain ⟨C, hC, hθ⟩ := P.theta_fracShift_ramified a ha
  set N : ℝ := (Fintype.card P.Res : ℝ)
  set I : ℝ := (Fintype.card P.FracIndex : ℝ)
  refine ⟨I * (N * C ^ 2), by positivity, fun j hj z v hv hav => ?_⟩
  rw [sourceFracTrace, P.fracTrace_eq_sum sourceTheta sourceTheta_automorphy]
  have hpt : ∀ (i : P.FracIndex) (t : O), ‖sourceTheta (P.fracShift t • complexMatrix (P.fracRep i) •
      integralComplexMatrix (cuspRepresentative j) • upperPoint z v hv)‖ ≤ C := by
    intro i t
    rw [← mul_smul (complexMatrix (P.fracRep i)) (integralComplexMatrix (cuspRepresentative j)), complexMatrix_eq,
      ← map_mul]
    exact hθ t _ (by rw [colRes_levelThree_mul]; exact colRes_cuspRepresentative j hj) z v hv hav
  have hG : ∀ i : P.FracIndex, ‖P.fracSum sourceTheta (complexMatrix (P.fracRep i) •
      integralComplexMatrix (cuspRepresentative j) • upperPoint z v hv)‖ ≤ N * C ^ 2 := by
    intro i
    unfold fracSum fracCorrelation
    refine (norm_sum_le _ _).trans ?_
    calc ∑ x : P.Res, ‖sourceTheta (P.fracShift (P.lift x) • complexMatrix (P.fracRep i) •
          integralComplexMatrix (cuspRepresentative j) • upperPoint z v hv) *
          sourceTheta (P.fracShift (-P.lift x) • complexMatrix (P.fracRep i) •
            integralComplexMatrix (cuspRepresentative j) • upperPoint z v hv)‖ ≤ ∑ _x : P.Res, C ^ 2 := by
          refine Finset.sum_le_sum fun x _ => ?_
          rw [norm_mul, sq]
          exact mul_le_mul (hpt i _) (hpt i _) (norm_nonneg _) hC
      _ = N * C ^ 2 := by simp [N]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i : P.FracIndex, ‖P.fracSum sourceTheta (complexMatrix (P.fracRep i) •
        integralComplexMatrix (cuspRepresentative j) • upperPoint z v hv)‖ ≤ ∑ _i : P.FracIndex, N * C ^ 2 :=
        Finset.sum_le_sum fun i _ => hG i
    _ = I * (N * C ^ 2) := by simp [I]

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
