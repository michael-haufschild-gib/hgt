import GaloisForLFunctions.OrderSixMetaplecticTheory.TheFractionalTraceIsASumOverTheProjectiveLineModuloTheSquare

/-!
# The cusp `0` of the fractional trace reads low points of low points

Conjugating the fractional translations by `S` turns them into lower ones: `T_tS = S A_qL(−t)A_q⁻¹`
(`fracShift_mul_sO`). For `q ∤ t` the Hecke-at-`q` identity `A_qL(−t) = M_{−t}A_q⁻¹T(−β_{−t})`
(`M_{−t} = [[q, 3β_{−t}], [−3t, δ_{−t}]]`) gives

`Θ(T_tSy) = (−3t/q)₃ Θ(A_q⁻¹T(−β_{−t})A_q⁻¹y)`   (`theta_fracShift_sO`),

so that (`fracSum_sO`)

`G_Θ(Sy) = Θ(y)² + Σ_{t ≢ 0} χ(−9t²) Θ^{(−β_{−t})}(A_q⁻¹y) Θ^{(−β_t)}(A_q⁻¹y)`:

products of low points of low points, at height `v/N(q)`, whose phases `χ(−9t²)` sum to zero.
-/

noncomputable section

open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

namespace PrimaryPrime

variable (P : PrimaryPrime)

theorem fracShift_zero : P.fracShift 0 = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [fracShift, complexTranslation]

theorem contraction_mul_dilation : P.contraction * P.dilation = 1 := by
  have hr0 := P.root_ne_zero
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [PrimaryPrime.dilation, PrimaryPrime.contraction, complexDiagonal, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two, hr0]

theorem dilation_fracShift (t : O) :
    P.dilation * P.fracShift t = complexMatrix (transThree t) * P.dilation := by
  have hP := P.ringComplex_ne_zero
  have hr := P.root_sq
  have hr0 := P.root_ne_zero
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [fracShift, complexTranslation, PrimaryPrime.dilation, complexDiagonal, complexMatrix_apply, transThree,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, ringComplex_three]
  rw [← hr]
  field_simp

/-- `T_{3t/q} = A_q⁻¹T(t)A_q`. -/
theorem fracShift_eq (t : O) :
    P.fracShift t = P.contraction * complexMatrix (transThree t) * P.dilation := by
  rw [mul_assoc, ← P.dilation_fracShift, ← mul_assoc, P.contraction_mul_dilation, one_mul]

/-- `T(t)S = S L(−t)` in `SL₂(O)`. -/
theorem transThree_mul_sO (t : O) :
    ((transThree t : levelThree) : SL(2, O)) * sO = sO * ((lowerThree (-t) : levelThree) : SL(2, O)) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [transThree, lowerThree, coe_sO, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

/-- `T_tS = S A_qL(−t)A_q⁻¹`. -/
theorem fracShift_mul_sO (t : O) :
    P.fracShift t * integralComplexMatrix sO =
      integralComplexMatrix sO * (P.dilation * complexMatrix (lowerThree (-t)) * P.contraction) := by
  have h1 : complexMatrix (transThree t) * integralComplexMatrix sO =
      integralComplexMatrix sO * complexMatrix (lowerThree (-t)) := by
    rw [complexMatrix_eq, complexMatrix_eq, ← map_mul, ← map_mul, transThree_mul_sO]
  rw [P.fracShift_eq, mul_assoc, P.dilation_S, ← mul_assoc, mul_assoc P.contraction, h1, ← mul_assoc,
    P.contraction_S, mul_assoc, mul_assoc, mul_assoc]


section Points

variable (Θ : HyperbolicSpace → ℂ)
  (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
  (hΘr : ∀ (r : SL(2, ℤ)) (w : HyperbolicSpace), Θ (integralComplexMatrix (rationalEmbedding r) • w) = Θ w)
include hΘ hΘr

/-- `Θ(T_tSy) = (−3t/q)₃ Θ(A_q⁻¹T(−β_{−t})A_q⁻¹y)` for `q ∤ t`. -/
theorem theta_fracShift_sO (t : O) (ht : ¬ P.p ∣ t) (y : HyperbolicSpace) :
    Θ (P.fracShift t • integralComplexMatrix sO • y) =
      ringComplex (symbol (3 * -t) P.p) * P.heckeLow Θ (-P.lowBeta (-t)) (P.contraction • y) := by
  have ht' : ¬ P.p ∣ -t := fun h => ht (dvd_neg.mp h)
  have hS : ∀ x, Θ (integralComplexMatrix sO • x) = Θ x := hΘr ModularGroup.S
  rw [← mul_smul, P.fracShift_mul_sO, mul_smul, hS, P.dilation_lowerThree (-t) ht', mul_smul, mul_smul, mul_smul,
    hΘ, P.complexCharacter_lowMat]
  rfl

/-- **The fractional correlation at `S` is a sum of low points of low points.** -/
theorem fracSum_sO (y : HyperbolicSpace) :
    P.fracSum Θ (integralComplexMatrix sO • y) = Θ y ^ 2 +
      ∑ x : {x : P.Res // x ≠ 0}, P.chi (-9 * x.1 ^ 2) *
        (P.heckeLow Θ (-P.lowBeta (-P.lift x.1)) (P.contraction • y) *
          P.heckeLow Θ (-P.lowBeta (P.lift x.1)) (P.contraction • y)) := by
  have hS : ∀ x, Θ (integralComplexMatrix sO • x) = Θ x := hΘr ModularGroup.S
  unfold fracSum
  rw [Fintype.sum_eq_add_sum_compl (0 : P.Res),
    Finset.sum_subtype _ (fun x => by simp : ∀ x, x ∈ ({0}ᶜ : Finset P.Res) ↔ x ≠ 0)]
  congr 1
  · rw [show P.lift 0 = P.lift (P.res 0) by rw [map_zero], P.fracCorrelation_lift Θ hΘ, fracCorrelation, neg_zero,
      P.fracShift_zero, one_smul, hS, pow_two]
  · refine Finset.sum_congr rfl fun x _ => ?_
    have hx : ¬ P.p ∣ P.lift x.1 := fun h => x.2 (P.res_lift_eq_zero h)
    have hx' : ¬ P.p ∣ -P.lift x.1 := fun h => hx (dvd_neg.mp h)
    rw [fracCorrelation, P.theta_fracShift_sO Θ hΘ hΘr _ hx, P.theta_fracShift_sO Θ hΘ hΘr _ hx', neg_neg,
      ← P.chi_res, ← P.chi_res, mul_mul_mul_comm, ← map_mul]
    congr 2
    simp only [map_mul, map_neg, res_lift, map_ofNat]
    ring

/-- **The classes over the cusp `0`.** `Σ_{s ∈ O/q²} G_Θ(ST(3s)w) = N(q)²Θ(w)² + (low points of low points)`. -/
theorem sum_fracSum_cuspZero (w : HyperbolicSpace) :
    ∑ s : P.Res × P.Res, P.fracSum Θ (integralComplexMatrix sO • complexMatrix (transThree (P.sqLift s)) • w) =
      (Fintype.card P.Res : ℂ) ^ 2 * Θ w ^ 2 +
        ∑ s : P.Res × P.Res, ∑ x : {x : P.Res // x ≠ 0}, P.chi (-9 * x.1 ^ 2) *
          (P.heckeLow Θ (-P.lowBeta (-P.lift x.1)) (P.contraction • complexMatrix (transThree (P.sqLift s)) • w) *
            P.heckeLow Θ (-P.lowBeta (P.lift x.1)) (P.contraction • complexMatrix (transThree (P.sqLift s)) • w)) := by
  simp_rw [P.fracSum_sO Θ hΘ hΘr, hΘ, complexCharacter_transThree, one_mul]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul]
  push_cast
  ring

end Points

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
