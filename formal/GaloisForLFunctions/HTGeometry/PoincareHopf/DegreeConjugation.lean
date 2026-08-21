import GaloisForLFunctions.HTGeometry.PoincareHopf.DegreeInteger

/-!
# Invariance of the degree under a linear change of coordinates

Conjugating a field by an invertible matrix, `v ↦ A ∘ v ∘ A⁻¹`, and transporting the domain by the
same matrix leaves the degree at the origin unchanged.  In the degree integral the change of
variables `y = A x` contributes `|det A|` while the conjugated Jacobian has the same determinant as
the original one, so the effect is exactly to replace the weight `φ` by `z ↦ |det A| · φ (A z)`,
which again has total mass one and small support.

This is the linear case of the invariance of the local index under a change of chart.
-/

open Matrix Finset Set MeasureTheory

namespace GaloisForLFunctions.HTGeometry.PoincareHopf

variable {n : ℕ} {v : (Fin n → ℝ) → (Fin n → ℝ)} {Ω : Set (Fin n → ℝ)}
  {A : Matrix (Fin n) (Fin n) ℝ}

/-- An invertible matrix as a continuous linear equivalence of `ℝⁿ`. -/
noncomputable def matVecEquiv (A : Matrix (Fin n) (Fin n) ℝ) [Invertible A] :
    (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ) :=
  LinearEquiv.toContinuousLinearEquiv (Matrix.toLinearEquiv' A inferInstance)

theorem matVecEquiv_apply (A : Matrix (Fin n) (Fin n) ℝ) [Invertible A] (z : Fin n → ℝ) :
    matVecEquiv A z = matVec A z := rfl

theorem matVec_inv_left (hA : IsUnit A.det) (y : Fin n → ℝ) : matVec A (matVec A⁻¹ y) = y := by
  simp only [matVec_apply]
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hA, Matrix.one_mulVec]

theorem matVec_inv_right (hA : IsUnit A.det) (x : Fin n → ℝ) : matVec A⁻¹ (matVec A x) = x := by
  simp only [matVec_apply]
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hA, Matrix.one_mulVec]

theorem det_jac_conj (hA : A.det ≠ 0) (hv : ContDiff ℝ 2 v) (x : Fin n → ℝ) :
    (jac (fun y => matVec A (v (matVec A⁻¹ y))) (matVec A x)).det = (jac v x).det := by
  have hAu : IsUnit A.det := Ne.isUnit hA
  have hvd : HasFDerivAt v (fderiv ℝ v (matVec A⁻¹ (matVec A x))) (matVec A⁻¹ (matVec A x)) :=
    (hv.differentiable (by simp) _).hasFDerivAt
  have hcomp : HasFDerivAt (fun y => matVec A (v (matVec A⁻¹ y)))
      ((matVec A).comp ((fderiv ℝ v (matVec A⁻¹ (matVec A x))).comp (matVec A⁻¹)))
      (matVec A x) := by
    have h1 : HasFDerivAt (fun y => matVec A⁻¹ y) (matVec A⁻¹) (matVec A x) :=
      (matVec A⁻¹).hasFDerivAt
    have h2 := hvd.comp (matVec A x) h1
    have h3 := ((matVec A).hasFDerivAt (x := v (matVec A⁻¹ (matVec A x)))).comp (matVec A x) h2
    simpa [Function.comp_def] using h3
  rw [← det_fderiv_eq_det_jac, hcomp.fderiv, ← det_fderiv_eq_det_jac]
  simp only [ContinuousLinearMap.det]
  have hcoe : (((matVec A).comp ((fderiv ℝ v (matVec A⁻¹ (matVec A x))).comp (matVec A⁻¹))) :
      (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
      = ((matVec A : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) ∘ₗ
          ((fderiv ℝ v (matVec A⁻¹ (matVec A x)) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) ∘ₗ
            (matVec A⁻¹ : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))) := rfl
  rw [hcoe, LinearMap.det_comp, LinearMap.det_comp, matVec_inv_right hAu x]
  have hdA : LinearMap.det ((matVec A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :
      (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) = A.det := by
    rw [matVec, LinearMap.coe_toContinuousLinearMap, LinearMap.det_toLin']
  have hdAi : LinearMap.det ((matVec A⁻¹ : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :
      (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) = A⁻¹.det := by
    rw [matVec, LinearMap.coe_toContinuousLinearMap, LinearMap.det_toLin']
  rw [hdA, hdAi, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  field_simp

theorem degIntegral_conj (hA : A.det ≠ 0) (hv : ContDiff ℝ 2 v) (hΩ : IsOpen Ω)
    (φ : (Fin n → ℝ) → ℝ) :
    degIntegral (fun y => matVec A (v (matVec A⁻¹ y))) ((fun z => matVec A z) '' Ω) φ
      = degIntegral v Ω (fun z => |A.det| * φ (matVec A z)) := by
  have hAu : IsUnit A.det := Ne.isUnit hA
  have hinj : Function.Injective (fun z => matVec A z) :=
    Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det A).mpr hAu)
  set w : (Fin n → ℝ) → (Fin n → ℝ) := fun y => matVec A (v (matVec A⁻¹ y)) with hw
  have hcov := MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul volume
    hΩ.measurableSet (f := fun z => matVec A z) (f' := fun _ => matVec A)
    (fun x _ => ((matVec A).hasFDerivAt).hasFDerivWithinAt) (hinj.injOn)
    (fun y => φ (w y) * (jac w y).det)
  rw [degIntegral, degIntegral]
  rw [hcov]
  refine MeasureTheory.setIntegral_congr_fun hΩ.measurableSet fun x _ => ?_
  simp only [det_matVec, smul_eq_mul]
  rw [hw]
  simp only
  rw [matVec_inv_right hAu x]
  have hdet : (jac (fun y => matVec A (v (matVec A⁻¹ y))) (matVec A x)).det = (jac v x).det :=
    det_jac_conj hA hv x
  rw [← hw] at hdet
  rw [hdet]
  ring

theorem degIntegral_sub_zero (f : (Fin n → ℝ) → (Fin n → ℝ)) (Ω : Set (Fin n → ℝ))
    (φ : (Fin n → ℝ) → ℝ) : degIntegral (fun x => f x - 0) Ω φ = degIntegral f Ω φ := by
  simp only [degIntegral, sub_zero]

/-- An invertible matrix is bounded below. -/
theorem exists_lower_bound_matVec (hA : A.det ≠ 0) :
    ∃ c > 0, ∀ z : Fin n → ℝ, c * ‖z‖ ≤ ‖matVec A z‖ := by
  haveI : Invertible A := A.invertibleOfIsUnitDet (Ne.isUnit hA)
  set E := matVecEquiv A with hE
  set M := ‖(E.symm : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))‖ with hM
  have hMnn : 0 ≤ M := norm_nonneg _
  refine ⟨(M + 1)⁻¹, by positivity, fun z => ?_⟩
  have h1 : ‖z‖ ≤ M * ‖matVec A z‖ := by
    have h0 := (E.symm : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)).le_opNorm (E z)
    have hsym : (E.symm : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (E z) = z := by simp
    rw [hsym, matVecEquiv_apply] at h0
    rw [hM]
    exact h0
  rw [inv_mul_le_iff₀ (by linarith)]
  nlinarith [norm_nonneg (matVec A z)]

theorem integral_comp_matVec (hA : A.det ≠ 0) (φ : (Fin n → ℝ) → ℝ) :
    |A.det| * ∫ z, φ (matVec A z) = ∫ w, φ w := by
  have hAu : IsUnit A.det := Ne.isUnit hA
  have hinj : Function.Injective (fun z => matVec A z) :=
    Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det A).mpr hAu)
  have hsurj : (fun z => matVec A z) '' Set.univ = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ⟨matVec A⁻¹ y, Set.mem_univ _, ?_⟩
    exact matVec_inv_left hAu y
  have hcov := MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul volume
    MeasurableSet.univ (f := fun z => matVec A z) (f' := fun _ => matVec A)
    (fun x _ => ((matVec A).hasFDerivAt).hasFDerivWithinAt) (hinj.injOn) φ
  rw [hsurj] at hcov
  simp only [det_matVec, smul_eq_mul, MeasureTheory.setIntegral_univ] at hcov
  rw [hcov, ← MeasureTheory.integral_const_mul]

/-- **Invariance of the degree under a linear change of coordinates.** -/
theorem degree_conj (hA : A.det ≠ 0) (hv : ContDiff ℝ 2 v) (hΩ : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (hfront : ∀ x ∈ frontier Ω, v x ≠ 0) :
    degree (fun y => matVec A (v (matVec A⁻¹ y))) ((fun z => matVec A z) '' Ω) 0
      = degree v Ω 0 := by
  classical
  have hAu : IsUnit A.det := Ne.isUnit hA
  haveI : Invertible A := A.invertibleOfIsUnitDet hAu
  set E := matVecEquiv A with hE
  set w : (Fin n → ℝ) → (Fin n → ℝ) := fun y => matVec A (v (matVec A⁻¹ y)) with hw
  set Ω' := (fun z => matVec A z) '' Ω with hΩ'
  have hwcd : ContDiff ℝ 2 w :=
    (matVec A).contDiff.comp (hv.comp (matVec A⁻¹).contDiff)
  have hΩ'open : IsOpen Ω' := by
    have himeq : Ω' = E.toHomeomorph '' Ω := by
      rw [hΩ']
      exact Set.image_congr' fun z => (matVecEquiv_apply A z).symm
    rw [himeq]
    exact E.toHomeomorph.isOpenMap Ω hΩ
  have hΩ'b : Bornology.IsBounded Ω' := by
    rw [hΩ']
    exact ((matVec A).lipschitz).isBounded_image hΩb
  have hfrontier : frontier Ω' = (fun z => matVec A z) '' frontier Ω := by
    have himeq : Ω' = E.toHomeomorph '' Ω := by
      rw [hΩ']
      exact Set.image_congr' fun z => (matVecEquiv_apply A z).symm
    rw [himeq, frontier, frontier, ← E.toHomeomorph.image_closure,
      ← E.toHomeomorph.image_interior, ← Set.image_sdiff E.toHomeomorph.injective]
    exact Set.image_congr' fun z => matVecEquiv_apply A z
  obtain ⟨c, hcpos, hlow⟩ := exists_lower_bound_matVec hA
  have hKc : IsCompact (frontier Ω) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_frontier
      (hΩb.closure.subset frontier_subset_closure)
  obtain ⟨m, hmpos, hm⟩ := exists_pos_two_lt_of_isCompact hKc hv.continuous
    (fun x hx hcon => hfront x hx (by simpa using hcon))
  set ρ := c * m with hρ
  have hρpos : 0 < ρ := by rw [hρ]; positivity
  have hadmw : AdmissibleRadius w Ω' 0 ρ := by
    refine ⟨hρpos, fun y hy => ?_⟩
    rw [hfrontier] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have h1 := hm x hx
    simp only [sub_zero] at h1 ⊢
    have h2 : w (matVec A x) = matVec A (v x) := by
      rw [hw]
      simp only
      rw [matVec_inv_right hAu x]
    rw [h2]
    have h3 : c * ‖v x‖ ≤ ‖matVec A (v x)‖ := hlow _
    rw [hρ]
    nlinarith
  have hadmv : AdmissibleRadius v Ω 0 m := by
    refine ⟨hmpos, fun x hx => ?_⟩
    have := hm x hx
    simpa using this
  set φ := bumpWeight (n := n) ρ with hφ
  set ψ : (Fin n → ℝ) → ℝ := fun z => |A.det| * φ (matVec A z) with hψ
  have hψcd : ContDiff ℝ 1 ψ :=
    contDiff_const.mul ((bumpWeight_contDiff hρpos).comp (matVec A).contDiff)
  have hψsupp : ∀ z : Fin n → ℝ, m ≤ ‖z‖ → ψ z = 0 := by
    intro z hz
    have h1 : c * m ≤ ‖matVec A z‖ := le_trans (by nlinarith [hcpos]) (hlow z)
    have h2 : φ (matVec A z) = 0 := by
      rw [hφ]
      exact bumpWeight_eq_zero hρpos (matVec A z) (by rw [hρ]; exact h1)
    rw [hψ]
    simp only
    rw [h2, mul_zero]
  have hψmass : ∫ z, ψ z = 1 := by
    rw [hψ]
    simp only
    rw [MeasureTheory.integral_const_mul, integral_comp_matVec hA φ]
    exact bumpWeight_integral hρpos
  rw [degree_eq_degIntegral hwcd hΩ'open hΩ'b hadmw (bumpWeight_contDiff hρpos)
      (bumpWeight_eq_zero hρpos) (bumpWeight_integral hρpos),
    degree_eq_degIntegral hv hΩ hΩb hadmv hψcd hψsupp hψmass,
    degIntegral_sub_zero, degIntegral_sub_zero, hw, hΩ']
  exact degIntegral_conj hA hv hΩ φ

theorem det_jac_leftComp (hv : ContDiff ℝ 2 v) (x : Fin n → ℝ) :
    (jac (fun z => matVec A (v z)) x).det = A.det * (jac v x).det := by
  have hvd : HasFDerivAt v (fderiv ℝ v x) x := (hv.differentiable (by simp) x).hasFDerivAt
  have hcomp : HasFDerivAt (fun z => matVec A (v z)) ((matVec A).comp (fderiv ℝ v x)) x := by
    have h := ((matVec A).hasFDerivAt (x := v x)).comp x hvd
    simpa [Function.comp_def] using h
  rw [← det_fderiv_eq_det_jac, hcomp.fderiv, ← det_fderiv_eq_det_jac]
  simp only [ContinuousLinearMap.det]
  have hcoe : (((matVec A).comp (fderiv ℝ v x)) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
      = ((matVec A : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) ∘ₗ
          (fderiv ℝ v x : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) := rfl
  rw [hcoe, LinearMap.det_comp]
  congr 1
  rw [matVec, LinearMap.coe_toContinuousLinearMap, LinearMap.det_toLin']

/-- **Left composition with an invertible matrix multiplies the degree by the sign of the
determinant.** -/
theorem degree_leftComp_matVec (hA : A.det ≠ 0) (hv : ContDiff ℝ 2 v) (hΩ : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (hfront : ∀ x ∈ frontier Ω, v x ≠ 0) :
    degree (fun x => matVec A (v x)) Ω 0
      = (if 0 < A.det then (1 : ℝ) else -1) * degree v Ω 0 := by
  classical
  have hAu : IsUnit A.det := Ne.isUnit hA
  have hcd : ContDiff ℝ 2 (fun x => matVec A (v x)) := (matVec A).contDiff.comp hv
  obtain ⟨c, hcpos, hlow⟩ := exists_lower_bound_matVec hA
  have hKc : IsCompact (frontier Ω) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_frontier
      (hΩb.closure.subset frontier_subset_closure)
  obtain ⟨m, hmpos, hm⟩ := exists_pos_two_lt_of_isCompact hKc hv.continuous
    (fun x hx hcon => hfront x hx (by simpa using hcon))
  set ρ := c * m with hρ
  have hρpos : 0 < ρ := by rw [hρ]; positivity
  have hadmA : AdmissibleRadius (fun x => matVec A (v x)) Ω 0 ρ := by
    refine ⟨hρpos, fun x hx => ?_⟩
    have h1 := hm x hx
    simp only [sub_zero] at h1 ⊢
    have h3 : c * ‖v x‖ ≤ ‖matVec A (v x)‖ := hlow _
    rw [hρ]
    nlinarith
  have hadmv : AdmissibleRadius v Ω 0 m := by
    refine ⟨hmpos, fun x hx => ?_⟩
    have := hm x hx
    simpa using this
  set φ := bumpWeight (n := n) ρ with hφ
  set ψ : (Fin n → ℝ) → ℝ := fun z => |A.det| * φ (matVec A z) with hψ
  have hψcd : ContDiff ℝ 1 ψ :=
    contDiff_const.mul ((bumpWeight_contDiff hρpos).comp (matVec A).contDiff)
  have hψsupp : ∀ z : Fin n → ℝ, m ≤ ‖z‖ → ψ z = 0 := by
    intro z hz
    have h1 : c * m ≤ ‖matVec A z‖ := le_trans (by nlinarith [hcpos]) (hlow z)
    have h2 : φ (matVec A z) = 0 := by
      rw [hφ]
      exact bumpWeight_eq_zero hρpos (matVec A z) (by rw [hρ]; exact h1)
    rw [hψ]
    simp only
    rw [h2, mul_zero]
  have hψmass : ∫ z, ψ z = 1 := by
    rw [hψ]
    simp only
    rw [MeasureTheory.integral_const_mul, integral_comp_matVec hA φ]
    exact bumpWeight_integral hρpos
  rw [degree_eq_degIntegral hcd hΩ hΩb hadmA (bumpWeight_contDiff hρpos)
      (bumpWeight_eq_zero hρpos) (bumpWeight_integral hρpos),
    degree_eq_degIntegral hv hΩ hΩb hadmv hψcd hψsupp hψmass,
    degIntegral_sub_zero, degIntegral_sub_zero]
  have hstep : degIntegral (fun x => matVec A (v x)) Ω φ
      = A.det * degIntegral v Ω (fun z => φ (matVec A z)) := by
    rw [degIntegral, degIntegral, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun hΩ.measurableSet fun x _ => ?_
    rw [det_jac_leftComp hv x]
    ring
  have hψint : degIntegral v Ω ψ = |A.det| * degIntegral v Ω (fun z => φ (matVec A z)) := by
    rw [degIntegral, degIntegral, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun hΩ.measurableSet fun x _ => ?_
    rw [hψ]
    ring
  rw [hstep, hψint]
  rcases lt_or_gt_of_ne hA with hneg | hpos
  · rw [if_neg (by linarith), abs_of_neg hneg]
    ring
  · rw [if_pos hpos, abs_of_pos hpos]
    ring

end GaloisForLFunctions.HTGeometry.PoincareHopf
