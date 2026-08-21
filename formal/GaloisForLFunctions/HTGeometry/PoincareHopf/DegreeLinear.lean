import GaloisForLFunctions.HTGeometry.PoincareHopf.DegreeProperties

/-!
# The degree of a linear isomorphism

A matrix with nonzero determinant, viewed as a self-map of `ℝⁿ`, has degree `±1` at the origin on
any bounded open neighbourhood of the origin, the sign being that of the determinant.  The
determinant factor in the degree integral and the Jacobian factor of the change of variables cancel
up to that sign.

This is the local index of a nondegenerate zero of a vector field.
-/

open Matrix Finset Set MeasureTheory

namespace GaloisForLFunctions.HTGeometry.PoincareHopf

variable {n : ℕ} {Ω : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → (Fin n → ℝ)} {y : Fin n → ℝ} {ρ : ℝ}

theorem AdmissibleRadius.mono (h : AdmissibleRadius f Ω y ρ) {ρ' : ℝ} (hρ' : 0 < ρ')
    (hle : ρ' ≤ ρ) : AdmissibleRadius f Ω y ρ' :=
  ⟨hρ', fun x hx => lt_of_le_of_lt (by linarith) (h.2 x hx)⟩

/-- **A nonzero degree forces a solution.** -/
theorem exists_eq_of_degree_ne_zero (hf : ContDiff ℝ 2 f) (hΩ : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (h : degree f Ω y ≠ 0) : ∃ x ∈ closure Ω, f x = y := by
  by_contra hcon
  push Not at hcon
  have hK : IsCompact (closure Ω) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure hΩb.closure
  rcases eq_empty_or_nonempty (closure Ω) with hemp | hne
  · have hΩemp : Ω = ∅ := by
      rw [← subset_empty_iff, ← hemp]
      exact subset_closure
    apply h
    have hadm : AdmissibleRadius f Ω y 1 := by
      refine ⟨one_pos, fun x hx => ?_⟩
      rw [hΩemp] at hx
      simp at hx
    rw [degree_eq_degIntegral hf hΩ hΩb hadm (bumpWeight_contDiff one_pos)
      (bumpWeight_eq_zero one_pos) (bumpWeight_integral one_pos), degIntegral, hΩemp]
    simp
  · obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hne
      (((hf.continuous.sub continuous_const).norm).continuousOn)
    have hpos : 0 < ‖f x₀ - y‖ := by
      rw [norm_pos_iff, sub_ne_zero]
      exact hcon x₀ hx₀
    set ρ₀ := ‖f x₀ - y‖ / 3 with hρ₀
    have hρ₀pos : 0 < ρ₀ := by rw [hρ₀]; linarith
    have hbound : ∀ x ∈ closure Ω, ρ₀ + ρ₀ < ‖f x - y‖ := by
      intro x hx
      have hle : ‖f x₀ - y‖ ≤ ‖f x - y‖ := hmin hx
      rw [hρ₀]; linarith
    have hadm : AdmissibleRadius f Ω y ρ₀ :=
      ⟨hρ₀pos, fun x hx => hbound x (frontier_subset_closure hx)⟩
    apply h
    rw [degree_eq_degIntegral hf hΩ hΩb hadm (bumpWeight_contDiff hρ₀pos)
      (bumpWeight_eq_zero hρ₀pos) (bumpWeight_integral hρ₀pos), degIntegral]
    refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
    have hb := hbound x (subset_closure hx)
    rw [bumpWeight_eq_zero hρ₀pos (f x - y) (by linarith), zero_mul]

/-- A matrix as a continuous linear self-map of `ℝⁿ`. -/
noncomputable def matVec (A : Matrix (Fin n) (Fin n) ℝ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' A)

@[simp] theorem matVec_apply (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    matVec A v = A *ᵥ v := rfl

theorem det_matVec (A : Matrix (Fin n) (Fin n) ℝ) :
    ContinuousLinearMap.det (matVec A) = A.det := by
  rw [ContinuousLinearMap.det, matVec, LinearMap.coe_toContinuousLinearMap, LinearMap.det_toLin']

theorem jac_matVec_affine (A : Matrix (Fin n) (Fin n) ℝ) (p x : Fin n → ℝ) :
    jac (fun z => matVec A (z - p) - (0 : Fin n → ℝ)) x = A := by
  have h : HasFDerivAt (fun z => matVec A (z - p) - (0 : Fin n → ℝ)) (matVec A) x := by
    have h1 : HasFDerivAt (fun z : Fin n → ℝ => z - p) (ContinuousLinearMap.id ℝ (Fin n → ℝ)) x :=
      (hasFDerivAt_id x).sub_const p
    have h2 := ((matVec A).hasFDerivAt (x := x - p)).comp x h1
    simpa [Function.comp_def] using h2.sub_const 0
  funext a b
  rw [jac, Matrix.of_apply, h.fderiv]
  simp

/-- **The degree of an invertible affine map is the sign of its determinant.** -/
theorem degree_matVec_affine (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0) (p : Fin n → ℝ)
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (hp : p ∈ Ω) :
    degree (fun z => matVec A (z - p)) Ω 0 = if 0 < A.det then 1 else -1 := by
  classical
  have hcd : ContDiff ℝ 2 (fun z => matVec A (z - p)) :=
    (matVec A).contDiff.comp (contDiff_id.sub contDiff_const)
  have hunitA : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr (Ne.isUnit hA)
  have hinjA : Function.Injective (fun z => matVec A z) :=
    Matrix.mulVec_injective_iff_isUnit.mpr hunitA
  have hinj : Function.Injective (fun z => matVec A (z - p)) := fun u v huv => by
    have h1 := hinjA huv
    have h2 : u - p = v - p := h1
    exact sub_left_injective h2
  haveI : Invertible A := A.invertibleOfIsUnitDet (Ne.isUnit hA)
  set E : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ) :=
    LinearEquiv.toContinuousLinearEquiv (Matrix.toLinearEquiv' A inferInstance) with hE
  have hEapp : ∀ v : Fin n → ℝ, E v = matVec A v := fun v => rfl
  set H : (Fin n → ℝ) ≃ₜ (Fin n → ℝ) := (Homeomorph.subRight p).trans E.toHomeomorph with hH
  have hHapp : ∀ v : Fin n → ℝ, H v = matVec A (v - p) := fun v => rfl
  have himg : IsOpen ((fun z => matVec A (z - p)) '' Ω) := by
    have himeq : (fun z => matVec A (z - p)) '' Ω = H '' Ω :=
      Set.image_congr' (fun v => (hHapp v).symm)
    rw [himeq]
    exact H.isOpenMap Ω hΩ
  have h0img : (0 : Fin n → ℝ) ∈ (fun z => matVec A (z - p)) '' Ω := ⟨p, hp, by simp⟩
  obtain ⟨r, hr, hrball⟩ := Metric.isOpen_iff.mp himg 0 h0img
  have hnotmem : (0 : Fin n → ℝ) ∉ (fun z => matVec A (z - p)) '' frontier Ω := by
    rintro ⟨x, hx, hx0⟩
    have hxp : x = p := by
      have h3 : matVec A (x - p) = matVec A (0 : Fin n → ℝ) := by simpa using hx0
      have h4 := hinjA h3
      have h5 : x - p = 0 := h4
      exact sub_eq_zero.mp h5
    rw [hxp, hΩ.frontier_eq] at hx
    exact hx.2 hp
  obtain ⟨ρ₁, hadm₁⟩ := exists_admissibleRadius hcd.continuous hΩb hnotmem
  set ρ₀ := min ρ₁ (r / 2) with hρ₀
  have hρ₀pos : 0 < ρ₀ := lt_min hadm₁.1 (by linarith)
  have hadm : AdmissibleRadius (fun z => matVec A (z - p)) Ω 0 ρ₀ :=
    hadm₁.mono hρ₀pos (min_le_left _ _)
  have hballsub : Metric.ball (0 : Fin n → ℝ) ρ₀ ⊆ (fun z => matVec A (z - p)) '' Ω := by
    refine subset_trans (Metric.ball_subset_ball ?_) hrball
    calc ρ₀ ≤ r / 2 := min_le_right _ _
      _ ≤ r := by linarith
  set φ := bumpWeight (n := n) ρ₀ with hφ
  have hbc : ContDiff ℝ 1 φ := bumpWeight_contDiff hρ₀pos
  have hbs : ∀ w : Fin n → ℝ, ρ₀ ≤ ‖w‖ → φ w = 0 := bumpWeight_eq_zero hρ₀pos
  have hbm : ∫ w, φ w = 1 := bumpWeight_integral hρ₀pos
  rw [degree_eq_degIntegral hcd hΩ hΩb hadm hbc hbs hbm, degIntegral]
  have hfd : ∀ x : Fin n → ℝ, HasFDerivAt (fun z => matVec A (z - p)) (matVec A) x := by
    intro x
    have h1 : HasFDerivAt (fun z : Fin n → ℝ => z - p) (ContinuousLinearMap.id ℝ (Fin n → ℝ)) x :=
      (hasFDerivAt_id x).sub_const p
    have h2 := ((matVec A).hasFDerivAt (x := x - p)).comp x h1
    simpa [Function.comp_def] using h2
  have hcov : (∫ w in (fun z => matVec A (z - p)) '' Ω, φ w)
      = ∫ x in Ω, |A.det| * φ (matVec A (x - p)) := by
    have hch := MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul volume
      hΩ.measurableSet (f := fun z => matVec A (z - p)) (f' := fun _ => matVec A)
      (fun x _ => (hfd x).hasFDerivWithinAt) (hinj.injOn) φ
    simpa [det_matVec, smul_eq_mul] using hch
  have hfull : (∫ w in (fun z => matVec A (z - p)) '' Ω, φ w) = 1 := by
    rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero, hbm]
    intro w hw
    refine hbs w ?_
    by_contra hcon
    exact hw (hballsub (by rw [Metric.mem_ball, dist_zero_right]; exact lt_of_not_ge hcon))
  have hbase : (∫ x in Ω, φ (matVec A (x - p))) = |A.det|⁻¹ := by
    have habs : (0 : ℝ) < |A.det| := abs_pos.mpr hA
    have hkey : |A.det| * ∫ x in Ω, φ (matVec A (x - p)) = 1 := by
      rw [← MeasureTheory.integral_const_mul, ← hcov, hfull]
    field_simp at hkey ⊢
    linarith [hkey]
  have hjac : ∀ x : Fin n → ℝ,
      φ (matVec A (x - p) - 0) * (jac (fun z => matVec A (z - p) - (0 : Fin n → ℝ)) x).det
        = A.det * φ (matVec A (x - p)) := by
    intro x
    rw [jac_matVec_affine, sub_zero]
    ring
  rw [MeasureTheory.setIntegral_congr_fun hΩ.measurableSet (fun x _ => hjac x),
    MeasureTheory.integral_const_mul, hbase]
  rcases lt_or_gt_of_ne hA with hneg | hpos
  · rw [if_neg (by linarith), abs_of_neg hneg]
    field_simp
  · rw [if_pos hpos, abs_of_pos hpos]
    field_simp

/-- **The degree of an invertible linear map is the sign of its determinant.** -/
theorem degree_matVec (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0)
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (h0 : (0 : Fin n → ℝ) ∈ Ω) :
    degree (fun z => matVec A z) Ω 0 = if 0 < A.det then 1 else -1 := by
  have h := degree_matVec_affine A hA 0 hΩ hΩb h0
  simpa using h

end GaloisForLFunctions.HTGeometry.PoincareHopf
