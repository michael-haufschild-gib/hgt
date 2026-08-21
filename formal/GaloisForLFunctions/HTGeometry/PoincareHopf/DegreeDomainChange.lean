import GaloisForLFunctions.HTGeometry.PoincareHopf.DegreeLocality

/-!
# Change of the domain variable by an orientation preserving diffeomorphism

Transporting the domain of a degree computation along an injective map with positive Jacobian
determinant does not change the degree.  In the degree integral the change of variables contributes
`|det Dψ|` while the chain rule divides by `det Dψ`, and the two cancel exactly when the determinant
is positive.

The boundary bookkeeping works because an injective continuous map sends the frontier of a bounded
open set onto a set containing the frontier of the image, so a single admissible radius serves both
degrees.
-/

open Matrix Finset Set MeasureTheory

namespace GaloisForLFunctions.HTGeometry.PoincareHopf

variable {n : ℕ} {ψ w : (Fin n → ℝ) → (Fin n → ℝ)} {Ω : Set (Fin n → ℝ)}

theorem det_jac_comp (hψ : ContDiff ℝ 2 ψ) (hw : ContDiff ℝ 2 w) (x : Fin n → ℝ) :
    (jac (fun z => w (ψ z)) x).det = (jac w (ψ x)).det * (jac ψ x).det := by
  have hψd : HasFDerivAt ψ (fderiv ℝ ψ x) x := (hψ.differentiable (by simp) x).hasFDerivAt
  have hwd : HasFDerivAt w (fderiv ℝ w (ψ x)) (ψ x) :=
    (hw.differentiable (by simp) (ψ x)).hasFDerivAt
  have hcomp : HasFDerivAt (fun z => w (ψ z)) ((fderiv ℝ w (ψ x)).comp (fderiv ℝ ψ x)) x := by
    have h := hwd.comp x hψd
    simpa [Function.comp_def] using h
  rw [← det_fderiv_eq_det_jac, hcomp.fderiv, ← det_fderiv_eq_det_jac, ← det_fderiv_eq_det_jac]
  simp only [ContinuousLinearMap.det]
  have hcoe : (((fderiv ℝ w (ψ x)).comp (fderiv ℝ ψ x)) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
      = ((fderiv ℝ w (ψ x) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) ∘ₗ
          (fderiv ℝ ψ x : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) := rfl
  rw [hcoe, LinearMap.det_comp]

theorem frontier_image_subset (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hψc : Continuous ψ) (hopen : IsOpen (ψ '' Ω)) :
    frontier (ψ '' Ω) ⊆ ψ '' frontier Ω := by
  have hKc : IsCompact (closure Ω) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure hΩb.closure
  have hclosed : IsClosed (ψ '' closure Ω) := (hKc.image hψc).isClosed
  have hsub : closure (ψ '' Ω) ⊆ ψ '' closure Ω :=
    closure_minimal (Set.image_mono subset_closure) hclosed
  intro y hy
  have hy1 : y ∈ closure (ψ '' Ω) := hy.1
  have hy2 : y ∉ ψ '' Ω := by
    have h := hy.2
    rwa [hopen.interior_eq] at h
  obtain ⟨a, ha, rfl⟩ := hsub hy1
  refine ⟨a, ?_, rfl⟩
  rw [hΩ.frontier_eq]
  exact ⟨ha, fun haΩ => hy2 ⟨a, haΩ, rfl⟩⟩

/-- **Invariance of the degree under an orientation preserving change of the domain variable.** -/
theorem degree_domain_change
    (hψ : ContDiff ℝ 2 ψ) (hw : ContDiff ℝ 2 w)
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hopen : IsOpen (ψ '' Ω)) (hinj : Set.InjOn ψ (closure Ω))
    (hpos : ∀ x ∈ Ω, 0 < (jac ψ x).det)
    (hfront : ∀ x ∈ frontier Ω, w (ψ x) ≠ 0) :
    degree w (ψ '' Ω) 0 = degree (fun x => w (ψ x)) Ω 0 := by
  classical
  have hKc : IsCompact (closure Ω) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure hΩb.closure
  have hΩ'b : Bornology.IsBounded (ψ '' Ω) :=
    ((hKc.image hψ.continuous).isBounded).subset (Set.image_mono subset_closure)
  have hfrsub : frontier (ψ '' Ω) ⊆ ψ '' frontier Ω :=
    frontier_image_subset hΩ hΩb hψ.continuous hopen
  have hcompcd : ContDiff ℝ 2 (fun x => w (ψ x)) := hw.comp hψ
  have hKfr : IsCompact (frontier Ω) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_frontier
      (hΩb.closure.subset frontier_subset_closure)
  obtain ⟨ρ, hρpos, hρ⟩ := exists_pos_two_lt_of_isCompact hKfr hcompcd.continuous
    (fun x hx hcon => hfront x hx (by simpa using hcon))
  have hadmcomp : AdmissibleRadius (fun x => w (ψ x)) Ω 0 ρ := ⟨hρpos, fun x hx => hρ x hx⟩
  have hadmw : AdmissibleRadius w (ψ '' Ω) 0 ρ := by
    refine ⟨hρpos, fun y hy => ?_⟩
    obtain ⟨x, hx, rfl⟩ := hfrsub hy
    exact hρ x hx
  have hbc : ContDiff ℝ 1 (bumpWeight (n := n) ρ) := bumpWeight_contDiff hρpos
  have hbs : ∀ z : Fin n → ℝ, ρ ≤ ‖z‖ → bumpWeight ρ z = 0 := bumpWeight_eq_zero hρpos
  have hbm : ∫ z, bumpWeight (n := n) ρ z = 1 := bumpWeight_integral hρpos
  rw [degree_eq_degIntegral hw hopen hΩ'b hadmw hbc hbs hbm,
    degree_eq_degIntegral hcompcd hΩ hΩb hadmcomp hbc hbs hbm,
    degIntegral_sub_zero, degIntegral_sub_zero]
  have hcov := MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul volume
    hΩ.measurableSet (f := ψ) (f' := fun x => fderiv ℝ ψ x)
    (fun x _ => ((hψ.differentiable (by simp) x).hasFDerivAt).hasFDerivWithinAt)
    (hinj.mono subset_closure)
    (fun y => bumpWeight ρ (w y) * (jac w y).det)
  rw [degIntegral, degIntegral, hcov]
  refine MeasureTheory.setIntegral_congr_fun hΩ.measurableSet fun x hx => ?_
  have hd : 0 < (jac ψ x).det := hpos x hx
  rw [det_fderiv_eq_det_jac, smul_eq_mul, det_jac_comp hψ hw x, abs_of_pos hd]
  field_simp

/-- **Orientation reversing change of the domain variable** flips the sign of the degree. -/
theorem degree_domain_change_neg
    (hψ : ContDiff ℝ 2 ψ) (hw : ContDiff ℝ 2 w)
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hopen : IsOpen (ψ '' Ω)) (hinj : Set.InjOn ψ (closure Ω))
    (hneg : ∀ x ∈ Ω, (jac ψ x).det < 0)
    (hfront : ∀ x ∈ frontier Ω, w (ψ x) ≠ 0) :
    degree w (ψ '' Ω) 0 = -degree (fun x => w (ψ x)) Ω 0 := by
  classical
  have hKc : IsCompact (closure Ω) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure hΩb.closure
  have hΩ'b : Bornology.IsBounded (ψ '' Ω) :=
    ((hKc.image hψ.continuous).isBounded).subset (Set.image_mono subset_closure)
  have hfrsub : frontier (ψ '' Ω) ⊆ ψ '' frontier Ω :=
    frontier_image_subset hΩ hΩb hψ.continuous hopen
  have hcompcd : ContDiff ℝ 2 (fun x => w (ψ x)) := hw.comp hψ
  have hKfr : IsCompact (frontier Ω) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_frontier
      (hΩb.closure.subset frontier_subset_closure)
  obtain ⟨ρ, hρpos, hρ⟩ := exists_pos_two_lt_of_isCompact hKfr hcompcd.continuous
    (fun x hx hcon => hfront x hx (by simpa using hcon))
  have hadmcomp : AdmissibleRadius (fun x => w (ψ x)) Ω 0 ρ := ⟨hρpos, fun x hx => hρ x hx⟩
  have hadmw : AdmissibleRadius w (ψ '' Ω) 0 ρ := by
    refine ⟨hρpos, fun y hy => ?_⟩
    obtain ⟨x, hx, rfl⟩ := hfrsub hy
    exact hρ x hx
  have hbc : ContDiff ℝ 1 (bumpWeight (n := n) ρ) := bumpWeight_contDiff hρpos
  have hbs : ∀ z : Fin n → ℝ, ρ ≤ ‖z‖ → bumpWeight ρ z = 0 := bumpWeight_eq_zero hρpos
  have hbm : ∫ z, bumpWeight (n := n) ρ z = 1 := bumpWeight_integral hρpos
  rw [degree_eq_degIntegral hw hopen hΩ'b hadmw hbc hbs hbm,
    degree_eq_degIntegral hcompcd hΩ hΩb hadmcomp hbc hbs hbm,
    degIntegral_sub_zero, degIntegral_sub_zero]
  have hcov := MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul volume
    hΩ.measurableSet (f := ψ) (f' := fun x => fderiv ℝ ψ x)
    (fun x _ => ((hψ.differentiable (by simp) x).hasFDerivAt).hasFDerivWithinAt)
    (hinj.mono subset_closure)
    (fun y => bumpWeight ρ (w y) * (jac w y).det)
  rw [degIntegral, degIntegral, hcov, ← MeasureTheory.integral_neg]
  refine MeasureTheory.setIntegral_congr_fun hΩ.measurableSet fun x hx => ?_
  have hd : (jac ψ x).det < 0 := hneg x hx
  rw [det_fderiv_eq_det_jac, smul_eq_mul, det_jac_comp hψ hw x, abs_of_neg hd]
  field_simp

end GaloisForLFunctions.HTGeometry.PoincareHopf
