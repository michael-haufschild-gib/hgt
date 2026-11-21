import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Doublets.NormalizedJets
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! # Returning a normalized spectral root to physical units -/
open Filter Topology MvPolynomial
namespace GaloisForLFunctions.HTGeometry.SpectralJets.Doublets
noncomputable section

/-- Differentiating with the fields held at zero gives the spectral polynomial partial. -/
theorem energy_partial {n : ℕ} (p : MvPolynomial (Option (Fin n)) ℂ) (z : ℂ) :
    HasDerivAt (fun y => eval (fun o : Option (Fin n) => o.elim y 0) p)
      (eval (fun o : Option (Fin n) => o.elim z 0) (pderiv none p)) z := by
  let u (y : ℂ) (o : Option (Fin n)) := o.elim y 0
  let d (o : Option (Fin n)) : ℂ := o.elim 1 0
  have hu : HasDerivAt u d z := by
    apply hasDerivAt_pi.mpr
    intro o
    cases o with
    | none => exact hasDerivAt_id z
    | some i => exact hasDerivAt_const z 0
  simpa [u,d,Fintype.sum_option] using hasDerivAt_mvPolynomial_eval_comp p hu

/-- A simple spectral root determines an analytic response to independent fields. -/
theorem field_branch {n : ℕ} (p : MvPolynomial (Option (Fin n)) ℂ) (z : ℂ)
    (hz : eval (fun o : Option (Fin n) => o.elim z 0) p=0)
    (hs : eval (fun o : Option (Fin n) => o.elim z 0) (pderiv none p)≠0) :
    ∃ f : (Fin n → ℂ) → ℂ, AnalyticAt ℂ f 0 ∧ f 0=z ∧ onRoot p f =ᶠ[𝓝 0] fun _ => 0 := by
  let x (q : (Fin n → ℂ) × ℂ) (o : Option (Fin n)) := o.elim q.2 q.1
  let F (q : (Fin n → ℂ) × ℂ) := eval (x q) p
  have hpoly (P : MvPolynomial (Option (Fin n)) ℂ) :
      AnalyticAt ℂ (fun q => eval (x q) P) ((0:Fin n → ℂ),z) := by
    induction P using MvPolynomial.induction_on with
    | C c => simpa only [eval_C] using (analyticAt_const (v := c))
    | add P Q hP hQ => simpa only [map_add,Pi.add_def] using hP.add hQ
    | mul_X P i hP =>
      simp only [map_mul,eval_X]
      apply hP.mul
      cases i with
      | none => exact analyticAt_snd
      | some i => exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i).analyticAt _).comp analyticAt_fst
  have hF : AnalyticAt ℂ F (0,z) := hpoly p
  apply parametric_holo_implicit (f := F) hF hz
  have h1 : HasDerivAt (fun y : ℂ => ((0:Fin n → ℂ),y)) (0,1) z :=
    (hasDerivAt_const z (0:Fin n → ℂ)).prodMk (hasDerivAt_id z)
  have h2 := HasFDerivAt.comp_hasDerivAt (l := F) (f := fun y : ℂ => ((0:Fin n → ℂ),y)) z
    hF.differentiableAt.hasFDerivAt h1
  have h3 : HasDerivAt (fun y => F (0,y))
      (eval (fun o : Option (Fin n) => o.elim z 0) (pderiv none p)) z := energy_partial p z
  exact fun h => hs ((h3.unique h2).trans h)

theorem upper_branch {n : ℕ} (p : MvPolynomial (Option (Fin n)) ℂ)
    (hz : atUpper p=0) (hs : atUpper (pderiv none p)≠0) :
    ∃ f : (Fin n → ℂ) → ℂ, AnalyticAt ℂ f 0 ∧ f 0=1 ∧ onRoot p f =ᶠ[𝓝 0] fun _ => 0 :=
  field_branch p 1 hz hs

private theorem scale_line {ι : Type*} [DecidableEq ι] (c : ℂ) (x : ι → ℂ) (i : ι) (t : ℂ) :
    c • coordLine x i t = coordLine (c • x) i (c*t) := by
  funext j
  by_cases h : j=i <;> simp [coordLine,h,mul_add]

private theorem mixed_scale {ι : Type*} [DecidableEq ι] (c d : ℂ) (w : List ι) (f : (ι → ℂ) → ℂ)
    (x : ι → ℂ) :
    mixed w (fun y => d*f (c • y)) x = (d*c^w.length)*mixed w f (c • x) := by
  induction w generalizing x with
  | nil => simp [mixed]
  | cons i w ih =>
    simp only [mixed,ih,scale_line,deriv_const_mul_field,List.length_cons,pow_succ]
    have hd := deriv_comp_mul_left c (fun t => mixed w f (coordLine (c • x) i t)) (0:ℂ)
    simp only [mul_zero,smul_eq_mul] at hd
    rw [hd]
    ring

private theorem mixed_shift {ι : Type*} [DecidableEq ι] (b : ℂ) (w : List ι) (hw : w≠[])
    (f : (ι → ℂ) → ℂ) (x : ι → ℂ) : mixed w (fun y => b+f y) x=mixed w f x := by
  induction w generalizing x with
  | nil => exact (hw rfl).elim
  | cons i w ih =>
    cases w with
    | nil => exact deriv_const_add b
    | cons j w => simp only [mixed] at ih ⊢; simp_rw [ih (List.cons_ne_nil _ _)]

/-- In a common derivative order m>0, physical rescaling multiplies each entire column
by the same factor r·(1/r)ᵐ. -/
theorem mixed_physical {ι : Type*} [DecidableEq ι] (b r : ℂ) (w : List ι) (hw : w≠[])
    (f : (ι → ℂ) → ℂ) :
    mixed w (fun y => b+r*f (r⁻¹ • y)) 0 = (r*(r⁻¹)^w.length)*mixed w f 0 := by
  rw [mixed_shift b w hw,mixed_scale,smul_zero]

end
end GaloisForLFunctions.HTGeometry.SpectralJets.Doublets
