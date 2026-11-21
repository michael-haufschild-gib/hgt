import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Doublets.WalshWords
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Doublets.FieldSpecialization
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Doublets.BranchRescaling

/-! # Reading the polynomial field rows from physical eigenbranches -/
open MvPolynomial Matrix Filter Topology
namespace GaloisForLFunctions.HTGeometry.SpectralJets.Doublets
noncomputable section
variable {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]

/-- Simple spectrum makes the longitudinal characteristic partial nonzero at every eigenvalue. -/
theorem field_separant (H : Matrix I I ℂ) (u : I → Fin n → ℂ) (hH : H.charpoly.Separable)
    (z : ℂ) (hz : H.charpoly.eval z = 0) :
    eval (fun o : Option (Fin n) => o.elim z 0) (pderiv none (fieldCharacteristic H u)) ≠ 0 := by
  let p := fieldCharacteristic H u
  have he (y : ℂ) : eval (fun o : Option (Fin n) => o.elim y 0) p = H.charpoly.eval y := by
    rw [Matrix.eval_charpoly,eval_fieldCharacteristic]
    simp
  have h := energy_partial p z
  simp_rw [he] at h
  have h' := h.unique (Polynomial.hasDerivAt H.charpoly z)
  rw [h']
  simpa using hH.eval₂_derivative_ne_zero (RingHom.id ℂ) (by simpa using hz)

/-- The local zero-field jet of a physical root supplies the corresponding column
of every rectangular trace detector after multiplication by one separant power. -/
theorem field_row_of_branch (H : Matrix I I ℂ) (u : I → Fin n → ℂ) (hH : H.charpoly.Separable)
    (f : (Fin n → ℂ) → ℂ) (hf : AnalyticAt ℂ f 0)
    (hroot : ∀ᶠ h in 𝓝 0, matrixCharpolyRelation (H+diagonal (fun j => fieldEnergy (u j) h),f h)=0)
    (w : List (Fin n)) :
    let p := fieldCharacteristic H u
    let χ (o : Option (Fin n)) := o.elim (f 0) 0
    eval χ (jetRow p w.length (some w)) = mixed w f 0 * (eval χ (pderiv none p))^(2*w.length) := by
  intro p χ
  have hr : onRoot p f =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [hroot] with h hh
    exact (eval_fieldCharacteristic H u (f h) h).trans hh
  have h0 : H.charpoly.eval (f 0)=0 := by
    have he := hroot.self_of_nhds
    simpa [Matrix.eval_charpoly,matrixCharpolyRelation,fieldEnergy] using he
  have hs := field_separant H u hH (f 0) h0
  have hc : ContinuousAt (onRoot (pderiv none p) f) 0 := by
    apply (contDiff_mvPolynomial_eval _).continuous.continuousAt.comp
    apply continuousAt_pi.mpr
    intro o
    cases o with
    | none => exact hf.continuousAt
    | some i => exact (continuous_apply i).continuousAt
  obtain ⟨U,hU,ho,hmem⟩ := mem_nhds_iff.mp ((hf.eventually_analyticAt.and hr).and (hc.eventually_ne hs))
  exact row_eval p w.length (some w) (by intro v hv; cases hv; rfl) f ho
    (fun y hy => (hU hy).1.1.differentiableAt.differentiableWithinAt)
    (fun y hy => (hU hy).1.2) (fun y hy => (hU hy).2) 0 hmem

theorem simple_field_branch (H : Matrix I I ℂ) (u : I → Fin n → ℂ) (hH : H.charpoly.Separable)
    (z : ℂ) (hz : H.charpoly.eval z=0) :
    ∃ f : (Fin n → ℂ) → ℂ, AnalyticAt ℂ f 0 ∧ f 0=z ∧
      ∀ᶠ h in 𝓝 0, matrixCharpolyRelation (H+diagonal (fun j => fieldEnergy (u j) h),f h)=0 := by
  apply (field_branch (fieldCharacteristic H u) z ?_ (field_separant H u hH z hz)).imp
  · intro f hf
    refine ⟨hf.1,hf.2.1,?_⟩
    filter_upwards [hf.2.2] with h hh
    exact (eval_fieldCharacteristic H u (f h) h).symm.trans hh
  · rw [eval_fieldCharacteristic]
    simpa [Matrix.eval_charpoly] using hz

end
end GaloisForLFunctions.HTGeometry.SpectralJets.Doublets
