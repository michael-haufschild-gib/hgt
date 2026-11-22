import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.Boundary.Branches
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.Boundary.BranchSeparation
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.Boundary.ShiftedField
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.RootTangent
import Mathlib.Tactic.Module

/-! # A boundary-controlled transverse flip separates all new boundary slopes -/
open Matrix Filter Topology
open GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension
namespace GaloisForLFunctions.HTGeometry.FirstGate.Boundary
noncomputable section
variable {I : Type} [Fintype I] [DecidableEq I]
private abbrev Mat (I : Type) := Matrix I I ℂ

private theorem normalized_controlled {H Z : Mat I} (hZ : Z*Z=1) (hsep : H.charpoly.Separable)
    (f : ℂ→ℂ) (hf : AnalyticAt ℂ f 0)
    (hr : ∀ᶠ s in 𝓝 0, matrixCharpolyRelation (H+s • Z,f s)=0) :
    let W := 1+Z
    ∃ e : ℂ→ℂ, AnalyticAt ℂ e 0 ∧ e 0=f 0 ∧ deriv e 0=1+deriv f 0 ∧
      ∀ᶠ u in 𝓝 0, splitDet (scalar I (e u)-H) W W 2 u=0 := by
  intro W
  have hz : H.charpoly.eval (f 0)=0 := by
    simpa only [matrixCharpolyRelation,←Matrix.eval_charpoly,zero_smul,add_zero] using hr.self_of_nhds
  have hs : H.charpoly.derivative.eval (f 0) ≠ 0 := by
    simpa using hsep.eval₂_derivative_ne_zero (RingHom.id ℂ) (by simpa using hz)
  obtain ⟨e,he,he₀,her⟩ := normalized_branch H W W 2 (f 0) (by norm_num) hz hs
  have hprod : (1/2:ℂ) • (W*W) = (1:ℂ) • (1 : Mat I) + (1:ℂ) • Z := by
    simp only [W,add_mul,mul_add,one_mul,mul_one,hZ,smul_add,one_smul]
    module
  have htan := spin_root_tangent H Z W W 2 (1/2) 1 1 (by norm_num) hprod f e hf he he₀ hr her hs
  exact ⟨e,he,he₀,by simpa only [one_mul] using htan,her⟩

/-- With one new X field and one ZX bond the new boundary Z distinguishes every
level for every sufficiently large real splitting. -/
theorem resolved_controlled_flip (H Z : Mat I) (hZ : Z*Z=1) (h : Resolved H Z) :
    ∀ᶠ u in 𝓝 (0:ℂ), u≠0 → Resolved (sectorMatrix H (1+Z) (1+Z) u⁻¹) (sectorZ I) := by
  obtain ⟨f,hf,hi,hd⟩ := h
  have hs := separable_of_branches H Z f (fun j => (hf j).2) hi
  choose e he h₀ h₁ hr using fun j => normalized_controlled hZ hs (f j) (hf j).1 (hf j).2
  have hei : Function.Injective (fun j => e j 0) := by simpa only [h₀] using hi
  have hdi : Function.Injective (fun j => deriv (e j) 0) := by
    intro i j hij
    exact hd (add_left_cancel (by simpa only [h₁] using hij : 1+deriv (f i) 0=1+deriv (f j) 0))
  have hsep := two_sector_separation e he hei hdi
  let W := (1 : Mat I)+Z
  have hlocal : ∀ᶠ u in 𝓝 (0:ℂ), ∀ j,
      AnalyticAt ℂ (e j) u ∧ ∀ᶠ v in 𝓝 u, splitDet (scalar I (e j v)-H) W W 2 v=0 :=
    eventually_all.mpr fun j => (he j).eventually_analyticAt.and (hr j).eventually_nhds
  have hneg : Tendsto (fun u : ℂ => -u) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_neg.continuousAt (x := (0:ℂ))).tendsto
  filter_upwards [hsep,hlocal,hneg.eventually hlocal] with u hsep hp hm
  intro hu
  let d := u⁻¹
  have hd' : d≠0 := inv_ne_zero hu
  have hep (j : I) := shifted_response (e j) d hd' (by simpa only [d,inv_inv] using (hp j).1)
  have hem (j : I) := shifted_response (e j) (-d) (neg_ne_zero.mpr hd')
    (by simpa only [d,inv_neg,inv_inv] using (hm j).1)
  let F : I ⊕ I → ℂ → ℂ := Sum.elim (fun j => shifted (e j) d) (fun j s => shifted (e j) (-d) (-s))
  refine ⟨F,?_,?_,?_⟩
  · rintro (j|j)
    · refine ⟨(hep j).1,?_⟩
      have hrp := shifted_root H W (e j) d hd' (by simpa only [d,inv_inv] using (hp j).2)
      simpa only [F,Sum.elim_inl,shift_sector] using hrp
    · have hA : AnalyticAt ℂ (shifted (e j) (-d)) (-(0:ℂ)) := by simpa using (hem j).1
      refine ⟨hA.comp (f := fun s : ℂ => -s) analyticAt_id.neg,?_⟩
      have hrm := shifted_root H W (e j) (-d) (neg_ne_zero.mpr hd')
        (by simpa only [d,inv_neg,inv_inv] using (hm j).2)
      filter_upwards [hneg.eventually hrm] with s hroot
      simpa only [F,Sum.elim_inr,shift_sector,←neg_add,sector_swap] using hroot
  · have hv : (fun i => F i 0) = Sum.elim (fun j => d+e j u) (fun j => -d+e j (-u)) := by
      funext i
      cases i <;> simp [F,shifted,d]
    rw [hv]
    exact (hsep hu).1
  · have hv : (fun i => deriv (F i) 0) = Sum.elim (fun j => 1-u^2*deriv (e j) u)
        (fun j => -1+u^2*deriv (e j) (-u)) := by
      funext i
      cases i with
      | inl j => simpa only [F,Sum.elim_inl,d,inv_inv] using (hep j).2.2
      | inr j =>
        have hd₁ := (hem j).1.differentiableAt.hasDerivAt
        have hd₂ : HasDerivAt (shifted (e j) (-d)) (deriv (shifted (e j) (-d)) 0) (-(0:ℂ)) := by simpa using hd₁
        have hd₃ := (hd₂.comp 0 (hasDerivAt_id (0:ℂ)).neg).deriv
        change deriv (shifted (e j) (-d) ∘ Neg.neg) 0 = -1+u^2*deriv (e j) (-u)
        rw [hd₃,(hem j).2.2]
        simp only [d,inv_neg,inv_inv,neg_sq,mul_neg,mul_one]
        ring
    rw [hv]
    exact (hsep hu).2

end
end GaloisForLFunctions.HTGeometry.FirstGate.Boundary
