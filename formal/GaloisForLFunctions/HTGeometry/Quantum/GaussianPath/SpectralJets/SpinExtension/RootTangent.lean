import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.EffectiveSector
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.NormalizedRelation

/-! # First variation of a simple root in the two spin sectors -/
open Matrix Filter Topology
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]
private abbrev Mat (I : Type*) := Matrix I I ℂ

private theorem simple_root_contact {F : ℂ × ℂ → ℂ} {z : ℂ} (hF : AnalyticAt ℂ F (0,z))
    (hs : fderiv ℂ F (0,z) (0,1) ≠ 0) {e g : ℂ → ℂ}
    (he : DifferentiableAt ℂ e 0) (hg : DifferentiableAt ℂ g 0) (he₀ : e 0=z) (hg₀ : g 0=z)
    (ht : deriv (fun t => F (t,e t)) 0 = deriv (fun t => F (t,g t)) 0) :
    deriv e 0 = deriv g 0 := by
  let L := fderiv ℂ F (0,z)
  have h (f : ℂ → ℂ) (hf : DifferentiableAt ℂ f 0) (hf₀ : f 0=z) :
      deriv (fun t => F (t,f t)) 0 = L (1,deriv f 0) := by
    have hD : HasFDerivAt F L (0,f 0) := by rw [hf₀]; exact hF.differentiableAt.hasFDerivAt
    exact (hD.comp_hasDerivAt (f := fun t : ℂ => (t,f t)) (0:ℂ) ((hasDerivAt_id (0:ℂ)).prodMk hf.hasDerivAt)).deriv
  rw [h e he he₀,h g hg hg₀] at ht
  have hvec : ((1,deriv e 0) : ℂ × ℂ) - (1,deriv g 0) = (deriv e 0-deriv g 0) • (0,1) := by
    ext <;> simp
  have hzero := congrArg L hvec
  rw [map_sub,ht,sub_self,map_smul] at hzero
  exact sub_eq_zero.mp ((mul_eq_zero.mp hzero.symm).resolve_right hs)

/-- The new root sees an old onsite displacement βu and scalar displacement αu
whenever the virtual flip product cWV equals αI+βZ. -/
theorem spin_root_tangent (H Z W V : Mat I) (b c α β : ℂ) (hb : b*c=1)
    (hWV : c • (W*V) = α • 1+β • Z) (f e : ℂ → ℂ)
    (hf : AnalyticAt ℂ f 0) (he : AnalyticAt ℂ e 0) (he₀ : e 0=f 0)
    (hfroot : ∀ᶠ s in 𝓝 0, matrixCharpolyRelation (H+s • Z,f s)=0)
    (heroot : ∀ᶠ u in 𝓝 0, splitDet (scalar I (e u)-H) W V b u=0)
    (hs : H.charpoly.derivative.eval (f 0) ≠ 0) : deriv e 0 = α+β*deriv f 0 := by
  let F (p : ℂ × ℂ) := splitDet (scalar I p.2-H) W V b p.1
  let g (t : ℂ) := α*t+f (β*t)
  have hg₀ : g 0=f 0 := by simp [g]
  have hβ : HasDerivAt (fun t : ℂ => β*t) β 0 := by simpa using (hasDerivAt_id (0:ℂ)).const_mul β
  have hα : HasDerivAt (fun t : ℂ => α*t) α 0 := by simpa using (hasDerivAt_id (0:ℂ)).const_mul α
  have hdg : HasDerivAt g (α+β*deriv f 0) 0 := by
    have hdf : HasDerivAt f (deriv f 0) (β*0) := by simpa using hf.differentiableAt.hasDerivAt
    simpa only [g,Pi.add_def,Function.comp_def,mul_comm (deriv f 0) β] using! hα.add (hdf.comp 0 hβ)
  have hF := normalized_analytic H W V b (f 0)
  have hpart : fderiv ℂ F (0,f 0) (0,1) ≠ 0 := by
    have hbn : b≠0 := fun hz' => zero_ne_one (by simpa only [hz',zero_mul] using hb)
    exact (normalized_energy_partial H W V b (f 0)).trans_ne (mul_ne_zero hs (pow_ne_zero _ hbn))
  have hA (i j : I) : AnalyticAt ℂ (fun t => (scalar I (g t)-H) i j) 0 := by
    have hβa : AnalyticAt ℂ (fun t : ℂ => β*t) 0 := analyticAt_const.mul analyticAt_id
    have hfa : AnalyticAt ℂ f (β*0) := by simpa using hf
    have hga : AnalyticAt ℂ g 0 := (analyticAt_const.mul analyticAt_id).add (hfa.comp hβa)
    by_cases hij : i=j
    · subst j; simpa [scalar_apply] using! hga.sub (analyticAt_const (v := H i i))
    · simp [scalar_apply,hij,analyticAt_const]
  have hmodel : ∀ᶠ t in 𝓝 (0:ℂ),
      ((scalar I (g t)-H) - (c*t) • (W*V)).det = 0 := by
    have htend : Tendsto (fun t : ℂ => β*t) (𝓝 0) (𝓝 0) := by simpa using hβ.continuousAt.tendsto
    filter_upwards [htend hfroot] with t ht
    change matrixCharpolyRelation (H+(β*t) • Z,f (β*t))=0 at ht
    rw [←ht]
    unfold matrixCharpolyRelation
    apply congrArg Matrix.det
    rw [mul_comm c t,mul_smul,hWV,smul_add,smul_smul,smul_smul]
    ext i j
    by_cases hij : i=j <;> simp [g,scalar_apply,hij] <;> ring
  have hⱼ := splitDet_deriv (fun t => scalar I (g t)-H) hA W V b c hb
  have hzero : deriv (fun t => F (t,g t)) 0 = 0 := by
    have hh : (fun t => ((scalar I (g t)-H)-(c*t) • (W*V)).det *
        (b • 1+t • (scalar I (g t)-H)).det) =ᶠ[𝓝 (0:ℂ)] fun _ => 0 := by
      filter_upwards [hmodel] with t ht
      exact mul_eq_zero_of_left ht _
    exact hⱼ.trans (hh.deriv_eq.trans (deriv_const ..))
  have hezero : (fun t => F (t,e t)) =ᶠ[𝓝 (0:ℂ)] fun _ => 0 := heroot
  have hcontact := simple_root_contact hF hpart he.differentiableAt hdg.differentiableAt he₀ hg₀
    ((hezero.deriv_eq.trans (deriv_const ..)).trans hzero.symm)
  exact hcontact.trans hdg.deriv

#print axioms spin_root_tangent
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension
