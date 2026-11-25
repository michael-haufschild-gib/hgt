import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.CircuitContacts.FieldBranches
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.CircuitContacts.CharacterPolynomials

/-! # Integer action levels prevent constant complex germs on the field line -/

open Filter Topology MeasureTheory Set
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.CircuitContacts
noncomputable section

/-- A constant complex action germ would put an entire real interval of
fields in one level of the corresponding real energy action. -/
theorem nonconstant_action_germ {J : Type*} [Fintype J] (g : J→ℂ→ℂ) (w : J→ℝ→ℝ)
    (hg : ∀ i, AnalyticAt ℂ (g i) 0) {χ : ℂ} (hχ : χ≠0) {t : ℝ}
    (hr : ∀ᶠ v : ℝ in 𝓝 0, ∀ i, g i v=χ*(w i (t+v):ℂ))
    (m : J→ℤ) (hnull : ∀ c : ℝ, volume {y | (∑ i, (m i:ℝ)*w i y)=c}=0)
    (c : ℂ) : ¬((fun z => ∑ i, (m i:ℂ)*g i z) =ᶠ[𝓝[≠] 0] fun _ => c) := by
  intro he
  let f (z : ℂ) := ∑ i, (m i:ℂ)*g i z
  let a (y : ℝ) := ∑ i, (m i:ℝ)*w i y
  have hf : AnalyticAt ℂ f 0 := Finset.analyticAt_fun_sum _ fun i _ => analyticAt_const.mul (hg i)
  have hfull : f =ᶠ[𝓝 0] fun _ => c :=
    (hf.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE continuousAt_const).mp he
  have ht : Tendsto (fun v : ℝ => (v:ℂ)) (𝓝 0) (𝓝 0) := by simpa using Complex.continuous_ofReal.tendsto 0
  have ha : ∀ᶠ v : ℝ in 𝓝 0, χ*(a (t+v):ℂ)=c := by
    filter_upwards [hr,hfull.comp_tendsto ht] with v hv hconst
    change f (v:ℂ)=c at hconst
    rw [←hconst]
    simp only [a,f,hv,Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_intCast,Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have he₀ : χ*(a t:ℂ)=c := by simpa only [add_zero] using ha.self_of_nhds
  have hloc : ∀ᶠ v : ℝ in 𝓝 0, a (t+v)=a t := ha.mono fun v hv =>
    Complex.ofReal_injective (mul_left_cancel₀ hχ (hv.trans he₀.symm))
  have hshift : Tendsto (fun y : ℝ => y-t) (𝓝 t) (𝓝 0) := by
    simpa only [sub_self] using (continuous_id.sub continuous_const).tendsto t
  have hmem : {y | a y=a t} ∈ 𝓝 t :=
    (hshift.eventually hloc).mono fun y hy => by
      change a (t+(y-t)) = a t at hy
      rwa [show t+(y-t)=y by ring] at hy
  obtain ⟨O,hO,ho,htO⟩ := mem_nhds_iff.mp hmem
  exact (ho.measure_pos volume ⟨t,htO⟩).ne' (measure_mono_null hO (hnull (a t)))

#print axioms nonconstant_action_germ
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.CircuitContacts
