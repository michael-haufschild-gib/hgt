import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.GermPhases
import GaloisForLFunctions.HTGeometry.HermitianLocalExtensionRelationEscape

/-! # Independence of exponential sums on the real slice of a spectral curve -/

open Filter Topology
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves
noncomputable section

/-- Taking a meromorphic germ commutes with finite sums. -/
theorem sum_germs {ι : Type*} [Fintype ι] (g : ι → ℂ → ℂ) (hg : ∀ i, MeromorphicAt (g i) 0)
    (h : MeromorphicAt (fun z => ∑ i, g i z) 0) :
    ∑ i, ofMero (g i) (hg i)=ofMero (fun z => ∑ i, g i z) h := by
  let G : MeroGerm →+* Germ (𝓝[≠] (0:ℂ)) ℂ := meroGermSubring.subtype
  let J := Germ.coeRingHom (𝓝[≠] (0:ℂ)) (R:=ℂ)
  apply MeroGerm.germ_injective
  change G (∑ i, ofMero (g i) (hg i))=J (fun z => ∑ i, g i z)
  rw [map_sum]
  change ∑ i, J (g i)=_
  rw [←map_sum]
  exact congrArg J (funext fun z => Finset.sum_apply z _ _)

/-- A relation on a real interval between exponentials of algebraic
actions already holds in the complex germ field. Pairwise nonconstant
action differences force every constant coefficient to vanish. -/
theorem exp_sum_real_slice {ι : Type*} [Fintype ι] (f : ι → ℂ → ℂ)
    (hf : ∀ i, AnalyticAt ℂ (f i) 0)
    (ha : ∀ i, IsAlgebraic (RatFunc ℂ) (ofMero (f i) (hf i).meromorphicAt))
    (hd : ∀ i j, i≠j → ∀ c : ℂ, ¬ ((fun z => f i z-f j z) =ᶠ[𝓝[≠] 0] fun _ => c))
    (a : ι → ℂ) (hz : ∀ᶠ t : ℝ in 𝓝 0, ∑ i, a i*Complex.exp (f i t)=0) : ∀ i, a i=0 := by
  let g (i : ι) (z : ℂ) := a i*Complex.exp (f i z)
  have hg (i : ι) : AnalyticAt ℂ (g i) 0 := analyticAt_const.mul (hf i).cexp
  have hs : AnalyticAt ℂ (fun z => ∑ i, g i z) 0 := Finset.analyticAt_fun_sum _ fun i _ => hg i
  have he := AnalyticAt.eventuallyEq_zero_of_eventually_ofReal_eq_zero hs hz
  let c (i : ι) := algebraMap ℂ curveField (a i)
  have hc (i : ι) : (c i:MeroGerm)*ofMero (fun z => Complex.exp (f i z)) (hf i).cexp.meromorphicAt =
      ofMero (g i) (hg i).meromorphicAt := by
    change algebraMap ℂ MeroGerm (a i)*_ = _
    rw [algebraMap_complex_meroGerm,ofMero_mul]
    rfl
  have hzero : ∑ i, (c i:MeroGerm)*ofMero (fun z => Complex.exp (f i z)) (hf i).cexp.meromorphicAt=0 := by
    simp_rw [hc]
    rw [sum_germs g _ hs.meromorphicAt,ofMero_eq_zero_iff]
    exact he.filter_mono nhdsWithin_le_nhds
  have h := algebraic_action_exponentials f hf ha hd c hzero
  exact fun i => (algebraMap ℂ curveField).injective ((h i).trans (map_zero _).symm)

#print axioms exp_sum_real_slice
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves
