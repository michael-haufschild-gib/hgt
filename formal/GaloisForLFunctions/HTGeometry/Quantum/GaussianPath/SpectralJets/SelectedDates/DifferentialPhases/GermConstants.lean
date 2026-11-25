import GaloisForLFunctions.HTGeometry.MeromorphicGermField
import GaloisForLFunctions.Bottcher.RelativeRigidityCountableAvoidance

/-! # Constants of the meromorphic differentiation field -/

open Set Filter Topology Metric
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.DifferentialPhases
noncomputable section

/-- A meromorphic germ with zero derivative is a complex constant.
A punctured disk supports an analytic representative with derivative zero. -/
theorem complex_constant_of_meroDeriv_zero (x : MeroGerm) (hx : meroDeriv x=0) :
    ∃ c : ℂ, algebraMap ℂ MeroGerm c=x := by
  obtain ⟨f,hf,rfl⟩ := x.exists_rep
  rw [meroDeriv_ofMero,ofMero_eq_zero_iff] at hx
  have h := hf.eventually_analyticAt.and hx
  obtain ⟨r,hr,hd⟩ := Metric.mem_nhdsWithin_iff.mp h
  let U := ball (0:ℂ) r ∩ ({0}:Set ℂ)ᶜ
  have ho : IsOpen U := isOpen_ball.inter isClosed_singleton.isOpen_compl
  have hc : IsPreconnected U := Bottcher.punctured_ball_isPreconnected_complex hr
  obtain ⟨c,hc⟩ := ho.exists_is_const_of_deriv_eq_zero hc
    (fun z hz => (hd hz).1.differentiableAt.differentiableWithinAt) (fun _ hz => (hd hz).2)
  refine ⟨c,?_⟩
  rw [algebraMap_complex_meroGerm,ofMero_eq_iff]
  exact Metric.mem_nhdsWithin_iff.mpr ⟨r,hr,fun z hz => (hc z hz).symm⟩

#print axioms complex_constant_of_meroDeriv_zero
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.DifferentialPhases
