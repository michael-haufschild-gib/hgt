import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.Aliasing
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! # The integral generator of the resonances of a sampled energy flow -/

namespace GaloisForLFunctions.HTGeometry.AdaptiveSampling.CenteredOccupation
noncomputable section
variable {I : Type*} [Fintype I]

private def windings (ω : I → ℝ) (τ : ℝ) : AddSubgroup ℤ where
  carrier := {k | ∃ m : I → ℤ, τ*finiteTorusCharacterDetuning m ω=(k:ℝ)*(2*Real.pi)}
  zero_mem' := ⟨0,by simp [finiteTorusCharacterDetuning]⟩
  add_mem' := by
    rintro k l ⟨m,hm⟩ ⟨n,hn⟩
    refine ⟨m+n,?_⟩
    simp only [finiteTorusCharacterDetuning,Pi.add_apply,Int.cast_add,add_mul,Finset.sum_add_distrib,
      mul_add] at *
    exact congrArg₂ (·+·) hm hn
  neg_mem' := by
    rintro k ⟨m,hm⟩
    refine ⟨-m,?_⟩
    simpa only [finiteTorusCharacterDetuning,Pi.neg_apply,Int.cast_neg,neg_mul,Finset.sum_neg_distrib,
      mul_neg,neg_inj] using hm

/-- All resonances are integer multiples of one realized charge. Using
the realized winding subgroup retains disconnected components of the
orbit closure when its generator has a common divisor. -/
theorem exists_resonance_generator (ω : I → ℝ) (hi : RationallyIndependentFrequency ω)
    {τ : ℝ} (hτ : τ≠0) :
    ∃ (m : I → ℤ) (k : ℤ), τ*finiteTorusCharacterDetuning m ω=(k:ℝ)*(2*Real.pi) ∧
      ∀ (w : I → ℤ) (l : ℤ), τ*finiteTorusCharacterDetuning w ω=(l:ℝ)*(2*Real.pi) →
        ∃ a : ℤ, w=fun i => a*m i := by
  obtain ⟨g,hg⟩ := IsAddCyclic.exists_generator (α:=windings ω τ)
  obtain ⟨m,hm⟩ := g.property
  refine ⟨m,g.val,hm,?_⟩
  intro w l hw
  let v : windings ω τ := ⟨l,w,hw⟩
  obtain ⟨a,ha⟩ := AddSubgroup.mem_zmultiples_iff.mp (hg v)
  have he : a*g.val=l := by
    have h : a • g.val=l := congrArg (fun z : windings ω τ => z.val) ha
    simpa only [zsmul_eq_mul] using h
  let z (i : I) := w i-a*m i
  have hd : finiteTorusCharacterDetuning z ω=
      finiteTorusCharacterDetuning w ω-(a:ℝ)*finiteTorusCharacterDetuning m ω := by
    simp only [z,finiteTorusCharacterDetuning,Int.cast_sub,Int.cast_mul,sub_mul,mul_assoc,
      Finset.sum_sub_distrib,Finset.mul_sum]
  have hzero : τ*finiteTorusCharacterDetuning z ω=0 := by
    rw [hd,mul_sub,mul_left_comm τ (a:ℝ),hm,hw,←he,Int.cast_mul]
    ring
  have hz := hi z ((mul_eq_zero.mp hzero).resolve_left hτ)
  exact ⟨a,funext fun i => sub_eq_zero.mp (congrFun hz i)⟩

#print axioms exists_resonance_generator
end
end GaloisForLFunctions.HTGeometry.AdaptiveSampling.CenteredOccupation
