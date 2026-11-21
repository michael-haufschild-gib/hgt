import GaloisForLFunctions.HTGeometry.FiniteSpectralHaarRecurrenceLaw

/-! # At most one integer resonance at an arbitrary sampling period -/
open Filter
namespace GaloisForLFunctions.HTGeometry.AdaptiveSampling
noncomputable section
variable {I : Type*} [Fintype I]

/-- A lattice of step τ sees every nonconstant character rotate nontrivially. -/
def FreeAtStep (ω : I → ℝ) (τ : ℝ) : Prop :=
  ∀ m : I → ℤ, ∀ k : ℤ, τ * finiteTorusCharacterDetuning m ω = (k:ℝ)*(2*Real.pi) → m = 0

/-- Two resonances at one step give an exact continuous-frequency relation
after eliminating the common angular period. -/
theorem resonance_proportional {ω : I → ℝ} (hi : RationallyIndependentFrequency ω)
    {τ : ℝ} (hτ : τ ≠ 0) {v w : I → ℤ} {k l : ℤ}
    (hv : τ * finiteTorusCharacterDetuning v ω = (k:ℝ)*(2*Real.pi))
    (hw : τ * finiteTorusCharacterDetuning w ω = (l:ℝ)*(2*Real.pi)) :
    ∀ i, k*w i = l*v i := by
  let z := fun i => k*w i-l*v i
  have hdet : finiteTorusCharacterDetuning z ω =
      k*finiteTorusCharacterDetuning w ω - l*finiteTorusCharacterDetuning v ω := by
    simp only [finiteTorusCharacterDetuning,z,Int.cast_sub,Int.cast_mul,sub_mul,Finset.sum_sub_distrib,
      mul_assoc,Finset.mul_sum]
  have hzero : τ*finiteTorusCharacterDetuning z ω = 0 := by
    rw [hdet]
    linear_combination (k:ℝ)*hw - (l:ℝ)*hv
  have hz := hi z ((mul_eq_zero.mp hzero).resolve_left hτ)
  exact fun i => sub_eq_zero.mp (congrFun hz i)

variable [DecidableEq I]

private theorem deletion_of_test (ω : I → ℝ) (τ : ℝ) (b : I)
    (ht : ∀ (w : I → ℤ) (l : ℤ), w b=0 →
      τ*finiteTorusCharacterDetuning w ω = (l:ℝ)*(2*Real.pi) → w=0) :
    FreeAtStep (fun j : {j : I // j ≠ b} => ω j) τ := by
  classical
  intro m l h
  let w (i : I) : ℤ := if hi : i ≠ b then m ⟨i,hi⟩ else 0
  have hd : finiteTorusCharacterDetuning w ω =
      finiteTorusCharacterDetuning m (fun j : {j : I // j ≠ b} => ω j) := by
    unfold finiteTorusCharacterDetuning
    rw [←Fintype.sum_subtype_add_sum_subtype (fun i : I => i ≠ b) (fun i => (w i:ℝ)*ω i)]
    have keep (j : {i : I // i ≠ b}) : w j = m j := dif_pos j.property
    have drop (j : {i : I // ¬i ≠ b}) : w j = 0 := dif_neg j.property
    simp only [keep,drop,Int.cast_zero,zero_mul,Finset.sum_const_zero,add_zero]
  have hz := ht w l (by simp [w]) (hd.symm ▸ h)
  funext j
  simpa only [w,dif_pos j.property,Pi.zero_apply] using congrFun hz j.val

/-- Deleting one coordinate suffices for every nonzero step, even one chosen
from the full frequency vector. In the resonant case delete any coordinate
where a nonzero resonant character is supported. -/
theorem exists_free_deletion [Nonempty I] (ω : I → ℝ) (hi : RationallyIndependentFrequency ω)
    (τ : ℝ) (hτ : τ ≠ 0) : ∃ b : I, FreeAtStep (fun j : {j : I // j ≠ b} => ω j) τ := by
  classical
  by_cases h : FreeAtStep ω τ
  · exact ⟨Classical.arbitrary I,deletion_of_test ω τ _ (fun w l _ hw => h w l hw)⟩
  unfold FreeAtStep at h
  push Not at h
  obtain ⟨v,k,hv,hv0⟩ := h
  obtain ⟨b,hb⟩ : ∃ i, v i ≠ 0 := by
    by_contra! hz
    exact hv0 (funext hz)
  refine ⟨b,deletion_of_test ω τ b ?_⟩
  intro w l hwb hw
  have hp := resonance_proportional hi hτ hv hw b
  rw [hwb,mul_zero] at hp
  have hl := (mul_eq_zero.mp hp.symm).resolve_right hb
  rw [hl,Int.cast_zero,zero_mul] at hw
  exact hi w ((mul_eq_zero.mp hw).resolve_left hτ)

#print axioms resonance_proportional
#print axioms exists_free_deletion
end
end GaloisForLFunctions.HTGeometry.AdaptiveSampling
