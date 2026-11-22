import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.CutEnergies

/-! # Resolving a target energy using signs of the crossed path bonds -/
namespace GaloisForLFunctions.HTGeometry.SpanningDensity
noncomputable section

private theorem subset_near {ι : Type*} [DecidableEq ι] (s : Finset ι) (w : ι→ℝ)
    (M : ℝ) (hM : 0≤M) (hw : ∀ i∈s, 0≤w i ∧ w i≤M) (y : ℝ)
    (hy : 0≤y) (hs : y ≤ ∑ i∈s,w i) :
    ∃ b ⊆ s, (∑ i∈b,w i)≤y ∧ y≤(∑ i∈b,w i)+M := by
  induction s using Finset.induction_on generalizing y with
  | empty =>
    refine ⟨∅,Finset.Subset.rfl,by simpa using hy,?_⟩
    simp only [Finset.sum_empty] at hs ⊢
    linarith only [hs,hM]
  | @insert a s ha ih =>
    have hw' : ∀ i∈s, 0≤w i ∧ w i≤M := fun i hi => hw i (Finset.mem_insert_of_mem hi)
    have hwa := hw a (Finset.mem_insert_self ..)
    rw [Finset.sum_insert ha] at hs
    by_cases h : w a≤y
    · obtain ⟨b,hb,h₁,h₂⟩ := ih hw' (y-w a) (sub_nonneg.mpr h) (by linarith only [hs])
      refine ⟨insert a b,Finset.insert_subset_insert _ hb,?_⟩
      rw [Finset.sum_insert (fun hh => ha (hb hh))]
      exact ⟨by linarith only [h₁],by linarith only [h₂]⟩
    · refine ⟨∅,Finset.empty_subset _,by simpa using hy,?_⟩
      simp only [Finset.sum_empty,zero_add]
      exact (le_of_not_ge h).trans hwa.2

/-- Signed values of crossed longitudinal bonds approximate every
energy in the full interval up to twice the largest bond strength. -/
theorem realize_signed_energy {n : ℕ} (s : Finset (Fin n)) (J : Fin n→ℝ) (M y : ℝ)
    (hM : 0≤M) (hJ : ∀ e∈s, |J e|≤M) (hy : |y|≤∑ e∈s, |J e|) :
    ∃ x : Fin (n+1)→Bool, |(∑ e∈s, J e*(spin (x e.castSucc)*spin (x e.succ)))-y|≤2*M := by
  classical
  let S := ∑ e∈s, |J e|
  have hS : -S≤y ∧ y≤S := abs_le.mp hy
  obtain ⟨b,hb,h₁,h₂⟩ := subset_near s (fun e => |J e|) M hM
    (fun e he => ⟨abs_nonneg _,hJ e he⟩) ((S-y)/2) (by linarith only [hS.2]) (by linarith only [hS.1])
  let p (e : Fin n) := xor (decide (J e<0)) (decide (e∈b))
  obtain ⟨x,hx⟩ := realize_edge_signs p
  have hp (e : Fin n) : J e*spin (p e)=|J e|-(if e∈b then 2*|J e| else 0) := by
    by_cases he : J e<0
    · by_cases hb' : e∈b <;> simp [p,he,hb',spin,abs_of_neg he]
      ring
    · by_cases hb' : e∈b <;> simp [p,he,hb',spin,abs_of_nonneg (le_of_not_gt he)]
      ring
  have hsum : (∑ e∈s, J e*(spin (x e.castSucc)*spin (x e.succ)))=S-2*∑ e∈b, |J e| := by
    simp_rw [hx,hp]
    rw [Finset.sum_sub_distrib,← Finset.sum_filter,show s.filter (·∈b)=b from by
      ext e; simp only [Finset.mem_filter]; exact and_iff_right_of_imp (fun he => hb he),Finset.mul_sum]
  refine ⟨x,?_⟩
  rw [hsum,abs_le]
  constructor <;> linarith only [h₁,h₂,hM]

#print axioms realize_signed_energy
end
end GaloisForLFunctions.HTGeometry.SpanningDensity
