import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicFaces

/-!
# Every nonempty cubic face is realized

Uniform positive mass on a finite face gives a physical unit probe with exactly
that support. The realized supports of the cubic norming section are precisely
the nonempty faces in CubicFaces, so the face description contains no extra
nonempty faces absent from the physical probe space.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set Finset


def cubicFaceBarycenter (σ : Finset (Fin 5)) (q : Fin 5) : ℝ :=
  if q ∈ σ then 1/(σ.card : ℝ) else 0

theorem cubicFaceBarycenter_nonneg (σ : Finset (Fin 5)) (q : Fin 5) :
    0 ≤ cubicFaceBarycenter σ q := by
  unfold cubicFaceBarycenter
  split_ifs <;> positivity

theorem cubicFaceBarycenter_support (σ : Finset (Fin 5)) :
    cubicProbeSupport (cubicFaceBarycenter σ)=σ := by
  ext q
  by_cases hq : q ∈ σ
  · have hc : (σ.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero_of_mem hq
    simp [cubicProbeSupport,cubicFaceBarycenter,hq,hc]
  · simp [cubicProbeSupport,cubicFaceBarycenter,hq]

theorem cubicFaceBarycenter_sum (σ : Finset (Fin 5)) :
    ∑ q, cubicFaceBarycenter σ q = if σ.Nonempty then 1 else 0 := by
  by_cases hs : σ.Nonempty
  · have hc : (σ.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_ne_zero
    simp [cubicFaceBarycenter,Finset.sum_ite_mem,hs,hc]
  · have he : σ=∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst σ
    simp [cubicFaceBarycenter]

theorem cubicFaceBarycenter_realizes :
    ∀ σ ∈ cubicFaces, σ.Nonempty → cubicFaceBarycenter σ ∈ cubicProbeSection := by
  intro σ hσ hs
  rw [cubicProbeSection_faces]
  refine ⟨cubicFaceBarycenter_nonneg σ,?_,?_⟩
  · have hsum := cubicFaceBarycenter_sum σ
    rw [if_pos hs] at hsum
    simpa [Fin.sum_univ_succ,add_assoc] using hsum
  · rw [cubicFaceBarycenter_support]
    exact hσ

theorem cubicProbeSupport_realizedFaces :
    cubicProbeSupport '' cubicProbeSection = {σ | σ ∈ cubicFaces ∧ σ.Nonempty} := by
  ext σ
  constructor
  · rintro ⟨g,hg,rfl⟩
    have hsection := hg
    rw [cubicProbeSection_faces] at hsection
    refine ⟨hsection.2.2,?_⟩
    by_contra he
    have hem : cubicProbeSupport g=∅ := Finset.not_nonempty_iff_eq_empty.mp he
    have hz : ∀ q, g q=0 := by
      intro q
      by_contra hq
      have hmem : q ∈ cubicProbeSupport g := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hq⟩
      rw [hem] at hmem
      exact Finset.notMem_empty _ hmem
    have hsum := hg.2.1
    simp only [hz,add_zero] at hsum
    exact zero_ne_one hsum
  · rintro ⟨hσ,hs⟩
    exact ⟨cubicFaceBarycenter σ,cubicFaceBarycenter_realizes σ hσ hs,
      cubicFaceBarycenter_support σ⟩

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
