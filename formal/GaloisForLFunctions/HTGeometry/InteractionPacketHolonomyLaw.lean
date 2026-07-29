import GaloisForLFunctions.HTGeometry.LocalSpectralObserverDirectSumLaw

/-!
# Interaction-packet holonomy law

Boolean interaction packets detect the first control sector that cannot be
removed by a gauge transformation.  If two coupling configurations are
indistinguishable on every proper restriction but distinguish the full
spectral branch, their full Möbius packet is necessarily nonzero.

This is the abstract bridge from local gauge holonomy to an irreducible
observer-time sector.  It uses no matrix dimension, graph shape, or
perturbative coefficient formula.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

open FiniteLocalInteractionFamily

/-- If every proper restriction is gauge invariant, the difference of full
packet responses is exactly the unreduced full-branch difference. -/
theorem spectralPacketResponse_univ_sub_eq_full_sub_of_proper_eq
    {E : Type*} [Fintype E] [DecidableEq E]
    (branch : (E → ℂ) → ℂ)
    (positive negative : E → ℂ)
    (hproper :
      ∀ active : Finset E, active ≠ Finset.univ →
        branch (restrictInteractionPacket active positive) =
          branch (restrictInteractionPacket active negative)) :
    spectralPacketResponse branch Finset.univ positive -
        spectralPacketResponse branch Finset.univ negative =
      branch positive - branch negative := by
  unfold spectralPacketResponse finsetMobiusResponse
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  rw [Finset.sum_eq_single ∅]
  · have hpositive :
        restrictInteractionPacket Finset.univ positive = positive := by
      funext i
      simp [restrictInteractionPacket]
    have hnegative :
        restrictInteractionPacket Finset.univ negative = negative := by
      funext i
      simp [restrictInteractionPacket]
    simp only [Finset.sdiff_empty, Finset.card_empty, pow_zero, one_mul]
    rw [hpositive, hnegative]
  · intro d hdPower hdne
    have hactive :
        Finset.univ \ d ≠ (Finset.univ : Finset E) := by
      intro heq
      obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hdne
      have himem : i ∈ (Finset.univ \ d : Finset E) := by
        rw [heq]
        simp
      exact (Finset.mem_sdiff.mp himem).2 hi
    rw [hproper (Finset.univ \ d) hactive, sub_self, mul_zero]
  · simp

/-- **Möbius--holonomy transgression.** If every proper control packet is
gauge invariant but the full branch distinguishes two coupling germs, then
the full Boolean interaction packet is a nonzero germ. -/
theorem spectralPacketResponse_univ_germ_ne_zero_of_holonomy
    {E P : Type*} [Fintype E] [DecidableEq E]
    [TopologicalSpace P] {p₀ : P}
    (branch : (E → ℂ) → ℂ)
    (positive negative : P → E → ℂ)
    (hpositive : Tendsto positive (𝓝 p₀) (𝓝 0))
    (hnegative : Tendsto negative (𝓝 p₀) (𝓝 0))
    (hproper :
      ∀ active : Finset E, active ≠ Finset.univ →
        (fun p =>
          branch (restrictInteractionPacket active (positive p))) =ᶠ[𝓝 p₀]
        (fun p =>
          branch (restrictInteractionPacket active (negative p))))
    (hholonomy :
      ¬(fun p => branch (positive p)) =ᶠ[𝓝 p₀]
        (fun p => branch (negative p))) :
    ¬spectralPacketResponse branch Finset.univ =ᶠ[𝓝 0]
      (fun _ : E → ℂ => 0) := by
  intro hzero
  have hzeroPositive := hzero.comp_tendsto hpositive
  have hzeroNegative := hzero.comp_tendsto hnegative
  have hproperAll :
      ∀ᶠ p : P in 𝓝 p₀,
        ∀ active : Finset E, active ≠ Finset.univ →
          branch (restrictInteractionPacket active (positive p)) =
            branch (restrictInteractionPacket active (negative p)) := by
    have hall :
        ∀ᶠ p : P in 𝓝 p₀,
          ∀ active ∈ (Finset.univ : Finset (Finset E)),
            active ≠ Finset.univ →
              branch (restrictInteractionPacket active (positive p)) =
                branch
                  (restrictInteractionPacket active (negative p)) := by
      rw [Finset.eventually_all]
      intro active hactive
      by_cases hactiveFull : active = Finset.univ
      · filter_upwards with p
        intro hne
        exact (hne hactiveFull).elim
      · have h := hproper active hactiveFull
        filter_upwards [h] with p hp
        intro _
        exact hp
    filter_upwards [hall] with p hp
    intro active hactive
    exact hp active (by simp) hactive
  apply hholonomy
  filter_upwards
    [hzeroPositive, hzeroNegative, hproperAll]
    with p hpos hneg hproperAt
  have hdiff :=
    spectralPacketResponse_univ_sub_eq_full_sub_of_proper_eq
      branch (positive p) (negative p) hproperAt
  change spectralPacketResponse branch Finset.univ (positive p) = 0 at hpos
  change spectralPacketResponse branch Finset.univ (negative p) = 0 at hneg
  rw [hpos, hneg, sub_self] at hdiff
  exact sub_eq_zero.mp hdiff.symm

end GaloisForLFunctions.HTGeometry
