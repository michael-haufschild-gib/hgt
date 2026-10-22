import GaloisForLFunctions.RHTower.Deninger.DeningerDepletedPoisson
import GaloisForLFunctions.RHTower.Deninger.DeningerGreenSumSource
import GaloisForLFunctions.RHTower.Deninger.DeningerRadialNuclear

/-!
# No finite prime family separates the source

The periodization defects commute and each kills its own periodization, so the depletion operator
of a finite family lands in every one of that family's periodization kernels.  Since the depletion
operator is injective and the source is nonzero, that kernel is nonzero:

`0 ≠ Δ_Q H_- ⊆ ker 𝒫_Q` for every finite `Q`.

This is the contrast half of the tomography theorem — the statement that finite prime families
cannot determine a Meyer cochain.

* `deningerDepletion_mem_range` : `Δ_S h` lies in the range of each factor.
* `deningerSourceWitness_ne_zero` : the source is nonzero.
* `deningerFinitePeriodization_kernel_nontrivial` : **`(7)`.**
-/

namespace RHTower

open SchwartzMap

noncomputable section

/-- The depletion operator of a list lands in the range of each of its factors. -/
theorem deningerDepletion_mem_range (L : ℝ) : ∀ (S : List ℝ), L ∈ S →
    ∀ h : DeningerExpSchwartz,
      deningerDepletion S h ∈ Set.range (deningerPeriodizationDefect L) := by
  intro S
  induction S with
  | nil => intro hmem; exact absurd hmem (List.not_mem_nil)
  | cons M Ms ih =>
    intro hmem h
    rcases List.mem_cons.mp hmem with rfl | hMs
    · exact ⟨deningerDepletion Ms h, rfl⟩
    · obtain ⟨g, hg⟩ := ih hMs h
      refine ⟨deningerPeriodizationDefect M g, ?_⟩
      rw [deningerDepletion_cons, LinearMap.comp_apply, ← hg,
        deningerPeriodizationDefect_comm]

/-- A nonzero element of the source: the Poisson boundary of the corpus's Meyer witness. -/
def deningerSourceWitness : DeningerExpSchwartz :=
  deningerPoissonSource ⟨deningerMeyerCapWitness, deningerMeyerCapWitness_mem⟩

theorem deningerSourceWitness_ne_zero : deningerSourceWitness ≠ 0 := by
  intro hzero
  have hz : deningerPoissonSourceLM ⟨deningerMeyerCapWitness, deningerMeyerCapWitness_mem⟩
      = deningerPoissonSourceLM 0 := by
    rw [map_zero]
    exact hzero
  have hw : (⟨deningerMeyerCapWitness, deningerMeyerCapWitness_mem⟩ : DeningerMeyerCap) = 0 :=
    deningerPoissonSource_injective hz
  exact deningerMeyerCapWitness_ne_zero (congrArg Subtype.val hw)

/-- **`(7)`: no finite family of periods separates the source.**  The depletion operator of the
family is injective, so it produces a nonzero cochain, and that cochain is killed by every
periodization in the family. -/
theorem deningerFinitePeriodization_kernel_nontrivial (S : List ℝ) (hS : ∀ L ∈ S, 0 < L) :
    ∃ h : DeningerExpSchwartz, h ≠ 0 ∧
      ∀ L ∈ S, ∀ t : ℝ,
        deningerPeriodizationSum ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) L t = 0 := by
  refine ⟨deningerDepletion S deningerSourceWitness, ?_, ?_⟩
  · intro hzero
    have h0 : deningerDepletion S deningerSourceWitness = deningerDepletion S 0 := by
      rw [map_zero]
      exact hzero
    exact deningerSourceWitness_ne_zero (deningerDepletion_injective S hS h0)
  · intro L hL t
    have hmem := deningerDepletion_mem_range L S hL deningerSourceWitness
    have hker := deningerPeriodization_range_eq_kernel (hS L hL)
    rw [hker] at hmem
    exact hmem t

end

end RHTower
