/-
# Paying a finite grid once

The continuous-block form of an onset bound is the pointwise form applied at finitely many grid
times, with the exceptional event paid once and the grid paid by a union bound.  Deterministic
speed interpolation then upgrades "good at every grid point" to "good on the whole block", so the
good event contains the intersection of the grid-good events with the non-exceptional event.

Main results:
* `measureReal_iUnion_le_card_mul` — a finite union of uniformly small events.
* `one_sub_le_measureReal_of_grid` — the continuous-block onset bound.
-/
import GaloisForLFunctions.HTGeometry.OnsetProbabilityAssembly

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A finite union of uniformly small events is small, with the grid size as the only loss. -/
theorem measureReal_iUnion_le_card_mul (μ : Measure Ω) [IsFiniteMeasure μ]
    {ι : Type*} [Fintype ι] (B : ι → Set Ω) {β : ℝ} (hB : ∀ i, μ.real (B i) ≤ β) :
    μ.real (⋃ i, B i) ≤ (Fintype.card ι : ℝ) * β := by
  classical
  have hcover : (⋃ i, B i) = ⋃ i ∈ (Finset.univ : Finset ι), B i := by
    simp
  rw [hcover]
  refine le_trans (measureReal_biUnion_finset_le _ _) ?_
  calc ∑ i ∈ (Finset.univ : Finset ι), μ.real (B i)
      ≤ ∑ _i ∈ (Finset.univ : Finset ι), β := Finset.sum_le_sum fun i _ => hB i
    _ = (Fintype.card ι : ℝ) * β := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **The continuous-block onset bound.**  If the good event contains the intersection of the
grid-good events with the non-exceptional event, its probability is at least one minus the
exceptional mass minus the grid size times the pointwise bound. -/
theorem one_sub_le_measureReal_of_grid (μ : Measure Ω) [IsProbabilityMeasure μ]
    {ι : Type*} [Fintype ι] (B : ι → Set Ω) (G Good : Set Ω)
    (hGood : MeasurableSet Good) (hsub : ((⋂ i, (B i)ᶜ) ∩ G) ⊆ Good)
    {ε₁ β : ℝ} (hGc : μ.real Gᶜ ≤ ε₁) (hB : ∀ i, μ.real (B i) ≤ β) :
    1 - ε₁ - (Fintype.card ι : ℝ) * β ≤ μ.real Good := by
  classical
  have hcompl : Goodᶜ ⊆ (⋃ i, B i) ∪ Gᶜ := by
    intro ω hω
    by_contra hcon
    have h1 : ω ∉ (⋃ i, B i) := fun h => hcon (Set.mem_union_left _ h)
    have h2 : ω ∉ Gᶜ := fun h => hcon (Set.mem_union_right _ h)
    refine hω (hsub ⟨?_, not_not.mp h2⟩)
    refine Set.mem_iInter.mpr fun i => ?_
    intro hmem
    exact h1 (Set.mem_iUnion.mpr ⟨i, hmem⟩)
  have hle : μ.real Goodᶜ ≤ (Fintype.card ι : ℝ) * β + ε₁ :=
    le_trans (measureReal_mono hcompl)
      (le_trans (measureReal_union_le _ _)
        (add_le_add (measureReal_iUnion_le_card_mul μ B hB) hGc))
  have hsum : μ.real Good + μ.real Goodᶜ = 1 := by
    rw [measureReal_add_measureReal_compl hGood, probReal_univ]
  linarith

end GaloisForLFunctions.HTGeometry
