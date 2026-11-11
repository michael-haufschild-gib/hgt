import GaloisForLFunctions.HTGeometry.FiniteGramsOfAnOperator
import GaloisForLFunctions.RHTower.PaperRestrictedWeilInertia
import GaloisForLFunctions.RHTower.CCM.CCMZetaWeilSmoothIdentity
import GaloisForLFunctions.RHTower.Suzuki.SuzukiRayleighInfimum
import GaloisForLFunctions.ArithmeticIndexDescent.FiniteGramDescent

/-!
# Smooth Weil Grams respect the restricted index

The full zeta Weil matrix, with an arbitrary physical mass shift, is the
Gram of the literal restricted form-domain operator. Its index is bounded
by the actual aperture index, retaining every prime and polar term.
-/

noncomputable section

namespace RHTower.PaperRestrictedWeil

open Zeta23 GaloisForLFunctions.HTGeometry
open Filter Topology

variable {ι : Type*} [Fintype ι]

/-- Full zeta Weil Gram minus the physical `L²` mass Gram. -/
def smoothShiftedWeilGram {a : SuzukiPositiveAperture} (E : ℝ)
    (f : ι → CCMComplexSmoothInteriorSource a) : Matrix ι ι ℂ := fun i j =>
  zetaZeroConfig.W (f j) (f i) - (E : ℂ) *
    inner ℂ (ccmArchimedeanFormToAperture a (f i).toCCMFormVector)
      (ccmArchimedeanFormToAperture a (f j).toCCMFormVector)

theorem smoothShiftedWeilGram_eq_finiteGram {a : SuzukiPositiveAperture} (E : ℝ)
    (f : ι → CCMComplexSmoothInteriorSource a) :
    smoothShiftedWeilGram E f =
      PaperNegativePart.finiteGram (operator a E) (fun i => (f i).toCCMFormVector) := by
  ext i j
  change _ = inner ℂ (operator a E (f i).toCCMFormVector) (f j).toCCMFormVector
  rw [operator_mixed, ccmRestrictedWeilForm_complexSmooth_eq_zetaWeil]
  rfl

/-- Smooth finite matrices cannot introduce negative directions beyond
the restricted Weil index at the same aperture and energy. -/
theorem hermNegIndex_smoothShiftedWeilGram_le {a : SuzukiPositiveAperture} (E : ℝ)
    (f : ι → CCMComplexSmoothInteriorSource a) :
    hermNegIndex (smoothShiftedWeilGram E f) ≤ negativeRank a E := by
  rw [smoothShiftedWeilGram_eq_finiteGram]
  exact PaperNegativePart.hermNegIndex_finiteGram_le
    (operator a E) (operator_selfAdjoint a E) _

private theorem exists_index_realizing_family_of_denseRange
    {H S : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Q : H →L[ℂ] H) (hQ : IsSelfAdjoint Q)
    [FiniteDimensional ℂ (PaperNegativePart.negativeSpace Q)]
    (F : S → H) (hF : DenseRange F) :
    ∃ f : Fin (PaperNegativePart.negativeRank Q) → S,
      hermNegIndex (PaperNegativePart.finiteGram Q (F ∘ f)) =
        PaperNegativePart.negativeRank Q := by
  classical
  obtain ⟨v, hv⟩ := PaperNegativePart.exists_finiteGram_index_eq Q hQ
  have hseq : ∀ i, ∃ s : ℕ → S, Tendsto (F ∘ s) atTop (𝓝 (v i)) := by
    intro i
    obtain ⟨w, hw, hlim⟩ := mem_closure_iff_seq_limit.mp (hF (v i))
    choose s hs using hw
    refine ⟨s, ?_⟩
    simpa only [Function.comp_apply, hs] using hlim
  choose s hs using hseq
  let G : ℕ → Matrix (Fin (PaperNegativePart.negativeRank Q))
      (Fin (PaperNegativePart.negativeRank Q)) ℂ :=
    fun n => PaperNegativePart.finiteGram Q (fun i => F (s i n))
  have hconv : ∀ i j, Tendsto (fun n => G n i j) atTop
      (𝓝 (PaperNegativePart.finiteGram Q v i j)) := by
    intro i j
    exact ((Q.continuous.tendsto (v i)).comp (hs i)).inner (𝕜 := ℂ) (hs j)
  obtain ⟨n, hn⟩ :=
    (GaloisForLFunctions.ArithmeticIndexDescent.eventually_negIndex_limit_le G _ hconv).exists
  rw [hv] at hn
  refine ⟨fun i => s i n, le_antisymm ?_ hn⟩
  exact PaperNegativePart.hermNegIndex_finiteGram_le Q hQ _

/-- A finite family of strict-interior smooth packets realizes the entire
restricted Weil index at every aperture and real energy. -/
theorem exists_smoothShiftedWeilGram_index_eq (a : SuzukiPositiveAperture) (E : ℝ) :
    ∃ f : Fin (negativeRank a E) → CCMComplexSmoothInteriorSource a,
      hermNegIndex (smoothShiftedWeilGram E f) = negativeRank a E := by
  obtain ⟨f, hf⟩ := exists_index_realizing_family_of_denseRange
    (operator a E) (operator_selfAdjoint a E)
    (fun u : CCMComplexSmoothInteriorSource a => u.toCCMFormVector)
    (denseRange_ccmComplexSmoothInteriorSource_toCCMFormVector a)
  refine ⟨f, ?_⟩
  rw [smoothShiftedWeilGram_eq_finiteGram]
  exact hf

end RHTower.PaperRestrictedWeil
