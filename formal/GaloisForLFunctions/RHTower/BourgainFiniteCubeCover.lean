/-
# Finite translated-cube covering connector

This module isolates the measure-theoretic part of Bourgain's physical-box
covering argument.  Translation preserves Lebesgue set integrals, and a
finite cover bounds a nonnegative integral by the sum of its local bounds.
-/
import GaloisForLFunctions.RHTower.BourgainExactLocalTranslation

open MeasureTheory

namespace RHTower

noncomputable section

def bourgainTranslatedNormCube
    (y : BourgainPhaseSpace) (R : ℝ) : Set BourgainPhaseSpace :=
  (fun x => x + y) '' {x : BourgainPhaseSpace | ‖x‖ ≤ R}

theorem mem_bourgainTranslatedNormCube_iff
    {y z : BourgainPhaseSpace} {R : ℝ} :
    z ∈ bourgainTranslatedNormCube y R ↔ ‖z - y‖ ≤ R := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro hz
    refine ⟨z - y, hz, ?_⟩
    simp

theorem setLIntegral_bourgainTranslatedNormCube
    (y : BourgainPhaseSpace) (R : ℝ)
    (f : BourgainPhaseSpace → ENNReal) :
    (∫⁻ z in bourgainTranslatedNormCube y R, f z) =
      ∫⁻ x in {x : BourgainPhaseSpace | ‖x‖ ≤ R}, f (x + y) := by
  symm
  exact
    (measurePreserving_add_right volume y).setLIntegral_comp_emb
      (Homeomorph.addRight y).isClosedEmbedding.measurableEmbedding
      f {x : BourgainPhaseSpace | ‖x‖ ≤ R}

theorem setLIntegral_le_card_mul_of_finite_cover
    {ι : Type*} [Fintype ι]
    (A : Set BourgainPhaseSpace) (U : ι → Set BourgainPhaseSpace)
    (f : BourgainPhaseSpace → ENNReal)
    (hcover : A ⊆ ⋃ i, U i) {B : ENNReal}
    (hlocal : ∀ i, (∫⁻ x in U i, f x) ≤ B) :
    (∫⁻ x in A, f x) ≤ (Fintype.card ι : ENNReal) * B := by
  calc
    (∫⁻ x in A, f x) ≤ ∫⁻ x in ⋃ i, U i, f x :=
      lintegral_mono_set hcover
    _ ≤ ∑' i, ∫⁻ x in U i, f x :=
      lintegral_iUnion_le U f
    _ = ∑ i, ∫⁻ x in U i, f x := tsum_fintype _
    _ ≤ ∑ _i : ι, B := by
      exact Finset.sum_le_sum fun i _ => hlocal i
    _ = (Fintype.card ι : ENNReal) * B := by simp

end

end RHTower
