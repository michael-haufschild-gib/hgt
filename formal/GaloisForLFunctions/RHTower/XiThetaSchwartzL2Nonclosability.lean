import GaloisForLFunctions.RHTower.CyclicNullFormNonclosability
import GaloisForLFunctions.RHTower.XiThetaSchwartzL2ExtensionObstruction

/-!
# The Hedenmalm theta metric is nonclosable in ordinary `L²`

The actual normalized theta source is cyclic for ordinary real translations
in `L²(R)`.  Momentum symmetry and theta nullity put its complete Schwartz
translation orbit in the radical of every candidate nonnegative form.  The
abstract cyclic-null theorem then constructs an `L²`-null sequence with fixed
positive form energy, proving forced nonclosability.
-/

open Complex Function Filter Set MeasureTheory
open scoped Topology SchwartzMap

namespace RHTower

noncomputable section

/-- The complex-linear inclusion of Schwartz space into ordinary `L²(R)`. -/
def xiThetaSchwartzToL2 : 𝓢(ℝ, ℂ) →ₗ[ℂ] XiThetaL2 :=
  (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ)).toLinearMap

/-- The actual normalized theta source translated inside Schwartz space. -/
def xiThetaSchwartzTranslationOrbit (a : ℝ) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.translateCLM ℂ a xiThetaSchwartzSource

/-- The Schwartz orbit maps exactly to the already constructed ordinary-`L²` orbit. -/
theorem xiThetaSchwartzToL2_translationOrbit (a : ℝ) :
    xiThetaSchwartzToL2 (xiThetaSchwartzTranslationOrbit a) =
      xiThetaTranslationOrbit a := by
  rw [xiThetaSchwartzTranslationOrbit, xiThetaTranslationOrbit,
    xiThetaSourceL2, MellinL2.additiveTranslation_toLp,
    mellinL2_schwartzTranslate_eq_translateCLM]
  rfl

/-- The actual translated theta source remains in the left radical of every
momentum-symmetric theta-null Schwartz form. -/
theorem xiThetaSchwartzTranslationOrbit_mem_leftRadical
    (Q : SchwartzMap.ContinuousSchwartzSesquilinearForm)
    (hMomentum : Q.MomentumSymmetric)
    (hThetaNull : ∀ w : 𝓢(ℝ, ℂ), Q xiThetaSchwartzSource w = 0)
    (a : ℝ) :
    xiThetaSchwartzTranslationOrbit a ∈ Q.leftRadical := by
  rw [Q.mem_leftRadical_iff]
  intro w
  let w₀ : 𝓢(ℝ, ℂ) := SchwartzMap.translateCLM ℂ (-a) w
  have hw : SchwartzMap.translateCLM ℂ a w₀ = w := by
    simp [w₀]
  rw [← hw, xiThetaSchwartzTranslationOrbit,
    Q.translate_pair_invariant hMomentum]
  exact hThetaNull w₀

/-- **Hedenmalm singular sequence.** Around every Schwartz vector, a nonnegative
momentum-symmetric theta-null form has an ordinary-`L²` null sequence with
constant form energy and pairwise zero difference energy. -/
theorem exists_xiThetaL2Null_constantEnergy_sequence
    (Q : SchwartzMap.ContinuousSchwartzSesquilinearForm)
    (hNonnegative : Q.IsNonnegative)
    (hMomentum : Q.MomentumSymmetric)
    (hThetaNull : ∀ w : 𝓢(ℝ, ℂ), Q xiThetaSchwartzSource w = 0)
    (u : 𝓢(ℝ, ℂ)) :
    ∃ z : ℕ → 𝓢(ℝ, ℂ),
      Tendsto (fun n ↦ xiThetaSchwartzToL2 (z n)) atTop (nhds 0) ∧
      (∀ m n, Q (z m - z n) (z m - z n) = 0) ∧
      (∀ n, Q (z n) (z n) = Q u u) := by
  have hcyclic : IsCyclicFamily (𝕜 := ℂ)
      (fun a ↦ xiThetaSchwartzToL2 (xiThetaSchwartzTranslationOrbit a)) := by
    simpa only [xiThetaSchwartzToL2_translationOrbit] using
      isCyclicFamily_xiThetaTranslationOrbit
  have hHermitian : Q.IsHermitian := Q.isHermitian_of_isNonnegative hNonnegative
  have hnullOrbit : ∀ a w, Q (xiThetaSchwartzTranslationOrbit a) w = 0 := by
    intro a w
    exact (xiThetaSchwartzTranslationOrbit_mem_leftRadical
      Q hMomentum hThetaNull a) w
  exact Q.exists_ambientNull_constantEnergy_sequence_of_cyclic_null
    xiThetaSchwartzToL2 xiThetaSchwartzTranslationOrbit
    hcyclic hHermitian hnullOrbit u

/-- **Forced nonclosability for the actual Hedenmalm theta source.** Every
nonnegative momentum-symmetric theta-null Schwartz form with a nonzero diagonal
fails sequential closability through ordinary `L²(R)`. -/
theorem not_xiThetaSchwartzForm_sequentiallyL2Closable
    (Q : SchwartzMap.ContinuousSchwartzSesquilinearForm)
    (hNonnegative : Q.IsNonnegative)
    (hMomentum : Q.MomentumSymmetric)
    (hThetaNull : ∀ w : 𝓢(ℝ, ℂ), Q xiThetaSchwartzSource w = 0)
    {u : 𝓢(ℝ, ℂ)} (hu : Q u u ≠ 0) :
    ¬ Q.IsSequentiallyClosableThrough xiThetaSchwartzToL2 := by
  have hcyclic : IsCyclicFamily (𝕜 := ℂ)
      (fun a ↦ xiThetaSchwartzToL2 (xiThetaSchwartzTranslationOrbit a)) := by
    simpa only [xiThetaSchwartzToL2_translationOrbit] using
      isCyclicFamily_xiThetaTranslationOrbit
  have hHermitian : Q.IsHermitian := Q.isHermitian_of_isNonnegative hNonnegative
  have hnullOrbit : ∀ a w, Q (xiThetaSchwartzTranslationOrbit a) w = 0 := by
    intro a w
    exact (xiThetaSchwartzTranslationOrbit_mem_leftRadical
      Q hMomentum hThetaNull a) w
  exact Q.not_isSequentiallyClosableThrough_of_cyclic_null
    xiThetaSchwartzToL2 xiThetaSchwartzTranslationOrbit
    hcyclic hHermitian hnullOrbit hu

/-- There is no nonzero nonnegative Hedenmalm source form which is sequentially
closable through ordinary `L²(R)`. -/
theorem not_exists_nonzero_nonnegative_xiThetaSchwartzForm_sequentiallyL2Closable :
    ¬ ∃ Q : SchwartzMap.ContinuousSchwartzSesquilinearForm,
      Q.IsNonnegative ∧
      Q.MomentumSymmetric ∧
      (∀ w : 𝓢(ℝ, ℂ), Q xiThetaSchwartzSource w = 0) ∧
      Q.IsSequentiallyClosableThrough xiThetaSchwartzToL2 ∧
      ∃ u v : 𝓢(ℝ, ℂ), Q u v ≠ 0 := by
  rintro ⟨Q, hNonnegative, hMomentum, hThetaNull, hClosable, hNonzero⟩
  obtain ⟨u, hu⟩ := Q.exists_diagonal_ne_zero_of_exists_apply_ne_zero hNonzero
  exact (not_xiThetaSchwartzForm_sequentiallyL2Closable
    Q hNonnegative hMomentum hThetaNull hu) hClosable

end

end RHTower
