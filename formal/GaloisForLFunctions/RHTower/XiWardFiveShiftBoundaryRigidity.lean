import GaloisForLFunctions.RHTower.XiWardFiveShiftPairedSubmicroscopicSeparator
import GaloisForLFunctions.RHTower.XiWardSourceWindowMultiplicity

/-!
# Boundary rigidity of the five-shift Euler--Gamma separator

The inverse-square five-shift separator has a uniform positive quantum at every strict positive
transverse displacement and is totalized to zero on the critical diagonal.  Consequently its
critical-boundary discontinuity is forced: no bounded regular source coefficient continuous at
the diagonal can realize this normalized current.

This is a closure theorem for the source-landing problem, not a density estimate.  Any successful
arithmetic landing must retain an unbounded tangent/Green graph or an intrinsically discontinuous
index channel; a bounded continuous trace coefficient cannot carry the submicroscopic quantum.
-/

namespace RHTower

noncomputable section

/-- The uniform inverse-square five-shift quantum forces discontinuity at the critical boundary. -/
theorem not_continuousAt_zero_fiveShiftEulerGammaPairedRenormalizedFeature_one :
    ¬ ContinuousAt
      (fun a : ℝ => fiveShiftEulerGammaPairedRenormalizedFeature 1 a) 0 := by
  intro hcontinuous
  let g : ℝ → ℝ := fun a => a / (2 * (1 + a))
  let F : ℝ → ℝ := fun a =>
    fiveShiftEulerGammaPairedRenormalizedFeature 1 (g a)
  have hg : ContinuousAt g 0 := by
    dsimp only [g]
    have hdencont : ContinuousAt (fun a : ℝ => 2 * (1 + a)) 0 :=
      continuousAt_const.mul (continuousAt_const.add continuousAt_id)
    exact continuousAt_id.div hdencont (by norm_num)
  have hF : ContinuousAt F 0 := by
    have hcomp := hcontinuous.comp_of_eq hg (by simp [g])
    change ContinuousAt
      ((fun a : ℝ => fiveShiftEulerGammaPairedRenormalizedFeature 1 a) ∘ g) 0
    exact hcomp
  have hF0 : F 0 = 0 := by
    simp [F, g, fiveShiftEulerGammaPairedRenormalizedFeature_zero]
  apply not_exists_uniform_positive_continuous_boundarySeparator F hF hF0
  refine ⟨1 / 81, by norm_num, ?_⟩
  intro a ha
  have hden : 0 < 2 * (1 + a) := by positivity
  have hgpos : 0 < g a := by
    dsimp [g]
    positivity
  have hgle : g a ≤ 1 / 2 := by
    dsimp [g]
    rw [div_le_iff₀ hden]
    nlinarith
  exact fiveShiftEulerGammaPairedRenormalizedFeature_one_ge hgpos hgle

/-- No continuous diagonal-vanishing coefficient can agree with the normalized five-shift
separator throughout the open right half-strip. -/
theorem not_exists_continuous_boundaryLanding_fiveShiftEulerGamma :
    ¬ ∃ L : ℝ → ℝ,
      ContinuousAt L 0 ∧ L 0 = 0 ∧
        ∀ a : ℝ, 0 < a → a ≤ 1 / 2 →
          L a = fiveShiftEulerGammaPairedRenormalizedFeature 1 a := by
  rintro ⟨L, hL, hL0, hagree⟩
  let g : ℝ → ℝ := fun a => a / (2 * (1 + a))
  let F : ℝ → ℝ := fun a => L (g a)
  have hg : ContinuousAt g 0 := by
    dsimp only [g]
    have hdencont : ContinuousAt (fun a : ℝ => 2 * (1 + a)) 0 :=
      continuousAt_const.mul (continuousAt_const.add continuousAt_id)
    exact continuousAt_id.div hdencont (by norm_num)
  have hF : ContinuousAt F 0 := by
    change ContinuousAt (L ∘ g) 0
    exact hL.comp_of_eq hg (by simp [g])
  have hF0 : F 0 = 0 := by simp [F, g, hL0]
  apply not_exists_uniform_positive_continuous_boundarySeparator F hF hF0
  refine ⟨1 / 81, by norm_num, ?_⟩
  intro a ha
  have hden : 0 < 2 * (1 + a) := by positivity
  have hgpos : 0 < g a := by
    dsimp [g]
    positivity
  have hgle : g a ≤ 1 / 2 := by
    dsimp [g]
    rw [div_le_iff₀ hden]
    nlinarith
  change 1 / 81 ≤ L (g a)
  rw [hagree (g a) hgpos hgle]
  exact fiveShiftEulerGammaPairedRenormalizedFeature_one_ge hgpos hgle

end

end RHTower
