import GaloisForLFunctions.RHTower.ThetaRationalCuspBoundary
import GaloisForLFunctions.HTGeometry.BorelResurgence.ContinuationRigidity

/-!
# Affine cancellation at the theta source's strip boundary

At each point of either boundary line, an arbitrary added function can cancel the completed
theta source for at most one coefficient. Across both entire lines, only countably many
coefficients can remove even one continuation obstruction.
-/

open Filter Topology Set
open GaloisForLFunctions.HTGeometry

namespace RHTower

private theorem thetaCuspStripSource_not_continuesAcross {z : ℂ}
    (hz : |z.im| = Real.pi / 4) :
    ¬ ContinuesAcross thetaCuspStripSource thetaCuspStrip z := by
  rintro ⟨F, hF, he⟩
  exact not_exists_continuation_thetaCuspStripSource hz
    ⟨F, hF, eventually_nhdsWithin_iff.mp he⟩

/-- The completed theta source is singular on both full boundary lines. -/
theorem thetaCuspStripSource_boundary_singular (x : ℝ) :
    ¬ ContinuesAcross thetaCuspStripSource thetaCuspStrip
      ((x : ℂ) + (Real.pi / 4 : ℝ) * Complex.I) ∧
    ¬ ContinuesAcross thetaCuspStripSource thetaCuspStrip
      ((x : ℂ) - (Real.pi / 4 : ℝ) * Complex.I) := by
  constructor <;> apply thetaCuspStripSource_not_continuesAcross
  · simp [abs_of_nonneg (by positivity : 0 ≤ Real.pi / 4)]
  · simp [abs_of_nonneg (by positivity : 0 ≤ Real.pi / 4)]

/-- At each point of either boundary line, at most one affine coefficient can continue. -/
theorem thetaCuspStripSource_affine_coefficients_subsingleton (f : ℂ → ℂ) (x : ℝ) :
    {c : ℂ | ContinuesAcross (fun z => f z + c * thetaCuspStripSource z)
      thetaCuspStrip ((x : ℂ) + (Real.pi / 4 : ℝ) * Complex.I)}.Subsingleton ∧
    {c : ℂ | ContinuesAcross (fun z => f z + c * thetaCuspStripSource z)
      thetaCuspStrip ((x : ℂ) - (Real.pi / 4 : ℝ) * Complex.I)}.Subsingleton := by
  have h := thetaCuspStripSource_boundary_singular x
  exact ⟨(not_continuesAcross_iff_affine_coefficients_subsingleton _ _ _).mp h.1 f,
    (not_continuesAcross_iff_affine_coefficients_subsingleton _ _ _).mp h.2 f⟩

/-- Across both strip boundaries together, the exceptional cancellation coefficients are countable. -/
theorem thetaCuspStripSource_countable_boundary_cancellation (f : ℂ → ℂ) :
    {c : ℂ | ∃ z : ℂ, |z.im| = Real.pi / 4 ∧
      ContinuesAcross (fun w => f w + c * thetaCuspStripSource w)
        thetaCuspStrip z}.Countable := by
  apply (countable_coefficients_continuing_at_singular_points f
    thetaCuspStripSource thetaCuspStrip).mono
  rintro c ⟨z, hz, hc⟩
  exact ⟨z, thetaCuspStripSource_not_continuesAcross hz, hc⟩

end RHTower

#print axioms RHTower.thetaCuspStripSource_boundary_singular
#print axioms RHTower.thetaCuspStripSource_affine_coefficients_subsingleton
#print axioms RHTower.thetaCuspStripSource_countable_boundary_cancellation
