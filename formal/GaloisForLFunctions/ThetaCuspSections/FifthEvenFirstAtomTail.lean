import GaloisForLFunctions.ThetaCuspSections.FifthEvenFirstAtomTailModel
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Incomplete-gamma tails of the fifth even theta atom

The radial substitution leaves half-integer gamma tails. Their integration
by parts recurrence identifies the exact tail mass with the positive matrix
model and retains the positive incomplete-gamma remainder.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace GaloisForLFunctions.ThetaCuspSections.FifthAtomTail

/-- The common radial density at a tail endpoint. -/
def boundary (q : ℝ) : ℝ := q^(3/2 : ℝ)*Real.exp (-2*q)

/-- An incomplete-gamma moment with rate two. -/
def powerTail (s q : ℝ) : ℝ := ∫ t in Ioi q, t^s*Real.exp (-2*t)

/-- The normalized gamma mass shared by all radial moments. -/
def gammaMass (q : ℝ) : ℝ := powerTail (3/2) q/boundary q

theorem boundary_pos {q : ℝ} (hq : 0<q) : 0<boundary q := by
 unfold boundary
 positivity

end GaloisForLFunctions.ThetaCuspSections.FifthAtomTail
