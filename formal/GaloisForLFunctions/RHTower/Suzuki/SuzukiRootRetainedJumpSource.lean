import GaloisForLFunctions.RHTower.GammaJumpFourierMultiplier
import GaloisForLFunctions.HTGeometry.FourierFirstOrderWeight

/-!
# The jump applied to the prime derivative is an ordinary `L²` source

The jump multiplier costs exactly one derivative: its symbol is at most affine, so it is bounded
from the first-order weight to `L²`, and the first-order weight of a Fourier transform is the
transform of the derivative.  Composing the two, the jump sends a profile whose value and derivative
are both square integrable to a square-integrable profile.

Applied to the prime derivative — which decays like `L^{-3/2}` with second derivative `L^{-5/2}`,
hence lies in `H¹` on a terminal ray — this makes the forcing of the difference equation an ordinary
unweighted `L²` source, with no weight and no compression involved.  Adding it to the already
square-integrable correction derivative leaves the whole carrier derivative square integrable.
-/

open MeasureTheory
open scoped ENNReal FourierTransform

noncomputable section

namespace GaloisForLFunctions.RHTower

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

omit [CompleteSpace X] in
/-- **The jump of an `H¹` profile is `L²`.**  One derivative pays for the affine growth of the
symbol; nothing else is used. -/
theorem eLpNorm_gammaJump_fourier_ne_top {v : ℝ → X} (hv : Integrable v)
    (hv' : Differentiable ℝ v) (hdv : Integrable (deriv v))
    (h1 : eLpNorm (𝓕 v) 2 volume ≠ ⊤) (h2 : eLpNorm (𝓕 (deriv v)) 2 volume ≠ ⊤) :
    eLpNorm (fun ξ => ((gammaJumpMultiplier ξ : ℝ) : ℂ) • 𝓕 v ξ) 2 volume ≠ ⊤ := by
  have hbase := eLpNorm_gammaJumpMultiplier_smul_le (X := X) (𝓕 v)
  have hfirst : eLpNorm (fun ξ => (((1 + |ξ| : ℝ)) : ℂ) • 𝓕 v ξ) 2 volume ≠ ⊤ :=
    HTGeometry.eLpNorm_firstOrder_fourier_ne_top hv hv' hdv h1 h2
  exact ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfirst) hbase

/-! ## The carrier derivative -/

variable {Y : Type*} [NormedAddCommGroup Y]

/-- Two square-integrable profiles have a square-integrable sum: the carrier derivative is the sum
of the prime derivative and the correction derivative, so it inherits `L²`. -/
theorem lintegral_sq_add_ne_top {u w : ℝ → Y} {s : Set ℝ}
    (hum : AEStronglyMeasurable u (volume.restrict s))
    (hu : (∫⁻ L in s, ‖u L‖ₑ ^ 2) ≠ ⊤) (hw : (∫⁻ L in s, ‖w L‖ₑ ^ 2) ≠ ⊤) :
    (∫⁻ L in s, ‖u L + w L‖ₑ ^ 2) ≠ ⊤ := by
  have hadd : ∀ a b : ℝ≥0∞, (a + b) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2) := by
    intro a b
    have h1 : a + b ≤ 2 * max a b :=
      (add_le_add (le_max_left a b) (le_max_right a b)).trans (by rw [two_mul])
    have h2 : max a b ^ 2 ≤ a ^ 2 + b ^ 2 := by
      rcases max_choice a b with h | h <;> rw [h]
      · exact le_self_add
      · exact le_add_self
    calc (a + b) ^ 2 ≤ (2 * max a b) ^ 2 := pow_le_pow_left' h1 2
      _ = 4 * max a b ^ 2 := by ring
      _ ≤ 4 * (a ^ 2 + b ^ 2) := mul_le_mul' le_rfl h2
  have hmono : ∀ L : ℝ, ‖u L + w L‖ₑ ^ 2 ≤ 4 * (‖u L‖ₑ ^ 2 + ‖w L‖ₑ ^ 2) := by
    intro L
    exact (pow_le_pow_left' (enorm_add_le _ _) 2).trans (hadd _ _)
  have hstep : (∫⁻ L in s, ‖u L + w L‖ₑ ^ 2)
      ≤ ∫⁻ L in s, 4 * (‖u L‖ₑ ^ 2 + ‖w L‖ₑ ^ 2) := lintegral_mono hmono
  have hsplit : (∫⁻ L in s, 4 * (‖u L‖ₑ ^ 2 + ‖w L‖ₑ ^ 2))
      ≤ 4 * ((∫⁻ L in s, ‖u L‖ₑ ^ 2) + (∫⁻ L in s, ‖w L‖ₑ ^ 2)) := by
    rw [lintegral_const_mul' _ _ (by simp : (4 : ℝ≥0∞) ≠ ⊤),
      lintegral_add_left' (hum.enorm.pow_const 2)]
  refine ne_top_of_le_ne_top ?_ (hstep.trans hsplit)
  exact ENNReal.mul_ne_top (by simp) (ENNReal.add_ne_top.mpr ⟨hu, hw⟩)

end GaloisForLFunctions.RHTower
