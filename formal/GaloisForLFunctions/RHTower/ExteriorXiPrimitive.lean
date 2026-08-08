import GaloisForLFunctions.RHTower.ExteriorProfileBounds
import GaloisForLFunctions.RHTower.XiReciprocalSpeed

/-!
# The exterior primitive for the prolate Liouville–Green phase

The general exterior bound is stated for any phase whose speed is at least one and whose reciprocal
speed has controlled variation.  For the prolate exterior phase both conditions are theorems: the
speed bound is already in the corpus and the reciprocal variation was computed exactly, with
constant one.

So the phase side of the estimate carries no conditions at all here: only the amplitude decay of the
Liouville–Green expansion is assumed, and that is what an expansion supplies by construction.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- The derivative of the reciprocal prolate phase speed, as a function. -/
def xiInvSpeedDeriv (s x : ℝ) : ℝ :=
  -(x * (s - 1) / ((x ^ 2 - 1) ^ 2 * xiSpeed s x)) / (xiSpeed s x) ^ 2

theorem hasDerivAt_xiInvSpeedDeriv {s x : ℝ} (hs1 : s ≤ 1) (hx : 1 < x) :
    HasDerivAt (fun u : ℝ => (xiSpeed s u)⁻¹) (xiInvSpeedDeriv s x) x :=
  hasDerivAt_inv_xiSpeed hs1 hx

theorem continuousOn_xiInvSpeedDeriv {s : ℝ} (hs1 : s ≤ 1) :
    ContinuousOn (xiInvSpeedDeriv s) (Set.Ioi 1) := by
  have hspeedne : ∀ x ∈ Set.Ioi (1 : ℝ), xiSpeed s x ≠ 0 := fun x hx =>
    (lt_of_lt_of_le zero_lt_one (one_le_xiSpeed hs1 hx)).ne'
  have hdne : ∀ x ∈ Set.Ioi (1 : ℝ), (x ^ 2 - 1) ^ 2 * xiSpeed s x ≠ 0 := by
    intro x hx
    have hx1 : (1 : ℝ) < x := hx
    have : (0 : ℝ) < x ^ 2 - 1 := by nlinarith
    exact mul_ne_zero (by positivity) (hspeedne x hx)
  refine ContinuousOn.div (ContinuousOn.neg (ContinuousOn.div ?_ ?_ hdne)) ?_ ?_
  · exact continuousOn_id.mul continuousOn_const
  · exact (((continuousOn_pow 2).sub continuousOn_const).pow 2).mul (continuousOn_xiSpeed s)
  · exact (continuousOn_xiSpeed s).pow 2
  · intro x hx
    exact pow_ne_zero 2 (hspeedne x hx)

/-- **The exterior primitive for the prolate phase.**  For an amplitude with the decay of a
Liouville–Green expansion, the branch integral against the prolate exterior phase is bounded by a
constant over the frequency, uniformly in the endpoint.  No condition is placed on the phase: its
speed bound and reciprocal variation are theorems. -/
theorem norm_integral_exterior_xiPhase_le
    {X C c eps s : ℝ} (hX : 2 ≤ X) (hc : 0 < c) (heps : |eps| = 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) {a a' : ℝ → ℂ}
    (ha : ∀ x ∈ Set.uIcc (2 : ℝ) X, HasDerivAt a (a' x) x)
    (hac : ContinuousOn a (Set.uIcc (2 : ℝ) X))
    (ha'c : ContinuousOn a' (Set.uIcc (2 : ℝ) X))
    (haB : ∀ x ∈ Set.uIcc (2 : ℝ) X, ‖a x‖ ≤ C / Real.sqrt x)
    (ha'B : ∀ x ∈ Set.uIcc (2 : ℝ) X, ‖a' x‖ ≤ C / (x * Real.sqrt x)) :
    ‖∫ t in (2 : ℝ)..X, (a t * (((Real.sqrt t)⁻¹ : ℝ) : ℂ))
        * Complex.exp (Complex.I * ((eps * c * xiEndpointPhase s t : ℝ) : ℂ))‖
      ≤ 3 * (3 * max C 1 / 2 + (max C 1) ^ 2 / 2) / (2 * c) := by
  have hsub : Set.uIcc (2 : ℝ) X ⊆ Set.Ioi 1 := by
    rw [Set.uIcc_of_le hX]
    intro x hx
    exact lt_of_lt_of_le one_lt_two hx.1
  have hx1 : ∀ x ∈ Set.uIcc (2 : ℝ) X, (1 : ℝ) < x := fun x hx => hsub hx
  have hx2 : ∀ x ∈ Set.uIcc (2 : ℝ) X, (2 : ℝ) ≤ x := by
    intro x hx
    rw [Set.uIcc_of_le hX] at hx
    exact hx.1
  have hs1' : s ≤ 1 := by linarith
  have hCmax : C ≤ max C 1 := le_max_left _ _
  have hC1 : (1 : ℝ) ≤ max C 1 := le_max_right _ _
  have hC0 : (0 : ℝ) ≤ max C 1 := le_trans zero_le_one hC1
  refine _root_.RHTower.norm_integral_exterior_le (C := max C 1) hX hC0 hc heps
    (fun x hx => hasDerivAt_xiEndpointPhase hs0 (hx1 x hx))
    (fun x hx => hasDerivAt_xiInvSpeedDeriv hs1' (hx1 x hx))
    ha hac ha'c ((continuousOn_xiSpeed s).mono hsub)
    ((continuousOn_xiInvSpeedDeriv hs1').mono hsub)
    (fun x hx => one_le_xiSpeed hs1' (hx1 x hx)) ?_ ?_ ?_
  · intro x hx
    refine le_trans (haB x hx) ?_
    have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr (by linarith [hx1 x hx])
    gcongr
  · intro x hx
    refine le_trans (ha'B x hx) ?_
    have hx0 : (0 : ℝ) < x := by linarith [hx1 x hx]
    have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx0
    gcongr
  · intro x hx
    refine le_trans (abs_deriv_inv_xiSpeed_le hs0 hs1' (hx2 x hx)) ?_
    have hx0 : (0 : ℝ) < x := by linarith [hx1 x hx]
    gcongr

end GaloisForLFunctions.RHTower
