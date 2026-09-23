import GaloisForLFunctions.RHTower.XiAmplitudeDecay
import GaloisForLFunctions.RHTower.ExteriorXiPrimitive
import GaloisForLFunctions.RHTower.CCMFirstRowEnvelopeTail

/-!
# The exterior primitive of the prolate Liouville–Green branch

Both inputs of the exterior oscillatory estimate are now theorems for the actual prolate objects:
the amplitude decay of Dunster's amplitude and its derivative, and the speed and reciprocal-speed
variation of the exterior phase.  Substituting them leaves an estimate with no analytic conditions
at all, only the parameter ranges `0 ≤ s ≤ 1/2` and `c > 0`.

The bound is uniform in the endpoint: the branch integral over `[2, X]` is at most `21/c` however
far the endpoint is taken.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

theorem continuousOn_xiAmplitudeDeriv {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    ContinuousOn (xiAmplitudeDeriv s) (Set.Ioi 1) := by
  have hden : ∀ x ∈ Set.Ioi (1 : ℝ), 2 * (x ^ (2 : ℕ) - s) ≠ 0 := by
    intro x hx
    have hx1 : (1 : ℝ) < x := hx
    have h : (0 : ℝ) < x ^ (2 : ℕ) - s := by nlinarith
    exact ne_of_gt (by positivity)
  refine (continuousOn_xiAmplitude hs0 hs1).mul ?_
  refine ((continuousOn_phaseLogDefect hs0 hs1).div_const 2).sub ?_
  exact continuousOn_id.div (continuousOn_const.mul
    ((continuousOn_pow 2).sub continuousOn_const)) hden

/-- **The exterior branch primitive for the prolate problem.**  With Dunster's amplitude and the
exterior phase, the oscillatory integral over `[2, X]` is at most `21/c`, uniformly in `X`.  No
analytic hypothesis is imposed: every input is a theorem. -/
theorem norm_integral_exterior_dunster_le {X c eps s : ℝ}
    (hX : 2 ≤ X) (hc : 0 < c) (heps : |eps| = 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    ‖∫ t in (2 : ℝ)..X, (((xiAmplitude s t : ℝ) : ℂ) * (((Real.sqrt t)⁻¹ : ℝ) : ℂ))
        * Complex.exp (Complex.I * ((eps * c * xiEndpointPhase s t : ℝ) : ℂ))‖
      ≤ 21 / c := by
  have hsub : Set.uIcc (2 : ℝ) X ⊆ Set.Ioi 1 := by
    rw [Set.uIcc_of_le hX]
    intro x hx
    exact lt_of_lt_of_le one_lt_two hx.1
  have hx1 : ∀ x ∈ Set.uIcc (2 : ℝ) X, (1 : ℝ) < x := fun x hx => hsub hx
  have hx2 : ∀ x ∈ Set.uIcc (2 : ℝ) X, (2 : ℝ) ≤ x := by
    intro x hx
    rw [Set.uIcc_of_le hX] at hx
    exact hx.1
  have hmain := norm_integral_exterior_xiPhase_le (C := 4)
    (a := fun t : ℝ => ((xiAmplitude s t : ℝ) : ℂ))
    (a' := fun t : ℝ => ((xiAmplitudeDeriv s t : ℝ) : ℂ))
    hX hc heps hs0 hs1
    (fun x hx => ((hasDerivAt_xiAmplitude hs0 hs1 (hx1 x hx)).ofReal_comp))
    (Complex.continuous_ofReal.comp_continuousOn
      ((continuousOn_xiAmplitude hs0 hs1).mono hsub))
    (Complex.continuous_ofReal.comp_continuousOn
      ((continuousOn_xiAmplitudeDeriv hs0 hs1).mono hsub))
    (fun x hx => by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact abs_xiAmplitude_le_four hs0 hs1 (hx2 x hx))
    (fun x hx => by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact abs_xiAmplitudeDeriv_le hs0 hs1 (hx2 x hx))
  have hmax : max (4 : ℝ) 1 = 4 := max_eq_left (by norm_num)
  rw [hmax] at hmain
  have hval : 3 * (3 * (4 : ℝ) / 2 + (4 : ℝ) ^ (2 : ℕ) / 2) / (2 * c) = 21 / c := by
    field_simp
    ring
  rwa [hval] at hmain

end GaloisForLFunctions.RHTower
