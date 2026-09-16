import GaloisForLFunctions.RHTower.XiWardCanonicalTransverseScan

/-!
# All-height admissibility for canonical Ward caps

The all-height source-cap problem cannot choose a zero-free contour from the
divisor.  Countability supplies a stronger replacement than finite-edge
admissibility: an injectively moving horizontal line in the open centered
strip is divisor-free at every real coordinate for almost every parameter.
The canonical lower transverse scan therefore gives literal all-height,
source-defined cap lines on a conull parameter set.

This only removes the pole-avoidance gate.  It supplies neither cap
integrability nor the completed prime--polar cancellation required to bound a
cap.
-/

open Complex MeasureTheory Set

namespace RHTower

noncomputable section

/-- A countable centered Xi divisor misses every point of an injectively moving
horizontal source line for almost every parameter. -/
theorem ae_forall_XiExplicitAdmissible_horizontal_of_injective
    (g : ℝ → ℝ) (hg : Function.Injective g)
    (hstrip : ∀ t : ℝ, -(1 / 2 : ℝ) < g t ∧ g t < 1 / 2) :
    ∀ᵐ t : ℝ ∂volume, ∀ x : ℝ,
      XiExplicitAdmissible ((x : ℂ) + (g t : ℂ) * I) := by
  let bad : Set ℝ := Complex.im '' {z : ℂ | XiC z = 0}
  have hbad : bad.Countable := countable_xiZeroSet.image Complex.im
  have hpre : (g ⁻¹' bad).Countable := hbad.preimage hg
  filter_upwards [hpre.ae_notMem volume] with t ht
  intro x
  have hXi : XiC ((x : ℂ) + (g t : ℂ) * I) ≠ 0 := by
    intro hzero
    apply ht
    refine ⟨(x : ℂ) + (g t : ℂ) * I, hzero, ?_⟩
    simp
  refine SlabFullWidthAdmissibility.XiExplicitAdmissible_of_abs_im_lt_half ?_ hXi
  have him : ((x : ℂ) + (g t : ℂ) * I).im = g t := by simp
  rw [him]
  exact abs_lt.mpr (hstrip t)

/-- Canonical lower Ward caps are admissible at every height for almost every
source-defined transverse scan level. -/
theorem ae_forall_XiExplicitAdmissible_canonicalLowerCapLine :
    ∀ᵐ s : ℝ ∂volume, ∀ x : ℝ,
      XiExplicitAdmissible ((x : ℂ) - (xiWardTransverseLevel s : ℂ) * I) := by
  have hinj : Function.Injective (fun s : ℝ => -xiWardTransverseLevel s) :=
    neg_injective.comp xiWardTransverseLevel_injective
  have hstrip : ∀ s : ℝ,
      -(1 / 2 : ℝ) < -xiWardTransverseLevel s ∧
        -xiWardTransverseLevel s < 1 / 2 := by
    intro s
    have hlevel := xiWardTransverseLevel_mem_Ioo s
    constructor <;> linarith [hlevel.1, hlevel.2]
  simpa [sub_eq_add_neg, mul_neg] using
    (ae_forall_XiExplicitAdmissible_horizontal_of_injective
      (fun s : ℝ => -xiWardTransverseLevel s) hinj hstrip)

end

end RHTower
