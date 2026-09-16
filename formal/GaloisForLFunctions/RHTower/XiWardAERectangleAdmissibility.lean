import GaloisForLFunctions.RHTower.SlabFullWidthAdmissibility
import GaloisForLFunctions.RHTower.XiCauchyTransformCompleteness

/-!
# Almost-everywhere admissibility for literal Xi source-rectangle edges

The Ward source-rectangle receiver requires its four literal contour edges to avoid the
centered Xi divisor.  Selecting such edges from a finite zero packet would make a producer
divisor-dependent.  Instead, the actual divisor is countable: every injectively moving
horizontal or vertical edge is admissible for almost every parameter value, provided the edge
stays strictly inside the source strip.

This is an edge-admissibility result only.  It supplies no source-energy upper bound and hence
does not assert RH.
-/

open Complex MeasureTheory Set

namespace RHTower

noncomputable section

/-- An injectively moving vertical edge misses the complete centered Xi divisor almost
everywhere. -/
theorem ae_XiExplicitAdmissible_vertical_edge_of_injective
    (g : ℝ → ℝ) (hg : Function.Injective g)
    {a b : ℝ} (ha : -(1 / 2 : ℝ) < a) (hb : b < 1 / 2) :
    ∀ᵐ t : ℝ ∂volume, ∀ y ∈ Set.Icc a b,
      XiExplicitAdmissible ((g t : ℂ) + (y : ℂ) * I) := by
  let bad : Set ℝ := Complex.re '' {z : ℂ | XiC z = 0}
  have hbad : bad.Countable := countable_xiZeroSet.image Complex.re
  have hpre : (g ⁻¹' bad).Countable := hbad.preimage hg
  filter_upwards [hpre.ae_notMem volume] with t ht
  intro y hy
  have hXi : XiC ((g t : ℂ) + (y : ℂ) * I) ≠ 0 := by
    intro hzero
    apply ht
    refine ⟨(g t : ℂ) + (y : ℂ) * I, hzero, ?_⟩
    simp
  refine SlabFullWidthAdmissibility.XiExplicitAdmissible_of_abs_im_lt_half ?_ hXi
  have him : ((g t : ℂ) + (y : ℂ) * I).im = y := by simp
  rw [him]
  exact abs_lt.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩

/-- An injectively moving horizontal edge inside the source strip misses the complete centered
Xi divisor almost everywhere. -/
theorem ae_XiExplicitAdmissible_horizontal_edge_of_injective
    (g : ℝ → ℝ) (hg : Function.Injective g)
    (hstrip : ∀ t : ℝ, -(1 / 2 : ℝ) < g t ∧ g t < 1 / 2)
    (a b : ℝ) :
    ∀ᵐ t : ℝ ∂volume, ∀ x ∈ Set.Icc a b,
      XiExplicitAdmissible ((x : ℂ) + (g t : ℂ) * I) := by
  let bad : Set ℝ := Complex.im '' {z : ℂ | XiC z = 0}
  have hbad : bad.Countable := countable_xiZeroSet.image Complex.im
  have hpre : (g ⁻¹' bad).Countable := hbad.preimage hg
  filter_upwards [hpre.ae_notMem volume] with t ht
  intro x hx
  have hXi : XiC ((x : ℂ) + (g t : ℂ) * I) ≠ 0 := by
    intro hzero
    apply ht
    refine ⟨(x : ℂ) + (g t : ℂ) * I, hzero, ?_⟩
    simp
  refine SlabFullWidthAdmissibility.XiExplicitAdmissible_of_abs_im_lt_half ?_ hXi
  have him : ((x : ℂ) + (g t : ℂ) * I).im = g t := by simp
  rw [him]
  exact abs_lt.mpr (hstrip t)

end

end RHTower
