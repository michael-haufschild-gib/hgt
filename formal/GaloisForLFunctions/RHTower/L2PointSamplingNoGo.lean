import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Point sampling does not descend to the canonical `L²` source space

The completed theta source has a canonical class in complex `L²(ℝ)`, but point values belong to
representatives, not to almost-everywhere equivalence classes.  This file proves the obstruction
without a boundedness assumption: no map out of `L²(ℝ)` can recover `f(x)` from the `L²` class of
every representative `f`.

Consequently the literal `L²` theta density and prime-log point sampling cannot define the pair
`(h_theta,S)` needed by the Hilbert sampling defect.  A valid sampling problem must first supply a
source-selected reproducing-kernel or other point-evaluable Hilbert space; it cannot silently use
the ambient `L²` source space.
-/

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace RHTower

/-- A representative supported at one point.  It has value one at the selected point but is zero
as an `L²` class. -/
def l2PointSpike (x : ℝ) : ℝ → ℂ :=
  ({x} : Set ℝ).indicator (fun _ => (1 : ℂ))

theorem l2PointSpike_memLp (x : ℝ) : MemLp (l2PointSpike x) 2 volume := by
  exact memLp_indicator_const (μ := volume) 2 (measurableSet_singleton x) (1 : ℂ)
    (Or.inr (by simp))

theorem l2PointSpike_ae_zero (x : ℝ) : l2PointSpike x =ᵐ[volume] 0 := by
  have hne : ∀ᵐ y : ℝ ∂volume, y ≠ x := by
    rw [ae_iff]
    simp only [not_ne_iff]
    exact measure_singleton x
  filter_upwards [hne] with y hy
  simp [l2PointSpike, hy]

/-- Point evaluation on representatives does not descend through the `L²` quotient, even as an
arbitrary map; a fortiori there is no continuous linear point-evaluation operator on ambient
`L²(ℝ)`. -/
theorem no_l2_pointEvaluator_on_representatives (x : ℝ) :
    ¬ ∃ E : Lp (α := ℝ) ℂ 2 volume → ℂ,
      ∀ (f : ℝ → ℂ) (hf : MemLp f 2 volume), E (hf.toLp f) = f x := by
  rintro ⟨E, hE⟩
  let f := l2PointSpike x
  have hf : MemLp f 2 volume := l2PointSpike_memLp x
  have htoLp : hf.toLp f = 0 := by
    rw [← MemLp.toLp_zero (MemLp.zero : MemLp (0 : ℝ → ℂ) 2 volume)]
    exact MemLp.toLp_congr hf MemLp.zero (l2PointSpike_ae_zero x)
  have hzero := hE (fun _ : ℝ => (0 : ℂ)) MemLp.zero
  have hspike := hE f hf
  rw [htoLp] at hspike
  have hfx : f x = 1 := by simp [f, l2PointSpike]
  rw [hfx] at hspike
  exact zero_ne_one (hzero.symm.trans hspike)

end RHTower
