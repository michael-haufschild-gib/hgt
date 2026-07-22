import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.Basic

/-!
# Quadratic boundary contact obstructs Pick contractivity

A scalar kernel multiplier can be strictly contractive at every interior point and still fail
two-point Pick contractivity.  The universal obstruction is superlinear contact with a lossless
boundary: the normalized diagonal defect tends to zero while every fixed interior-to-boundary
cross defect has a nonzero limit.  Its two-point determinant is therefore eventually negative.

This is the finite real-kernel form of the Julia--Carathéodory boundary principle.  It is stated
for an arbitrary filter so source applications can use a one-sided aperture limit directly.
-/

open Filter Topology

namespace HTGeometry

noncomputable section

/-- Normalized diagonal of a scalar de Branges--Rovnyak defect. -/
def pickDiagonalDefect (c q : ℝ) : ℝ :=
  (1 - c ^ 2) / (1 - q ^ 2)

/-- Normalized cross entry of a scalar de Branges--Rovnyak defect. -/
def pickCrossDefect (c₀ q₀ c q : ℝ) : ℝ :=
  (1 - c₀ * c) / (1 - q₀ * q)

/-- Determinant of the normalized two-point scalar Pick defect. -/
def pickTwoPointDeterminant (c₀ q₀ c q : ℝ) : ℝ :=
  pickDiagonalDefect c₀ q₀ * pickDiagonalDefect c q -
    pickCrossDefect c₀ q₀ c q ^ 2

/-- **Quadratic-contact determinant law.**  If source and multiplier nodes both approach the
lossless boundary and the normalized moving diagonal defect vanishes, then every fixed-interior
two-point determinant converges to a strictly signed negative square. -/
theorem tendsto_pickTwoPointDeterminant_of_boundaryContact
    {α : Type*} {l : Filter α} (c q : α → ℝ) (c₀ q₀ : ℝ)
    (hc : Tendsto c l (𝓝 1))
    (hq : Tendsto q l (𝓝 1))
    (hdiag : Tendsto (fun a => pickDiagonalDefect (c a) (q a)) l (𝓝 0))
    (hq₀ : q₀ ≠ 1) :
    Tendsto (fun a => pickTwoPointDeterminant c₀ q₀ (c a) (q a)) l
      (𝓝 (-((1 - c₀) / (1 - q₀)) ^ 2)) := by
  have hcmul : Tendsto (fun a => c₀ * c a) l (𝓝 (c₀ * 1)) :=
    tendsto_const_nhds.mul hc
  have hqmul : Tendsto (fun a => q₀ * q a) l (𝓝 (q₀ * 1)) :=
    tendsto_const_nhds.mul hq
  have hnum : Tendsto (fun a => 1 - c₀ * c a) l (𝓝 (1 - c₀)) := by
    simpa using tendsto_const_nhds.sub hcmul
  have hden : Tendsto (fun a => 1 - q₀ * q a) l (𝓝 (1 - q₀)) := by
    simpa using tendsto_const_nhds.sub hqmul
  have hden_ne : 1 - q₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm hq₀)
  have hcross :
      Tendsto (fun a => pickCrossDefect c₀ q₀ (c a) (q a)) l
        (𝓝 ((1 - c₀) / (1 - q₀))) := by
    simpa [pickCrossDefect] using hnum.div hden hden_ne
  have hfirst :
      Tendsto (fun a => pickDiagonalDefect c₀ q₀ * pickDiagonalDefect (c a) (q a)) l
        (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hdiag
  simpa [pickTwoPointDeterminant] using hfirst.sub (hcross.pow 2)

/-- Superlinear lossless-boundary contact forces a negative two-point Pick determinant against
every strict interior multiplier value. -/
theorem eventually_pickTwoPointDeterminant_neg_of_boundaryContact
    {α : Type*} {l : Filter α} (c q : α → ℝ) (c₀ q₀ : ℝ)
    (hc : Tendsto c l (𝓝 1))
    (hq : Tendsto q l (𝓝 1))
    (hdiag : Tendsto (fun a => pickDiagonalDefect (c a) (q a)) l (𝓝 0))
    (hc₀ : c₀ ≠ 1) (hq₀ : q₀ ≠ 1) :
    ∀ᶠ a in l, pickTwoPointDeterminant c₀ q₀ (c a) (q a) < 0 := by
  have hlim := tendsto_pickTwoPointDeterminant_of_boundaryContact c q c₀ q₀
    hc hq hdiag hq₀
  have hquot_ne : (1 - c₀) / (1 - q₀) ≠ 0 := by
    apply div_ne_zero
    · exact sub_ne_zero.mpr (Ne.symm hc₀)
    · exact sub_ne_zero.mpr (Ne.symm hq₀)
  exact hlim.eventually_lt_const (neg_lt_zero.mpr (sq_pos_of_ne_zero hquot_ne))

end

end HTGeometry
