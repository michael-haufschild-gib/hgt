import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-!
# Global stability of a strict theta score floor

A continuous positive slack on the half-line survives every sufficiently small
nonnegative perturbation whose score contribution is eventually nonnegative.
Compactness handles the bounded interval; the tail keeps its sign.
-/

open Filter Set Topology
namespace RHTower
noncomputable section

/-- A strict half-line floor persists under a continuous perturbation with a nonnegative tail. -/
theorem thetaScoreFloor_compactTail_stable {E H : ℝ → ℝ}
    (hE : Continuous E) (hH : Continuous H)
    (hpos : ∀ x : ℝ, 0 ≤ x → 0 < E x)
    (htail : ∀ᶠ x in atTop, 0 ≤ H x) :
    ∃ ε > 0, ∀ t : ℝ, 0 ≤ t → t < ε → ∀ x : ℝ, 0 ≤ x →
      0 < E x + t * H x := by
  obtain ⟨R, hR⟩ := eventually_atTop.1 htail
  let K : ℝ := max 0 R
  have hK : 0 ≤ K := le_max_left _ _
  obtain ⟨e, he, hmin⟩ := isCompact_Icc.exists_forall_le'
    hE.continuousOn (fun x hx => hpos x hx.1)
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image hH.abs.continuousOn
  have hM0 : 0 ≤ M := by
    have hb : |H 0| ≤ M := hM ⟨0, ⟨le_rfl, hK⟩, rfl⟩
    exact (abs_nonneg _).trans hb
  refine ⟨e / (M + 1), div_pos he (by linarith), fun t ht htε x hx => ?_⟩
  by_cases hxK : x ≤ K
  · have hEx := hmin x ⟨hx, hxK⟩
    have hHx : |H x| ≤ M := hM ⟨x, ⟨hx, hxK⟩, rfl⟩
    have hHm : -M ≤ H x := by
      have := neg_abs_le (H x)
      linarith
    have htM : t * (M + 1) < e := (lt_div_iff₀ (by linarith)).1 htε
    have hmul := mul_le_mul_of_nonneg_left hHm ht
    nlinarith
  · have hRx : R ≤ x := (le_max_right 0 R).trans (le_of_not_ge hxK)
    exact add_pos_of_pos_of_nonneg (hpos x hx) (mul_nonneg ht (hR x hRx))

/-- Linear differential score operator for the raw theta moment recurrence. -/
def thetaScoreFloorOperator (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  (1 - 303 * x ^ 2) * g x - 16 * x * deriv g x

/-- The score operator respects differentiable affine source perturbations. -/
theorem thetaScoreFloorOperator_add_const_mul {g h : ℝ → ℝ}
    (hg : Differentiable ℝ g) (hh : Differentiable ℝ h) (t x : ℝ) :
    thetaScoreFloorOperator (fun y => g y + t * h y) x =
      thetaScoreFloorOperator g x + t * thetaScoreFloorOperator h x := by
  have hd : deriv (fun y => g y + t * h y) x = deriv g x + t * deriv h x :=
    ((hg x).hasDerivAt.add ((hh x).hasDerivAt.const_mul t)).deriv
  simp only [thetaScoreFloorOperator, hd]
  ring
end
end RHTower
