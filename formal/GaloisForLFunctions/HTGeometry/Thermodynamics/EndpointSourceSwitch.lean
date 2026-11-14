import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact endpoint competition under an external source

The two-endpoint lower envelope in arXiv:2611.16364, equations (4.3)--(4.4),
has a source threshold fixed by a secant of the zero-source energies.
Positive endpoint separation is parameterized by an exponential. Both
ordering classifications and both off-coexistence derivatives are exact.
-/

noncomputable section
open Filter Topology
namespace GaloisForLFunctions.HTGeometry.Thermodynamics

def coexistenceSource (H₀ H₁ k : ℝ) : ℝ := (H₁ - H₀) / Real.exp k

def endpointPotential (H₀ H₁ a k z : ℝ) : ℝ :=
  min (H₀ - z * a) (H₁ - z * (a + Real.exp k))

/-- Only the coupling difference enters the coexistence source. -/
theorem endpoint_gap (H₀ H₁ a k z : ℝ) :
    (H₁ - z * (a + Real.exp k)) - (H₀ - z * a) =
      Real.exp k * (coexistenceSource H₀ H₁ k - z) := by
  unfold coexistenceSource
  field_simp
  ring

theorem lower_endpoint_le_iff (H₀ H₁ a k z : ℝ) :
    H₀ - z * a ≤ H₁ - z * (a + Real.exp k) ↔
      z ≤ coexistenceSource H₀ H₁ k := by
  rw [← sub_nonneg, endpoint_gap, mul_nonneg_iff_of_pos_left (Real.exp_pos k), sub_nonneg]

theorem upper_endpoint_le_iff (H₀ H₁ a k z : ℝ) :
    H₁ - z * (a + Real.exp k) ≤ H₀ - z * a ↔
      coexistenceSource H₀ H₁ k ≤ z := by
  rw [← sub_nonpos, endpoint_gap]
  constructor
  · intro h
    have hz : coexistenceSource H₀ H₁ k - z ≤ 0 := by
      by_contra hn
      have hp := mul_pos (Real.exp_pos k) (lt_of_not_ge hn)
      exact (not_lt_of_ge h) hp
    linarith only [hz]
  · intro h
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos k).le (sub_nonpos.mpr h)

theorem endpointPotential_eq_lower_iff (H₀ H₁ a k z : ℝ) :
    endpointPotential H₀ H₁ a k z = H₀ - z * a ↔
      z ≤ coexistenceSource H₀ H₁ k := by
  rw [endpointPotential, min_eq_left_iff, lower_endpoint_le_iff]

theorem endpointPotential_eq_upper_iff (H₀ H₁ a k z : ℝ) :
    endpointPotential H₀ H₁ a k z = H₁ - z * (a + Real.exp k) ↔
      coexistenceSource H₀ H₁ k ≤ z := by
  rw [endpointPotential, min_eq_right_iff, upper_endpoint_le_iff]

theorem endpoint_coexistence (H₀ H₁ a k : ℝ) :
    H₁ - coexistenceSource H₀ H₁ k * (a + Real.exp k) =
      H₀ - coexistenceSource H₀ H₁ k * a := by
  have h := endpoint_gap H₀ H₁ a k (coexistenceSource H₀ H₁ k)
  simp only [sub_self, mul_zero] at h
  exact sub_eq_zero.mp h

private theorem source_line_hasDerivAt (H a z : ℝ) :
    HasDerivAt (fun x => H - x * a) (-a) z := by
  apply ((hasDerivAt_const z H).sub ((hasDerivAt_id z).mul_const a)).congr_deriv
  ring

/-- The left source derivative is minus the lower endpoint coupling. -/
theorem endpointPotential_left_hasDerivAt (H₀ H₁ a k v : ℝ) :
    HasDerivAt (endpointPotential H₀ H₁ a k) (-a)
      (coexistenceSource H₀ H₁ k - Real.exp v) := by
  have hd := source_line_hasDerivAt H₀ a (coexistenceSource H₀ H₁ k - Real.exp v)
  apply hd.congr_of_eventuallyEq
  have hlt : coexistenceSource H₀ H₁ k - Real.exp v < coexistenceSource H₀ H₁ k :=
    sub_lt_self _ (Real.exp_pos v)
  filter_upwards [Iio_mem_nhds hlt] with z hz
  exact (endpointPotential_eq_lower_iff H₀ H₁ a k z).mpr hz.le

/-- The right source derivative is minus the upper endpoint coupling. -/
theorem endpointPotential_right_hasDerivAt (H₀ H₁ a k v : ℝ) :
    HasDerivAt (endpointPotential H₀ H₁ a k) (-(a + Real.exp k))
      (coexistenceSource H₀ H₁ k + Real.exp v) := by
  have hd := source_line_hasDerivAt H₁ (a + Real.exp k) (coexistenceSource H₀ H₁ k + Real.exp v)
  apply hd.congr_of_eventuallyEq
  have hlt : coexistenceSource H₀ H₁ k < coexistenceSource H₀ H₁ k + Real.exp v :=
    lt_add_of_pos_right _ (Real.exp_pos v)
  filter_upwards [Ioi_mem_nhds hlt] with z hz
  exact (endpointPotential_eq_upper_iff H₀ H₁ a k z).mpr hz.le

/-- The source-response jump is exactly the prescribed interval width. -/
theorem endpointPotential_derivative_jump (H₀ H₁ a k v w : ℝ) :
    deriv (endpointPotential H₀ H₁ a k) (coexistenceSource H₀ H₁ k + Real.exp v) -
      deriv (endpointPotential H₀ H₁ a k) (coexistenceSource H₀ H₁ k - Real.exp w) =
        -Real.exp k := by
  rw [(endpointPotential_right_hasDerivAt _ _ _ _ _).deriv,
    (endpointPotential_left_hasDerivAt _ _ _ _ _).deriv]
  ring

theorem endpointPotential_left_boundary (H₀ H₁ a k : ℝ) :
    HasDerivWithinAt (endpointPotential H₀ H₁ a k) (-a)
      (Set.Iic (coexistenceSource H₀ H₁ k)) (coexistenceSource H₀ H₁ k) := by
  have hd := source_line_hasDerivAt H₀ a (coexistenceSource H₀ H₁ k)
  exact hd.hasDerivWithinAt.congr
    (fun z hz => (endpointPotential_eq_lower_iff H₀ H₁ a k z).mpr hz)
    ((endpointPotential_eq_lower_iff H₀ H₁ a k _).mpr le_rfl)

theorem endpointPotential_right_boundary (H₀ H₁ a k : ℝ) :
    HasDerivWithinAt (endpointPotential H₀ H₁ a k) (-(a + Real.exp k))
      (Set.Ici (coexistenceSource H₀ H₁ k)) (coexistenceSource H₀ H₁ k) := by
  have hd := source_line_hasDerivAt H₁ (a + Real.exp k) (coexistenceSource H₀ H₁ k)
  exact hd.hasDerivWithinAt.congr
    (fun z hz => (endpointPotential_eq_upper_iff H₀ H₁ a k z).mpr hz)
    ((endpointPotential_eq_upper_iff H₀ H₁ a k _).mpr le_rfl)

/-- Every nonzero endpoint interval produces a genuine nondifferentiable coexistence point. -/
theorem endpointPotential_not_differentiable (H₀ H₁ a k : ℝ) :
    ¬ DifferentiableAt ℝ (endpointPotential H₀ H₁ a k) (coexistenceSource H₀ H₁ k) := by
  intro h
  have hl := (endpointPotential_left_boundary H₀ H₁ a k).derivWithin
    (uniqueDiffWithinAt_Iic _)
  have hr := (endpointPotential_right_boundary H₀ H₁ a k).derivWithin
    (uniqueDiffWithinAt_Ici _)
  have hgl := h.hasDerivAt.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iic _)
  have hgr := h.hasDerivAt.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici _)
  have hz : Real.exp k = 0 := by linarith only [hl, hr, hgl, hgr]
  exact Real.exp_ne_zero k hz

/-- Independent endpoint energy shifts translate the threshold by their secant. -/
theorem coexistenceSource_scheme_shift (H₀ H₁ F₀ F₁ k : ℝ) :
    coexistenceSource (H₀ + F₀) (H₁ + F₁) k =
      coexistenceSource H₀ H₁ k + (F₁ - F₀) / Real.exp k := by
  unfold coexistenceSource
  ring

#print axioms endpointPotential_eq_lower_iff
#print axioms endpointPotential_derivative_jump
#print axioms endpointPotential_not_differentiable
#print axioms coexistenceSource_scheme_shift

end GaloisForLFunctions.HTGeometry.Thermodynamics
