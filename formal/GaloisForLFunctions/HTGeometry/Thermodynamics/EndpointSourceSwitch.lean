import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv
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
  <;> ring

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

/-- The left source derivative is minus the lower endpoint coupling. -/
theorem endpointPotential_left_hasDerivAt (H₀ H₁ a k v : ℝ) :
    HasDerivAt (endpointPotential H₀ H₁ a k) (-a)
      (coexistenceSource H₀ H₁ k - Real.exp v) := by
  have hd : HasDerivAt (fun z => H₀ - z * a) (-a)
      (coexistenceSource H₀ H₁ k - Real.exp v) := by
    convert (hasDerivAt_const _ H₀).sub ((hasDerivAt_id _).mul_const a) using 1 <;> simp
  apply hd.congr_of_eventuallyEq
  have hlt : coexistenceSource H₀ H₁ k - Real.exp v < coexistenceSource H₀ H₁ k :=
    sub_lt_self _ (Real.exp_pos v)
  filter_upwards [Iio_mem_nhds hlt] with z hz
  exact (endpointPotential_eq_lower_iff H₀ H₁ a k z).mpr hz.le

/-- The right source derivative is minus the upper endpoint coupling. -/
theorem endpointPotential_right_hasDerivAt (H₀ H₁ a k v : ℝ) :
    HasDerivAt (endpointPotential H₀ H₁ a k) (-(a + Real.exp k))
      (coexistenceSource H₀ H₁ k + Real.exp v) := by
  have hd : HasDerivAt (fun z => H₁ - z * (a + Real.exp k)) (-(a + Real.exp k))
      (coexistenceSource H₀ H₁ k + Real.exp v) := by
    convert (hasDerivAt_const _ H₁).sub ((hasDerivAt_id _).mul_const (a + Real.exp k))
      using 1 <;> simp
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

/-- Independent endpoint energy shifts translate the threshold by their secant. -/
theorem coexistenceSource_scheme_shift (H₀ H₁ F₀ F₁ k : ℝ) :
    coexistenceSource (H₀ + F₀) (H₁ + F₁) k =
      coexistenceSource H₀ H₁ k + (F₁ - F₀) / Real.exp k := by
  unfold coexistenceSource
  ring

#print axioms endpointPotential_eq_lower_iff
#print axioms endpointPotential_derivative_jump
#print axioms coexistenceSource_scheme_shift

end GaloisForLFunctions.HTGeometry.Thermodynamics
