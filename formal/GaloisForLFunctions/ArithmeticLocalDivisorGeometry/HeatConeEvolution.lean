import GaloisForLFunctions.HTGeometry.PolynomialHeatProduct
import Mathlib.Topology.Order.Monotone

/-!
# Evolution of polynomial coefficient cones

The finite heat operators form a semigroup. Nonnegative heat preserves the coefficient
cone, so the admissible heat times form a closed upper set. The semigroup proof uses the
commutator with multiplication by `X`, avoiding any rearrangement of double derivative sums.
-/

open Polynomial
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.ArithmeticLocalDivisorGeometry
noncomputable section

/-- Polynomial heat times add, for arbitrary real times and every polynomial. -/
theorem forwardPolyHeat_comp (s t : ℝ) (p : ℝ[X]) :
    forwardPolyHeat s (forwardPolyHeat t p) = forwardPolyHeat (s + t) p := by
  induction p using Polynomial.induction_on with
  | C c => simp only [forwardPolyHeat_C]
  | add p q hp hq => simp only [forwardPolyHeat_add, hp, hq]
  | monomial n c ih =>
    have he : C c * X ^ (n + 1) = X * (C c * X ^ n) := by ring
    rw [he, forwardPolyHeat_X_mul t, forwardPolyHeat_add, forwardPolyHeat_X_mul,
      forwardPolyHeat_C_mul s (2 * t) (derivative (forwardPolyHeat t (C c * X ^ n))),
      ← derivative_forwardPolyHeat s (forwardPolyHeat t (C c * X ^ n)), ih,
      forwardPolyHeat_X_mul]
    simp only [map_add, map_mul, map_ofNat]
    ring

theorem forwardPolyHeat_zero (p : ℝ[X]) : forwardPolyHeat 0 p = p := by
  simp [forwardPolyHeat, Finset.sum_range_succ']

/-- Every heat-series term preserves the coefficient cone at nonnegative time. -/
theorem coeffNonneg_forwardPolyHeat {p : ℝ[X]} (hp : CoeffNonneg p) {s : ℝ} (hs : 0 ≤ s) :
    CoeffNonneg (forwardPolyHeat s p) := by
  unfold forwardPolyHeat
  exact CoeffNonneg.sum _ fun k _ => (hp.iterate_derivative (2 * k)).C_mul (by positivity)

/-- Once attained, the heat cone persists at every later time. -/
theorem coeffNonneg_forwardPolyHeat_mono (p : ℝ[X]) {s t : ℝ} (hst : s ≤ t)
    (hs : CoeffNonneg (forwardPolyHeat s p)) : CoeffNonneg (forwardPolyHeat t p) := by
  have h := coeffNonneg_forwardPolyHeat hs (sub_nonneg.mpr hst)
  rwa [forwardPolyHeat_comp, sub_add_cancel] at h

theorem continuous_forwardPolyHeat_coeff (p : ℝ[X]) (n : ℕ) :
    Continuous (fun s : ℝ => (forwardPolyHeat s p).coeff n) := by
  simp only [forwardPolyHeat, finsetSum_coeff, coeff_C_mul]
  fun_prop

/-- The coefficient inequalities remain valid at a limiting heat time. -/
theorem isClosed_forwardPolyHeat_cone (p : ℝ[X]) :
    IsClosed {s : ℝ | CoeffNonneg (forwardPolyHeat s p)} := by
  change IsClosed {s : ℝ | ∀ n, 0 ≤ (forwardPolyHeat s p).coeff n}
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun n => isClosed_le continuous_const (continuous_forwardPolyHeat_coeff p n)

end
end GaloisForLFunctions.ArithmeticLocalDivisorGeometry
