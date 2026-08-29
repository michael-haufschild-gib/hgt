import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# Convex integral trapezoid bound

A convex real integrand lies below its endpoint chord.  Integrating that chord gives the upper
Hermite--Hadamard inequality.  This complements `ConvexOn.midpoint_mul_le_integral`, which supplies
the lower comparison.
-/

open MeasureTheory Set

namespace GaloisForLFunctions

/-- A convex integrand is bounded above by its endpoint trapezoid. -/
theorem ConvexOn.integral_le_trapezoid {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ConvexOn ℝ (Icc a b) f) (hint : IntervalIntegrable f volume a b) :
    (∫ x in a..b, f x) ≤ (b - a) * (f a + f b) / 2 := by
  let d := b - a
  let k := (f b - f a) / d
  let c := (b * f a - a * f b) / d
  have hd : 0 < d := by dsimp only [d]; linarith
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hchord : ∀ x ∈ Icc a b, f x ≤ x * k + c := by
    intro x hx
    let p := (b - x) / d
    let q := (x - a) / d
    have hp : 0 ≤ p := by
      dsimp only [p]
      exact div_nonneg (by linarith [hx.2]) hd.le
    have hq : 0 ≤ q := by
      dsimp only [q]
      exact div_nonneg (by linarith [hx.1]) hd.le
    have hpq : p + q = 1 := by
      dsimp only [p, q]
      field_simp [hd0]
      dsimp only [d]
      ring
    have harg : p • a + q • b = x := by
      dsimp only [p, q]
      simp only [smul_eq_mul]
      field_simp [hd0]
      dsimp only [d]
      ring
    have hconv := hf.2 (show a ∈ Icc a b by exact ⟨le_rfl, hab.le⟩)
      (show b ∈ Icc a b by exact ⟨hab.le, le_rfl⟩) hp hq hpq
    rw [harg] at hconv
    calc
      f x ≤ p • f a + q • f b := hconv
      _ = x * k + c := by
        dsimp only [p, q, k, c]
        simp only [smul_eq_mul]
        field_simp [hd0]
        ring
  have hid : IntervalIntegrable (fun x : ℝ => x * k) volume a b := by
    exact (by fun_prop : Continuous (fun x : ℝ => x * k)).intervalIntegrable a b
  have hlinear : IntervalIntegrable (fun x => x * k + c) volume a b := by
    exact (by fun_prop : Continuous (fun x : ℝ => x * k + c)).intervalIntegrable a b
  have hmono := intervalIntegral.integral_mono_on hab.le hint hlinear hchord
  have heval : (∫ x in a..b, x * k + c) = (b - a) * (f a + f b) / 2 := by
    rw [intervalIntegral.integral_add hid intervalIntegrable_const,
      intervalIntegral.integral_mul_const, integral_id,
      intervalIntegral.integral_const]
    dsimp only [k, c]
    simp only [smul_eq_mul]
    field_simp [hd0]
    ring
  rw [heval] at hmono
  exact hmono

end GaloisForLFunctions
