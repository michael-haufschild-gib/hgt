import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Orthogonal quadratic transfer of a relative norm floor

A floor valid for every monic quadratic remains valid at the shifted Gram
minimizer.  The conclusion is a multiplicative lower bound on the Schur
residual rather than merely strict positivity.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Transfer a relative weighted-monic-quadratic norm floor to the shifted
size-three Gram residual. -/
theorem relative_monicQuadratic_floor_implies_shiftedGram_ratio
    (a b c e f : ℝ) (hq : 0 < a * c - b ^ (2 : ℕ))
    (hfloor : ∀ α β : ℝ,
      (64 / 3969 : ℝ) * f ≤
        f + 2 * α * e + (α ^ (2 : ℕ) + 2 * β) * c +
          2 * α * β * b + β ^ (2 : ℕ) * a) :
    (64 / 3969 : ℝ) * (a * c - b ^ (2 : ℕ)) * f ≤
      (a * c - b ^ (2 : ℕ)) * f -
        (a * e ^ (2 : ℕ) - 2 * b * c * e + c ^ (3 : ℕ)) := by
  let q := a * c - b ^ (2 : ℕ)
  let p := a * e ^ (2 : ℕ) - 2 * b * c * e + c ^ (3 : ℕ)
  let α := (b * c - a * e) / q
  let β := (b * e - c ^ (2 : ℕ)) / q
  have hq' : 0 < q := hq
  have h := hfloor α β
  have hcore : q ^ (2 : ℕ) *
      (f + 2 * α * e + (α ^ (2 : ℕ) + 2 * β) * c +
        2 * α * β * b + β ^ (2 : ℕ) * a) = q * (q * f - p) := by
    dsimp [α, β, p]
    field_simp [hq'.ne']
    dsimp [q]
    ring
  have hmul := mul_le_mul_of_nonneg_left h (sq_nonneg q)
  rw [hcore] at hmul
  have hleft : q ^ (2 : ℕ) * ((64 / 3969 : ℝ) * f) =
      q * ((64 / 3969 : ℝ) * q * f) := by ring
  rw [hleft] at hmul
  have hratio : (64 / 3969 : ℝ) * q * f ≤ q * f - p := by
    by_contra hn
    have hdiff : 0 < (64 / 3969 : ℝ) * q * f - (q * f - p) := by
      linarith
    have hprod := mul_pos hq' hdiff
    nlinarith [hmul]
  simpa only [q, p] using hratio

end GaloisForLFunctions.HTGeometry
