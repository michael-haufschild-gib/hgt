import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Schur elimination for the radius-mixing moment cone

For a decreasing half-line density, radius moments are
`(3a,5b,7c,9e,11f)`.  The positive monic-quadratic radius form implies a
second fifth-moment lower bound once its size-two shifted minor is positive.
-/

namespace GaloisForLFunctions.HTGeometry

theorem radiusQuadratic_nonneg_implies_shiftedGram
    (a b c e f : ℝ) (hq : 0 < 21 * a * c - 25 * b ^ (2 : ℕ))
    (hfloor : ∀ α β : ℝ,
      0 ≤ 11 * f + 18 * α * e +
        (7 * α ^ (2 : ℕ) + 14 * β) * c +
        10 * α * β * b + 3 * β ^ (2 : ℕ) * a) :
    0 ≤ 11 * (21 * a * c - 25 * b ^ (2 : ℕ)) * f -
      (243 * a * e ^ (2 : ℕ) - 630 * b * c * e + 343 * c ^ (3 : ℕ)) := by
  let q := 21 * a * c - 25 * b ^ (2 : ℕ)
  let p := 243 * a * e ^ (2 : ℕ) - 630 * b * c * e + 343 * c ^ (3 : ℕ)
  let α := (35 * b * c - 27 * a * e) / q
  let β := (45 * b * e - 49 * c ^ (2 : ℕ)) / q
  have hq' : 0 < q := hq
  have h := hfloor α β
  have hcore : q ^ (2 : ℕ) *
      (11 * f + 18 * α * e +
        (7 * α ^ (2 : ℕ) + 14 * β) * c +
        10 * α * β * b + 3 * β ^ (2 : ℕ) * a) =
      q * (11 * q * f - p) := by
    dsimp [α, β, p]
    field_simp [hq'.ne']
    dsimp [q]
    ring
  have hmul : 0 ≤ q * (11 * q * f - p) := by
    rw [← hcore]
    exact mul_nonneg (sq_nonneg q) h
  have hratio : 0 ≤ 11 * q * f - p := by
    by_contra hn
    have hneg : 11 * q * f - p < 0 := lt_of_not_ge hn
    have hprod := mul_pos hq' (neg_pos.mpr hneg)
    nlinarith [hmul]
  simpa only [q, p] using hratio

end GaloisForLFunctions.HTGeometry
