import GaloisForLFunctions.RHTower.MobiusLaplaceGammaHankelWall
import Mathlib.Algebra.QuadraticDiscriminant

/-!
# Full signed polarization of the native Gamma--Hankel energy

The mixed term is the literal double sum, not a diagonal or absolute-value
surrogate. Native positivity pays Cauchy--Schwarz and an exact completed
square, including degenerate cutoffs where the second energy vanishes.
-/

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower
open scoped BigOperators

noncomputable section

/-- Literal signed mixed Gamma--Hankel pairing of two finite source prefixes. -/
def paperGammaHankelPairing (a b : ℕ → ℝ) (N : ℕ) (r : ℝ) : ℝ :=
  Real.Gamma r * ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
    a m * b n / (((m + n + 2 : ℕ) : ℝ) ^ r)

@[simp] theorem paperGammaHankelPairing_self (a : ℕ → ℝ) (N : ℕ) (r : ℝ) :
    paperGammaHankelPairing a a N r = finiteGammaHankelEnergy a N r := rfl

/-- Symmetry retains the entire double sum. -/
theorem paperGammaHankelPairing_symm (a b : ℕ → ℝ) (N : ℕ) (r : ℝ) :
    paperGammaHankelPairing a b N r = paperGammaHankelPairing b a N r := by
  unfold paperGammaHankelPairing
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro m _
  rw [Nat.add_comm m n, mul_comm (a m) (b n)]

/-- Exact energy of a signed source displacement, with its full mixed term. -/
theorem paperGammaHankelEnergy_sub (a b : ℕ → ℝ) (t : ℝ) (N : ℕ) (r : ℝ) :
    finiteGammaHankelEnergy (fun n => a n - t * b n) N r =
      finiteGammaHankelEnergy a N r - 2 * t * paperGammaHankelPairing a b N r +
        t ^ 2 * finiteGammaHankelEnergy b N r := by
  calc
    _ = finiteGammaHankelEnergy a N r - t * paperGammaHankelPairing a b N r -
        t * paperGammaHankelPairing b a N r + t ^ 2 * finiteGammaHankelEnergy b N r := by
      simp only [finiteGammaHankelEnergy, paperGammaHankelPairing,
        Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
      ring
    _ = _ := by
      rw [paperGammaHankelPairing_symm b a]
      ring

/-- Native energy positivity bounds the actual signed mixed term. -/
theorem paperGammaHankelPairing_sq_le (a b : ℕ → ℝ) (N : ℕ)
    (r : {r : ℝ // 0 < r}) :
    paperGammaHankelPairing a b N r ^ 2 ≤
      finiteGammaHankelEnergy a N r * finiteGammaHankelEnergy b N r := by
  have hd := discrim_le_zero (a := finiteGammaHankelEnergy b N r)
    (b := -2 * paperGammaHankelPairing a b N r) (c := finiteGammaHankelEnergy a N r)
    (fun t => by
      have ht := finiteGammaHankelEnergy_nonneg (fun n => a n - t * b n) N r.property
      rw [paperGammaHankelEnergy_sub] at ht
      nlinarith only [ht])
  dsimp only [discrim] at hd
  nlinarith only [hd]

/-- Exact square completion remains valid even when the second source has zero energy. -/
theorem paperGammaHankelEnergy_complete_square (a b : ℕ → ℝ) (t : ℝ) (N : ℕ)
    (r : {r : ℝ // 0 < r}) :
    finiteGammaHankelEnergy (fun n => a n - t * b n) N r =
      finiteGammaHankelEnergy a N r -
        paperGammaHankelPairing a b N r ^ 2 / finiteGammaHankelEnergy b N r +
      finiteGammaHankelEnergy b N r *
        (t - paperGammaHankelPairing a b N r / finiteGammaHankelEnergy b N r) ^ 2 := by
  rw [paperGammaHankelEnergy_sub]
  by_cases hb : finiteGammaHankelEnergy b N r = 0
  · have h := paperGammaHankelPairing_sq_le a b N r
    rw [hb, mul_zero] at h
    have hab : paperGammaHankelPairing a b N r = 0 := by nlinarith
    simp [hb, hab]
  · field_simp [hb]
    ring

/-- The exact signed-pairing quotient minimizes energy over every real displacement. -/
theorem paperGammaHankelEnergy_minimizer (a b : ℕ → ℝ) (N : ℕ)
    (r : {r : ℝ // 0 < r}) (t : ℝ) :
    finiteGammaHankelEnergy (fun n => a n -
        (paperGammaHankelPairing a b N r / finiteGammaHankelEnergy b N r) * b n) N r ≤
      finiteGammaHankelEnergy (fun n => a n - t * b n) N r := by
  rw [paperGammaHankelEnergy_complete_square, paperGammaHankelEnergy_complete_square]
  simp only [sub_self, zero_pow (NeZero.ne _), mul_zero, add_zero]
  exact le_add_of_nonneg_right
    (mul_nonneg (finiteGammaHankelEnergy_nonneg b N r.property) (sq_nonneg _))

/-- Opposite displacements retain a positive source-energy cost. -/
theorem paperGammaHankelEnergy_opposite (a b : ℕ → ℝ) (t : ℝ) (N : ℕ) (r : ℝ) :
    finiteGammaHankelEnergy (fun n => a n - t * b n) N r +
      finiteGammaHankelEnergy (fun n => a n - (-t) * b n) N r =
        2 * finiteGammaHankelEnergy a N r + 2 * t ^ 2 * finiteGammaHankelEnergy b N r := by
  rw [paperGammaHankelEnergy_sub, paperGammaHankelEnergy_sub]
  ring

end

end GaloisForLFunctions.HTGeometry
