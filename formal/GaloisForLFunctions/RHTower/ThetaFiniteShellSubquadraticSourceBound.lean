import GaloisForLFunctions.RHTower.ThetaCuspFinitePrimeSource

/-!
# Source envelope for finite theta-shell Fourier transforms

The first shell has a literal double-exponential majorant.  Pointwise atom
domination transfers it to every canonical finite prefix.  This is the
source-specific analytic input for a subquadratic growth bound on its complex
cosine transform.
-/

open Real

namespace RHTower

noncomputable section

/-- The first source atom is bounded by its positive leading Gaussian term. -/
theorem thetaCuspFirstAtom_le_doubleExponentialEnvelope (x : ℝ) :
    thetaCuspSourceTerm x 1 ≤
      4 * Real.pi ^ (2 : ℕ) *
        Real.exp (9 * x / 2 - Real.pi * Real.exp (2 * x)) := by
  let q : ℝ := Real.exp x
  have hq : 0 ≤ q := (Real.exp_pos x).le
  have hpoly :
      2 * Real.pi * (2 * Real.pi * q ^ (4 : ℕ) - 3 * q ^ (2 : ℕ)) ≤
        4 * Real.pi ^ (2 : ℕ) * q ^ (4 : ℕ) := by
    nlinarith [mul_nonneg Real.pi_pos.le (sq_nonneg q)]
  unfold thetaCuspSourceTerm thetaCuspSeed
  norm_num only [Nat.cast_one, one_mul]
  change Real.exp (x / 2) *
      ((2 * Real.pi * (2 * Real.pi * q ^ (4 : ℕ) - 3 * q ^ (2 : ℕ))) *
        Real.exp (-Real.pi * q ^ (2 : ℕ))) ≤ _
  calc
    _ ≤ Real.exp (x / 2) *
          ((4 * Real.pi ^ (2 : ℕ) * q ^ (4 : ℕ)) *
            Real.exp (-Real.pi * q ^ (2 : ℕ))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le)
        (Real.exp_pos _).le
    _ = 4 * Real.pi ^ (2 : ℕ) *
          Real.exp (9 * x / 2 - Real.pi * Real.exp (2 * x)) := by
      dsimp [q]
      rw [show Real.exp x ^ (2 : ℕ) = Real.exp (2 * x) by
        rw [← Real.exp_nat_mul]
        congr 1]
      rw [show Real.exp x ^ (4 : ℕ) = Real.exp (4 * x) by
        rw [← Real.exp_nat_mul]
        congr 1]
      calc
        _ = 4 * Real.pi ^ (2 : ℕ) *
            (Real.exp (x / 2) * Real.exp (4 * x) *
              Real.exp (-Real.pi * Real.exp (2 * x))) := by ring
        _ = _ := by
          rw [show Real.exp (x / 2) * Real.exp (4 * x) *
              Real.exp (-Real.pi * Real.exp (2 * x)) =
              Real.exp (9 * x / 2 - Real.pi * Real.exp (2 * x)) by
            rw [← Real.exp_add, ← Real.exp_add]
            congr 1
            ring]

end

end RHTower
