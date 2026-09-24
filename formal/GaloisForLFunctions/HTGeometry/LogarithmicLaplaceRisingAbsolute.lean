import GaloisForLFunctions.HTGeometry.LogarithmicLaplaceScoreBounds

/-!
# All-order absolute control of logarithmic Laplace scores

The triangular cooling recurrence admits a rising-factorial envelope at every
order. Unlike a uniform power envelope, this retains the cumulative degree
structure needed at the fourteenth derivative near the theta transition.
-/

namespace HTGeometry
noncomputable section

/-- Rising-factorial envelope for logarithmic Laplace scores. -/
def coolingRising : ℕ → ℕ → ℝ → ℝ
  | 0, _, _ => 1
  | n + 1, m, z => (z + (m : ℝ)) * coolingRising n (m + 1) z

private theorem coolingRising_nonneg (n m : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    0 ≤ coolingRising n m z := by
  induction n generalizing m with
  | zero => simp [coolingRising]
  | succ n ih =>
      rw [coolingRising]
      exact mul_nonneg (add_nonneg hz (Nat.cast_nonneg m)) (ih (m + 1))

private theorem coolingRising_succ_right (n m : ℕ) (z : ℝ) :
    coolingRising (n + 1) m z =
      coolingRising n m z * (z + (m : ℝ) + (n : ℝ)) := by
  induction n generalizing m with
  | zero => simp [coolingRising]
  | succ n ih =>
      rw [coolingRising, ih (m + 1), coolingRising]
      push_cast
      ring

private theorem coolingRising_step_le (n m : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    (m : ℝ) * coolingRising n m z + z * coolingRising n (m + 1) z ≤
      coolingRising (n + 1) m z := by
  cases n with
  | zero =>
      simp only [coolingRising, mul_one]
      exact le_of_eq (add_comm _ _)
  | succ n =>
      have hid :
          coolingRising (n + 2) m z -
            ((m : ℝ) * coolingRising (n + 1) m z +
              z * coolingRising (n + 1) (m + 1) z) =
            (m : ℝ) * ((n : ℝ) + 1) * coolingRising n (m + 1) z := by
        rw [coolingRising_succ_right (n + 1) m,
          coolingRising_succ_right n (m + 1), coolingRising]
        push_cast
        ring
      have hp : 0 ≤ (m : ℝ) * ((n : ℝ) + 1) * coolingRising n (m + 1) z := by
        exact mul_nonneg
          (mul_nonneg (Nat.cast_nonneg m) (by positivity))
          (coolingRising_nonneg n (m + 1) hz)
      linarith only [hid, hp]

/-- Even rising products are bounded by their midpoint to the same power.
The induction pairs the two endpoints at each step. -/
theorem coolingRising_even_le_midpow (k m : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    coolingRising (2 * k) m z ≤
      (z + (m : ℝ) + (k : ℝ) - 1 / 2) ^ (2 * k) := by
  induction k generalizing m with
  | zero => simp [coolingRising]
  | succ k ih =>
      let mid : ℝ := z + (m : ℝ) + (k : ℝ) + 1 / 2
      have hmid : 0 ≤ mid := by dsimp [mid]; positivity
      have hpair :
          (z + (m : ℝ)) * (z + (m : ℝ) + 2 * (k : ℝ) + 1) ≤ mid ^ (2 : ℕ) := by
        dsimp [mid]
        nlinarith [sq_nonneg ((k : ℝ) + 1 / 2)]
      have houter : 0 ≤
          (z + (m : ℝ)) * (z + (m : ℝ) + 2 * (k : ℝ) + 1) := by
        positivity
      have heq : coolingRising (2 * (k + 1)) m z =
          (z + (m : ℝ)) * (z + (m : ℝ) + 2 * (k : ℝ) + 1) *
            coolingRising (2 * k) (m + 1) z := by
        rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega,
          coolingRising, coolingRising_succ_right (2 * k) (m + 1)]
        push_cast
        ring
      rw [heq]
      have hinner := ih (m + 1)
      have hinner' : coolingRising (2 * k) (m + 1) z ≤ mid ^ (2 * k) := by
        convert hinner using 1
        dsimp [mid]
        push_cast
        ring
      calc
        _ ≤ ((z + (m : ℝ)) * (z + (m : ℝ) + 2 * (k : ℝ) + 1)) *
              mid ^ (2 * k) := mul_le_mul_of_nonneg_left hinner' houter
        _ ≤ mid ^ (2 : ℕ) * mid ^ (2 * k) :=
          mul_le_mul_of_nonneg_right hpair (pow_nonneg hmid _)
        _ = (z + (m : ℝ) + ((k + 1 : ℕ) : ℝ) - 1 / 2) ^
              (2 * (k + 1)) := by
                have hmideq : mid = z + (m : ℝ) + ((k + 1 : ℕ) : ℝ) - 1 / 2 := by
                  dsimp [mid]
                  push_cast
                  ring
                rw [← pow_add, hmideq]
                congr 1
                omega

/-- Odd rising products admit the exact integer midpoint envelope. -/
theorem coolingRising_odd_le_midpow (k m : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    coolingRising (2 * k + 1) m z ≤
      (z + (m : ℝ) + (k : ℝ)) ^ (2 * k + 1) := by
  induction k generalizing m with
  | zero => simp [coolingRising]
  | succ k ih =>
      let mid : ℝ := z + (m : ℝ) + (k : ℝ) + 1
      have hmid : 0 ≤ mid := by dsimp [mid]; positivity
      have hpair :
          (z + (m : ℝ)) * (z + (m : ℝ) + 2 * (k : ℝ) + 2) ≤ mid ^ (2 : ℕ) := by
        dsimp [mid]
        nlinarith [sq_nonneg ((k : ℝ) + 1)]
      have houter : 0 ≤
          (z + (m : ℝ)) * (z + (m : ℝ) + 2 * (k : ℝ) + 2) := by
        positivity
      have heq : coolingRising (2 * (k + 1) + 1) m z =
          (z + (m : ℝ)) * (z + (m : ℝ) + 2 * (k : ℝ) + 2) *
            coolingRising (2 * k + 1) (m + 1) z := by
        rw [show 2 * (k + 1) + 1 = (2 * k + 1 + 1) + 1 by omega,
          coolingRising, coolingRising_succ_right (2 * k + 1) (m + 1)]
        push_cast
        ring
      rw [heq]
      have hinner := ih (m + 1)
      have hinner' : coolingRising (2 * k + 1) (m + 1) z ≤
          mid ^ (2 * k + 1) := by
        convert hinner using 1
        dsimp [mid]
        push_cast
        ring
      calc
        _ ≤ ((z + (m : ℝ)) * (z + (m : ℝ) + 2 * (k : ℝ) + 2)) *
              mid ^ (2 * k + 1) := mul_le_mul_of_nonneg_left hinner' houter
        _ ≤ mid ^ (2 : ℕ) * mid ^ (2 * k + 1) :=
          mul_le_mul_of_nonneg_right hpair (pow_nonneg hmid _)
        _ = (z + (m : ℝ) + ((k + 1 : ℕ) : ℝ)) ^
              (2 * (k + 1) + 1) := by
                have hmideq : mid = z + (m : ℝ) + ((k + 1 : ℕ) : ℝ) := by
                  dsimp [mid]
                  push_cast
                  ring
                rw [← pow_add, hmideq]
                congr 1
                omega

/-- All-order coefficient-free absolute score bound, with rising-factorial
growth instead of a much larger uniform power envelope. -/
theorem abs_laplaceCoolingJet_le_rising
    (n m : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    |laplaceCoolingJet n m z| ≤
      (2 : ℝ) ^ n * z ^ m * coolingRising n m z := by
  induction n generalizing m with
  | zero =>
      simp [laplaceCoolingJet, coolingRising, abs_of_nonneg (pow_nonneg hz m)]
  | succ n ih =>
      have hlow := ih m
      have hhigh := ih (m + 1)
      calc
        |laplaceCoolingJet (n + 1) m z| ≤
            2 * (m : ℝ) * |laplaceCoolingJet n m z| +
              2 * |laplaceCoolingJet n (m + 1) z| := by
                rw [laplaceCoolingJet]
                calc
                  |2 * (m : ℝ) * laplaceCoolingJet n m z -
                    2 * laplaceCoolingJet n (m + 1) z| ≤
                      |2 * (m : ℝ) * laplaceCoolingJet n m z| +
                        |2 * laplaceCoolingJet n (m + 1) z| := by
                          simpa using (abs_sub_le
                            (2 * (m : ℝ) * laplaceCoolingJet n m z) 0
                            (2 * laplaceCoolingJet n (m + 1) z))
                  _ = _ := by
                    simp [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (m : ℝ) by positivity)]
        _ ≤ 2 * (m : ℝ) * ((2 : ℝ) ^ n * z ^ m * coolingRising n m z) +
              2 * ((2 : ℝ) ^ n * z ^ (m + 1) * coolingRising n (m + 1) z) :=
                add_le_add
                  (mul_le_mul_of_nonneg_left hlow (by positivity))
                  (mul_le_mul_of_nonneg_left hhigh (by norm_num))
        _ = (2 : ℝ) ^ (n + 1) * z ^ m *
              ((m : ℝ) * coolingRising n m z +
                z * coolingRising n (m + 1) z) := by
                  rw [pow_succ, pow_succ]
                  ring
        _ ≤ (2 : ℝ) ^ (n + 1) * z ^ m * coolingRising (n + 1) m z :=
              mul_le_mul_of_nonneg_left (coolingRising_step_le n m hz) (by positivity)

/-- A uniform affine absolute envelope at every cooling order. -/
theorem abs_laplaceCoolingJet_le_affine
    (n : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    |laplaceCoolingJet n 0 z| ≤ (2 * z + (n : ℝ) - 1) ^ n := by
  let k := n / 2
  have hcases : n = 2 * k ∨ n = 2 * k + 1 := by omega
  rcases hcases with heven | hodd
  · rw [heven]
    have hs := abs_laplaceCoolingJet_le_rising (2 * k) 0 hz
    simp only [pow_zero, mul_one] at hs
    have hr := coolingRising_even_le_midpow k 0 hz
    calc
      |laplaceCoolingJet (2 * k) 0 z| ≤
          (2 : ℝ) ^ (2 * k) * coolingRising (2 * k) 0 z := hs
      _ ≤ (2 : ℝ) ^ (2 * k) * (z + (0 : ℝ) + (k : ℝ) - 1 / 2) ^ (2 * k) :=
        mul_le_mul_of_nonneg_left (by simpa only [Nat.cast_zero] using hr) (by positivity)
      _ = (2 * z + ((2 * k : ℕ) : ℝ) - 1) ^ (2 * k) := by
        rw [← mul_pow]
        congr 1
        push_cast
        ring
  · rw [hodd]
    have hs := abs_laplaceCoolingJet_le_rising (2 * k + 1) 0 hz
    simp only [pow_zero, mul_one] at hs
    have hr := coolingRising_odd_le_midpow k 0 hz
    calc
      |laplaceCoolingJet (2 * k + 1) 0 z| ≤
          (2 : ℝ) ^ (2 * k + 1) * coolingRising (2 * k + 1) 0 z := hs
      _ ≤ (2 : ℝ) ^ (2 * k + 1) * (z + (0 : ℝ) + (k : ℝ)) ^ (2 * k + 1) :=
        mul_le_mul_of_nonneg_left (by simpa only [Nat.cast_zero] using hr) (by positivity)
      _ = (2 * z + ((2 * k + 1 : ℕ) : ℝ) - 1) ^ (2 * k + 1) := by
        rw [← mul_pow]
        congr 1
        push_cast
        ring

/-- Sharp coefficient-free pointwise envelope at the missing fourteenth source
order on the actual deep-tail support scale `z ≥ 40`. -/
theorem abs_laplaceCoolingJet_fourteen_le_midpoint
    {z : ℝ} (hz : 40 ≤ z) :
    |laplaceCoolingJet 14 0 z| ≤ ((93 / 40) * z) ^ (14 : ℕ) := by
  have hz0 : 0 ≤ z := by linarith
  have hscore := abs_laplaceCoolingJet_le_rising 14 0 hz0
  simp only [pow_zero, mul_one] at hscore
  have hrising := coolingRising_even_le_midpow 7 0 hz0
  have hmid : z + 13 / 2 ≤ (93 / 80) * z := by nlinarith only [hz]
  calc
    |laplaceCoolingJet 14 0 z| ≤
        (2 : ℝ) ^ (14 : ℕ) * coolingRising 14 0 z := hscore
    _ ≤ (2 : ℝ) ^ (14 : ℕ) * (z + 13 / 2) ^ (14 : ℕ) :=
      mul_le_mul_of_nonneg_left (by norm_num at hrising ⊢; nlinarith only [hrising])
        (by positivity)
    _ ≤ (2 : ℝ) ^ (14 : ℕ) * ((93 / 80) * z) ^ (14 : ℕ) :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by linarith) hmid 14) (by positivity)
    _ = ((93 / 40) * z) ^ (14 : ℕ) := by
      rw [mul_pow]
      ring

end
end HTGeometry
