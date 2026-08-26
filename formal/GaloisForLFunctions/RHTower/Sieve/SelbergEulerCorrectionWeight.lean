import GaloisForLFunctions.RHTower.Sieve.LocalizedReciprocalMoebiusAmplitude
import GaloisForLFunctions.RHTower.Sieve.DivisorSquareSummability
import GaloisForLFunctions.RHTower.Sieve.SquarefreeDivisorCount

open ArithmeticFunction Finset
open scoped BigOperators ArithmeticFunction.Moebius

/-!
# Absolutely summable Barban–Vehov Euler correction

At every active prime the correction to the principal bivariate Euler factor has coefficient
`-p⁻² A_i A_j`, where `A` is the reciprocal--Möbius amplitude. Grouping active primes into a
squarefree support `r` gives the global fibre

`mu(r) / r² * A_r(u) * A_r(v)`.

The localized amplitude identities show that every nonempty support fibre has signed mass zero and
absolute mass `4 ^ ω(r) / r²`. The latter is the square of the divisor count on squarefree `r`, so
the existing divisor-square Dirichlet series proves absolute summability. Total signed correction
mass is therefore exactly one.
-/

namespace RHTower.Sieve

noncomputable section

def selbergCorrectionWeight (r u v : ℕ) : ℝ :=
  (((ArithmeticFunction.moebius r : ℤ) : ℝ) / ((r : ℝ) ^ 2)) *
    localizedReciprocalMoebiusAmplitude r u *
    localizedReciprocalMoebiusAmplitude r v

theorem selbergCorrectionWeight_eq_zero_of_not_squarefree
    {r : ℕ} (hr : ¬ Squarefree r) (u v : ℕ) :
    selbergCorrectionWeight r u v = 0 := by
  rw [selbergCorrectionWeight, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hr]
  norm_num

theorem selbergCorrectionWeight_zero (u v : ℕ) :
    selbergCorrectionWeight 0 u v = 0 := by
  rw [selbergCorrectionWeight]
  norm_num

private theorem summable_norm_abs_localizedReciprocalMoebiusAmplitude
    {r : ℕ} (hr : 0 < r) :
    Summable (fun n : ℕ => ‖|localizedReciprocalMoebiusAmplitude r n|‖) := by
  simpa [Real.norm_eq_abs] using summable_abs_localizedReciprocalMoebiusAmplitude hr

/-- Every fixed squarefree-support correction fibre is absolutely summable. -/
theorem summable_abs_selbergCorrectionWeight_pair (r : ℕ) :
    Summable (fun uv : ℕ × ℕ => |selbergCorrectionWeight r uv.1 uv.2|) := by
  rcases eq_or_ne r 0 with rfl | hr0
  · exact summable_zero.congr (fun uv => by simp [selbergCorrectionWeight_zero])
  by_cases hsq : Squarefree r
  · have hr : 0 < r := Nat.pos_of_ne_zero hr0
    let c : ℝ := ((ArithmeticFunction.moebius r : ℤ) : ℝ) / ((r : ℝ) ^ 2)
    have hprod : Summable (fun uv : ℕ × ℕ =>
        |localizedReciprocalMoebiusAmplitude r uv.1| *
          |localizedReciprocalMoebiusAmplitude r uv.2|) :=
      summable_mul_of_summable_norm
        (summable_norm_abs_localizedReciprocalMoebiusAmplitude hr)
        (summable_norm_abs_localizedReciprocalMoebiusAmplitude hr)
    exact (hprod.mul_left |c|).congr
      (fun uv => by simp [c, selbergCorrectionWeight, abs_mul, mul_assoc])
  · exact summable_zero.congr (fun uv => by
      simp [selbergCorrectionWeight_eq_zero_of_not_squarefree hsq])

private theorem abs_moebius_real_eq_one_of_squarefree {r : ℕ} (hsq : Squarefree r) :
    |((ArithmeticFunction.moebius r : ℤ) : ℝ)| = 1 := by
  have hmu := ArithmeticFunction.moebius_sq (n := r)
  rw [if_pos hsq] at hmu
  have hmuR : (((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2) = 1 := by
    exact_mod_cast hmu
  nlinarith [sq_abs (((ArithmeticFunction.moebius r : ℤ) : ℝ)),
    abs_nonneg (((ArithmeticFunction.moebius r : ℤ) : ℝ))]

/-- Absolute mass of a squarefree correction fibre. -/
theorem tsum_abs_selbergCorrectionWeight_pair_of_squarefree
    {r : ℕ} (hr : 0 < r) (hsq : Squarefree r) :
    (∑' uv : ℕ × ℕ, |selbergCorrectionWeight r uv.1 uv.2|) =
      ((r.divisors.card : ℝ) ^ 2) / ((r : ℝ) ^ 2) := by
  have hnorm := summable_norm_abs_localizedReciprocalMoebiusAmplitude hr
  have hmul := tsum_mul_tsum_of_summable_norm hnorm hnorm
  have hmass := tsum_abs_localizedReciprocalMoebiusAmplitude hr
  let c : ℝ := ((ArithmeticFunction.moebius r : ℤ) : ℝ) / ((r : ℝ) ^ 2)
  have hcoeff :
      |c| = 1 / ((r : ℝ) ^ 2) := by
    dsimp [c]
    rw [abs_div, abs_moebius_real_eq_one_of_squarefree hsq, abs_pow,
      abs_of_pos (by exact_mod_cast hr)]
  calc
    (∑' uv : ℕ × ℕ, |selbergCorrectionWeight r uv.1 uv.2|) =
        ∑' uv : ℕ × ℕ,
          |c| *
            (|localizedReciprocalMoebiusAmplitude r uv.1| *
              |localizedReciprocalMoebiusAmplitude r uv.2|) := by
      apply tsum_congr
      intro uv
      simp only [c, selbergCorrectionWeight, abs_mul]
      ring
    _ = |c| *
          ∑' uv : ℕ × ℕ,
            (|localizedReciprocalMoebiusAmplitude r uv.1| *
              |localizedReciprocalMoebiusAmplitude r uv.2|) := tsum_mul_left
    _ = (1 / ((r : ℝ) ^ 2)) *
          (((2 : ℝ) ^ r.primeFactors.card) ^ 2) := by
      rw [hcoeff, ← hmul, hmass]
      ring
    _ = ((r.divisors.card : ℝ) ^ 2) / ((r : ℝ) ^ 2) := by
      rw [card_divisors_of_squarefree hsq hr.ne']
      push_cast
      ring

theorem tsum_abs_selbergCorrectionWeight_pair (r : ℕ) :
    (∑' uv : ℕ × ℕ, |selbergCorrectionWeight r uv.1 uv.2|) =
      if 0 < r ∧ Squarefree r then
        ((r.divisors.card : ℝ) ^ 2) / ((r : ℝ) ^ 2) else 0 := by
  by_cases hr : 0 < r ∧ Squarefree r
  · rw [if_pos hr]
    exact tsum_abs_selbergCorrectionWeight_pair_of_squarefree hr.1 hr.2
  · rw [if_neg hr]
    rcases eq_or_ne r 0 with rfl | hr0
    · rw [show (fun uv : ℕ × ℕ => |selbergCorrectionWeight 0 uv.1 uv.2|) =
          fun _ => 0 by
        funext uv
        simp [selbergCorrectionWeight_zero]]
      exact tsum_zero
    · have hsq : ¬ Squarefree r := fun hsq =>
          hr ⟨Nat.pos_of_ne_zero hr0, hsq⟩
      rw [show (fun uv : ℕ × ℕ => |selbergCorrectionWeight r uv.1 uv.2|) =
          fun _ => 0 by
        funext uv
        simp [selbergCorrectionWeight_eq_zero_of_not_squarefree hsq]]
      exact tsum_zero

private theorem summable_tsum_abs_selbergCorrectionWeight_pair :
    Summable (fun r : ℕ =>
      ∑' uv : ℕ × ℕ, |selbergCorrectionWeight r uv.1 uv.2|) := by
  apply Summable.of_nonneg_of_le
    (fun r => tsum_nonneg (fun _ => abs_nonneg _))
    (fun r => ?_)
    summable_divisorSquare_div_sq
  rw [tsum_abs_selbergCorrectionWeight_pair]
  split_ifs
  · exact le_rfl
  · positivity

/-- The complete three-variable Euler correction is absolutely summable. -/
theorem summable_abs_selbergCorrectionWeight :
    Summable (fun x : ℕ × (ℕ × ℕ) =>
      |selbergCorrectionWeight x.1 x.2.1 x.2.2|) := by
  rw [summable_prod_of_nonneg (fun _ => abs_nonneg _)]
  exact ⟨summable_abs_selbergCorrectionWeight_pair,
    summable_tsum_abs_selbergCorrectionWeight_pair⟩

/-- Every nonempty prime-support correction fibre has signed mass zero. -/
theorem tsum_selbergCorrectionWeight_pair (r : ℕ) :
    (∑' uv : ℕ × ℕ, selbergCorrectionWeight r uv.1 uv.2) =
      if r = 1 then 1 else 0 := by
  rcases eq_or_ne r 0 with rfl | hr0
  · rw [show (fun uv : ℕ × ℕ => selbergCorrectionWeight 0 uv.1 uv.2) =
        fun _ => 0 by
      funext uv
      exact selbergCorrectionWeight_zero uv.1 uv.2]
    simp
  · have hr : 0 < r := Nat.pos_of_ne_zero hr0
    let c : ℝ := ((ArithmeticFunction.moebius r : ℤ) : ℝ) / ((r : ℝ) ^ 2)
    have hnorm : Summable (fun n : ℕ =>
        ‖localizedReciprocalMoebiusAmplitude r n‖) := by
      simpa [Real.norm_eq_abs] using summable_abs_localizedReciprocalMoebiusAmplitude hr
    have hmul := tsum_mul_tsum_of_summable_norm hnorm hnorm
    have hmass := tsum_localizedReciprocalMoebiusAmplitude hr
    calc
      (∑' uv : ℕ × ℕ, selbergCorrectionWeight r uv.1 uv.2) =
          ∑' uv : ℕ × ℕ, c *
            (localizedReciprocalMoebiusAmplitude r uv.1 *
              localizedReciprocalMoebiusAmplitude r uv.2) := by
        apply tsum_congr
        intro uv
        simp only [c, selbergCorrectionWeight]
        ring
      _ = c * ∑' uv : ℕ × ℕ,
            (localizedReciprocalMoebiusAmplitude r uv.1 *
              localizedReciprocalMoebiusAmplitude r uv.2) := tsum_mul_left
      _ = c * ((∑' u : ℕ, localizedReciprocalMoebiusAmplitude r u) *
            ∑' v : ℕ, localizedReciprocalMoebiusAmplitude r v) := by
        rw [hmul]
      _ = if r = 1 then 1 else 0 := by
        rw [hmass]
        by_cases hr1 : r = 1
        · subst r
          simp [c]
        · simp [hr1]

theorem summable_selbergCorrectionWeight :
    Summable (fun x : ℕ × (ℕ × ℕ) =>
      selbergCorrectionWeight x.1 x.2.1 x.2.2) := by
  rw [← summable_norm_iff]
  simpa [Real.norm_eq_abs] using summable_abs_selbergCorrectionWeight

/-- Total signed mass of the Barban--Vehov Euler correction is exactly one. -/
theorem tsum_selbergCorrectionWeight :
    (∑' x : ℕ × (ℕ × ℕ),
      selbergCorrectionWeight x.1 x.2.1 x.2.2) = 1 := by
  rw [summable_selbergCorrectionWeight.tsum_prod]
  calc
    (∑' r : ℕ, ∑' uv : ℕ × ℕ, selbergCorrectionWeight r uv.1 uv.2) =
        ∑' r : ℕ, if r = 1 then 1 else 0 := by
      apply tsum_congr
      exact tsum_selbergCorrectionWeight_pair
    _ = 1 := by
      rw [tsum_eq_single 1]
      · simp
      · intro b hb
        simp [hb]

end

end RHTower.Sieve
