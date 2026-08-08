import GaloisForLFunctions.RHTower.Sieve.TruncatedPrimeSieveMeanSquare
import GaloisForLFunctions.HTGeometry.IntervalMeanSquareMoment

/-!
# The prime-sieve mean square in affine form

The truncated mean square of a prime-supported Dirichlet series carries its truncation height `T` in
two places: multiplying the neighbour count `T(e^{1/T} − e^{−1/T})`, which is *bounded*, and
multiplying the sieve's own error and level, which is genuinely linear.  Separating the two puts the
estimate in the affine shape

`∫_{|y| ≤ T} ‖L(a,σ+iy)‖² dy ≤ Q + κT`,   `Q = 10πe·(∑_n n‖a_n n^{−σ}‖²)/log Y`,

`κ = (5π/2)·∑_n (2/log Y + selbergFibreError z Y + z)‖a_n n^{−σ}‖²`,

because `e^u − e^{−u} ≤ 2u e^u` makes `T(e^{1/T} − e^{−1/T}) ≤ 2e` for `T ≥ 1`.

The separation is exactly what a decaying kernel wants: `Q` — the `n`-weighted mass divided by the
sieve's logarithmic level — is charged a geometric series over dyadic heights, while `κ` is charged one
constant per block.  The `n`-weighting is what makes `Q` small for prime weights: `∑_p p·(log p)²p^{−2σ}`
is a convergent prime sum, not a multiple of the length of the support.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Set

/-- `e^u − e^{−u} ≤ 2u e^u`, from `1 − 2u ≤ e^{−2u}`. -/
theorem exp_sub_exp_neg_le (u : ℝ) :
    Real.exp u - Real.exp (-u) ≤ 2 * u * Real.exp u := by
  have h1 : 1 - 2 * u ≤ Real.exp (-(2 * u)) := by
    have := Real.add_one_le_exp (-(2 * u))
    linarith
  have hfact : Real.exp u - Real.exp (-u) = Real.exp u * (1 - Real.exp (-(2 * u))) := by
    have hmul : Real.exp u * Real.exp (-(2 * u)) = Real.exp (-u) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [mul_sub, mul_one, hmul]
  rw [hfact]
  have hepos : (0 : ℝ) < Real.exp u := Real.exp_pos u
  calc Real.exp u * (1 - Real.exp (-(2 * u)))
      ≤ Real.exp u * (2 * u) := mul_le_mul_of_nonneg_left (by linarith) hepos.le
    _ = 2 * u * Real.exp u := by ring

/-- **The neighbour count is bounded in the height.**  `T(e^{1/T} − e^{−1/T}) ≤ 2e` for `T ≥ 1`: the
window width `1/T` forced by the truncation cancels the factor `T` in front of it. -/
theorem mul_exp_sub_exp_neg_le {T : ℝ} (hT : 1 ≤ T) :
    T * (Real.exp (1 / T) - Real.exp (-(1 / T))) ≤ 2 * Real.exp 1 := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hu : (0 : ℝ) ≤ 1 / T := by positivity
  have hu1 : 1 / T ≤ 1 := by
    rw [div_le_one hT0]
    exact hT
  have h := exp_sub_exp_neg_le (1 / T)
  have hstep : T * (Real.exp (1 / T) - Real.exp (-(1 / T)))
      ≤ T * (2 * (1 / T) * Real.exp (1 / T)) := mul_le_mul_of_nonneg_left h hT0.le
  have hcancel : T * (2 * (1 / T) * Real.exp (1 / T)) = 2 * Real.exp (1 / T) := by
    field_simp
  have hmono : Real.exp (1 / T) ≤ Real.exp 1 := Real.exp_le_exp.2 hu1
  calc T * (Real.exp (1 / T) - Real.exp (-(1 / T)))
      ≤ T * (2 * (1 / T) * Real.exp (1 / T)) := hstep
    _ = 2 * Real.exp (1 / T) := hcancel
    _ ≤ 2 * Real.exp 1 := by linarith

/-- **From a square-root bound to an affine one.**  A bound `√(MS U) ≤ A + B√U` gives
`MS U ≤ (A² + AB) + (AB + B²)U`, because `2√U ≤ 1 + U`. -/
theorem le_affine_of_sqrt_le {MS A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hMS : 0 ≤ MS) {U : ℝ}
    (hU : 0 < U) (h : Real.sqrt MS ≤ A + B * Real.sqrt U) :
    MS ≤ (A ^ 2 + A * B) + (A * B + B ^ 2) * U := by
  have hsU : (0 : ℝ) ≤ Real.sqrt U := Real.sqrt_nonneg U
  have hsUsq : Real.sqrt U ^ 2 = U := Real.sq_sqrt hU.le
  have hsq : Real.sqrt MS ^ 2 = MS := Real.sq_sqrt hMS
  have h2 : 2 * Real.sqrt U ≤ 1 + U := by
    nlinarith [sq_nonneg (Real.sqrt U - 1)]
  have hmono : Real.sqrt MS ^ 2 ≤ (A + B * Real.sqrt U) ^ 2 := by
    have hnn : (0 : ℝ) ≤ Real.sqrt MS := Real.sqrt_nonneg _
    nlinarith [h]
  rw [hsq] at hmono
  nlinarith [hmono, mul_nonneg hA hB, sq_nonneg B]

/-- The height-independent part of the prime-sieve mean square: the `n`-weighted mass of the
coefficients divided by the sieve's logarithmic level. -/
def sieveMeanSquareConst (a : ℕ → ℂ) (s : Finset ℕ) (σ : ℝ) (Y : ℕ) : ℝ :=
  10 * Real.pi * Real.exp 1
      * (∑ n ∈ s, (n : ℝ) * ‖a n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2) / Real.log Y

/-- The height-linear part of the prime-sieve mean square: the sieve's own error and level against
the plain mass of the coefficients. -/
def sieveMeanSquareRate (a : ℕ → ℂ) (s : Finset ℕ) (σ : ℝ) (z Y : ℕ) : ℝ :=
  (5 * Real.pi / 2) * ∑ n ∈ s, (2 / Real.log Y + selbergFibreError z Y + (z : ℝ))
      * ‖a n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2

theorem sieveMeanSquareConst_nonneg (a : ℕ → ℂ) (s : Finset ℕ) (σ : ℝ) {Y : ℕ}
    (hlog : 0 < Real.log Y) : 0 ≤ sieveMeanSquareConst a s σ Y := by
  rw [sieveMeanSquareConst]
  have hsum : (0 : ℝ) ≤ ∑ n ∈ s, (n : ℝ) * ‖a n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2 :=
    Finset.sum_nonneg fun n _ => by positivity
  positivity

theorem sieveMeanSquareRate_nonneg (a : ℕ → ℂ) (s : Finset ℕ) (σ : ℝ) {z Y : ℕ} (hz : 2 ≤ z)
    (hlog : 0 < Real.log Y) : 0 ≤ sieveMeanSquareRate a s σ z Y := by
  rw [sieveMeanSquareRate]
  have hE : (0 : ℝ) ≤ selbergFibreError z Y := selbergFibreError_nonneg hz Y
  have hz0 : (0 : ℝ) ≤ (z : ℝ) := Nat.cast_nonneg z
  have hsum : (0 : ℝ) ≤ ∑ n ∈ s, (2 / Real.log Y + selbergFibreError z Y + (z : ℝ))
      * ‖a n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2 := by
    refine Finset.sum_nonneg fun n _ => ?_
    have hcoef : (0 : ℝ) ≤ 2 / Real.log Y + selbergFibreError z Y + (z : ℝ) := by
      have : (0 : ℝ) ≤ 2 / Real.log Y := by positivity
      linarith
    positivity
  positivity

/-- **The prime-sieve mean square, affine in the height.**  The corpus estimate with its bounded and
its linear parts separated. -/
theorem integral_Icc_normSq_LSeries_le_affine {a : ℕ → ℂ} {s : Finset ℕ} (hs0 : 0 ∉ s)
    (hsupp : ∀ n : ℕ, a n ≠ 0 → n ∈ s) (hprime : ∀ n ∈ s, a n ≠ 0 → n.Prime) (σ : ℝ)
    {T : ℝ} (hT : 1 ≤ T) (z Y : ℕ) (hY : 1 ≤ Y) (hYz : Y ≤ z) (hz : 2 ≤ z)
    (hlog : 0 < Real.log Y) :
    (∫ y in Set.Icc (-T) T, ‖LSeries a ((σ : ℂ) + (y : ℝ) * I)‖ ^ 2)
      ≤ sieveMeanSquareConst a s σ Y + sieveMeanSquareRate a s σ z Y * T := by
  rw [sieveMeanSquareConst, sieveMeanSquareRate]
  have hT0 : (0 : ℝ) < T := by linarith
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  set w : ℕ → ℝ := fun n => ‖a n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2 with hw
  set δ : ℝ := Real.exp (1 / T) - Real.exp (-(1 / T)) with hδ
  have hδbound : T * δ ≤ 2 * Real.exp 1 := mul_exp_sub_exp_neg_le hT
  have hw0 : ∀ n, 0 ≤ w n := by
    intro n
    rw [hw]
    positivity
  have hmain : (5 * T / 4) * ∑ n ∈ s,
        (2 * ((n : ℝ) * δ + 1) / Real.log Y + selbergFibreError z Y + (z : ℝ)) * w n
      ≤ 5 * Real.exp 1 * (∑ n ∈ s, (n : ℝ) * w n) / Real.log Y
        + (5 * T / 4) * ∑ n ∈ s,
            (2 / Real.log Y + selbergFibreError z Y + (z : ℝ)) * w n := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun n hn => ?_
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hfac : (0 : ℝ) ≤ 2 * (n : ℝ) * w n / Real.log Y := by
      have := hw0 n
      positivity
    have hsplit : (5 * T / 4) *
          ((2 * ((n : ℝ) * δ + 1) / Real.log Y + selbergFibreError z Y + (z : ℝ)) * w n)
        = (5 / 4) * (T * δ) * (2 * (n : ℝ) * w n / Real.log Y)
            + (5 * T / 4) * ((2 / Real.log Y + selbergFibreError z Y + (z : ℝ)) * w n) := by
      field_simp
      ring
    have hbound : (5 / 4) * (T * δ) * (2 * (n : ℝ) * w n / Real.log Y)
        ≤ 5 * Real.exp 1 * ((n : ℝ) * w n) / Real.log Y := by
      have hstep := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hδbound (by norm_num : (0 : ℝ) ≤ 5 / 4)) hfac
      calc (5 / 4) * (T * δ) * (2 * (n : ℝ) * w n / Real.log Y)
          ≤ (5 / 4) * (2 * Real.exp 1) * (2 * (n : ℝ) * w n / Real.log Y) := hstep
        _ = 5 * Real.exp 1 * ((n : ℝ) * w n) / Real.log Y := by
            field_simp
            ring
    rw [hsplit]
    linarith
  refine le_trans (integral_Icc_normSq_LSeries_le_prime_sieve hs0 hsupp hprime σ hT0 z Y hY hYz hz
    hlog) ?_
  refine le_trans (mul_le_mul_of_nonneg_left hmain (by positivity)) (le_of_eq ?_)
  ring

end RHTower.Sieve
end
