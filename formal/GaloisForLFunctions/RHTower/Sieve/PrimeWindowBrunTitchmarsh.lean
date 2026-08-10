import GaloisForLFunctions.RHTower.Sieve.PrimeLogWindowCount
import GaloisForLFunctions.RHTower.Sieve.GeneralAffineMeanSquare
import GaloisForLFunctions.PNTPlus.BrunTitchmarsh

/-!
# The prime window count without a level cap

`logNeighbourCount_le_sieve` bounds the primes in a multiplicative window by

```text
2·(length + 1)/log Y + selbergFibreError z Y + z ,
```

with two independent parameters: the sieve level `Y` and the sifting range `z`.  The fibre error
`selbergFibreError z Y` grows like `Y²(log z)⁴`, so `log Y` is forced to stay bounded and the
promised saving of one logarithm never materialises — the bound is `O(length)`, the same as the
number of *integers* in the window.

Brun–Titchmarsh has the same shape with the two parameters identified and no fibre term:

```text
#{primes in (A, B]} ≤ 2(B − A)/log z + 6z(1 + log z)³ + 1
```

for every `z > 1`.  The level is now free, so it may be taken as a power of the window length and
the saving is a genuine logarithm.  Feeding this into the almost-diagonal mean value theorem
replaces the Montgomery–Vaughan near-diagonal weight `n` by `n/log n` on prime supports.
-/

noncomputable section

namespace RHTower.Sieve

open Finset Complex

/-- **Brun–Titchmarsh on a half-open integer interval.**  The `+1` covers the degenerate windows
that carry at most one integer. -/
theorem card_prime_Ioc_le_bt {A B : ℕ} (hAB : A ≤ B) {z : ℝ} (hz : 1 < z) :
    (#{m ∈ Finset.Ioc A B | m.Prime} : ℝ)
      ≤ 2 * ((B : ℝ) - (A : ℝ)) / Real.log z + 6 * z * (1 + Real.log z) ^ 3 + 1 := by
  classical
  have hlogz : (0 : ℝ) < Real.log z := Real.log_pos hz
  have hz0 : (0 : ℝ) < z := by linarith
  have hlognn : (0 : ℝ) ≤ Real.log z := hlogz.le
  have herr : (0 : ℝ) < 6 * z * (1 + Real.log z) ^ 3 := by positivity
  have hABR : (A : ℝ) ≤ (B : ℝ) := by exact_mod_cast hAB
  have hmain0 : (0 : ℝ) ≤ 2 * ((B : ℝ) - (A : ℝ)) / Real.log z :=
    div_nonneg (by linarith) hlognn
  rcases le_or_gt B (A + 1) with hsmall | hbig
  · have hcard : #{m ∈ Finset.Ioc A B | m.Prime} ≤ 1 := by
      refine le_trans (Finset.card_filter_le _ _) ?_
      rw [Nat.card_Ioc]
      omega
    have hcast : (#{m ∈ Finset.Ioc A B | m.Prime} : ℝ) ≤ 1 := by exact_mod_cast hcard
    linarith
  · have hx : (0 : ℝ) < (A : ℝ) + 1 := by positivity
    have hABgt : (A : ℝ) + 1 < (B : ℝ) := by exact_mod_cast hbig
    have hy : (0 : ℝ) < (B : ℝ) - ((A : ℝ) + 1) := by linarith
    have hbt := BrunTitchmarsh.primesBetween_le ((A : ℝ) + 1) ((B : ℝ) - ((A : ℝ) + 1)) z hx hy hz
    rw [show ((A : ℝ) + 1) + ((B : ℝ) - ((A : ℝ) + 1)) = (B : ℝ) by ring] at hbt
    have hpb : BrunTitchmarsh.primesBetween ((A : ℝ) + 1) (B : ℝ)
        = #{m ∈ Finset.Ioc A B | m.Prime} := by
      rw [BrunTitchmarsh.primesBetween]
      congr 1
      rw [show ((A : ℝ) + 1) = ((A + 1 : ℕ) : ℝ) by push_cast; ring, Nat.ceil_natCast,
        Nat.floor_natCast, Finset.Icc_add_one_left_eq_Ioc]
    rw [hpb] at hbt
    have hshrink : 2 * ((B : ℝ) - ((A : ℝ) + 1)) / Real.log z
        ≤ 2 * ((B : ℝ) - (A : ℝ)) / Real.log z := by
      gcongr
      linarith
    linarith

/-- **The prime window count, with the level free.**  Brun–Titchmarsh transported to the neighbour
count of the almost-diagonal mean value theorem. -/
theorem logNeighbourCount_le_bt (s : Finset ℕ) (hs : ∀ m ∈ s, m.Prime)
    {δ : ℝ} (hδ : 0 ≤ δ) {n : ℕ} (hn : 1 ≤ n) {z : ℝ} (hz : 1 < z) :
    (logNeighbourCount s δ n : ℝ)
      ≤ 2 * ((n : ℝ) * (Real.exp δ - Real.exp (-δ)) + 1) / Real.log z
        + 6 * z * (1 + Real.log z) ^ 3 + 1 := by
  classical
  have hlogz : (0 : ℝ) < Real.log z := Real.log_pos hz
  have hnR : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hexp : Real.exp (-δ) ≤ Real.exp δ := Real.exp_le_exp.2 (by linarith)
  have hab : ⌊(n : ℝ) * Real.exp (-δ)⌋₊ ≤ ⌊(n : ℝ) * Real.exp δ⌋₊ :=
    Nat.floor_le_floor (mul_le_mul_of_nonneg_left hexp hnR)
  have hcard := card_prime_Ioc_le_bt hab hz
  have hsub := logNeighbourCount_le_card_prime_Ioc s hs (δ := δ) hn
  have hsubR : (logNeighbourCount s δ n : ℝ)
      ≤ ((#{m ∈ Finset.Ioc ⌊(n : ℝ) * Real.exp (-δ)⌋₊ ⌊(n : ℝ) * Real.exp δ⌋₊ | m.Prime} : ℕ) : ℝ) := by
    exact_mod_cast hsub
  have hlen : ((⌊(n : ℝ) * Real.exp δ⌋₊ : ℝ)) - ((⌊(n : ℝ) * Real.exp (-δ)⌋₊ : ℝ))
      ≤ (n : ℝ) * (Real.exp δ - Real.exp (-δ)) + 1 := by
    have h := floor_sub_floor_le (x := (n : ℝ) * Real.exp (-δ))
      (y := (n : ℝ) * Real.exp δ) (by positivity)
    calc ((⌊(n : ℝ) * Real.exp δ⌋₊ : ℝ)) - ((⌊(n : ℝ) * Real.exp (-δ)⌋₊ : ℝ))
        ≤ (n : ℝ) * Real.exp δ - (n : ℝ) * Real.exp (-δ) + 1 := h
      _ = (n : ℝ) * (Real.exp δ - Real.exp (-δ)) + 1 := by ring
  have hmain : 2 * (((⌊(n : ℝ) * Real.exp δ⌋₊ : ℝ)) - ((⌊(n : ℝ) * Real.exp (-δ)⌋₊ : ℝ)))
        / Real.log z
      ≤ 2 * ((n : ℝ) * (Real.exp δ - Real.exp (-δ)) + 1) / Real.log z := by
    gcongr
  linarith [hsubR, hcard, hmain]

/-- **The prime-supported mean value theorem with a free level.**  The almost-diagonal mean value
theorem with its neighbour count discharged by Brun–Titchmarsh. -/
theorem integral_Icc_normSq_logPoly_le_prime_bt (a : ℕ → ℂ) (s : Finset ℕ)
    (hs : ∀ m ∈ s, m.Prime) {δ W : ℝ} (hδ : 0 < δ) (hWδ : 2 * Real.pi * δ * W ≤ 1)
    {z : ℝ} (hz : 1 < z) :
    (∫ w in Set.Icc (-W) W, ‖logPoly a s w‖ ^ 2)
      ≤ (5 / (4 * δ)) * ∑ n ∈ s,
          (2 * ((n : ℝ) * (Real.exp δ - Real.exp (-δ)) + 1) / Real.log z
            + 6 * z * (1 + Real.log z) ^ 3 + 1) * ‖a n‖ ^ 2 := by
  refine le_trans (integral_Icc_normSq_logPoly_le_count a s hδ hWδ) ?_
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n hn => ?_) (by positivity)
  have hn1 : 1 ≤ n := (hs n hn).one_lt.le.trans' (by norm_num)
  exact mul_le_mul_of_nonneg_right (logNeighbourCount_le_bt s hs hδ.le hn1 hz) (by positivity)

/-! ### The affine form

The mean square on the Perron line, in the `Q + κ·T` shape the vertical-integral estimates consume.
The height-independent part carries the `n`-weighted mass divided by `log z`; the height-linear part
carries the plain mass times the Brun–Titchmarsh error. -/

/-- The height-independent part of the Brun–Titchmarsh mean square. -/
def btMeanSquareConst (a : ℕ → ℂ) (s : Finset ℕ) (σ z : ℝ) : ℝ :=
  10 * Real.pi * Real.exp 1
      * (∑ n ∈ s, (n : ℝ) * ‖a n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2) / Real.log z

/-- The height-linear part of the Brun–Titchmarsh mean square. -/
def btMeanSquareRate (a : ℕ → ℂ) (s : Finset ℕ) (σ z : ℝ) : ℝ :=
  (5 * Real.pi / 2) * (2 / Real.log z + 6 * z * (1 + Real.log z) ^ 3 + 1)
    * ∑ n ∈ s, ‖a n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2

theorem btMeanSquareConst_nonneg (a : ℕ → ℂ) (s : Finset ℕ) (σ : ℝ) {z : ℝ} (hz : 1 < z) :
    0 ≤ btMeanSquareConst a s σ z := by
  have hlogz : (0 : ℝ) < Real.log z := Real.log_pos hz
  have hsum : (0 : ℝ) ≤ ∑ n ∈ s, (n : ℝ) * ‖a n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2 :=
    Finset.sum_nonneg fun n _ => by positivity
  rw [btMeanSquareConst]
  positivity

theorem btMeanSquareRate_nonneg (a : ℕ → ℂ) (s : Finset ℕ) (σ : ℝ) {z : ℝ} (hz : 1 < z) :
    0 ≤ btMeanSquareRate a s σ z := by
  have hlogz : (0 : ℝ) < Real.log z := Real.log_pos hz
  have hz0 : (0 : ℝ) < z := by linarith
  have hsum : (0 : ℝ) ≤ ∑ n ∈ s, ‖a n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2 :=
    Finset.sum_nonneg fun n _ => by positivity
  rw [btMeanSquareRate]
  positivity

/-- **The affine mean square of a prime-supported Dirichlet series.**  The neighbour count's factor
`T` is cancelled by the window width `1/T` it forces, so the `n`-weighted mass — now divided by
`log z` — is charged no height at all. -/
theorem integral_Icc_normSq_LSeries_le_prime_bt_affine {a : ℕ → ℂ} {s : Finset ℕ}
    (hs : ∀ m ∈ s, m.Prime) (hs0 : 0 ∉ s) (hsupp : ∀ n : ℕ, a n ≠ 0 → n ∈ s) (σ : ℝ)
    {T : ℝ} (hT : 1 ≤ T) {z : ℝ} (hz : 1 < z) :
    (∫ y in Set.Icc (-T) T, ‖LSeries a ((σ : ℂ) + (y : ℝ) * I)‖ ^ 2)
      ≤ btMeanSquareConst a s σ z + btMeanSquareRate a s σ z * T := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hlogz : (0 : ℝ) < Real.log z := Real.log_pos hz
  have hz0 : (0 : ℝ) < z := by linarith
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hδ : (0 : ℝ) < 1 / T := by positivity
  have hWδ : 2 * Real.pi * (1 / T) * (T / (2 * Real.pi)) ≤ 1 := by
    rw [show 2 * Real.pi * (1 / T) * (T / (2 * Real.pi)) = 1 by field_simp]
  rw [integral_Icc_normSq_LSeries_eq hs0 hsupp σ hT0.le]
  refine le_trans (mul_le_mul_of_nonneg_left
    (integral_Icc_normSq_logPoly_le_prime_bt
      (fun n => a n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)) s hs hδ hWδ hz) hpi.le) ?_
  rw [show (5 : ℝ) / (4 * (1 / T)) = 5 * T / 4 by field_simp]
  -- split the sum into the `n`-weighted part and the plain part
  set c : ℕ → ℂ := fun n => a n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ) with hc
  have hsplit : ∑ n ∈ s,
        (2 * ((n : ℝ) * (Real.exp (1 / T) - Real.exp (-(1 / T))) + 1) / Real.log z
          + 6 * z * (1 + Real.log z) ^ 3 + 1) * ‖c n‖ ^ 2
      = (2 * (Real.exp (1 / T) - Real.exp (-(1 / T))) / Real.log z)
          * (∑ n ∈ s, (n : ℝ) * ‖c n‖ ^ 2)
        + (2 / Real.log z + 6 * z * (1 + Real.log z) ^ 3 + 1)
          * ∑ n ∈ s, ‖c n‖ ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    field_simp
    ring
  rw [hsplit, btMeanSquareConst, btMeanSquareRate]
  have hS1 : (0 : ℝ) ≤ ∑ n ∈ s, (n : ℝ) * ‖c n‖ ^ 2 :=
    Finset.sum_nonneg fun n _ => by positivity
  have hS0 : (0 : ℝ) ≤ ∑ n ∈ s, ‖c n‖ ^ 2 := Finset.sum_nonneg fun n _ => by positivity
  have hkey : (T * (Real.exp (1 / T) - Real.exp (-(1 / T)))) ≤ 2 * Real.exp 1 :=
    mul_exp_sub_exp_neg_le hT
  have hfirst : 2 * Real.pi * (5 * T / 4
        * ((2 * (Real.exp (1 / T) - Real.exp (-(1 / T))) / Real.log z)
            * ∑ n ∈ s, (n : ℝ) * ‖c n‖ ^ 2))
      ≤ 10 * Real.pi * Real.exp 1 * (∑ n ∈ s, (n : ℝ) * ‖c n‖ ^ 2) / Real.log z := by
    have hnum : 2 * Real.pi * (5 * T / 4
          * ((2 * (Real.exp (1 / T) - Real.exp (-(1 / T))) / Real.log z)
              * ∑ n ∈ s, (n : ℝ) * ‖c n‖ ^ 2))
        = (5 * Real.pi * ((T * (Real.exp (1 / T) - Real.exp (-(1 / T))))
            * ∑ n ∈ s, (n : ℝ) * ‖c n‖ ^ 2)) / Real.log z := by
      field_simp
      ring
    rw [hnum, div_le_div_iff₀ hlogz hlogz]
    have hmul : (T * (Real.exp (1 / T) - Real.exp (-(1 / T))))
          * ∑ n ∈ s, (n : ℝ) * ‖c n‖ ^ 2
        ≤ (2 * Real.exp 1) * ∑ n ∈ s, (n : ℝ) * ‖c n‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hkey hS1
    have hpos : (0 : ℝ) ≤ 5 * Real.pi * Real.log z := by
      nlinarith [Real.pi_pos, hlogz]
    nlinarith [mul_le_mul_of_nonneg_left hmul hpos]
  have hsecond : 2 * Real.pi * (5 * T / 4
        * ((2 / Real.log z + 6 * z * (1 + Real.log z) ^ 3 + 1) * ∑ n ∈ s, ‖c n‖ ^ 2))
      = (5 * Real.pi / 2 * (2 / Real.log z + 6 * z * (1 + Real.log z) ^ 3 + 1)
          * ∑ n ∈ s, ‖c n‖ ^ 2) * T := by ring
  rw [mul_add]
  linarith [hfirst, hsecond.le, hsecond.ge]

end RHTower.Sieve

end
