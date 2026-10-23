import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.ResonatorKroneckerLaw

/-!
# The adjunction remainder on resonators is negative definite

The review's adjunction formula on resonators compares the cross-prime aggregate
`Σ_{r ≠ s} w_r w_s A_F(log(s/r))`, `w_r = log r/√r`, with the Euler envelopes
`E_r = 2 log r/(√r − 1)` times `A_F(0)`, and asks whether the remainder is a positive form in the
train's coefficients.

On a `{p, q}`-resonator `F = Σ_{i,j} c(i, j) g(· − i log p − j log q)` with `g` narrower than half the
lattice separation, the logarithms of distinct primes being `ℤ`-independent, only the pairs
`(p, q)`, `(q, p)` produce lattice lags, and `A_F(±log(q/p))` counts the coefficient pairs one step
apart in the anti-diagonal direction: in units of `A_g(0)` it is the **cross lag count**
`X(c) = Σ c(i + 1, j) c(i, j + 1)` (`crossLag`). The remainder is then

    R(c) = 2 w_p w_q X(c) − (E_p + E_q) Σ c(i, j)²       (`resonatorRemainder`).

**Theorem** (`resonatorRemainder_le`). `R(c) ≤ −(E_p + E_q − w_p² − w_q²) Σ c²` and
`w_r² < E_r` for every `r ≥ 2` (`resonatorWeight_sq_lt_eulerEnvelope`), so `R` is **negative definite** on every
resonator. The cross term never pays for the envelopes: on resonators, where the prime
self-intersection is the Kronecker sum of the two towers (`heckeForm_box_eq`), positivity of the
Weil form must come from the archimedean collar and the pole, not from the prime side.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- The comb weight `w_r = log r/√r`. -/
def resonatorWeight (r : ℕ) : ℝ := Real.log r / Real.sqrt r

/-- The Euler envelope `E_r = 2 log r/(√r − 1)`. -/
def eulerEnvelope (r : ℕ) : ℝ := 2 * Real.log r / (Real.sqrt r - 1)

/-- The cross lag count `X(c) = Σ_{i < M, j < N} c(i + 1, j) c(i, j + 1)`. -/
def crossLag (M N : ℕ) (c : ℕ × ℕ → ℝ) : ℝ :=
  ∑ i ∈ range M, ∑ j ∈ range N, c (i + 1, j) * c (i, j + 1)

/-- The coefficient energy `Σ_{i ≤ M, j ≤ N} c(i, j)²`. -/
def boxEnergy (M N : ℕ) (c : ℕ × ℕ → ℝ) : ℝ :=
  ∑ i ∈ range (M + 1), ∑ j ∈ range (N + 1), c (i, j) ^ 2

/-- The adjunction remainder `2 w_p w_q X(c) − (E_p + E_q) Σ c²` on a `{p, q}`-resonator. -/
def resonatorRemainder (p q M N : ℕ) (c : ℕ × ℕ → ℝ) : ℝ :=
  2 * resonatorWeight p * resonatorWeight q * crossLag M N c -
    (eulerEnvelope p + eulerEnvelope q) * boxEnergy M N c

theorem boxEnergy_nonneg (M N : ℕ) (c : ℕ × ℕ → ℝ) : 0 ≤ boxEnergy M N c :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Shifted squares stay inside the enlarged box. -/
theorem sum_sq_shift_fst_le (M N : ℕ) (c : ℕ × ℕ → ℝ) :
    ∑ i ∈ range M, ∑ j ∈ range N, c (i + 1, j) ^ 2 ≤ boxEnergy M N c := by
  unfold boxEnergy
  rw [Finset.sum_range_succ']
  refine le_add_of_le_of_nonneg (Finset.sum_le_sum fun i _ => ?_)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  rw [Finset.sum_range_succ]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem sum_sq_shift_snd_le (M N : ℕ) (c : ℕ × ℕ → ℝ) :
    ∑ i ∈ range M, ∑ j ∈ range N, c (i, j + 1) ^ 2 ≤ boxEnergy M N c := by
  unfold boxEnergy
  rw [Finset.sum_range_succ]
  refine le_add_of_le_of_nonneg (Finset.sum_le_sum fun i _ => ?_)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  rw [Finset.sum_range_succ']
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- `|X(c)| ≤ Σ c²`. -/
theorem abs_crossLag_le (M N : ℕ) (c : ℕ × ℕ → ℝ) : |crossLag M N c| ≤ boxEnergy M N c := by
  have h1 := sum_sq_shift_fst_le M N c
  have h2 := sum_sq_shift_snd_le M N c
  have hpt : ∀ i j, 2 * |c (i + 1, j) * c (i, j + 1)| ≤ c (i + 1, j) ^ 2 + c (i, j + 1) ^ 2 :=
    fun i j => by
      rw [abs_mul]
      nlinarith [sq_nonneg (|c (i + 1, j)| - |c (i, j + 1)|), sq_abs (c (i + 1, j)),
        sq_abs (c (i, j + 1))]
  have habs : |crossLag M N c| ≤ ∑ i ∈ range M, ∑ j ∈ range N, |c (i + 1, j) * c (i, j + 1)| :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
  have hsum : 2 * ∑ i ∈ range M, ∑ j ∈ range N, |c (i + 1, j) * c (i, j + 1)| ≤
      (∑ i ∈ range M, ∑ j ∈ range N, c (i + 1, j) ^ 2) +
        ∑ i ∈ range M, ∑ j ∈ range N, c (i, j + 1) ^ 2 := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => hpt i j
  linarith

/-- `log x ≤ 2(√x − 1)` for `x > 0`. -/
theorem log_le_two_mul_sqrt_sub_one {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * (Real.sqrt x - 1) := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h := Real.log_le_sub_one_of_pos hs
  rw [Real.log_sqrt hx.le] at h
  linarith

theorem resonatorWeight_nonneg {r : ℕ} (hr : 1 ≤ r) : 0 ≤ resonatorWeight r :=
  div_nonneg (Real.log_nonneg (by exact_mod_cast hr)) (Real.sqrt_nonneg _)

/-- **The square of the comb weight is below the Euler envelope**: `w_r² < E_r` for `r ≥ 2`. -/
theorem resonatorWeight_sq_lt_eulerEnvelope {r : ℕ} (hr : 2 ≤ r) :
    resonatorWeight r ^ 2 < eulerEnvelope r := by
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hpos : (0 : ℝ) < r := by linarith
  have hs1 : 1 < Real.sqrt r := by
    rw [Real.lt_sqrt (by norm_num)]
    linarith
  have hL : 0 < Real.log r := Real.log_pos (by linarith)
  have hLs := log_le_two_mul_sqrt_sub_one hpos
  unfold resonatorWeight eulerEnvelope
  rw [div_pow, div_lt_div_iff₀ (by positivity) (by linarith)]
  set s := Real.sqrt r
  set L := Real.log r
  have h1 : L * (L * (s - 1)) ≤ L * (2 * (s - 1) * (s - 1)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hLs (by linarith)) hL.le
  nlinarith [mul_pos hL (by linarith : (0 : ℝ) < 2 * s - 1)]

/-- **The remainder is bounded by the envelope gap**:
`R(c) ≤ −(E_p + E_q − w_p² − w_q²) Σ c²`. -/
theorem resonatorRemainder_le {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (M N : ℕ)
    (c : ℕ × ℕ → ℝ) :
    resonatorRemainder p q M N c ≤
      -(eulerEnvelope p + eulerEnvelope q - resonatorWeight p ^ 2 - resonatorWeight q ^ 2) *
        boxEnergy M N c := by
  have hX := abs_crossLag_le M N c
  have hE := boxEnergy_nonneg M N c
  have hwp := resonatorWeight_nonneg (le_trans (by norm_num) hp)
  have hwq := resonatorWeight_nonneg (le_trans (by norm_num) hq)
  have hw : 2 * resonatorWeight p * resonatorWeight q ≤
      resonatorWeight p ^ 2 + resonatorWeight q ^ 2 := by
    nlinarith [sq_nonneg (resonatorWeight p - resonatorWeight q)]
  have hww : 0 ≤ 2 * resonatorWeight p * resonatorWeight q := by positivity
  have h1 : 2 * resonatorWeight p * resonatorWeight q * crossLag M N c ≤
      (resonatorWeight p ^ 2 + resonatorWeight q ^ 2) * boxEnergy M N c :=
    calc 2 * resonatorWeight p * resonatorWeight q * crossLag M N c
        ≤ 2 * resonatorWeight p * resonatorWeight q * |crossLag M N c| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) hww
      _ ≤ 2 * resonatorWeight p * resonatorWeight q * boxEnergy M N c :=
          mul_le_mul_of_nonneg_left hX hww
      _ ≤ (resonatorWeight p ^ 2 + resonatorWeight q ^ 2) * boxEnergy M N c :=
          mul_le_mul_of_nonneg_right hw hE
  unfold resonatorRemainder
  linarith

/-- **The adjunction remainder is negative definite on every resonator.** -/
theorem resonatorRemainder_neg {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (M N : ℕ)
    {c : ℕ × ℕ → ℝ} (hc : 0 < boxEnergy M N c) : resonatorRemainder p q M N c < 0 := by
  have h := resonatorRemainder_le hp hq M N c
  have hk : 0 < eulerEnvelope p + eulerEnvelope q - resonatorWeight p ^ 2 -
      resonatorWeight q ^ 2 := by
    linarith [resonatorWeight_sq_lt_eulerEnvelope hp, resonatorWeight_sq_lt_eulerEnvelope hq]
  nlinarith

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
