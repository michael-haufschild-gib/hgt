import GaloisForLFunctions.RHTower.Sieve.SelbergInversion

/-!
# The error term of a `Λ²` sieve

Two structural facts control `errSum (Λ² w)`.

First, the `Λ²` coefficients inherit a bound from the weights: `|Λ²_d| ≤ (∑_{e ∣ d} |w e|)²`, by
the triangle inequality on the defining double sum.

Second, they inherit the support: if `w` vanishes above `Y`, then `Λ²_d = 0` above `Y²`, because a
nonzero term needs `d = lcm d₁ d₂` with `w d₁ w d₂ ≠ 0`, whence `d ≤ d₁ d₂ ≤ Y²`.  This is what
makes the level of a Selberg sieve `D = Y²`, and it is the reason the error sum runs only over
`d ≤ D` rather than over all divisors of the sifting modulus.
-/

namespace RHTower.Sieve

open Finset Nat BoundingSieve

/-- **Triangle bound for the `Λ²` coefficients.** -/
theorem abs_lambdaSquared_le (w : ℕ → ℝ) (d : ℕ) :
    |lambdaSquared w d| ≤ (∑ e ∈ d.divisors, |w e|) ^ 2 := by
  classical
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hinner : ∀ d1 ∈ d.divisors,
      |∑ d2 ∈ d.divisors, if d = Nat.lcm d1 d2 then w d1 * w d2 else 0|
        ≤ |w d1| * ∑ e ∈ d.divisors, |w e| := by
    intro d1 _
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro d2 _
    by_cases h : d = Nat.lcm d1 d2
    · rw [if_pos h, abs_mul]
    · rw [if_neg h, abs_zero]
      positivity
  refine le_trans (Finset.sum_le_sum hinner) ?_
  rw [← Finset.sum_mul, sq]

/-- **Support inheritance.**  A `Λ²` sieve built from weights supported below `Y` has level
`Y²`. -/
theorem lambdaSquared_eq_zero_of_lt {w : ℕ → ℝ} {Y : ℕ} (hw : ∀ n, Y < n → w n = 0)
    {d : ℕ} (hd : Y * Y < d) : lambdaSquared w d = 0 := by
  classical
  have hd0 : d ≠ 0 := by omega
  refine Finset.sum_eq_zero ?_
  intro d1 hd1
  refine Finset.sum_eq_zero ?_
  intro d2 hd2
  by_cases h : d = Nat.lcm d1 d2
  · rw [if_pos h]
    by_cases h1 : Y < d1
    · rw [hw d1 h1, zero_mul]
    · by_cases h2 : Y < d2
      · rw [hw d2 h2, mul_zero]
      · exfalso
        have hd1pos : 0 < d1 := Nat.pos_of_mem_divisors hd1
        have hd2pos : 0 < d2 := Nat.pos_of_mem_divisors hd2
        have hlcm : Nat.lcm d1 d2 ≤ d1 * d2 :=
          Nat.le_of_dvd (Nat.mul_pos hd1pos hd2pos)
            (Nat.lcm_dvd (Dvd.intro d2 rfl) (Dvd.intro_left d1 rfl))
        have hprod : d1 * d2 ≤ Y * Y :=
          Nat.mul_le_mul (by omega) (by omega)
        omega
  · rw [if_neg h]

/-- **Error bound.**  A uniform bound on the weights and on the remainders bounds the whole error
sum by the number of divisors involved. -/
theorem errSum_lambdaSquared_le (s : BoundingSieve) (w : ℕ → ℝ) {B : ℝ}
    (hB : ∀ d ∈ s.prodPrimes.divisors, |s.rem d| ≤ B) :
    s.errSum (lambdaSquared w)
      ≤ B * ∑ d ∈ s.prodPrimes.divisors, (∑ e ∈ d.divisors, |w e|) ^ 2 := by
  classical
  rw [errSum, Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro d hd
  have h1 : |lambdaSquared w d| ≤ (∑ e ∈ d.divisors, |w e|) ^ 2 := abs_lambdaSquared_le w d
  have h2 : |s.rem d| ≤ B := hB d hd
  have hnn : (0 : ℝ) ≤ (∑ e ∈ d.divisors, |w e|) ^ 2 := sq_nonneg _
  have habs : (0 : ℝ) ≤ |s.rem d| := abs_nonneg _
  calc |lambdaSquared w d| * |s.rem d|
      ≤ (∑ e ∈ d.divisors, |w e|) ^ 2 * |s.rem d| :=
        mul_le_mul_of_nonneg_right h1 habs
    _ ≤ (∑ e ∈ d.divisors, |w e|) ^ 2 * B := mul_le_mul_of_nonneg_left h2 hnn
    _ = B * (∑ e ∈ d.divisors, |w e|) ^ 2 := by ring

/-- With unit weights the divisor bound is the square of the divisor count. -/
theorem abs_lambdaSquared_le_card_sq {w : ℕ → ℝ} (hw : ∀ n, |w n| ≤ 1) (d : ℕ) :
    |lambdaSquared w d| ≤ ((d.divisors.card : ℝ)) ^ 2 := by
  refine le_trans (abs_lambdaSquared_le w d) ?_
  have hle : ∑ e ∈ d.divisors, |w e| ≤ (d.divisors.card : ℝ) := by
    calc ∑ e ∈ d.divisors, |w e| ≤ ∑ _e ∈ d.divisors, (1 : ℝ) :=
          Finset.sum_le_sum fun e _ => hw e
      _ = (d.divisors.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hnn : (0 : ℝ) ≤ ∑ e ∈ d.divisors, |w e| :=
    Finset.sum_nonneg fun e _ => abs_nonneg _
  exact pow_le_pow_left₀ hnn hle 2

open scoped ArithmeticFunction.Moebius

/-- The Selberg mass truncated at level `Y`. -/
noncomputable def selbergMassLE (s : BoundingSieve) (Y : ℕ) : ℝ :=
  ∑ l ∈ {l ∈ s.prodPrimes.divisors | l ≤ Y}, s.selbergTerms l

theorem selbergMassLE_pos (s : BoundingSieve) {Y : ℕ} (hY : 1 ≤ Y) :
    0 < selbergMassLE s Y := by
  classical
  refine Finset.sum_pos (fun l hl => selbergTerms_pos ?_) ⟨1, ?_⟩
  · exact Nat.dvd_of_mem_divisors (Finset.mem_filter.1 hl).1
  · exact Finset.mem_filter.2
      ⟨Nat.mem_divisors.2 ⟨one_dvd _, s.prodPrimes_squarefree.ne_zero⟩, hY⟩

/-- The truncated diagonal profile. -/
noncomputable def selbergTruncY (s : BoundingSieve) (Y l : ℕ) : ℝ :=
  if l ≤ Y then (μ l : ℝ) * s.selbergTerms l / selbergMassLE s Y else 0

/-- The truncated Selberg weight. -/
noncomputable def selbergTruncWeight (s : BoundingSieve) (Y : ℕ) : ℕ → ℝ :=
  selbergW s (selbergTruncY s Y)

/-- **Support of the truncated weight.**  It vanishes above the truncation level. -/
theorem selbergTruncWeight_eq_zero_of_lt (s : BoundingSieve) {Y d : ℕ} (hd : Y < d) :
    selbergTruncWeight s Y d = 0 := by
  classical
  unfold selbergTruncWeight selbergW
  have hzero : ∀ l ∈ s.prodPrimes.divisors,
      (if d ∣ l then (μ (l / d) : ℝ) * selbergTruncY s Y l else 0) = 0 := by
    intro l hl
    by_cases hdl : d ∣ l
    · rw [if_pos hdl]
      have hl0 : l ≠ 0 := Nat.pos_of_mem_divisors hl |>.ne'
      have hdle : d ≤ l := Nat.le_of_dvd (Nat.pos_of_ne_zero hl0) hdl
      have : ¬ l ≤ Y := by omega
      rw [selbergTruncY, if_neg this, mul_zero]
    · rw [if_neg hdl]
  rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero, zero_div]

/-- The truncated weight is admissible. -/
theorem selbergTruncWeight_one (s : BoundingSieve) {Y : ℕ} (hY : 1 ≤ Y) :
    selbergTruncWeight s Y 1 = 1 := by
  classical
  have hS := selbergMassLE_pos s hY
  unfold selbergTruncWeight selbergW
  rw [s.nu_mult.map_one, div_one]
  have hterm : ∀ l ∈ s.prodPrimes.divisors,
      (if (1 : ℕ) ∣ l then (μ (l / 1) : ℝ) * selbergTruncY s Y l else 0)
        = if l ≤ Y then s.selbergTerms l / selbergMassLE s Y else 0 := by
    intro l hl
    rw [if_pos (one_dvd l), Nat.div_one, selbergTruncY]
    by_cases hle : l ≤ Y
    · rw [if_pos hle, if_pos hle]
      have hmusq := moebius_sq_eq_one_of_dvd (s := s) (Nat.dvd_of_mem_divisors hl)
      have hrw : (μ l : ℝ) * ((μ l : ℝ) * s.selbergTerms l / selbergMassLE s Y)
          = (μ l : ℝ) ^ 2 * s.selbergTerms l / selbergMassLE s Y := by ring
      rw [hrw, hmusq, one_mul]
    · rw [if_neg hle, if_neg hle, mul_zero]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul, ← selbergMassLE]
  exact mul_inv_cancel₀ hS.ne'

/-- **The truncated Selberg optimum.** -/
theorem mainSum_selbergTruncWeight (s : BoundingSieve) {Y : ℕ} (hY : 1 ≤ Y) :
    s.mainSum (lambdaSquared (selbergTruncWeight s Y)) = (selbergMassLE s Y)⁻¹ := by
  classical
  have hS := selbergMassLE_pos s hY
  rw [mainSum_lambdaSquared_eq_sum_selbergY]
  have hterm : ∀ l ∈ s.prodPrimes.divisors,
      (s.selbergTerms l)⁻¹ * (selbergY s (selbergTruncWeight s Y) l) ^ 2
        = if l ≤ Y then s.selbergTerms l / (selbergMassLE s Y) ^ 2 else 0 := by
    intro l hl
    have hdvd := Nat.dvd_of_mem_divisors hl
    have hy : selbergY s (selbergTruncWeight s Y) l = selbergTruncY s Y l :=
      selbergY_selbergW s (selbergTruncY s Y) hdvd
    have hg : 0 < s.selbergTerms l := selbergTerms_pos hdvd
    rw [hy, selbergTruncY]
    by_cases hle : l ≤ Y
    · rw [if_pos hle, if_pos hle]
      have hmusq := moebius_sq_eq_one_of_dvd (s := s) hdvd
      rw [div_pow, mul_pow, hmusq, one_mul]
      field_simp
    · rw [if_neg hle, if_neg hle]
      simp
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul, ← selbergMassLE, sq, mul_inv, ← mul_assoc,
    mul_inv_cancel₀ hS.ne', one_mul]

/-- **Truncated Selberg sieve.**  The level is `Y²`: the `Λ²` coefficients vanish above it. -/
theorem siftedSum_le_selbergTrunc (s : BoundingSieve) {Y : ℕ} (hY : 1 ≤ Y) :
    s.siftedSum ≤ s.totalMass / selbergMassLE s Y
      + s.errSum (lambdaSquared (selbergTruncWeight s Y)) := by
  have h := siftedSum_le_mainSum_errSum_of_upperMoebius (s := s)
    (lambdaSquared (selbergTruncWeight s Y))
    (upperMoebius_lambdaSquared _ (selbergTruncWeight_one s hY))
  rw [mainSum_selbergTruncWeight s hY] at h
  rwa [div_eq_mul_inv]

/-- The truncated `Λ²` coefficients are supported at level `Y²`. -/
theorem lambdaSquared_selbergTruncWeight_eq_zero (s : BoundingSieve) {Y d : ℕ}
    (hd : Y * Y < d) : lambdaSquared (selbergTruncWeight s Y) d = 0 :=
  lambdaSquared_eq_zero_of_lt (fun _n hn => selbergTruncWeight_eq_zero_of_lt s hn) hd

end RHTower.Sieve
