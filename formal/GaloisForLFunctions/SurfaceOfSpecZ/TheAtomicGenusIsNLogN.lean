import GaloisForLFunctions.SurfaceOfSpecZ.ThePointCountOfSpecZ

/-!
# The atomic Frobenius graphs need genus of order `N log N` at degree `N`

`ThePointCountOfSpecZ` tests the atomic Frobenius graphs `Γ_n` of `Spec ℤ` on the planes `⟨Γ_1, Γ_n⟩`:
a diagonal of genus `g` passes only if `g ≳ √n`. This file tests them on a dyadic block of degrees
`[N, 2N)`. Give `Γ_n` the self-defect `δ(Γ_n, Γ_n) = 2gn`; off the diagonal the defect is
`δ(Γ_m, Γ_n) = m + n − Γ_m·Γ_n`, which is `√(mn)` times Weil's distribution at `log m − log n`
(`genusDefect`). Then

  `N(log N − 17)/16 ≤ g`   whenever the defect is `≥ 0` on `Σ_{N ≤ n < 2N} Γ_n`
  (`genus_ge_of_genusDefect_nonneg`),

  the defect is `≥ 0` on every `Σ y_n Γ_n` over the block once `g ≥ N(4 log N + 6)`
  (`genusDefect_nonneg_of_le`).

So the genus needed at degree `N` is of exact order `N log N`.

**Mechanism.** Inside a dyadic block no degree divides another, so no torsion orbits meet and the
intersection is the cusp with its jets (`frobeniusIntersection_block`):
`Γ_m·Γ_n = ab²/((b − a)(b + a))` for `a = min, b = max`, which lies between `N²/(4|m − n|)` and
`4N²/|m − n|` (`frobeniusIntersection_block_bounds`). The off-diagonal defect is thus a negative
harmonic matrix: the jets of the trivial zeros behave like `1/|log m − log n|` at the spacing `1/N`
of the atoms, and their harmonic sum over the block is `N log N` per row (`sum_block_ge`,
`row_inv_le`). The two-term test of `ThePointCountOfSpecZ` sees the size `n` of the trace; the block
test sees the logarithmic divergence of the archimedean kernel at the diagonal.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticEffectivityTheory

/-- The defect of `Σ_{n ∈ S} y_n Γ_n` with a diagonal of genus `g`. -/
def genusDefect (g : ℝ) (S : Finset ℕ) (y : ℕ → ℝ) : ℝ :=
  ∑ n ∈ S, 2 * g * n * y n ^ 2 +
    ∑ m ∈ S, ∑ n ∈ S, if m = n then 0 else y m * y n * (((m : ℝ) + n) - frobeniusIntersection m n)

/-! ### The jets in a dyadic block -/

theorem jet_eq {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    a / (1 - (a / b) ^ 2) = a * b ^ 2 / ((b - a) * (b + a)) := by
  have hb : 0 < b := ha.trans hab
  have h : (1 : ℝ) - (a / b) ^ 2 = (b - a) * (b + a) / b ^ 2 := by field_simp; ring
  rw [h, div_div_eq_mul_div]

/-- For `N ≤ a < b < 2N`: `N²/(4(b − a)) ≤ a/(1 − (a/b)²) ≤ 4N²/(b − a)`. -/
theorem jet_bounds {N a b : ℝ} (hN : 0 < N) (ha : N ≤ a) (hab : a < b) (hb : b < 2 * N) :
    N ^ 2 / (4 * (b - a)) ≤ a / (1 - (a / b) ^ 2) ∧ a / (1 - (a / b) ^ 2) ≤ 4 * N ^ 2 / (b - a) := by
  have ha0 : 0 < a := hN.trans_le ha
  have hb0 : 0 < b := ha0.trans hab
  have hd : 0 < b - a := by linarith
  have hs : 0 < b + a := by linarith
  rw [jet_eq ha0 hab]
  constructor
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : N ^ 3 ≤ a * b ^ 2 :=
      calc N ^ 3 = N * N ^ 2 := by ring
        _ ≤ a * b ^ 2 := mul_le_mul ha (pow_le_pow_left₀ hN.le (by linarith) 2) (by positivity)
            ha0.le
    have h1 : N ^ 2 * (b + a) ≤ 4 * (a * b ^ 2) :=
      calc N ^ 2 * (b + a) ≤ N ^ 2 * (4 * N) :=
            mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg N)
        _ = 4 * N ^ 3 := by ring
        _ ≤ 4 * (a * b ^ 2) := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h1 hd.le]
  · rw [div_le_div_iff₀ (by positivity) hd]
    have hab' : a * b ≤ 4 * N ^ 2 := by nlinarith
    have h1 : a * b ^ 2 ≤ 4 * N ^ 2 * (b + a) :=
      calc a * b ^ 2 = (a * b) * b := by ring
        _ ≤ 4 * N ^ 2 * b := mul_le_mul_of_nonneg_right hab' hb0.le
        _ ≤ 4 * N ^ 2 * (b + a) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h1 hd.le]

/-- **No torsion inside a dyadic block.** For distinct degrees in `[N, 2N)` neither divides the
other, and `Γ_m·Γ_n` is the cusp with its jets. -/
theorem frobeniusIntersection_block {N m n : ℕ} (hm : m ∈ Ico N (2 * N))
    (hn : n ∈ Ico N (2 * N)) (hmn : m ≠ n) :
    frobeniusIntersection m n = min (m : ℝ) n / (1 - (min (m : ℝ) n / max (m : ℝ) n) ^ 2) := by
  rw [mem_Ico] at hm hn
  have hm0 : 0 < m := by omega
  have hn0 : 0 < n := by omega
  have hndvd : ∀ a b : ℕ, N ≤ a → a < b → b < 2 * N → ¬ a ∣ b := by
    rintro a b ha hab hb ⟨t, rfl⟩
    have ht : 2 ≤ t := by
      by_contra h
      push Not at h
      interval_cases t <;> omega
    have : a * 2 ≤ a * t := Nat.mul_le_mul_left a ht
    omega
  have h1 : ¬ n ∣ m := by
    rcases lt_or_gt_of_ne hmn with h | h
    · exact fun hd => absurd (Nat.le_of_dvd hm0 hd) (by omega)
    · exact hndvd n m hn.1 h hm.2
  have h2 : ¬ m ∣ n := by
    rcases lt_or_gt_of_ne hmn with h | h
    · exact hndvd m n hm.1 h hn.2
    · exact fun hd => absurd (Nat.le_of_dvd hn0 hd) (by omega)
  rw [frobeniusIntersection_eq hm0 hn0 hmn, orbitIntersection_eq hm0 hn0 hmn, if_neg h1, if_neg h2,
    mul_zero, add_zero]

theorem max_sub_min_eq_abs_sub (a b : ℝ) : max a b - min a b = |a - b| := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, min_eq_left h, abs_of_nonpos (by linarith)]; ring
  · rw [max_eq_left h, min_eq_right h, abs_of_nonneg (by linarith)]

/-- **The jets dominate the block.** `N²/(4|m − n|) ≤ Γ_m·Γ_n ≤ 4N²/|m − n|`. -/
theorem frobeniusIntersection_block_bounds {N m n : ℕ} (hm : m ∈ Ico N (2 * N))
    (hn : n ∈ Ico N (2 * N)) (hmn : m ≠ n) :
    (N : ℝ) ^ 2 / (4 * |(m : ℝ) - n|) ≤ frobeniusIntersection m n ∧
      frobeniusIntersection m n ≤ 4 * (N : ℝ) ^ 2 / |(m : ℝ) - n| := by
  rw [frobeniusIntersection_block hm hn hmn, ← max_sub_min_eq_abs_sub]
  rw [mem_Ico] at hm hn
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmn' : (m : ℝ) ≠ n := by exact_mod_cast hmn
  refine jet_bounds hN ?_ (min_lt_max.mpr hmn') ?_
  · exact le_min (by exact_mod_cast hm.1) (by exact_mod_cast hn.1)
  · exact max_lt (by exact_mod_cast hm.2) (by exact_mod_cast hn.2)

/-! ### Harmonic sums -/

/-- `H_j = Σ_{k < j} 1/(k + 1)`. -/
def invSum (j : ℕ) : ℝ := ∑ k ∈ range j, 1 / ((k : ℝ) + 1)

theorem harmonic_cast_eq (j : ℕ) : ((harmonic j : ℚ) : ℝ) = invSum j := by
  rw [harmonic, invSum, Rat.cast_sum]
  refine sum_congr rfl fun i _ => ?_
  push_cast
  ring

theorem log_le_invSum (j : ℕ) : Real.log ((j : ℝ) + 1) ≤ invSum j := by
  have h := log_add_one_le_harmonic j
  rw [harmonic_cast_eq] at h
  exact_mod_cast h

theorem invSum_le (j : ℕ) : invSum j ≤ 1 + Real.log j := by
  have h := harmonic_le_one_add_log j
  rwa [harmonic_cast_eq] at h

theorem invSum_mono {j j' : ℕ} (h : j ≤ j') : invSum j ≤ invSum j' :=
  sum_le_sum_of_subset_of_nonneg (range_mono h) fun _ _ _ => by positivity

/-- `Σ_{m < n < M} 1/(n − m) = H_{M − m − 1}`. -/
theorem sum_Ico_inv_sub (m M : ℕ) :
    ∑ n ∈ Ico (m + 1) M, 1 / ((n : ℝ) - m) = invSum (M - (m + 1)) := by
  rw [sum_Ico_eq_sum_range, invSum]
  refine sum_congr rfl fun k _ => ?_
  congr 1
  push_cast
  ring

/-- `Σ_{N ≤ n < m} 1/(m − n) = H_{m − N}`. -/
theorem sum_Ico_inv_sub' {N m : ℕ} (h : N ≤ m) :
    ∑ n ∈ Ico N m, 1 / ((m : ℝ) - n) = invSum (m - N) := by
  rw [sum_Ico_eq_sum_range, invSum, ← sum_range_reflect (fun j => 1 / ((j : ℝ) + 1)) (m - N)]
  refine sum_congr rfl fun k hk => ?_
  rw [mem_range] at hk
  have e : ((m - N - 1 - k : ℕ) : ℝ) = (m : ℝ) - N - 1 - k := by
    rw [show m - N - 1 - k = m - (N + 1 + k) by omega, Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [e]
  congr 1
  push_cast
  ring

/-- `log N! ≥ N log N − N`. -/
theorem log_factorial_ge (N : ℕ) : (N : ℝ) * Real.log N - N ≤ Real.log (N.factorial) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hf : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  have h := Real.pow_div_factorial_le_exp (N : ℝ) hN'.le N
  have h2 := Real.log_le_log (by positivity) h
  rw [Real.log_exp, Real.log_div (by positivity) hf.ne', Real.log_pow] at h2
  linarith

theorem log_factorial_eq (N : ℕ) :
    Real.log (N.factorial) = ∑ j ∈ range N, Real.log ((j : ℝ) + 1) := by
  rw [← prod_range_add_one_eq_factorial, Nat.cast_prod, Real.log_prod]
  · push_cast
    rfl
  · intro j _
    positivity

/-- **The harmonic mass of a dyadic block.** `Σ_{N ≤ m < n < 2N} 1/(n − m) ≥ N log N − N`. -/
theorem sum_block_ge (N : ℕ) :
    (N : ℝ) * Real.log N - N ≤
      ∑ m ∈ Ico N (2 * N), ∑ n ∈ Ico (m + 1) (2 * N), 1 / ((n : ℝ) - m) := by
  have hrow : ∀ m ∈ Ico N (2 * N),
      ∑ n ∈ Ico (m + 1) (2 * N), 1 / ((n : ℝ) - m) = invSum (2 * N - (m + 1)) :=
    fun m _ => sum_Ico_inv_sub m (2 * N)
  rw [sum_congr rfl hrow, sum_Ico_eq_sum_range, show 2 * N - N = N by omega]
  have hre : ∀ j ∈ range N, invSum (2 * N - (N + j + 1)) = invSum (N - 1 - j) :=
    fun j _ => by congr 1; omega
  rw [sum_congr rfl hre, sum_range_reflect (fun j => invSum j) N]
  calc (N : ℝ) * Real.log N - N ≤ Real.log (N.factorial) := log_factorial_ge N
    _ = ∑ j ∈ range N, Real.log ((j : ℝ) + 1) := log_factorial_eq N
    _ ≤ ∑ j ∈ range N, invSum j := sum_le_sum fun j _ => log_le_invSum j

/-- **A row of a dyadic block has harmonic mass at most `2(1 + log N)`.** -/
theorem row_inv_le {N m : ℕ} (hm : m ∈ Ico N (2 * N)) :
    ∑ n ∈ Ico N (2 * N), (if m = n then 0 else 1 / |(m : ℝ) - n|) ≤ 2 * (1 + Real.log N) := by
  rw [mem_Ico] at hm
  have hsplit : ∀ n ∈ Ico N (2 * N), (if m = n then (0 : ℝ) else 1 / |(m : ℝ) - n|) =
      (if m < n then 1 / ((n : ℝ) - m) else 0) + (if n < m then 1 / ((m : ℝ) - n) else 0) := by
    intro n _
    rcases lt_trichotomy m n with h | rfl | h
    · have h' : (m : ℝ) < n := by exact_mod_cast h
      rw [if_neg h.ne, if_pos h, if_neg (not_lt.mpr h.le), add_zero, abs_of_neg (by linarith),
        neg_sub]
    · simp
    · have h' : (n : ℝ) < m := by exact_mod_cast h
      rw [if_neg h.ne', if_neg (not_lt.mpr h.le), if_pos h, zero_add, abs_of_pos (by linarith)]
  rw [sum_congr rfl hsplit, sum_add_distrib, ← sum_filter, ← sum_filter]
  have hf1 : (Ico N (2 * N)).filter (fun n => m < n) = Ico (m + 1) (2 * N) := by
    ext n; simp only [mem_filter, mem_Ico]; omega
  have hf2 : (Ico N (2 * N)).filter (fun n => n < m) = Ico N m := by
    ext n; simp only [mem_filter, mem_Ico]; omega
  rw [hf1, hf2, sum_Ico_inv_sub, sum_Ico_inv_sub' hm.1]
  have h1 : invSum (2 * N - (m + 1)) ≤ 1 + Real.log N :=
    (invSum_mono (by omega)).trans (invSum_le N)
  have h2 : invSum (m - N) ≤ 1 + Real.log N := (invSum_mono (by omega)).trans (invSum_le N)
  linarith

/-! ### The genus of the block -/

/-- **The atomic graphs need genus `≳ N log N`.** If the defect of `Σ_{N ≤ n < 2N} Γ_n` with a diagonal
of genus `g ≥ 0` is nonnegative, then `g ≥ N(log N − 17)/16`. -/
theorem genus_ge_of_genusDefect_nonneg {g : ℝ} (hg : 0 ≤ g) {N : ℕ}
    (h : 0 ≤ genusDefect g (Ico N (2 * N)) 1) : (N : ℝ) * (Real.log N - 17) / 16 ≤ g := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simpa using hg
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hcard : ((Ico N (2 * N)).card : ℝ) = N := by
    rw [Nat.card_Ico, show 2 * N - N = N by omega]
  -- the diagonal is at most `4gN²`
  have hdiag : ∑ n ∈ Ico N (2 * N), 2 * g * n * (1 : ℕ → ℝ) n ^ 2 ≤ 4 * g * N ^ 2 := by
    calc ∑ n ∈ Ico N (2 * N), 2 * g * n * (1 : ℕ → ℝ) n ^ 2
        ≤ ∑ n ∈ Ico N (2 * N), 2 * g * (2 * N) := by
          refine sum_le_sum fun n hn => ?_
          rw [mem_Ico] at hn
          have : (n : ℝ) ≤ 2 * N := by exact_mod_cast hn.2.le
          simp only [Pi.one_apply, one_pow, mul_one]
          nlinarith
      _ = 4 * g * N ^ 2 := by rw [sum_const, nsmul_eq_mul, hcard]; ring
  -- each row of the off-diagonal part is at most `4N² − (N²/4)·(harmonic mass to the right)`
  have hrow : ∀ m ∈ Ico N (2 * N), (∑ n ∈ Ico N (2 * N), if m = n then (0 : ℝ) else
      (1 : ℕ → ℝ) m * (1 : ℕ → ℝ) n * (((m : ℝ) + n) - frobeniusIntersection m n)) ≤
      4 * N * N - (N : ℝ) ^ 2 / 4 * ∑ n ∈ Ico (m + 1) (2 * N), 1 / ((n : ℝ) - m) := by
    intro m hm
    have hpt : ∀ n ∈ Ico N (2 * N), (if m = n then (0 : ℝ) else
        (1 : ℕ → ℝ) m * (1 : ℕ → ℝ) n * (((m : ℝ) + n) - frobeniusIntersection m n)) ≤
        4 * N - (if m < n then (N : ℝ) ^ 2 / 4 * (1 / ((n : ℝ) - m)) else 0) := by
      intro n hn
      have hm' := mem_Ico.mp hm
      have hn' := mem_Ico.mp hn
      have hsum : (m : ℝ) + n ≤ 4 * N := by
        have : m + n ≤ 4 * N := by omega
        exact_mod_cast this
      by_cases hmn : m = n
      · subst hmn
        rw [if_pos rfl, if_neg (lt_irrefl m)]
        linarith
      rw [if_neg hmn]
      simp only [Pi.one_apply, one_mul]
      obtain ⟨hlo, -⟩ := frobeniusIntersection_block_bounds hm hn hmn
      by_cases hlt : m < n
      · rw [if_pos hlt]
        have hlt' : (m : ℝ) < n := by exact_mod_cast hlt
        rw [abs_of_neg (by linarith), neg_sub] at hlo
        have : (N : ℝ) ^ 2 / 4 * (1 / ((n : ℝ) - m)) = (N : ℝ) ^ 2 / (4 * ((n : ℝ) - m)) := by
          field_simp
        linarith
      · rw [if_neg hlt]
        have h0 : 0 ≤ (N : ℝ) ^ 2 / (4 * |(m : ℝ) - n|) := by positivity
        linarith
    calc _ ≤ ∑ n ∈ Ico N (2 * N),
          (4 * (N : ℝ) - (if m < n then (N : ℝ) ^ 2 / 4 * (1 / ((n : ℝ) - m)) else 0)) :=
          sum_le_sum hpt
      _ = 4 * N * N - (N : ℝ) ^ 2 / 4 * ∑ n ∈ Ico (m + 1) (2 * N), 1 / ((n : ℝ) - m) := by
          rw [sum_sub_distrib, sum_const, nsmul_eq_mul, hcard, ← sum_filter, mul_sum]
          have hf : (Ico N (2 * N)).filter (fun n => m < n) = Ico (m + 1) (2 * N) := by
            have hm' := mem_Ico.mp hm
            ext n; simp only [mem_filter, mem_Ico]; omega
          rw [hf]
          ring
  have hoff : (∑ m ∈ Ico N (2 * N), ∑ n ∈ Ico N (2 * N), if m = n then (0 : ℝ) else
      (1 : ℕ → ℝ) m * (1 : ℕ → ℝ) n * (((m : ℝ) + n) - frobeniusIntersection m n)) ≤
      4 * (N : ℝ) ^ 3 - (N : ℝ) ^ 2 / 4 * ((N : ℝ) * Real.log N - N) := by
    calc _ ≤ ∑ m ∈ Ico N (2 * N),
          (4 * N * N - (N : ℝ) ^ 2 / 4 * ∑ n ∈ Ico (m + 1) (2 * N), 1 / ((n : ℝ) - m)) :=
          sum_le_sum hrow
      _ = 4 * (N : ℝ) ^ 3 - (N : ℝ) ^ 2 / 4 *
            ∑ m ∈ Ico N (2 * N), ∑ n ∈ Ico (m + 1) (2 * N), 1 / ((n : ℝ) - m) := by
          rw [sum_sub_distrib, sum_const, nsmul_eq_mul, hcard, ← mul_sum]
          ring
      _ ≤ 4 * (N : ℝ) ^ 3 - (N : ℝ) ^ 2 / 4 * ((N : ℝ) * Real.log N - N) := by
          have := sum_block_ge N
          have h4 : (0 : ℝ) ≤ (N : ℝ) ^ 2 / 4 := by positivity
          nlinarith [mul_le_mul_of_nonneg_left this h4]
  unfold genusDefect at h
  have hX : 0 ≤ (N : ℝ) ^ 2 * (16 * g - N * Real.log N + 17 * N) := by nlinarith
  have := (mul_nonneg_iff_of_pos_left (by positivity : (0 : ℝ) < (N : ℝ) ^ 2)).mp hX
  linarith

/-- The pair weight `4N + 4N²/|m − n|`, which bounds `|δ(Γ_m, Γ_n)|` in the block. -/
def pairWeight (N m n : ℕ) : ℝ := 4 * N + 4 * (N : ℝ) ^ 2 / |(m : ℝ) - n|

theorem abs_defect_le_pairWeight {N m n : ℕ} (hm : m ∈ Ico N (2 * N))
    (hn : n ∈ Ico N (2 * N)) (hmn : m ≠ n) :
    |((m : ℝ) + n) - frobeniusIntersection m n| ≤ pairWeight N m n := by
  obtain ⟨hlo, hhi⟩ := frobeniusIntersection_block_bounds hm hn hmn
  have hm' := mem_Ico.mp hm
  have hn' := mem_Ico.mp hn
  have hsum : (m : ℝ) + n ≤ 4 * N := by
    have : m + n ≤ 4 * N := by omega
    exact_mod_cast this
  have h0 : 0 ≤ (N : ℝ) ^ 2 / (4 * |(m : ℝ) - n|) := by positivity
  have hmn0 : (0 : ℝ) ≤ (m : ℝ) + n := by positivity
  unfold pairWeight
  rw [abs_le]
  constructor <;> linarith

/-- Row sums of the pair weight: `Σ_{n ≠ m} (4N + 4N²/|m − n|) ≤ 4N² + 8N²(1 + log N)`. -/
theorem row_pairWeight_le {N m : ℕ} (hm : m ∈ Ico N (2 * N)) :
    ∑ n ∈ Ico N (2 * N), (if m = n then 0 else pairWeight N m n) ≤
      4 * (N : ℝ) ^ 2 + 8 * (N : ℝ) ^ 2 * (1 + Real.log N) := by
  have hcard : ((Ico N (2 * N)).card : ℝ) = N := by
    rw [Nat.card_Ico, show 2 * N - N = N by omega]
  have hpt : ∀ n ∈ Ico N (2 * N), (if m = n then (0 : ℝ) else pairWeight N m n) ≤
      4 * N + 4 * (N : ℝ) ^ 2 * (if m = n then 0 else 1 / |(m : ℝ) - n|) := by
    intro n _
    by_cases hmn : m = n
    · rw [if_pos hmn, if_pos hmn]; positivity
    · rw [if_neg hmn, if_neg hmn, pairWeight]; ring_nf; exact le_rfl
  calc _ ≤ ∑ n ∈ Ico N (2 * N),
        (4 * (N : ℝ) + 4 * (N : ℝ) ^ 2 * (if m = n then 0 else 1 / |(m : ℝ) - n|)) :=
        sum_le_sum hpt
    _ = 4 * (N : ℝ) ^ 2 + 4 * (N : ℝ) ^ 2 *
          ∑ n ∈ Ico N (2 * N), (if m = n then 0 else 1 / |(m : ℝ) - n|) := by
        rw [sum_add_distrib, sum_const, nsmul_eq_mul, hcard, ← mul_sum]; ring
    _ ≤ 4 * (N : ℝ) ^ 2 + 8 * (N : ℝ) ^ 2 * (1 + Real.log N) := by
        have := row_inv_le hm
        nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 4 * (N : ℝ) ^ 2)]

/-- **Genus `N(4 log N + 6)` suffices.** With that diagonal the defect is nonnegative on every
`Σ y_n Γ_n` over the block `[N, 2N)`. -/
theorem genusDefect_nonneg_of_le {g : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hg : (N : ℝ) * (4 * Real.log N + 6) ≤ g) (y : ℕ → ℝ) :
    0 ≤ genusDefect g (Ico N (2 * N)) y := by
  set B := Ico N (2 * N) with hB
  set ρ : ℝ := 4 * (N : ℝ) ^ 2 + 8 * (N : ℝ) ^ 2 * (1 + Real.log N) with hρ
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN'
  have hg0 : 0 ≤ g := by nlinarith
  -- each off-diagonal term is at least `−½(y_m² + y_n²)·w(m, n)`
  have hpt : ∀ m ∈ B, ∀ n ∈ B,
      (if m = n then (0 : ℝ) else -(y m ^ 2 / 2 * pairWeight N m n + y n ^ 2 / 2 * pairWeight N m n))
        ≤ if m = n then 0 else y m * y n * (((m : ℝ) + n) - frobeniusIntersection m n) := by
    intro m hm n hn
    by_cases hmn : m = n
    · rw [if_pos hmn, if_pos hmn]
    rw [if_neg hmn, if_neg hmn]
    have hA := abs_defect_le_pairWeight hm hn hmn
    have hw : 0 ≤ pairWeight N m n := (abs_nonneg _).trans hA
    have h1 : -(|y m * y n| * pairWeight N m n) ≤
        y m * y n * (((m : ℝ) + n) - frobeniusIntersection m n) := by
      have := neg_abs_le (y m * y n * (((m : ℝ) + n) - frobeniusIntersection m n))
      rw [abs_mul (y m * y n)] at this
      nlinarith [mul_le_mul_of_nonneg_left hA (abs_nonneg (y m * y n))]
    have h2 : |y m * y n| ≤ y m ^ 2 / 2 + y n ^ 2 / 2 := by
      rw [abs_mul]
      nlinarith [sq_nonneg (|y m| - |y n|), sq_abs (y m), sq_abs (y n)]
    nlinarith [mul_le_mul_of_nonneg_right h2 hw]
  -- the two halves of the lower bound are row and column sums of `w`
  have hsplit : ∀ m n : ℕ,
      (if m = n then (0 : ℝ) else -(y m ^ 2 / 2 * pairWeight N m n + y n ^ 2 / 2 * pairWeight N m n))
        = -(y m ^ 2 / 2 * (if m = n then 0 else pairWeight N m n)) -
            y n ^ 2 / 2 * (if n = m then 0 else pairWeight N n m) := by
    intro m n
    by_cases hmn : m = n
    · subst hmn; simp
    · rw [if_neg hmn, if_neg hmn, if_neg (Ne.symm hmn), pairWeight, pairWeight, abs_sub_comm]
      ring
  have hrows : ∀ m ∈ B, y m ^ 2 / 2 * ∑ n ∈ B, (if m = n then 0 else pairWeight N m n) ≤
      y m ^ 2 / 2 * ρ := fun m hm =>
    mul_le_mul_of_nonneg_left (row_pairWeight_le hm) (by positivity)
  have hlower : -(ρ * ∑ n ∈ B, y n ^ 2) ≤
      ∑ m ∈ B, ∑ n ∈ B, if m = n then 0 else y m * y n * (((m : ℝ) + n) - frobeniusIntersection m n) := by
    refine le_trans ?_ (sum_le_sum fun m hm => sum_le_sum fun n hn => hpt m hm n hn)
    simp_rw [hsplit, sum_sub_distrib, sum_neg_distrib]
    rw [sum_comm (s := B) (t := B) (f := fun m n => y n ^ 2 / 2 * (if n = m then 0 else pairWeight N n m))]
    simp_rw [← mul_sum]
    have h1 := sum_le_sum hrows
    have h2 : ∑ n ∈ B, y n ^ 2 / 2 * ∑ m ∈ B, (if n = m then 0 else pairWeight N n m) ≤
        ∑ n ∈ B, y n ^ 2 / 2 * ρ := sum_le_sum hrows
    have h3 : ∑ m ∈ B, y m ^ 2 / 2 * ρ = ρ / 2 * ∑ n ∈ B, y n ^ 2 := by
      rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
    linarith
  have hdiag : 2 * g * N * ∑ n ∈ B, y n ^ 2 ≤ ∑ n ∈ B, 2 * g * n * y n ^ 2 := by
    rw [mul_sum]
    refine sum_le_sum fun n hn => ?_
    have : (N : ℝ) ≤ n := by exact_mod_cast (mem_Ico.mp hn).1
    have hy : 0 ≤ y n ^ 2 := sq_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * g) hy)]
  have hρle : ρ ≤ 2 * g * N := by
    rw [hρ]; nlinarith
  have hsq : 0 ≤ ∑ n ∈ B, y n ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  unfold genusDefect
  nlinarith [mul_le_mul_of_nonneg_right hρle hsq]

end GaloisForLFunctions.SurfaceOfSpecZ

#print axioms GaloisForLFunctions.SurfaceOfSpecZ.genus_ge_of_genusDefect_nonneg
#print axioms GaloisForLFunctions.SurfaceOfSpecZ.genusDefect_nonneg_of_le
