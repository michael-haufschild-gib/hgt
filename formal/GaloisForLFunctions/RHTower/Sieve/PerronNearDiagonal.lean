import GaloisForLFunctions.RHTower.Sieve.PerronTruncationError

/-!
# The near-diagonal Perron truncation error

The uniform logarithmic separation `|log((N + 1/2)/n)| ≥ 1/(2N+2)` is attained only at the two
integers flanking the cutoff, and paying it at every `n` costs a factor `N`.  The near-diagonal
estimate replaces it by the exact local behaviour of the logarithm,

`|x − y| ≤ (x + y)·|log(x/y)|`,

which is `log t ≥ 1 − 1/t` read on both sides of `1`.  Combined with the triangle inequality
`x + y ≤ |x − y| + 2y` and the exponent drop `(x/y)^σ·y ≤ x^σ` for `σ ≥ 1 ≤ y`, it gives the
pointwise Perron weight bound

`(x/y)^σ/|log(x/y)| ≤ x^σ·(1/y + 2/|x − y|)`.

At the half-integer cutoff `x = N + 1/2` the reciprocal distances are summable: on each side of the
cutoff they are `k − 1/2` with `k ≥ 1`, so `1/|x − n| ≤ 2/k`, and

`∑_{n ≤ M} 1/|x − n| ≤ 2(1 + log N) + 2(1 + log M)`.

The truncation error is therefore `B·x^σ·(5(1 + log M) + 4(1 + log N))/(πT)`, smaller than the
uniform bound by the whole factor `N`.  The height needed to make the error negligible drops from
`T ≳ N` to `T` polylogarithmic, which is what a distance input degrading in `log log T` can afford.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Set

/-- **The logarithm controls the relative distance.**  For positive `x` and `y`,
`|x − y| ≤ (x + y)·|log(x/y)|`; on each side of `1` this is `log t ≥ 1 − 1/t`. -/
theorem abs_sub_le_add_mul_abs_log_div {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    |x - y| ≤ (x + y) * |Real.log (x / y)| := by
  rcases le_total y x with h | h
  · have hlog : 0 ≤ Real.log (x / y) := Real.log_nonneg ((one_le_div hy).2 h)
    have hkey : 1 - y / x ≤ Real.log (x / y) := by
      have h1 := one_sub_inv_le_log (y := x / y) (by positivity)
      rwa [one_div_div] at h1
    have hxy : x * (1 - y / x) = x - y := by field_simp
    have hstep : x * (1 - y / x) ≤ x * Real.log (x / y) :=
      mul_le_mul_of_nonneg_left hkey hx.le
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ x - y), abs_of_nonneg hlog]
    nlinarith [mul_nonneg hy.le hlog]
  · have hlog : 0 ≤ Real.log (y / x) := Real.log_nonneg ((one_le_div hx).2 h)
    have hkey : 1 - x / y ≤ Real.log (y / x) := by
      have h1 := one_sub_inv_le_log (y := y / x) (by positivity)
      rwa [one_div_div] at h1
    have hneg : Real.log (x / y) = -Real.log (y / x) := by
      rw [← Real.log_inv, inv_div]
    have hxy : y * (1 - x / y) = y - x := by field_simp
    have hstep : y * (1 - x / y) ≤ y * Real.log (y / x) :=
      mul_le_mul_of_nonneg_left hkey hy.le
    rw [abs_sub_comm, abs_of_nonneg (by linarith : (0 : ℝ) ≤ y - x), hneg, abs_neg,
      abs_of_nonneg hlog]
    nlinarith [mul_nonneg hx.le hlog]

/-- **The near-diagonal Perron weight bound.**  For `σ ≥ 1` and `y ≥ 1` distinct from `x > 0`,
`(x/y)^σ/|log(x/y)| ≤ x^σ·(1/y + 2/|x − y|)`.  The logarithm is bounded below by the relative
distance `|x − y|/(x + y)`, the triangle inequality gives `x + y ≤ |x − y| + 2y`, and the exponent
drops to one against a single factor `y`. -/
theorem rpow_div_abs_log_le {x y σ : ℝ} (hx : 0 < x) (hy : 1 ≤ y) (hσ : 1 ≤ σ) (hne : x ≠ y) :
    (x / y) ^ σ / |Real.log (x / y)| ≤ x ^ σ * (1 / y + 2 / |x - y|) := by
  have hy0 : (0 : ℝ) < y := by linarith
  have hd0 : (0 : ℝ) < |x - y| := abs_pos.2 (sub_ne_zero.2 hne)
  have hA : (0 : ℝ) < (x / y) ^ σ := Real.rpow_pos_of_pos (by positivity) σ
  have hxσ : (0 : ℝ) < x ^ σ := Real.rpow_pos_of_pos hx σ
  have hL : |x - y| ≤ (x + y) * |Real.log (x / y)| := abs_sub_le_add_mul_abs_log_div hx hy0
  have hL0 : (0 : ℝ) < |Real.log (x / y)| := by
    rcases lt_or_ge 0 |Real.log (x / y)| with hpos | hzero
    · exact hpos
    · have h0 : |Real.log (x / y)| = 0 := le_antisymm hzero (abs_nonneg _)
      rw [h0, mul_zero] at hL
      linarith
  -- the exponent drops to one against a single factor `y`
  have hpow : (x / y) ^ σ * y ≤ x ^ σ := by
    have hid : (x / y) ^ σ * y ^ σ = x ^ σ := by
      rw [← Real.mul_rpow (by positivity) hy0.le, div_mul_cancel₀ _ (ne_of_gt hy0)]
    have hge : y ≤ y ^ σ := by
      have h1 : y ^ (1 : ℝ) ≤ y ^ σ := Real.rpow_le_rpow_of_exponent_le hy hσ
      rwa [Real.rpow_one] at h1
    have := mul_le_mul_of_nonneg_left hge hA.le
    linarith
  rw [div_le_iff₀ hL0]
  refine le_of_mul_le_mul_right ?_ (show (0 : ℝ) < y * |x - y| by positivity)
  have hu : (1 / y + 2 / |x - y|) * (y * |x - y|) = |x - y| + 2 * y := by
    field_simp
  have hrhs : x ^ σ * (1 / y + 2 / |x - y|) * |Real.log (x / y)| * (y * |x - y|)
      = x ^ σ * |Real.log (x / y)| * (|x - y| + 2 * y) := by
    rw [← hu]; ring
  rw [hrhs]
  have htri : x + y ≤ |x - y| + 2 * y := by
    have := le_abs_self (x - y)
    linarith
  have s1 : (x / y) ^ σ * y * |x - y| ≤ x ^ σ * |x - y| :=
    mul_le_mul_of_nonneg_right hpow hd0.le
  have s2 : x ^ σ * |x - y| ≤ x ^ σ * ((x + y) * |Real.log (x / y)|) :=
    mul_le_mul_of_nonneg_left hL hxσ.le
  have s3 : x ^ σ * ((x + y) * |Real.log (x / y)|)
      ≤ x ^ σ * ((|x - y| + 2 * y) * |Real.log (x / y)|) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right htri (abs_nonneg _)) hxσ.le
  linarith

/-- The half-integer cutoff misses every integer. -/
theorem natCast_ne_half (N n : ℕ) : (n : ℝ) ≠ (N : ℝ) + 1 / 2 := by
  intro h
  have h2 : (2 * n : ℕ) = 2 * N + 1 := by
    have hcast : ((2 * n : ℕ) : ℝ) = ((2 * N + 1 : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast hcast
  omega

/-- A reciprocal sum reindexed along an injection into `Icc 1 L` is bounded by `1 + log L`. -/
theorem sum_inv_comp_le_one_add_log {s : Finset ℕ} {φ : ℕ → ℕ} {L : ℕ}
    (hinj : ∀ a ∈ s, ∀ b ∈ s, φ a = φ b → a = b)
    (hmem : ∀ a ∈ s, φ a ∈ Finset.Icc 1 L) :
    ∑ n ∈ s, 1 / ((φ n : ℕ) : ℝ) ≤ 1 + Real.log L := by
  have himg : Finset.image φ s ⊆ Finset.Icc 1 L := by
    intro k hk
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hk
    exact hmem a ha
  have hEq : ∑ k ∈ Finset.image φ s, 1 / (k : ℝ) = ∑ n ∈ s, 1 / ((φ n : ℕ) : ℝ) :=
    Finset.sum_image hinj
  rw [← hEq]
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg himg ?_) (sum_Icc_one_div_le_one_add_log L)
  intro k _ _
  positivity

/-- **The reciprocal distance sum at a half-integer cutoff.**  On each side of `N + 1/2` the
distances to the integers of `[1, M]` are `k − 1/2` with `k ≥ 1`, so `1/|x − n| ≤ 2/k`, and the two
reindexed harmonic sums give `2(1 + log N) + 2(1 + log M)`. -/
theorem sum_Icc_inv_abs_sub_half_le (M N : ℕ) :
    ∑ n ∈ Finset.Icc 1 M, 1 / |((N : ℝ) + 1 / 2) - (n : ℝ)|
      ≤ 2 * (1 + Real.log N) + 2 * (1 + Real.log M) := by
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 M) (fun n => n ≤ N)]
  have hlow : ∑ n ∈ Finset.filter (fun n => n ≤ N) (Finset.Icc 1 M),
      1 / |((N : ℝ) + 1 / 2) - (n : ℝ)| ≤ 2 * (1 + Real.log N) := by
    have hpt : ∀ n ∈ Finset.filter (fun n => n ≤ N) (Finset.Icc 1 M),
        1 / |((N : ℝ) + 1 / 2) - (n : ℝ)| ≤ 2 * (1 / ((N + 1 - n : ℕ) : ℝ)) := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn
      obtain ⟨⟨hn1, _⟩, hnN⟩ := hn
      have hnN' : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
      have hk : ((N + 1 - n : ℕ) : ℝ) = (N : ℝ) + 1 - (n : ℝ) := by
        rw [Nat.cast_sub (by omega : n ≤ N + 1)]
        push_cast
        ring
      have hk1 : (1 : ℝ) ≤ ((N + 1 - n : ℕ) : ℝ) := by
        rw [hk]; linarith
      have hdist : |((N : ℝ) + 1 / 2) - (n : ℝ)| = ((N + 1 - n : ℕ) : ℝ) - 1 / 2 := by
        rw [hk, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (N : ℝ) + 1 / 2 - (n : ℝ))]
        ring
      rw [hdist, show (2 : ℝ) * (1 / ((N + 1 - n : ℕ) : ℝ)) = 2 / ((N + 1 - n : ℕ) : ℝ) by ring,
        div_le_div_iff₀ (by linarith) (by linarith)]
      linarith
    have hsum : ∑ n ∈ Finset.filter (fun n => n ≤ N) (Finset.Icc 1 M),
        1 / ((N + 1 - n : ℕ) : ℝ) ≤ 1 + Real.log N := by
      refine sum_inv_comp_le_one_add_log (φ := fun n => N + 1 - n) ?_ ?_
      · intro a ha b hb hab
        simp only [Finset.mem_filter, Finset.mem_Icc] at ha hb
        have hab' : N + 1 - a = N + 1 - b := hab
        omega
      · intro a ha
        simp only [Finset.mem_filter, Finset.mem_Icc] at ha
        simp only [Finset.mem_Icc]
        omega
    refine le_trans (Finset.sum_le_sum hpt) ?_
    rw [← Finset.mul_sum]
    linarith
  have hhigh : ∑ n ∈ Finset.filter (fun n => ¬ n ≤ N) (Finset.Icc 1 M),
      1 / |((N : ℝ) + 1 / 2) - (n : ℝ)| ≤ 2 * (1 + Real.log M) := by
    have hpt : ∀ n ∈ Finset.filter (fun n => ¬ n ≤ N) (Finset.Icc 1 M),
        1 / |((N : ℝ) + 1 / 2) - (n : ℝ)| ≤ 2 * (1 / ((n - N : ℕ) : ℝ)) := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc, not_le] at hn
      obtain ⟨⟨_, _⟩, hNn⟩ := hn
      have hNn' : (N : ℝ) + 1 ≤ (n : ℝ) := by
        have : N + 1 ≤ n := hNn
        exact_mod_cast this
      have hk : ((n - N : ℕ) : ℝ) = (n : ℝ) - (N : ℝ) := by
        rw [Nat.cast_sub (by omega : N ≤ n)]
      have hk1 : (1 : ℝ) ≤ ((n - N : ℕ) : ℝ) := by
        rw [hk]; linarith
      have hdist : |((N : ℝ) + 1 / 2) - (n : ℝ)| = ((n - N : ℕ) : ℝ) - 1 / 2 := by
        rw [abs_sub_comm, hk,
          abs_of_nonneg (by linarith : (0 : ℝ) ≤ (n : ℝ) - ((N : ℝ) + 1 / 2))]
        ring
      rw [hdist, show (2 : ℝ) * (1 / ((n - N : ℕ) : ℝ)) = 2 / ((n - N : ℕ) : ℝ) by ring,
        div_le_div_iff₀ (by linarith) (by linarith)]
      linarith
    have hsum : ∑ n ∈ Finset.filter (fun n => ¬ n ≤ N) (Finset.Icc 1 M),
        1 / ((n - N : ℕ) : ℝ) ≤ 1 + Real.log M := by
      refine sum_inv_comp_le_one_add_log (φ := fun n => n - N) ?_ ?_
      · intro a ha b hb hab
        simp only [Finset.mem_filter, Finset.mem_Icc, not_le] at ha hb
        have hab' : a - N = b - N := hab
        omega
      · intro a ha
        simp only [Finset.mem_filter, Finset.mem_Icc, not_le] at ha
        simp only [Finset.mem_Icc]
        omega
    refine le_trans (Finset.sum_le_sum hpt) ?_
    rw [← Finset.mul_sum]
    linarith
  linarith

/-- **The near-diagonal Perron truncation error.**  A uniform coefficient bound and a support inside
`[1, M]` give an error `B·x^σ·(5(1 + log M) + 4(1 + log N))/(πT)` at the cutoff `x = N + 1/2` — the
uniform-separation bound with its factor `2(N+1)` removed. -/
theorem perron_truncation_error_near_le {c : ℕ → ℂ} {s : Finset ℕ} {M : ℕ}
    (hs : s ⊆ Finset.Icc 1 M) {B : ℝ} (hB : ∀ n, ‖c n‖ ≤ B) {N : ℕ} {σ T : ℝ} (hσ : 1 ≤ σ)
    (hT : 0 < T) :
    (∑ n ∈ s, ‖c n‖ * ((((N : ℝ) + 1 / 2) / n) ^ σ
        / (Real.pi * T * |Real.log (((N : ℝ) + 1 / 2) / n)|)))
      ≤ B * ((N : ℝ) + 1 / 2) ^ σ
          * (5 * (1 + Real.log M) + 4 * (1 + Real.log N)) / (Real.pi * T) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hx : (0 : ℝ) < (N : ℝ) + 1 / 2 := by linarith
  have hB0 : (0 : ℝ) ≤ B := le_trans (norm_nonneg (c 1)) (hB 1)
  set x : ℝ := (N : ℝ) + 1 / 2 with hxdef
  have hxσ : (0 : ℝ) ≤ x ^ σ := Real.rpow_nonneg hx.le σ
  set Kc : ℝ := B * x ^ σ / (Real.pi * T) with hKc
  have hKc0 : (0 : ℝ) ≤ Kc := by rw [hKc]; positivity
  have hterm : ∀ n ∈ s, ‖c n‖ * ((x / n) ^ σ / (Real.pi * T * |Real.log (x / n)|))
      ≤ Kc * (1 / (n : ℝ) + 2 / |x - (n : ℝ)|) := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.1 (hs hn)).1
    have hn0 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hne : (n : ℝ) ≠ x := by rw [hxdef]; exact natCast_ne_half N n
    have hre : (x / n) ^ σ / (Real.pi * T * |Real.log (x / n)|)
        = ((x / n) ^ σ / |Real.log (x / n)|) / (Real.pi * T) := by
      rw [mul_comm (Real.pi * T) |Real.log (x / (n : ℝ))|, ← div_div]
    have hkey := rpow_div_abs_log_le (x := x) (y := (n : ℝ)) hx hn0 hσ hne.symm
    rw [hre]
    calc ‖c n‖ * (((x / n) ^ σ / |Real.log (x / n)|) / (Real.pi * T))
        ≤ B * ((x ^ σ * (1 / (n : ℝ) + 2 / |x - (n : ℝ)|)) / (Real.pi * T)) := by
          refine mul_le_mul (hB n) ?_ (by positivity) hB0
          exact div_le_div_of_nonneg_right hkey (by positivity)
      _ = Kc * (1 / (n : ℝ) + 2 / |x - (n : ℝ)|) := by
          rw [hKc]; ring
  have hsum : ∑ n ∈ s, (1 / (n : ℝ) + 2 / |x - (n : ℝ)|)
      ≤ 5 * (1 + Real.log M) + 4 * (1 + Real.log N) := by
    have hsub : ∑ n ∈ s, (1 / (n : ℝ) + 2 / |x - (n : ℝ)|)
        ≤ ∑ n ∈ Finset.Icc 1 M, (1 / (n : ℝ) + 2 / |x - (n : ℝ)|) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hs ?_
      intro n _ _
      have h1 : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
      have h2 : (0 : ℝ) ≤ 2 / |x - (n : ℝ)| := div_nonneg (by norm_num) (abs_nonneg _)
      linarith
    have hsplit : ∑ n ∈ Finset.Icc 1 M, (1 / (n : ℝ) + 2 / |x - (n : ℝ)|)
        = (∑ n ∈ Finset.Icc 1 M, 1 / (n : ℝ))
          + 2 * ∑ n ∈ Finset.Icc 1 M, 1 / |x - (n : ℝ)| := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl ?_
      intro n _
      rw [mul_one_div]
    have h1 := sum_Icc_one_div_le_one_add_log M
    have h2 := sum_Icc_inv_abs_sub_half_le M N
    rw [← hxdef] at h2
    rw [hsplit] at hsub
    linarith
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  refine le_trans (mul_le_mul_of_nonneg_left hsum hKc0) (le_of_eq ?_)
  rw [hKc]
  ring

/-- **The truncated Perron formula with the near-diagonal error.**  For coefficients supported in
`[1, M]` and bounded by `B`, the partial sum over `[1, min M N]` is the truncated vertical integral
of the Dirichlet polynomial against `x^s/s` at `x = N + 1/2`, with error
`B·x^σ·(5(1 + log M) + 4(1 + log N))/(πT)`. -/
theorem norm_sum_Icc_sub_perron_integral_near_le {c : ℕ → ℂ} {M N : ℕ}
    {B : ℝ} (hB : ∀ n, ‖c n‖ ≤ B) {σ T : ℝ} (hσ : 1 ≤ σ) (hT : 0 < T) :
    ‖(∑ n ∈ Finset.Icc 1 (min M N), c n)
        - ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t in (-T)..T,
            (∑ n ∈ Finset.Icc 1 M, c n * ((n : ℂ) ^ (-((σ : ℂ) + (t : ℝ) * I))))
              * (((((N : ℝ) + 1 / 2) : ℝ) : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I)
                  / ((σ : ℂ) + (t : ℝ) * I))‖
      ≤ B * (((N : ℝ) + 1 / 2)) ^ σ
          * (5 * (1 + Real.log M) + 4 * (1 + Real.log N)) / (Real.pi * T) := by
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hx : (0 : ℝ) < (N : ℝ) + 1 / 2 := by linarith
  have hs0 : (0 : ℕ) ∉ Finset.Icc 1 M := by simp
  have hne : ∀ n ∈ Finset.Icc 1 M, (n : ℝ) ≠ (N : ℝ) + 1 / 2 := fun n _ => natCast_ne_half N n
  have hmain := norm_sum_lt_sub_perron_integral_le (c := c) (s := Finset.Icc 1 M) hs0 hx hne
    (σ := σ) (T := T) (by linarith) hT
  rw [filter_lt_half_integer M N] at hmain
  exact le_trans hmain (perron_truncation_error_near_le (le_refl _) hB hσ hT)

end RHTower.Sieve
end
