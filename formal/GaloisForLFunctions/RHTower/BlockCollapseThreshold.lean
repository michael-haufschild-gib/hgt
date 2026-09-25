import Mathlib

/-!
# The block collapse threshold: the pair is optimal

The virial law gives an exact internal collapse rate `2N(N-1)` for a block of `N` zeros, and the
external field of the surrounding configuration opposes collapse by at most `4 I₂ E`, where `I₂` is
the block's second moment about its centroid and `E = ∑_y |d_y|⁻²` is the outside field.  Collapse
is therefore guaranteed by

```text
  4 I₂ E < 2N(N-1) .
```

It is tempting to read the `N²` on the right as a gain: a larger block should be easier to collapse.
It is not.  For a block of `N` evenly spaced zeros with gap `δ`,

```text
  I₂ = N(N² - 1)δ²/12 ,
```

which grows one power of `N` faster than the pair count `N(N-1)/2`.  The two powers cancel exactly
and the criterion becomes

```text
  (N + 1)·δ²E < 6 ,
```

a threshold `δ²E < 6/(N+1)` that is strictly decreasing in `N`.  At `N = 2` it is the pair criterion
`δ²E < 2`; every larger block is strictly harder to collapse.  The mechanism is the exact ratio

```text
  I₂ / (N(N-1)) = (N + 1)δ²/12 ,
```

increasing in `N`: the moment of inertia outgrows the pair count.  Enlarging the window is therefore
not a route around the pair field bound.
-/

namespace RHTower

open Finset

private theorem sum_range_cast (N : ℕ) :
    ∑ j ∈ Finset.range N, (j : ℝ) = (N : ℝ) * ((N : ℝ) - 1) / 2 := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

private theorem sum_range_cast_sq (N : ℕ) :
    ∑ j ∈ Finset.range N, (j : ℝ) ^ (2 : ℕ)
      = (N : ℝ) * ((N : ℝ) - 1) * (2 * (N : ℝ) - 1) / 6 := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- **The second moment of an evenly spaced block.**  `N` zeros with common gap `δ`, measured
about their centroid, have second moment `N(N²-1)δ²/12`. -/
theorem evenBlock_secondMoment (N : ℕ) (δ : ℝ) :
    ∑ j ∈ Finset.range N, ((j : ℝ) * δ - ((N : ℝ) - 1) * δ / 2) ^ (2 : ℕ)
      = (N : ℝ) * ((N : ℝ) ^ (2 : ℕ) - 1) * δ ^ (2 : ℕ) / 12 := by
  have hexp : ∀ j : ℕ, ((j : ℝ) * δ - ((N : ℝ) - 1) * δ / 2) ^ (2 : ℕ)
      = (j : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ)
        - (j : ℝ) * (((N : ℝ) - 1) * δ ^ (2 : ℕ))
        + ((N : ℝ) - 1) ^ (2 : ℕ) * δ ^ (2 : ℕ) / 4 := by
    intro j; ring
  simp only [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    sum_range_cast, sum_range_cast_sq, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  ring

/-- The exact mechanism: the second moment per pair grows linearly in the block size. -/
theorem evenBlock_moment_per_pair {N : ℕ} (hN : 2 ≤ N) (δ : ℝ) :
    ((N : ℝ) * ((N : ℝ) ^ (2 : ℕ) - 1) * δ ^ (2 : ℕ) / 12) / ((N : ℝ) * ((N : ℝ) - 1))
      = ((N : ℝ) + 1) * δ ^ (2 : ℕ) / 12 := by
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have h0 : (N : ℝ) ≠ 0 := by linarith
  have h1 : (N : ℝ) - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- **The block collapse criterion.**  For an evenly spaced block the virial criterion
`4 I₂ E < 2N(N-1)` is exactly `(N+1)·δ²E < 6`. -/
theorem evenBlock_collapse_iff {N : ℕ} (hN : 2 ≤ N) (δ E : ℝ) :
    4 * ((N : ℝ) * ((N : ℝ) ^ (2 : ℕ) - 1) * δ ^ (2 : ℕ) / 12) * E
        < 2 * (N : ℝ) * ((N : ℝ) - 1)
      ↔ ((N : ℝ) + 1) * (δ ^ (2 : ℕ) * E) < 6 := by
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hpos : 0 < (N : ℝ) * ((N : ℝ) - 1) := by nlinarith
  constructor
  · intro h
    have hkey : (N : ℝ) * ((N : ℝ) - 1) * (((N : ℝ) + 1) * (δ ^ (2 : ℕ) * E))
        < (N : ℝ) * ((N : ℝ) - 1) * 6 := by nlinarith
    exact lt_of_mul_lt_mul_left (by linarith [hkey]) (le_of_lt hpos)
  · intro h
    nlinarith

/-- **The pair is optimal.**  The threshold `6/(N+1)` is strictly decreasing in the block size. -/
theorem evenBlock_threshold_lt {N M : ℕ} (hN : 2 ≤ N) (hNM : N < M) :
    6 / ((M : ℝ) + 1) < 6 / ((N : ℝ) + 1) := by
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNM' : (N : ℝ) < (M : ℝ) := by exact_mod_cast hNM
  have h1 : (0 : ℝ) < (N : ℝ) + 1 := by linarith
  have h2 : (0 : ℝ) < (M : ℝ) + 1 := by linarith
  rw [div_lt_div_iff₀ h2 h1]
  linarith

/-- At `N = 2` the block threshold is the pair threshold `δ²E < 2`. -/
theorem evenBlock_threshold_two : (6 : ℝ) / ((2 : ℝ) + 1) = 2 := by norm_num

/-- Telescoping tail bound: zeros at distances `G, 2G, 3G, …` contribute at most `2/G²`. -/
theorem sum_inv_sq_multiples_le {G : ℝ} (hG : 0 < G) {M : ℕ} (hM : 1 ≤ M) :
    ∑ m ∈ Finset.Icc 1 M, 1 / (((m : ℝ) * G) ^ (2 : ℕ)) ≤ 2 / G ^ (2 : ℕ) := by
  have hbase : ∀ K : ℕ, 1 ≤ K →
      ∑ m ∈ Finset.Icc 1 K, 1 / ((m : ℝ) ^ (2 : ℕ)) ≤ 2 - 1 / (K : ℝ) := by
    intro K hK
    induction K with
    | zero => omega
    | succ n ih =>
      rcases Nat.eq_or_lt_of_le hK with h | h
      · have hn : n = 0 := by omega
        subst hn; norm_num
      · have hn1 : 1 ≤ n := by omega
        have ihn := ih hn1
        have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
        rw [Finset.sum_Icc_succ_top (by omega)]
        have hstep : 1 / (((n : ℕ) + 1 : ℝ) ^ (2 : ℕ))
            ≤ 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) := by
          rw [div_sub_div _ _ (ne_of_gt hnpos) (by positivity), div_le_div_iff₀ (by positivity)
            (by positivity)]
          ring_nf
          nlinarith
        push_cast
        linarith
  have h1 : ∀ m : ℕ, 1 / (((m : ℝ) * G) ^ (2 : ℕ))
      = (1 / ((m : ℝ) ^ (2 : ℕ))) * (1 / G ^ (2 : ℕ)) := by
    intro m; rw [mul_pow]; field_simp
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hG2 : (0 : ℝ) < 1 / G ^ (2 : ℕ) := by positivity
  calc ∑ m ∈ Finset.Icc 1 M, 1 / (((m : ℝ) * G) ^ (2 : ℕ))
      = (∑ m ∈ Finset.Icc 1 M, 1 / ((m : ℝ) ^ (2 : ℕ))) * (1 / G ^ (2 : ℕ)) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun m _ => h1 m
    _ ≤ (2 - 1 / (M : ℝ)) * (1 / G ^ (2 : ℕ)) := by
        exact mul_le_mul_of_nonneg_right (hbase M hM) (le_of_lt hG2)
    _ ≤ 2 / G ^ (2 : ℕ) := by
        have hprod : 0 < (1 / (M : ℝ)) * (1 / G ^ (2 : ℕ)) := by positivity
        have hrw : (2 - 1 / (M : ℝ)) * (1 / G ^ (2 : ℕ))
            = 2 / G ^ (2 : ℕ) - (1 / (M : ℝ)) * (1 / G ^ (2 : ℕ)) := by ring
        rw [hrw]; linarith

end RHTower
