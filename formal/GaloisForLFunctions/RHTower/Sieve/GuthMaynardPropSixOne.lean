import GaloisForLFunctions.RHTower.Sieve.GuthMaynardTraceSingularValue

/-!
# Guth–Maynard, Proposition 6.1: the assembly of the `S₂` bound

Guth–Maynard (arXiv 2405.20552, §6) bound the two-nonzero-frequency sum `S₂` by

`S₂ ≲ N² |W|² + T N |W|^{2−1/k} + N² |W|² (T^{1/2} / |W|^{3/4})^{1/k}`  (6.4)

for every `k ≥ 1`, from three inputs: the reduction (6.1)
`S₂ ≲ (N²/M) Σ_{t₁,t₂ ∈ W} |Σ_{m ∼ M} a_m m^{i(t₁−t₂)}|²` for some `M ≲ T/N` (Lemma 6.2 and a dyadic
split), Hölder's inequality (6.2) turning the square into the `2k`-th power of the polynomial, i.e.
the square of the polynomial of length `M^k`, and Heath-Brown's theorem (6.3) for that longer polynomial,
`Σ_{t₁,t₂ ∈ W} |Σ_{m ≍ M^k} b_m m^{i(t₁−t₂)}|² ≲ |W|² M^k + |W| M^{2k} + |W|^{5/4} T^{1/2} M^k`.

This module proves the two elementary steps: the finite-sum power-mean inequality behind (6.2),
and the real-number assembly (6.4) from (6.1), (6.2), (6.3) with explicit constants.  The analytic
inputs — Lemma 6.2 for `ζ`, the symmetry reduction to (6.1), and Heath-Brown's theorem — are the
remaining bricks of the programme.
-/

open Finset

namespace RHTower.GuthMaynard

/-- Power-mean inequality: `(Σ_s x)^k ≤ |s|^{k−1} Σ_s x^k` for nonnegative `x` and `k ≥ 1`. -/
theorem sum_pow_le_card_pow_mul_sum_pow {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) {k : ℕ} (hk : 1 ≤ k) :
    (∑ i ∈ s, x i) ^ k ≤ (s.card : ℝ) ^ (k - 1) * ∑ i ∈ s, x i ^ k := by
  rcases s.eq_empty_or_nonempty with hs | hs
  · subst hs
    simp only [Finset.sum_empty, Finset.card_empty, Nat.cast_zero]
    rw [zero_pow (by omega)]
    exact le_of_eq (by ring)
  have hcard : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hw : ∀ i ∈ s, (0 : ℝ) ≤ 1 / s.card := fun _ _ => by positivity
  have hw' : ∑ i ∈ s, (1 / (s.card : ℝ)) = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul]; field_simp
  have h := Real.pow_arith_mean_le_arith_mean_pow s (fun _ => 1 / (s.card : ℝ)) x hw hw' hx k
  rw [← Finset.mul_sum, ← Finset.mul_sum, mul_pow] at h
  -- `(1/c)^k (Σx)^k ≤ (1/c) Σ x^k`
  have hck : (0 : ℝ) < (s.card : ℝ) ^ k := by positivity
  have hck1 : (0 : ℝ) < (s.card : ℝ) ^ (k - 1) := by positivity
  have hsplit : (s.card : ℝ) ^ k = (s.card : ℝ) ^ (k - 1) * s.card := by
    rw [← pow_succ]; congr 1; omega
  rw [div_pow, one_pow] at h
  have h' : (∑ i ∈ s, x i) ^ k ≤ (s.card : ℝ) ^ k * (1 / (s.card : ℝ) * ∑ i ∈ s, x i ^ k) := by
    calc (∑ i ∈ s, x i) ^ k
        = (s.card : ℝ) ^ k * (1 / (s.card : ℝ) ^ k * (∑ i ∈ s, x i) ^ k) := by field_simp
      _ ≤ (s.card : ℝ) ^ k * (1 / (s.card : ℝ) * ∑ i ∈ s, x i ^ k) :=
          mul_le_mul_of_nonneg_left h hck.le
  calc (∑ i ∈ s, x i) ^ k ≤ (s.card : ℝ) ^ k * (1 / (s.card : ℝ) * ∑ i ∈ s, x i ^ k) := h'
    _ = (s.card : ℝ) ^ (k - 1) * ∑ i ∈ s, x i ^ k := by
        rw [hsplit]; field_simp

/-- **Guth–Maynard (6.2), scalar form.**  For nonnegative `x` on a finite set and `k ≥ 1`,
`Σ x ≤ |s|^{1 − 1/k} (Σ x^k)^{1/k}`. -/
theorem sum_le_card_rpow_mul_sum_pow_rpow {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) {k : ℕ} (hk : 1 ≤ k) :
    ∑ i ∈ s, x i ≤ (s.card : ℝ) ^ (1 - 1 / (k : ℝ)) * (∑ i ∈ s, x i ^ k) ^ (1 / (k : ℝ)) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hS0 : 0 ≤ ∑ i ∈ s, x i := Finset.sum_nonneg hx
  have hSk0 : 0 ≤ ∑ i ∈ s, x i ^ k := Finset.sum_nonneg fun i hi => pow_nonneg (hx i hi) k
  have hpow := sum_pow_le_card_pow_mul_sum_pow s x hx hk
  -- take `k`-th roots
  have hroot : ((∑ i ∈ s, x i) ^ k) ^ (1 / (k : ℝ))
      ≤ ((s.card : ℝ) ^ (k - 1) * ∑ i ∈ s, x i ^ k) ^ (1 / (k : ℝ)) :=
    Real.rpow_le_rpow (by positivity) hpow (by positivity)
  rw [one_div, Real.pow_rpow_inv_natCast hS0 (by omega)] at hroot
  refine hroot.trans (le_of_eq ?_)
  rw [Real.mul_rpow (by positivity) hSk0, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
    one_div]
  congr 2
  rw [Nat.cast_sub hk, Nat.cast_one]
  field_simp

/-- Subadditivity of `x ↦ x^{1/k}` on three nonnegative terms. -/
theorem rpow_inv_add_three_le {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) {k : ℕ}
    (hk : 1 ≤ k) :
    (a + b + c) ^ (1 / (k : ℝ)) ≤ a ^ (1 / (k : ℝ)) + b ^ (1 / (k : ℝ)) + c ^ (1 / (k : ℝ)) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hp0 : (0 : ℝ) ≤ 1 / (k : ℝ) := by positivity
  have hp1 : 1 / (k : ℝ) ≤ 1 := by
    rw [div_le_one hkpos]; exact_mod_cast hk
  calc (a + b + c) ^ (1 / (k : ℝ)) ≤ (a + b) ^ (1 / (k : ℝ)) + c ^ (1 / (k : ℝ)) :=
        Real.rpow_add_le_add_rpow (by positivity) hc hp0 hp1
    _ ≤ a ^ (1 / (k : ℝ)) + b ^ (1 / (k : ℝ)) + c ^ (1 / (k : ℝ)) := by
        gcongr
        exact Real.rpow_add_le_add_rpow ha hb hp0 hp1

/-- **Guth–Maynard (6.4), abstract form.**  With `κ = k`, from
`S₂ ≤ C (N²/M) X` (6.1), `X ≤ (W²)^{1−1/κ} Y^{1/κ}` (6.2), and
`Y ≤ C' (W² M^k + W M^{2k} + W^{5/4} T^{1/2} M^k)` (6.3), together with `M ≤ T/N`:
`S₂ ≤ C C'^{1/κ} (N² W² + T N W^{2−1/κ} + N² W^{2−3/(4κ)} T^{1/(2κ)})`. -/
theorem prop61_abstract {W N M T S₂ X Y C C' : ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hW : 0 < W) (hN : 0 < N) (hM : 0 < M) (hT : 0 < T) (hMT : M ≤ T / N)
    (hC : 0 ≤ C) (hC' : 0 ≤ C') (hY0 : 0 ≤ Y)
    (h61 : S₂ ≤ C * (N ^ 2 / M) * X)
    (h62 : X ≤ (W ^ 2) ^ (1 - 1 / (k : ℝ)) * Y ^ (1 / (k : ℝ)))
    (h63 : Y ≤ C' * (W ^ 2 * M ^ k + W * M ^ (2 * k) + W ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * M ^ k)) :
    S₂ ≤ C * C' ^ (1 / (k : ℝ)) *
      (N ^ 2 * W ^ 2 + T * N * W ^ (2 - 1 / (k : ℝ))
        + N ^ 2 * W ^ (2 - 3 / (4 * (k : ℝ))) * T ^ (1 / (2 * (k : ℝ)))) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hk0 : k ≠ 0 := by omega
  set κ : ℝ := (k : ℝ) with hκ
  have hκpos : 0 < κ := hkpos
  -- the `k`-th roots of the factors
  have hMk : (M ^ k) ^ (1 / κ) = M := by
    rw [one_div, Real.pow_rpow_inv_natCast hM.le hk0]
  have hM2k : (M ^ (2 * k)) ^ (1 / κ) = M ^ 2 := by
    rw [pow_mul, one_div, Real.pow_rpow_inv_natCast (by positivity) hk0]
  have hW2κ : (W ^ 2) ^ (1 / κ) = W ^ (2 / κ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hW.le]
    congr 1; push_cast; ring
  have hW54 : (W ^ ((5 : ℝ) / 4)) ^ (1 / κ) = W ^ (5 / (4 * κ)) := by
    rw [← Real.rpow_mul hW.le]
    congr 1; field_simp
  have hT12 : (T ^ ((1 : ℝ) / 2)) ^ (1 / κ) = T ^ (1 / (2 * κ)) := by
    rw [← Real.rpow_mul hT.le]
    congr 1; field_simp
  have hp1 : (W ^ 2 * M ^ k) ^ (1 / κ) = W ^ (2 / κ) * M := by
    rw [Real.mul_rpow (by positivity) (by positivity), hW2κ, hMk]
  have hp2 : (W * M ^ (2 * k)) ^ (1 / κ) = W ^ (1 / κ) * M ^ 2 := by
    rw [Real.mul_rpow hW.le (by positivity), hM2k]
  have hp3 : (W ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * M ^ k) ^ (1 / κ)
      = W ^ (5 / (4 * κ)) * T ^ (1 / (2 * κ)) * M := by
    rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity),
      hW54, hT12, hMk]
  -- `Y^{1/κ}`
  have hY' : Y ^ (1 / κ) ≤ C' ^ (1 / κ) *
      (W ^ (2 / κ) * M + W ^ (1 / κ) * M ^ 2 + W ^ (5 / (4 * κ)) * T ^ (1 / (2 * κ)) * M) := by
    calc Y ^ (1 / κ)
        ≤ (C' * (W ^ 2 * M ^ k + W * M ^ (2 * k)
            + W ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * M ^ k)) ^ (1 / κ) :=
          Real.rpow_le_rpow hY0 h63 (by positivity)
      _ = C' ^ (1 / κ) * (W ^ 2 * M ^ k + W * M ^ (2 * k)
            + W ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * M ^ k) ^ (1 / κ) :=
          Real.mul_rpow hC' (by positivity)
      _ ≤ C' ^ (1 / κ) * ((W ^ 2 * M ^ k) ^ (1 / κ) + (W * M ^ (2 * k)) ^ (1 / κ)
            + (W ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * M ^ k) ^ (1 / κ)) := by
          gcongr
          exact rpow_inv_add_three_le (by positivity) (by positivity) (by positivity) hk
      _ = _ := by rw [hp1, hp2, hp3]
  -- Hölder with the powers of `W` combined
  have hW2 : (W ^ 2) ^ (1 - 1 / κ) = W ^ (2 - 2 / κ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hW.le]; congr 1; push_cast; ring
  have hX' : X ≤ C' ^ (1 / κ) *
      (W ^ 2 * M + W ^ (2 - 1 / κ) * M ^ 2 + W ^ (2 - 3 / (4 * κ)) * T ^ (1 / (2 * κ)) * M) := by
    have hWa : W ^ (2 - 2 / κ) * W ^ (2 / κ) = W ^ 2 := by
      rw [← Real.rpow_add hW]; norm_num
    have hWb : W ^ (2 - 2 / κ) * W ^ (1 / κ) = W ^ (2 - 1 / κ) := by
      rw [← Real.rpow_add hW]; congr 1; ring
    have hWc : W ^ (2 - 2 / κ) * W ^ (5 / (4 * κ)) = W ^ (2 - 3 / (4 * κ)) := by
      rw [← Real.rpow_add hW]; congr 1; field_simp; ring
    calc X ≤ (W ^ 2) ^ (1 - 1 / κ) * Y ^ (1 / κ) := h62
      _ ≤ (W ^ 2) ^ (1 - 1 / κ) * (C' ^ (1 / κ) *
          (W ^ (2 / κ) * M + W ^ (1 / κ) * M ^ 2 + W ^ (5 / (4 * κ)) * T ^ (1 / (2 * κ)) * M)) :=
          mul_le_mul_of_nonneg_left hY' (by positivity)
      _ = C' ^ (1 / κ) * (W ^ (2 - 2 / κ) * W ^ (2 / κ) * M + W ^ (2 - 2 / κ) * W ^ (1 / κ) * M ^ 2
          + W ^ (2 - 2 / κ) * W ^ (5 / (4 * κ)) * T ^ (1 / (2 * κ)) * M) := by
          rw [hW2]; ring
      _ = _ := by rw [hWa, hWb, hWc]
  -- assemble with (6.1) and `M ≤ T/N`
  have hMT' : N ^ 2 * M ≤ T * N := by
    have := mul_le_mul_of_nonneg_left hMT (by positivity : (0 : ℝ) ≤ N ^ 2)
    calc N ^ 2 * M ≤ N ^ 2 * (T / N) := this
      _ = T * N := by field_simp
  have hcoef : 0 ≤ C * (N ^ 2 / M) := by positivity
  calc S₂ ≤ C * (N ^ 2 / M) * X := h61
    _ ≤ C * (N ^ 2 / M) * (C' ^ (1 / κ) *
        (W ^ 2 * M + W ^ (2 - 1 / κ) * M ^ 2 + W ^ (2 - 3 / (4 * κ)) * T ^ (1 / (2 * κ)) * M)) :=
        mul_le_mul_of_nonneg_left hX' hcoef
    _ = C * C' ^ (1 / κ) * (N ^ 2 * W ^ 2 + N ^ 2 * M * W ^ (2 - 1 / κ)
        + N ^ 2 * W ^ (2 - 3 / (4 * κ)) * T ^ (1 / (2 * κ))) := by
        field_simp
    _ ≤ C * C' ^ (1 / κ) * (N ^ 2 * W ^ 2 + T * N * W ^ (2 - 1 / κ)
        + N ^ 2 * W ^ (2 - 3 / (4 * κ)) * T ^ (1 / (2 * κ))) := by
        gcongr

/-- The third term of (6.4) in the paper's form: `W^{2−3/(4κ)} T^{1/(2κ)} = W² (T^{1/2}/W^{3/4})^{1/κ}`. -/
theorem third_term_eq {W T : ℝ} (hW : 0 < W) (hT : 0 < T) {k : ℕ} (hk : 1 ≤ k) :
    W ^ (2 - 3 / (4 * (k : ℝ))) * T ^ (1 / (2 * (k : ℝ)))
      = W ^ 2 * (T ^ ((1 : ℝ) / 2) / W ^ ((3 : ℝ) / 4)) ^ (1 / (k : ℝ)) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  rw [Real.div_rpow (by positivity) (by positivity), ← Real.rpow_mul hT.le, ← Real.rpow_mul hW.le,
    show (2 : ℝ) - 3 / (4 * (k : ℝ)) = 2 + (-(3 / 4 * (1 / (k : ℝ)))) by ring,
    Real.rpow_add hW, Real.rpow_neg hW.le, Real.rpow_two]
  field_simp

end RHTower.GuthMaynard
