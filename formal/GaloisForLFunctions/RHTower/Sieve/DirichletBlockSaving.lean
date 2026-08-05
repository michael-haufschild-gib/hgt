import GaloisForLFunctions.RHTower.Sieve.DirichletBlockAbel

/-!
# Normalised dyadic block bound and its balanced saving

The block bound coming from the `k`-th derivative test carries the block length as an explicit
factor.  On a dyadic block the length is at most twice the base point, so the factor can be
absorbed and the bound becomes a pure function of the base point `N`, the order `k`, and the
derivative scale `λ`.

The second theorem is the saving that the dyadic schedule is designed to produce.  Once `λ` sits in
the balanced window

```text
4 ^ k * λ ≤ N⁻¹        and        N ^ (-3/2) ≤ λ,
```

both terms of the normalised bound drop below `N ^ (-1 / 2 ^ k)`, so a single dyadic block
contributes at most `1024 * N ^ (-1 / 2 ^ k)` to the Dirichlet sum on the line `Re s = 1`.
-/

namespace RHTower.Sieve

open Finset

/-- **Normalised block bound.**  On a dyadic block the length factor of the derivative-test bound is
absorbed, leaving a bound depending only on the base point, the order, and the derivative scale. -/
theorem dirichlet_block_one_normalized (t : ℝ) (ht : 0 < t) (k N M : ℕ) (hk : 2 ≤ k)
    (hN : 1 ≤ N) (hNM : N ≤ M) (hM : M ≤ 2 * N + 1)
    (hlam1 : t / (2 * Real.pi) * (Nat.factorial (k - 1) : ℝ) / (2 * (N : ℝ)) ^ k ≤ 1) :
    ‖∑ n ∈ Finset.Ico N M, (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖
      ≤ 512 * ((4 : ℝ) ^ k * (t / (2 * Real.pi) * (Nat.factorial (k - 1) : ℝ)
              / (2 * (N : ℝ)) ^ k)) ^ (1 / ((2 : ℝ) ^ k - 2))
        + 512 * (N : ℝ) ^ (-(4 / (2 : ℝ) ^ k))
            * (t / (2 * Real.pi) * (Nat.factorial (k - 1) : ℝ)
                / (2 * (N : ℝ)) ^ k) ^ (-(2 / (2 : ℝ) ^ k)) := by
  have hπ := Real.pi_pos
  set lam : ℝ := t / (2 * Real.pi) * (Nat.factorial (k - 1) : ℝ) / (2 * (N : ℝ)) ^ k with hlamdef
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hlam0 : 0 < lam := by
    have hfac : (0 : ℝ) < (Nat.factorial (k - 1) : ℝ) := by
      exact_mod_cast Nat.factorial_pos (k - 1)
    have : (0 : ℝ) < (2 * (N : ℝ)) ^ k := by positivity
    rw [hlamdef]
    positivity
  have hbase := dirichlet_block_one_full t ht k N M hk hN hNM hM hlam1
  -- The block length is at most twice the base point.
  have hL : ((M - N : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
    have : (M - N : ℕ) ≤ 2 * N := by omega
    exact_mod_cast this
  have hL0 : (0 : ℝ) ≤ ((M - N : ℕ) : ℝ) := Nat.cast_nonneg _
  set A : ℝ := ((4 : ℝ) ^ k * lam) ^ (1 / ((2 : ℝ) ^ k - 2)) with hAdef
  set Bexp : ℝ := 1 - 4 / (2 : ℝ) ^ k with hBexpdef
  set B : ℝ := lam ^ (-(2 / (2 : ℝ) ^ k)) with hBdef
  have hA0 : 0 ≤ A := Real.rpow_nonneg (by positivity) _
  have hB0 : 0 ≤ B := Real.rpow_nonneg hlam0.le _
  have hBexp0 : 0 ≤ Bexp := by
    have h4 : (4 : ℝ) ≤ (2 : ℝ) ^ k := by
      calc (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
        _ ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) hk
    have h2k : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    rw [hBexpdef, sub_nonneg, div_le_one h2k]
    exact h4
  -- first summand
  have hfirst : 256 * (((M - N : ℕ) : ℝ) * A) * ((N : ℝ))⁻¹ ≤ 512 * A := by
    have : ((M - N : ℕ) : ℝ) * A ≤ 2 * (N : ℝ) * A := by
      exact mul_le_mul_of_nonneg_right hL hA0
    calc 256 * (((M - N : ℕ) : ℝ) * A) * ((N : ℝ))⁻¹
        ≤ 256 * (2 * (N : ℝ) * A) * ((N : ℝ))⁻¹ := by
          have h256 : (0 : ℝ) ≤ 256 := by norm_num
          have := mul_le_mul_of_nonneg_left this h256
          exact mul_le_mul_of_nonneg_right this (by positivity)
      _ = 512 * A := by field_simp; ring
  -- second summand
  have hsecond : 256 * (((M - N : ℕ) : ℝ) ^ Bexp * B) * ((N : ℝ))⁻¹
      ≤ 512 * (N : ℝ) ^ (-(4 / (2 : ℝ) ^ k)) * B := by
    have hpow : ((M - N : ℕ) : ℝ) ^ Bexp ≤ (2 * (N : ℝ)) ^ Bexp :=
      Real.rpow_le_rpow hL0 hL hBexp0
    have hsplit : (2 * (N : ℝ)) ^ Bexp = (2 : ℝ) ^ Bexp * (N : ℝ) ^ Bexp :=
      Real.mul_rpow (by norm_num) hN0.le
    have htwo : (2 : ℝ) ^ Bexp ≤ 2 := by
      have hb1 : Bexp ≤ 1 := by
        rw [hBexpdef]
        have : (0 : ℝ) < 4 / (2 : ℝ) ^ k := by positivity
        linarith
      calc (2 : ℝ) ^ Bexp ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hb1
        _ = 2 := Real.rpow_one 2
    have hNsplit : (N : ℝ) ^ Bexp * ((N : ℝ))⁻¹ = (N : ℝ) ^ (-(4 / (2 : ℝ) ^ k)) := by
      have hinv : ((N : ℝ))⁻¹ = (N : ℝ) ^ (-1 : ℝ) := by
        rw [Real.rpow_neg_one]
      rw [hinv, ← Real.rpow_add hN0, hBexpdef]
      ring_nf
    calc 256 * (((M - N : ℕ) : ℝ) ^ Bexp * B) * ((N : ℝ))⁻¹
        ≤ 256 * ((2 : ℝ) ^ Bexp * (N : ℝ) ^ Bexp * B) * ((N : ℝ))⁻¹ := by
          have h1 : ((M - N : ℕ) : ℝ) ^ Bexp * B ≤ (2 : ℝ) ^ Bexp * (N : ℝ) ^ Bexp * B := by
            rw [← hsplit]
            exact mul_le_mul_of_nonneg_right hpow hB0
          have := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 256)
          exact mul_le_mul_of_nonneg_right this (by positivity)
      _ ≤ 256 * (2 * ((N : ℝ) ^ Bexp * B)) * ((N : ℝ))⁻¹ := by
          have h1 : (2 : ℝ) ^ Bexp * (N : ℝ) ^ Bexp * B ≤ 2 * ((N : ℝ) ^ Bexp * B) := by
            have hnb : (0 : ℝ) ≤ (N : ℝ) ^ Bexp * B :=
              mul_nonneg (Real.rpow_nonneg hN0.le _) hB0
            calc (2 : ℝ) ^ Bexp * (N : ℝ) ^ Bexp * B
                = (2 : ℝ) ^ Bexp * ((N : ℝ) ^ Bexp * B) := by ring
              _ ≤ 2 * ((N : ℝ) ^ Bexp * B) := mul_le_mul_of_nonneg_right htwo hnb
          have := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 256)
          exact mul_le_mul_of_nonneg_right this (by positivity)
      _ = 512 * ((N : ℝ) ^ Bexp * ((N : ℝ))⁻¹) * B := by ring
      _ = 512 * (N : ℝ) ^ (-(4 / (2 : ℝ) ^ k)) * B := by rw [hNsplit]
  calc ‖∑ n ∈ Finset.Ico N M, (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖
      ≤ 256 * (((M - N : ℕ) : ℝ) * A + ((M - N : ℕ) : ℝ) ^ Bexp * B) * ((N : ℝ))⁻¹ := hbase
    _ = 256 * (((M - N : ℕ) : ℝ) * A) * ((N : ℝ))⁻¹
          + 256 * (((M - N : ℕ) : ℝ) ^ Bexp * B) * ((N : ℝ))⁻¹ := by ring
    _ ≤ 512 * A + 512 * (N : ℝ) ^ (-(4 / (2 : ℝ) ^ k)) * B := add_le_add hfirst hsecond

/-- **Balanced block saving.**  Inside the window where the derivative scale is neither too small
nor too large, both terms of the normalised bound are at most `N ^ (-1 / 2 ^ k)`. -/
theorem block_saving (k N : ℕ) (hk : 2 ≤ k) (hN : 1 ≤ N) (lam : ℝ) (hlam0 : 0 < lam)
    (h1 : (4 : ℝ) ^ k * lam ≤ ((N : ℝ))⁻¹)
    (h2 : (N : ℝ) ^ (-(3 / 2) : ℝ) ≤ lam) :
    512 * ((4 : ℝ) ^ k * lam) ^ (1 / ((2 : ℝ) ^ k - 2))
        + 512 * (N : ℝ) ^ (-(4 / (2 : ℝ) ^ k)) * lam ^ (-(2 / (2 : ℝ) ^ k))
      ≤ 1024 * (N : ℝ) ^ (-(1 / (2 : ℝ) ^ k)) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le one_pos hN1
  have h2k : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have h4le : (4 : ℝ) ≤ (2 : ℝ) ^ k := by
    calc (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
      _ ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) hk
  have h2ksub : (0 : ℝ) < (2 : ℝ) ^ k - 2 := by linarith
  have he0 : 0 < 1 / ((2 : ℝ) ^ k - 2) := by positivity
  -- first term
  have hterm1 : ((4 : ℝ) ^ k * lam) ^ (1 / ((2 : ℝ) ^ k - 2))
      ≤ (N : ℝ) ^ (-(1 / (2 : ℝ) ^ k)) := by
    have hpos : (0 : ℝ) < (4 : ℝ) ^ k * lam := by positivity
    have hstep : ((4 : ℝ) ^ k * lam) ^ (1 / ((2 : ℝ) ^ k - 2))
        ≤ (((N : ℝ))⁻¹) ^ (1 / ((2 : ℝ) ^ k - 2)) :=
      Real.rpow_le_rpow hpos.le h1 he0.le
    have hinv : (((N : ℝ))⁻¹) ^ (1 / ((2 : ℝ) ^ k - 2))
        = (N : ℝ) ^ (-(1 / ((2 : ℝ) ^ k - 2))) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_mul hN0.le]
      ring_nf
    have hmono : (N : ℝ) ^ (-(1 / ((2 : ℝ) ^ k - 2))) ≤ (N : ℝ) ^ (-(1 / (2 : ℝ) ^ k)) := by
      refine Real.rpow_le_rpow_of_exponent_le hN1 ?_
      have : 1 / (2 : ℝ) ^ k ≤ 1 / ((2 : ℝ) ^ k - 2) :=
        one_div_le_one_div_of_le h2ksub (by linarith)
      linarith
    exact hstep.trans (hinv ▸ hmono)
  -- second term
  have hterm2 : (N : ℝ) ^ (-(4 / (2 : ℝ) ^ k)) * lam ^ (-(2 / (2 : ℝ) ^ k))
      ≤ (N : ℝ) ^ (-(1 / (2 : ℝ) ^ k)) := by
    have hlamstep : lam ^ (-(2 / (2 : ℝ) ^ k))
        ≤ ((N : ℝ) ^ (-(3 / 2) : ℝ)) ^ (-(2 / (2 : ℝ) ^ k)) := by
      refine Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hN0 _) h2 ?_
      have : (0 : ℝ) < 2 / (2 : ℝ) ^ k := by positivity
      linarith
    have hcollapse : ((N : ℝ) ^ (-(3 / 2) : ℝ)) ^ (-(2 / (2 : ℝ) ^ k))
        = (N : ℝ) ^ (3 / (2 : ℝ) ^ k) := by
      rw [← Real.rpow_mul hN0.le]
      ring_nf
    have hmul : (N : ℝ) ^ (-(4 / (2 : ℝ) ^ k)) * (N : ℝ) ^ (3 / (2 : ℝ) ^ k)
        = (N : ℝ) ^ (-(1 / (2 : ℝ) ^ k)) := by
      rw [← Real.rpow_add hN0]
      ring_nf
    calc (N : ℝ) ^ (-(4 / (2 : ℝ) ^ k)) * lam ^ (-(2 / (2 : ℝ) ^ k))
        ≤ (N : ℝ) ^ (-(4 / (2 : ℝ) ^ k)) * (N : ℝ) ^ (3 / (2 : ℝ) ^ k) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hN0.le _)
          exact hcollapse ▸ hlamstep
      _ = (N : ℝ) ^ (-(1 / (2 : ℝ) ^ k)) := hmul
  linarith [hterm1, hterm2]


/-! ## The wide balanced window

The window used by `block_saving` has multiplicative width `4 ^ (-k) * N ^ (1/2)` in `λ`, which is
narrower than the factor `2N/k` separating `λ` at consecutive orders, so no schedule can be
guaranteed to land in it.  Relaxing the target saving from `N ^ (-1/2^k)` to `N ^ (-1/(3·2^k))`
widens the window to `[N ^ (-5/3), N ^ (-1/3)]`, of multiplicative width `N ^ (4/3)`, which exceeds
`2N` as soon as `N ≥ 8`.  This is the window a dyadic schedule can actually hit.
-/

private theorem nat_le_two_pow_sub_two {k : ℕ} (hk : 2 ≤ k) : (k : ℝ) ≤ (2 : ℝ) ^ k - 2 := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have hpow : (2 : ℝ) ^ (n + 1) = 2 * (2 : ℝ) ^ n := by
        rw [pow_succ]; ring
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      rw [hpow]
      push_cast
      linarith

/-- **Wide balanced block saving.**  If the derivative scale lies in `[N ^ (-5/3), N ^ (-1/3)]`,
both terms of the normalised block bound are at most a constant times `N ^ (-1/(3·2^k))`. -/
theorem block_saving_wide (k N : ℕ) (hk : 2 ≤ k) (hN : 1 ≤ N) (lam : ℝ) (hlam0 : 0 < lam)
    (h1 : lam ≤ (N : ℝ) ^ (-(1 / 3) : ℝ))
    (h2 : (N : ℝ) ^ (-(5 / 3) : ℝ) ≤ lam) :
    512 * ((4 : ℝ) ^ k * lam) ^ (1 / ((2 : ℝ) ^ k - 2))
        + 512 * (N : ℝ) ^ (-(4 / (2 : ℝ) ^ k)) * lam ^ (-(2 / (2 : ℝ) ^ k))
      ≤ 2560 * (N : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ k))) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le one_pos hN1
  have h2k : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have h4le : (4 : ℝ) ≤ (2 : ℝ) ^ k := by
    calc (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
      _ ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) hk
  have h2ksub : (0 : ℝ) < (2 : ℝ) ^ k - 2 := by linarith
  set e : ℝ := 1 / ((2 : ℝ) ^ k - 2) with hedef
  have he0 : 0 < e := by rw [hedef]; positivity
  have hesmall : 1 / (2 : ℝ) ^ k ≤ e := by
    rw [hedef]
    exact one_div_le_one_div_of_le h2ksub (by linarith)
  -- first term
  have hterm1 : ((4 : ℝ) ^ k * lam) ^ e ≤ 4 * (N : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ k))) := by
    have hpos : (0 : ℝ) < (4 : ℝ) ^ k * lam := by positivity
    have hstep : ((4 : ℝ) ^ k * lam) ^ e ≤ ((4 : ℝ) ^ k * (N : ℝ) ^ (-(1 / 3) : ℝ)) ^ e := by
      refine Real.rpow_le_rpow hpos.le ?_ he0.le
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    have hsplit : ((4 : ℝ) ^ k * (N : ℝ) ^ (-(1 / 3) : ℝ)) ^ e
        = ((4 : ℝ) ^ k) ^ e * ((N : ℝ) ^ (-(1 / 3) : ℝ)) ^ e :=
      Real.mul_rpow (by positivity) (Real.rpow_nonneg hN0.le _)
    have hfour : ((4 : ℝ) ^ k) ^ e ≤ 4 := by
      have hcast : ((4 : ℝ) ^ k) ^ e = (4 : ℝ) ^ ((k : ℝ) * e) := by
        rw [← Real.rpow_natCast (4 : ℝ) k, ← Real.rpow_mul (by norm_num)]
      have hke : (k : ℝ) * e ≤ 1 := by
        rw [hedef]
        rw [mul_one_div, div_le_one h2ksub]
        exact nat_le_two_pow_sub_two hk
      rw [hcast]
      calc (4 : ℝ) ^ ((k : ℝ) * e) ≤ (4 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hke
        _ = 4 := Real.rpow_one 4
    have hNpart : ((N : ℝ) ^ (-(1 / 3) : ℝ)) ^ e ≤ (N : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ k))) := by
      rw [← Real.rpow_mul hN0.le]
      refine Real.rpow_le_rpow_of_exponent_le hN1 ?_
      have : 1 / (3 * (2 : ℝ) ^ k) ≤ 1 / 3 * e := by
        rw [show (1 : ℝ) / (3 * (2 : ℝ) ^ k) = 1 / 3 * (1 / (2 : ℝ) ^ k) by ring]
        exact mul_le_mul_of_nonneg_left hesmall (by norm_num)
      linarith
    have hNpart0 : (0 : ℝ) ≤ ((N : ℝ) ^ (-(1 / 3) : ℝ)) ^ e :=
      Real.rpow_nonneg (Real.rpow_nonneg hN0.le _) _
    calc ((4 : ℝ) ^ k * lam) ^ e
        ≤ ((4 : ℝ) ^ k) ^ e * ((N : ℝ) ^ (-(1 / 3) : ℝ)) ^ e := hsplit ▸ hstep
      _ ≤ 4 * ((N : ℝ) ^ (-(1 / 3) : ℝ)) ^ e := mul_le_mul_of_nonneg_right hfour hNpart0
      _ ≤ 4 * (N : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ k))) :=
          mul_le_mul_of_nonneg_left hNpart (by norm_num)
  -- second term
  have hterm2 : (N : ℝ) ^ (-(4 / (2 : ℝ) ^ k)) * lam ^ (-(2 / (2 : ℝ) ^ k))
      ≤ (N : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ k))) := by
    have hlamstep : lam ^ (-(2 / (2 : ℝ) ^ k))
        ≤ ((N : ℝ) ^ (-(5 / 3) : ℝ)) ^ (-(2 / (2 : ℝ) ^ k)) := by
      refine Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hN0 _) h2 ?_
      have : (0 : ℝ) < 2 / (2 : ℝ) ^ k := by positivity
      linarith
    have hcollapse : ((N : ℝ) ^ (-(5 / 3) : ℝ)) ^ (-(2 / (2 : ℝ) ^ k))
        = (N : ℝ) ^ ((10 / 3) / (2 : ℝ) ^ k) := by
      rw [← Real.rpow_mul hN0.le]
      ring_nf
    have hfinal : (N : ℝ) ^ (-(4 / (2 : ℝ) ^ k)) * (N : ℝ) ^ ((10 / 3) / (2 : ℝ) ^ k)
        ≤ (N : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ k))) := by
      rw [← Real.rpow_add hN0]
      refine Real.rpow_le_rpow_of_exponent_le hN1 ?_
      have hpos : (0 : ℝ) < (1 / 3) / (2 : ℝ) ^ k := by positivity
      have hid : -(1 / (3 * (2 : ℝ) ^ k))
          - (-(4 / (2 : ℝ) ^ k) + (10 / 3) / (2 : ℝ) ^ k) = (1 / 3) / (2 : ℝ) ^ k := by
        field_simp
        ring
      linarith
    calc (N : ℝ) ^ (-(4 / (2 : ℝ) ^ k)) * lam ^ (-(2 / (2 : ℝ) ^ k))
        ≤ (N : ℝ) ^ (-(4 / (2 : ℝ) ^ k)) * (N : ℝ) ^ ((10 / 3) / (2 : ℝ) ^ k) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hN0.le _)
          exact hcollapse ▸ hlamstep
      _ ≤ (N : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ k))) := hfinal
  linarith [hterm1, hterm2]

end RHTower.Sieve
