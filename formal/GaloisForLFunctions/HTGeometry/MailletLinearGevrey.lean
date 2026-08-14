import GaloisForLFunctions.HTGeometry.ShiftPolynomialBounds

/-!
# Maillet's theorem for linear equations with convergent coefficients

A formal solution of a linear differential equation

```text
L F = G ,      L = ∑_{j ≤ m} B_j θ^j ,   θ = t d/dt ,
```

with convergent `B_j` and `G` is Gevrey of order `m - deg Φ_0`, where `Φ_0` is the shift polynomial
at shift zero.  The exponent is exactly the drop between the order of the operator and the degree of
its indicial polynomial.

The proof is the coefficient recursion.  Dividing it by `Φ_0(n)`, whose modulus is at least
`c (n+1)^{deg Φ_0}` for large `n`, gives

```text
‖f_n‖ ≤ (1/(c (n+1)^{d})) ( ‖g_n‖ + ∑_{k < n} ‖Φ_{n-k}(k)‖ ‖f_k‖ ) .
```

Each factor of the sum is geometric in the shift `n - k`, while `(k+1)^m (k!/n!)^r ≤ (n+1)^d` for
`k < n`, because `k+1 ≤ n` and `k!/n! ≤ 1/n`.  The whole sum therefore contributes a geometric
series times `(n+1)^d`, which the lower bound on `Φ_0` absorbs once the geometric ratio is small
enough.
-/

open PowerSeries
open scoped Nat

namespace GaloisForLFunctions.HTGeometry

/-! ### The factorial ratio below the top index -/

theorem factorial_ratio_le {n k : ℕ} (hk : k < n) :
    ((k ! : ℝ)) / (n ! : ℝ) ≤ 1 / (n : ℝ) := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le k) hk
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hfacpos : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hkle : k ! ≤ (n - 1)! := Nat.factorial_le (by omega)
  have hkle' : ((k ! : ℕ) : ℝ) ≤ (((n - 1)! : ℕ) : ℝ) := by exact_mod_cast hkle
  have hsplit : (n ! : ℝ) = (n : ℝ) * (((n - 1)! : ℕ) : ℝ) := by
    obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel, Nat.factorial_succ]
    push_cast
    ring
  rw [div_le_div_iff₀ hfacpos hnpos]
  rw [hsplit]
  nlinarith [hkle', Nat.cast_nonneg (α := ℝ) ((n - 1)!), hnpos]

/-! ### The factorial gap over a shift -/

/-- Over a shift of `n - k` steps the factorial gains at least the factor `(k+1)^{n-k}`. -/
theorem pow_succ_mul_factorial_le_factorial (k : ℕ) : ∀ n : ℕ, k ≤ n →
    (k + 1) ^ (n - k) * k ! ≤ n ! := by
  intro n
  induction n with
  | zero =>
      intro h
      have hk : k = 0 := Nat.le_zero.mp h
      subst hk
      simp
  | succ n ih =>
      intro h
      rcases Nat.lt_or_ge k (n + 1) with hk | hk
      · have hkn : k ≤ n := by omega
        have hprev := ih hkn
        have hstep : (k + 1) ^ (n + 1 - k) * k ! = (k + 1) * ((k + 1) ^ (n - k) * k !) := by
          rw [show n + 1 - k = (n - k) + 1 by omega, pow_succ]
          ring
        rw [hstep, Nat.factorial_succ]
        calc (k + 1) * ((k + 1) ^ (n - k) * k !) ≤ (k + 1) * n ! :=
              Nat.mul_le_mul_left _ hprev
          _ ≤ (n + 1) * n ! := Nat.mul_le_mul_right _ (by omega)
      · have hk' : k = n + 1 := by omega
        subst hk'
        simp

theorem factorial_ratio_pow_le {n k : ℕ} (hk : k < n) :
    ((k ! : ℝ)) / (n ! : ℝ) ≤ (((k : ℝ) + 1) ^ (n - k))⁻¹ := by
  have hfacn : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hpow : (0 : ℝ) < ((k : ℝ) + 1) ^ (n - k) := by positivity
  have hkey : (((k : ℝ) + 1) ^ (n - k)) * (k ! : ℝ) ≤ (n ! : ℝ) := by
    have h := pow_succ_mul_factorial_le_factorial k n (le_of_lt hk)
    have h' : (((k + 1) ^ (n - k) * k ! : ℕ) : ℝ) ≤ ((n ! : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    exact h'
  rw [inv_eq_one_div, div_le_div_iff₀ hfacn hpow]
  nlinarith [hkey]

/-- **The Newton form of the shift factor bound.** -/
theorem shiftFactor_newton_le {d : ℕ} {r : ℝ} (hr : 0 ≤ r) {n k : ℕ} (hk : k < n) :
    ((k : ℝ) + 1) ^ ((d : ℝ) + r * (((n - k : ℕ)) : ℝ)) * ((k ! : ℝ) ^ r / (n ! : ℝ) ^ r)
      ≤ ((n : ℝ) + 1) ^ d := by
  have hbase : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hbase1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hfacn : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hfack : (0 : ℝ) < (k ! : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hratio : (k ! : ℝ) ^ r / (n ! : ℝ) ^ r
      ≤ ((k : ℝ) + 1) ^ (-(r * (((n - k : ℕ)) : ℝ))) := by
    have hstep : (k ! : ℝ) ^ r / (n ! : ℝ) ^ r = ((k ! : ℝ) / (n ! : ℝ)) ^ r :=
      (Real.div_rpow (le_of_lt hfack) (le_of_lt hfacn) r).symm
    have hpowinv : ((((k : ℝ) + 1) ^ (n - k))⁻¹) ^ r
        = ((k : ℝ) + 1) ^ (-(r * (((n - k : ℕ)) : ℝ))) := by
      rw [← Real.rpow_natCast ((k : ℝ) + 1) (n - k), ← Real.rpow_neg (le_of_lt hbase),
        ← Real.rpow_mul (le_of_lt hbase)]
      congr 1
      ring
    rw [hstep, ← hpowinv]
    exact Real.rpow_le_rpow (by positivity) (factorial_ratio_pow_le hk) hr
  calc ((k : ℝ) + 1) ^ ((d : ℝ) + r * (((n - k : ℕ)) : ℝ)) * ((k ! : ℝ) ^ r / (n ! : ℝ) ^ r)
      ≤ ((k : ℝ) + 1) ^ ((d : ℝ) + r * (((n - k : ℕ)) : ℝ))
          * ((k : ℝ) + 1) ^ (-(r * (((n - k : ℕ)) : ℝ))) := by
        refine mul_le_mul_of_nonneg_left hratio ?_
        exact le_of_lt (Real.rpow_pos_of_pos hbase _)
    _ = ((k : ℝ) + 1) ^ ((d : ℝ)) := by
        rw [← Real.rpow_add hbase]
        congr 1
        ring
    _ = ((k : ℝ) + 1) ^ d := Real.rpow_natCast _ _
    _ ≤ ((n : ℝ) + 1) ^ d := by
        refine pow_le_pow_left₀ (by positivity) ?_ d
        have : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_of_lt hk
        linarith

/-! ### The Gevrey exponent absorbs the shift factor -/

theorem cast_sub_le {m d : ℕ} : (m : ℝ) - ((m - d : ℕ) : ℝ) ≤ (d : ℝ) := by
  by_cases h : d ≤ m
  · rw [Nat.cast_sub h]
    linarith
  · push Not at h
    have hz : m - d = 0 := by omega
    rw [hz]
    simp only [Nat.cast_zero, sub_zero]
    exact_mod_cast le_of_lt h

/-- **The shift factor of the recursion is dominated by the indicial power.** -/
theorem shiftFactor_le {m d : ℕ} {n k : ℕ} (hk : k < n) :
    ((k : ℝ) + 1) ^ m * ((k ! : ℝ) ^ (((m - d : ℕ) : ℝ)) / (n ! : ℝ) ^ (((m - d : ℕ) : ℝ)))
      ≤ ((n : ℝ) + 1) ^ d := by
  set r : ℝ := ((m - d : ℕ) : ℝ) with hrdef
  have hr0 : 0 ≤ r := Nat.cast_nonneg _
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le k) hk
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hfacn : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hfack : (0 : ℝ) < (k ! : ℝ) := by exact_mod_cast Nat.factorial_pos k
  -- the polynomial factor
  have hpoly : ((k : ℝ) + 1) ^ m ≤ (n : ℝ) ^ m := by
    refine pow_le_pow_left₀ (by positivity) ?_ m
    have : (k : ℝ) + 1 ≤ (n : ℝ) := by
      have : (k : ℕ) + 1 ≤ n := hk
      exact_mod_cast this
    exact this
  -- the factorial factor
  have hfacratio : (k ! : ℝ) ^ r / (n ! : ℝ) ^ r ≤ 1 / (n : ℝ) ^ r := by
    rw [← Real.div_rpow (le_of_lt hfack) (le_of_lt hfacn),
      ← Real.one_rpow r, ← Real.div_rpow (by norm_num) (le_of_lt hnpos)]
    exact Real.rpow_le_rpow (by positivity) (factorial_ratio_le hk) hr0
  have hnr : (0 : ℝ) < (n : ℝ) ^ r := Real.rpow_pos_of_pos hnpos r
  calc ((k : ℝ) + 1) ^ m * ((k ! : ℝ) ^ r / (n ! : ℝ) ^ r)
      ≤ (n : ℝ) ^ m * (1 / (n : ℝ) ^ r) := by
        refine mul_le_mul hpoly hfacratio (by positivity) (by positivity)
    _ = (n : ℝ) ^ ((m : ℝ) - r) := by
        rw [Real.rpow_sub hnpos, ← Real.rpow_natCast (n : ℝ) m]
        field_simp
    _ ≤ (n : ℝ) ^ ((d : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hn1 cast_sub_le
    _ = (n : ℝ) ^ d := Real.rpow_natCast _ _
    _ ≤ ((n : ℝ) + 1) ^ d := by
        refine pow_le_pow_left₀ (by positivity) (by linarith) d

/-! ### The geometric tail -/

theorem geom_shift_sum_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    ∑ k ∈ Finset.range n, q ^ (n - k) ≤ q / (1 - q) := by
  classical
  have hrefl := Finset.sum_range_reflect (fun k : ℕ => q ^ (n - k)) n
  have hshape : ∑ k ∈ Finset.range n, q ^ (n - (n - 1 - k)) = ∑ k ∈ Finset.range n, q ^ (k + 1) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkn : k < n := Finset.mem_range.mp hk
    congr 1
    omega
  rw [hshape] at hrefl
  rw [← hrefl]
  have hden : (0 : ℝ) < 1 - q := by linarith
  have hne1 : q ≠ 1 := ne_of_lt hq1
  have hgeom : ∑ k ∈ Finset.range n, q ^ k ≤ 1 / (1 - q) := by
    have hval : ∑ k ∈ Finset.range n, q ^ k = (1 - q ^ n) / (1 - q) := by
      rw [geom_sum_eq hne1]
      have hsub : q - 1 ≠ 0 := sub_ne_zero.mpr hne1
      field_simp
      ring
    rw [hval, div_le_div_iff₀ hden hden]
    nlinarith [pow_nonneg hq0 n, hden]
  calc ∑ k ∈ Finset.range n, q ^ (k + 1) = q * ∑ k ∈ Finset.range n, q ^ k := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by rw [pow_succ]; ring
    _ ≤ q * (1 / (1 - q)) := mul_le_mul_of_nonneg_left hgeom hq0
    _ = q / (1 - q) := by ring

/-! ### Maillet's theorem -/

set_option maxHeartbeats 1600000 in
/-- **Maillet's theorem for a linear equation with convergent coefficients.**  Every formal solution
of `L F = G` is Gevrey of order `m - deg Φ_0`, the drop between the order of the operator and the
degree of its indicial polynomial. -/
theorem isGevreySeries_of_eulerLinearOp_eq {m : ℕ} (B : Fin (m + 1) → PowerSeries ℂ)
    (hB : ∀ j, IsGevreySeries 0 (B j)) (hΦ : shiftPolynomial B 0 ≠ 0)
    {F G : PowerSeries ℂ} (hG : IsGevreySeries 0 G)
    (hsol : eulerLinearOp B F = G) :
    IsGevreySeries (((m - (shiftPolynomial B 0).natDegree : ℕ) : ℝ)) F := by
  classical
  set d : ℕ := (shiftPolynomial B 0).natDegree with hd
  set r : ℝ := ((m - d : ℕ) : ℝ) with hrdef
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  obtain ⟨c, hc, N₀, hlow⟩ := exists_lower_bound_eval_natCast (shiftPolynomial B 0) hΦ
  obtain ⟨Cb, ρ, hCb, hρ, hshift⟩ := exists_bound_shiftPolynomial B hB
  obtain ⟨Cg, γ, hCg, hγ, hgb⟩ := hG
  have hc0 : (0 : ℝ) ≤ c := le_of_lt hc
  have hCb0 : (0 : ℝ) ≤ Cb := le_of_lt hCb
  have hρ0 : (0 : ℝ) ≤ ρ := le_of_lt hρ
  set A : ℝ := max γ 1 + ρ * (4 * Cb / c + 2) with hAdef
  have hrhs0 : (0 : ℝ) < ρ * (4 * Cb / c + 2) := by positivity
  have hmax1 : (1 : ℝ) ≤ max γ 1 := le_max_right _ _
  have hApos : 0 < A := by rw [hAdef]; linarith
  have hA0 : (0 : ℝ) ≤ A := le_of_lt hApos
  have hA1 : (1 : ℝ) ≤ A := by rw [hAdef]; linarith
  have hγA : γ ≤ A := by
    have h1 : γ ≤ max γ 1 := le_max_left _ _
    rw [hAdef]; linarith
  have hρA : ρ * (4 * Cb / c + 2) ≤ A := by rw [hAdef]; linarith
  set q : ℝ := ρ / A with hqdef
  have hq0 : 0 ≤ q := by rw [hqdef]; positivity
  have hCbc : (0 : ℝ) < 4 * Cb / c := by positivity
  have h2ρ : 2 * ρ ≤ A := by
    have hstep : ρ * 2 ≤ ρ * (4 * Cb / c + 2) := by nlinarith [hρ, hCbc]
    linarith [hρA]
  have hqhalf : q ≤ 1 / 2 := by
    rw [hqdef, div_le_iff₀ hApos]
    linarith
  have hq1 : q < 1 := by linarith
  have hone_sub : (1 : ℝ) / 2 ≤ 1 - q := by linarith
  have hqbound : Cb * (q / (1 - q)) ≤ c / 2 := by
    have hden : (0 : ℝ) < 1 - q := by linarith
    have hstep : q / (1 - q) ≤ 2 * q := by
      rw [div_le_iff₀ hden]
      nlinarith [hq0, hone_sub]
    have hq2 : 2 * q ≤ c / (2 * Cb) := by
      have hform : 2 * q = (2 * ρ) / A := by rw [hqdef]; ring
      rw [hform, div_le_div_iff₀ hApos (by positivity : (0 : ℝ) < 2 * Cb)]
      have hcA : c * (ρ * (4 * Cb / c + 2)) ≤ c * A :=
        mul_le_mul_of_nonneg_left hρA hc0
      have hexp : c * (ρ * (4 * Cb / c + 2)) = 4 * ρ * Cb + 2 * c * ρ := by
        field_simp
      nlinarith [hcA, hexp, hρ, hc]
    calc Cb * (q / (1 - q)) ≤ Cb * (2 * q) := mul_le_mul_of_nonneg_left hstep hCb0
      _ ≤ Cb * (c / (2 * Cb)) := mul_le_mul_of_nonneg_left hq2 hCb0
      _ = c / 2 := by field_simp
  set N : ℕ := max N₀ 1 with hNdef
  set C : ℝ := 2 * Cg / c
      + (∑ k ∈ Finset.range N, ‖PowerSeries.coeff k F‖ / (A ^ k * (k ! : ℝ) ^ r)) + 1 with hCdef
  have hsumnn : (0 : ℝ) ≤ ∑ k ∈ Finset.range N, ‖PowerSeries.coeff k F‖ / (A ^ k * (k ! : ℝ) ^ r) :=
    Finset.sum_nonneg fun k _ => by positivity
  have hCgc : (0 : ℝ) < 2 * Cg / c := by positivity
  have hCpos : 0 < C := by rw [hCdef]; linarith
  have hC0 : (0 : ℝ) ≤ C := le_of_lt hCpos
  have hCge : 2 * Cg / c ≤ C := by rw [hCdef]; linarith
  have hCg' : Cg ≤ c / 2 * C := by
    have h1 : c / 2 * (2 * Cg / c) = Cg := by field_simp
    calc Cg = c / 2 * (2 * Cg / c) := h1.symm
      _ ≤ c / 2 * C := mul_le_mul_of_nonneg_left hCge (by linarith)
  refine ⟨C, A, hCpos, hApos, ?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hfacpos : (0 : ℝ) < (n ! : ℝ) ^ r := factorial_rpow_pos n r
    have hApown : (0 : ℝ) < A ^ n := pow_pos hApos n
    have hnn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    by_cases hnN : n < N
    · have hmem : n ∈ Finset.range N := Finset.mem_range.mpr hnN
      have hterm : ‖PowerSeries.coeff n F‖ / (A ^ n * (n ! : ℝ) ^ r)
          ≤ ∑ k ∈ Finset.range N, ‖PowerSeries.coeff k F‖ / (A ^ k * (k ! : ℝ) ^ r) :=
        Finset.single_le_sum
          (f := fun k : ℕ => ‖PowerSeries.coeff k F‖ / (A ^ k * (k ! : ℝ) ^ r))
          (fun k _ => by positivity) hmem
      have hle : ‖PowerSeries.coeff n F‖ / (A ^ n * (n ! : ℝ) ^ r) ≤ C := by
        rw [hCdef]; linarith
      rw [div_le_iff₀ (by positivity)] at hle
      calc ‖PowerSeries.coeff n F‖ ≤ C * (A ^ n * (n ! : ℝ) ^ r) := hle
        _ = C * A ^ n * (n ! : ℝ) ^ r := by ring
    · push Not at hnN
      have hn1 : 1 ≤ n := le_trans (le_max_right N₀ 1) hnN
      have hN₀n : N₀ ≤ n := le_trans (le_max_left N₀ 1) hnN
      have hΦlow : c * ((n : ℝ) + 1) ^ d ≤ ‖(shiftPolynomial B 0).eval ((n : ℕ) : ℂ)‖ :=
        hlow n hN₀n
      have hpowd : (0 : ℝ) < ((n : ℝ) + 1) ^ d := by positivity
      have hΦpos : (0 : ℝ) < c * ((n : ℝ) + 1) ^ d := mul_pos hc hpowd
      have hrec := shiftPolynomial_zero_mul_coeff B F n
      rw [hsol] at hrec
      have hnormrec : ‖(shiftPolynomial B 0).eval ((n : ℕ) : ℂ)‖ * ‖PowerSeries.coeff n F‖
          ≤ ‖PowerSeries.coeff n G‖
            + ∑ k ∈ Finset.range n,
                ‖(shiftPolynomial B (n - k)).eval ((k : ℕ) : ℂ)‖ * ‖PowerSeries.coeff k F‖ := by
        have hleft : ‖(shiftPolynomial B 0).eval ((n : ℕ) : ℂ) * PowerSeries.coeff n F‖
            = ‖(shiftPolynomial B 0).eval ((n : ℕ) : ℂ)‖ * ‖PowerSeries.coeff n F‖ := norm_mul _ _
        have hA' : ‖(shiftPolynomial B 0).eval ((n : ℕ) : ℂ) * PowerSeries.coeff n F‖
            ≤ ‖PowerSeries.coeff n G‖
              + ‖∑ k ∈ Finset.range n,
                  (shiftPolynomial B (n - k)).eval ((k : ℕ) : ℂ) * PowerSeries.coeff k F‖ := by
          rw [hrec]
          exact norm_sub_le _ _
        have hB' : ‖∑ k ∈ Finset.range n,
              (shiftPolynomial B (n - k)).eval ((k : ℕ) : ℂ) * PowerSeries.coeff k F‖
            ≤ ∑ k ∈ Finset.range n,
                ‖(shiftPolynomial B (n - k)).eval ((k : ℕ) : ℂ)‖ * ‖PowerSeries.coeff k F‖ := by
          refine le_trans (norm_sum_le _ _) ?_
          exact le_of_eq (Finset.sum_congr rfl fun k _ => norm_mul _ _)
        rw [hleft] at hA'
        linarith
      have h3 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ d := one_le_pow₀ (by linarith)
      have h4 : (1 : ℝ) ≤ (n ! : ℝ) ^ r := by
        have := Real.rpow_le_rpow_of_exponent_le (one_le_factorial_cast n) hr0
        simpa using this
      have hGterm : ‖PowerSeries.coeff n G‖
          ≤ c / 2 * ((n : ℝ) + 1) ^ d * (C * A ^ n * (n ! : ℝ) ^ r) := by
        have h1 : ‖PowerSeries.coeff n G‖ ≤ Cg * γ ^ n := by
          have := hgb n
          simpa using this
        have h2 : γ ^ n ≤ A ^ n := pow_le_pow_left₀ (le_of_lt hγ) hγA n
        have h5 : Cg * γ ^ n ≤ (c / 2 * C) * A ^ n :=
          mul_le_mul hCg' h2 (pow_nonneg (le_of_lt hγ) n)
            (mul_nonneg (by linarith) hC0)
        have hbase : (0 : ℝ) ≤ c / 2 * C * A ^ n :=
          mul_nonneg (mul_nonneg (by linarith) hC0) (le_of_lt hApown)
        have hchain : (c / 2 * C) * A ^ n
            ≤ c / 2 * ((n : ℝ) + 1) ^ d * (C * A ^ n * (n ! : ℝ) ^ r) := by
          calc (c / 2 * C) * A ^ n = (c / 2 * C * A ^ n) * 1 := by ring
            _ ≤ (c / 2 * C * A ^ n) * (((n : ℝ) + 1) ^ d * (n ! : ℝ) ^ r) := by
                refine mul_le_mul_of_nonneg_left ?_ hbase
                nlinarith [h3, h4]
            _ = c / 2 * ((n : ℝ) + 1) ^ d * (C * A ^ n * (n ! : ℝ) ^ r) := by ring
        linarith
      have hconv : ∑ k ∈ Finset.range n,
            ‖(shiftPolynomial B (n - k)).eval ((k : ℕ) : ℂ)‖ * ‖PowerSeries.coeff k F‖
          ≤ c / 2 * ((n : ℝ) + 1) ^ d * (C * A ^ n * (n ! : ℝ) ^ r) := by
        have hbig0 : (0 : ℝ) ≤ Cb * (C * A ^ n * (n ! : ℝ) ^ r) * ((n : ℝ) + 1) ^ d :=
          mul_nonneg (mul_nonneg hCb0
            (mul_nonneg (mul_nonneg hC0 (le_of_lt hApown)) (le_of_lt hfacpos)))
            (le_of_lt hpowd)
        have hstep : ∀ k ∈ Finset.range n,
            ‖(shiftPolynomial B (n - k)).eval ((k : ℕ) : ℂ)‖ * ‖PowerSeries.coeff k F‖
              ≤ (Cb * (C * A ^ n * (n ! : ℝ) ^ r) * ((n : ℝ) + 1) ^ d) * q ^ (n - k) := by
          intro k hk
          have hkn : k < n := Finset.mem_range.mp hk
          have h1 : ‖(shiftPolynomial B (n - k)).eval ((k : ℕ) : ℂ)‖
              ≤ Cb * ρ ^ (n - k) * ((k : ℝ) + 1) ^ m := hshift (n - k) k
          have h2 : ‖PowerSeries.coeff k F‖ ≤ C * A ^ k * (k ! : ℝ) ^ r := ih k hkn
          have hfack : (0 : ℝ) < (k ! : ℝ) ^ r := factorial_rpow_pos k r
          have hk0 : (0 : ℝ) ≤ Cb * ρ ^ (n - k) * ((k : ℝ) + 1) ^ m :=
            mul_nonneg (mul_nonneg hCb0 (pow_nonneg hρ0 _))
              (pow_nonneg (by positivity) _)
          have hprod : (Cb * ρ ^ (n - k) * ((k : ℝ) + 1) ^ m) * (C * A ^ k * (k ! : ℝ) ^ r)
              = (Cb * (C * A ^ n * (n ! : ℝ) ^ r)) * (q ^ (n - k)
                  * (((k : ℝ) + 1) ^ m * ((k ! : ℝ) ^ r / (n ! : ℝ) ^ r))) := by
            rw [hqdef, div_pow]
            have hApow : A ^ n = A ^ (n - k) * A ^ k := by
              rw [← pow_add]
              congr 1
              omega
            rw [hApow]
            field_simp
          have hfactor : ((k : ℝ) + 1) ^ m * ((k ! : ℝ) ^ r / (n ! : ℝ) ^ r)
              ≤ ((n : ℝ) + 1) ^ d := shiftFactor_le hkn
          have hqk0 : (0 : ℝ) ≤ q ^ (n - k) := pow_nonneg hq0 _
          have hleft0 : (0 : ℝ) ≤ Cb * (C * A ^ n * (n ! : ℝ) ^ r) :=
            mul_nonneg hCb0 (mul_nonneg (mul_nonneg hC0 (le_of_lt hApown)) (le_of_lt hfacpos))
          calc ‖(shiftPolynomial B (n - k)).eval ((k : ℕ) : ℂ)‖ * ‖PowerSeries.coeff k F‖
              ≤ (Cb * ρ ^ (n - k) * ((k : ℝ) + 1) ^ m) * (C * A ^ k * (k ! : ℝ) ^ r) :=
                mul_le_mul h1 h2 (norm_nonneg _) hk0
            _ = (Cb * (C * A ^ n * (n ! : ℝ) ^ r)) * (q ^ (n - k)
                  * (((k : ℝ) + 1) ^ m * ((k ! : ℝ) ^ r / (n ! : ℝ) ^ r))) := hprod
            _ ≤ (Cb * (C * A ^ n * (n ! : ℝ) ^ r)) * (q ^ (n - k) * ((n : ℝ) + 1) ^ d) := by
                refine mul_le_mul_of_nonneg_left ?_ hleft0
                exact mul_le_mul_of_nonneg_left hfactor hqk0
            _ = (Cb * (C * A ^ n * (n ! : ℝ) ^ r) * ((n : ℝ) + 1) ^ d) * q ^ (n - k) := by ring
        calc ∑ k ∈ Finset.range n,
              ‖(shiftPolynomial B (n - k)).eval ((k : ℕ) : ℂ)‖ * ‖PowerSeries.coeff k F‖
            ≤ ∑ k ∈ Finset.range n,
                (Cb * (C * A ^ n * (n ! : ℝ) ^ r) * ((n : ℝ) + 1) ^ d) * q ^ (n - k) :=
              Finset.sum_le_sum hstep
          _ = (Cb * (C * A ^ n * (n ! : ℝ) ^ r) * ((n : ℝ) + 1) ^ d)
                * ∑ k ∈ Finset.range n, q ^ (n - k) := by
              rw [Finset.mul_sum]
          _ ≤ (Cb * (C * A ^ n * (n ! : ℝ) ^ r) * ((n : ℝ) + 1) ^ d) * (q / (1 - q)) :=
              mul_le_mul_of_nonneg_left (geom_shift_sum_le hq0 hq1 n) hbig0
          _ = (Cb * (q / (1 - q)))
                * ((C * A ^ n * (n ! : ℝ) ^ r) * ((n : ℝ) + 1) ^ d) := by ring
          _ ≤ (c / 2) * ((C * A ^ n * (n ! : ℝ) ^ r) * ((n : ℝ) + 1) ^ d) := by
              refine mul_le_mul_of_nonneg_right hqbound ?_
              exact mul_nonneg (mul_nonneg (mul_nonneg hC0 (le_of_lt hApown)) (le_of_lt hfacpos))
                (le_of_lt hpowd)
          _ = c / 2 * ((n : ℝ) + 1) ^ d * (C * A ^ n * (n ! : ℝ) ^ r) := by ring
      have hmid : c * ((n : ℝ) + 1) ^ d * ‖PowerSeries.coeff n F‖
          ≤ ‖(shiftPolynomial B 0).eval ((n : ℕ) : ℂ)‖ * ‖PowerSeries.coeff n F‖ :=
        mul_le_mul_of_nonneg_right hΦlow (norm_nonneg _)
      have hsum2 : ‖PowerSeries.coeff n G‖
            + ∑ k ∈ Finset.range n,
                ‖(shiftPolynomial B (n - k)).eval ((k : ℕ) : ℂ)‖ * ‖PowerSeries.coeff k F‖
          ≤ c * ((n : ℝ) + 1) ^ d * (C * A ^ n * (n ! : ℝ) ^ r) := by
        have hadd := add_le_add hGterm hconv
        have heq : c / 2 * ((n : ℝ) + 1) ^ d * (C * A ^ n * (n ! : ℝ) ^ r)
            + c / 2 * ((n : ℝ) + 1) ^ d * (C * A ^ n * (n ! : ℝ) ^ r)
            = c * ((n : ℝ) + 1) ^ d * (C * A ^ n * (n ! : ℝ) ^ r) := by ring
        linarith [hadd, heq]
      have hfinal : c * ((n : ℝ) + 1) ^ d * ‖PowerSeries.coeff n F‖
          ≤ c * ((n : ℝ) + 1) ^ d * (C * A ^ n * (n ! : ℝ) ^ r) :=
        le_trans (le_trans hmid hnormrec) hsum2
      exact le_of_mul_le_mul_left hfinal hΦpos

set_option maxHeartbeats 1600000 in
/-- **Maillet's theorem in Newton-polygon form.**  If every coefficient of the operator present at
shift `μ ≥ 1` has index at most `deg Φ_0 + r μ`, then every formal solution of `L F = G` is Gevrey
of order `r`.  The hypothesis says exactly that the Newton polygon has no slope ratio above `r`. -/
theorem isGevreySeries_of_eulerLinearOp_eq_newton {m : ℕ} {r : ℝ} (hr : 0 ≤ r)
    (B : Fin (m + 1) → PowerSeries ℂ)
    (hB : ∀ j, IsGevreySeries 0 (B j)) (hΦ : shiftPolynomial B 0 ≠ 0)
    (hdeg : ∀ (μ : ℕ) (j : Fin (m + 1)), 1 ≤ μ → PowerSeries.coeff μ (B j) ≠ 0 →
      ((j : ℕ) : ℝ) ≤ (((shiftPolynomial B 0).natDegree : ℕ) : ℝ) + r * μ)
    {F G : PowerSeries ℂ} (hG : IsGevreySeries 0 G)
    (hsol : eulerLinearOp B F = G) :
    IsGevreySeries r F := by
  classical
  set d : ℕ := (shiftPolynomial B 0).natDegree with hd
  have hr0 : (0 : ℝ) ≤ r := hr
  obtain ⟨c, hc, N₀, hlow⟩ := exists_lower_bound_eval_natCast (shiftPolynomial B 0) hΦ
  obtain ⟨Cb, ρ, hCb, hρ, hshift⟩ := exists_bound_shiftPolynomial_newton (d := d) (r := r) B hB hdeg
  obtain ⟨Cg, γ, hCg, hγ, hgb⟩ := hG
  have hc0 : (0 : ℝ) ≤ c := le_of_lt hc
  have hCb0 : (0 : ℝ) ≤ Cb := le_of_lt hCb
  have hρ0 : (0 : ℝ) ≤ ρ := le_of_lt hρ
  set A : ℝ := max γ 1 + ρ * (4 * Cb / c + 2) with hAdef
  have hrhs0 : (0 : ℝ) < ρ * (4 * Cb / c + 2) := by positivity
  have hmax1 : (1 : ℝ) ≤ max γ 1 := le_max_right _ _
  have hApos : 0 < A := by rw [hAdef]; linarith
  have hA0 : (0 : ℝ) ≤ A := le_of_lt hApos
  have hA1 : (1 : ℝ) ≤ A := by rw [hAdef]; linarith
  have hγA : γ ≤ A := by
    have h1 : γ ≤ max γ 1 := le_max_left _ _
    rw [hAdef]; linarith
  have hρA : ρ * (4 * Cb / c + 2) ≤ A := by rw [hAdef]; linarith
  set q : ℝ := ρ / A with hqdef
  have hq0 : 0 ≤ q := by rw [hqdef]; positivity
  have hCbc : (0 : ℝ) < 4 * Cb / c := by positivity
  have h2ρ : 2 * ρ ≤ A := by
    have hstep : ρ * 2 ≤ ρ * (4 * Cb / c + 2) := by nlinarith [hρ, hCbc]
    linarith [hρA]
  have hqhalf : q ≤ 1 / 2 := by
    rw [hqdef, div_le_iff₀ hApos]
    linarith
  have hq1 : q < 1 := by linarith
  have hone_sub : (1 : ℝ) / 2 ≤ 1 - q := by linarith
  have hqbound : Cb * (q / (1 - q)) ≤ c / 2 := by
    have hden : (0 : ℝ) < 1 - q := by linarith
    have hstep : q / (1 - q) ≤ 2 * q := by
      rw [div_le_iff₀ hden]
      nlinarith [hq0, hone_sub]
    have hq2 : 2 * q ≤ c / (2 * Cb) := by
      have hform : 2 * q = (2 * ρ) / A := by rw [hqdef]; ring
      rw [hform, div_le_div_iff₀ hApos (by positivity : (0 : ℝ) < 2 * Cb)]
      have hcA : c * (ρ * (4 * Cb / c + 2)) ≤ c * A :=
        mul_le_mul_of_nonneg_left hρA hc0
      have hexp : c * (ρ * (4 * Cb / c + 2)) = 4 * ρ * Cb + 2 * c * ρ := by
        field_simp
      nlinarith [hcA, hexp, hρ, hc]
    calc Cb * (q / (1 - q)) ≤ Cb * (2 * q) := mul_le_mul_of_nonneg_left hstep hCb0
      _ ≤ Cb * (c / (2 * Cb)) := mul_le_mul_of_nonneg_left hq2 hCb0
      _ = c / 2 := by field_simp
  set N : ℕ := max N₀ 1 with hNdef
  set C : ℝ := 2 * Cg / c
      + (∑ k ∈ Finset.range N, ‖PowerSeries.coeff k F‖ / (A ^ k * (k ! : ℝ) ^ r)) + 1 with hCdef
  have hsumnn : (0 : ℝ) ≤ ∑ k ∈ Finset.range N, ‖PowerSeries.coeff k F‖ / (A ^ k * (k ! : ℝ) ^ r) :=
    Finset.sum_nonneg fun k _ => by positivity
  have hCgc : (0 : ℝ) < 2 * Cg / c := by positivity
  have hCpos : 0 < C := by rw [hCdef]; linarith
  have hC0 : (0 : ℝ) ≤ C := le_of_lt hCpos
  have hCge : 2 * Cg / c ≤ C := by rw [hCdef]; linarith
  have hCg' : Cg ≤ c / 2 * C := by
    have h1 : c / 2 * (2 * Cg / c) = Cg := by field_simp
    calc Cg = c / 2 * (2 * Cg / c) := h1.symm
      _ ≤ c / 2 * C := mul_le_mul_of_nonneg_left hCge (by linarith)
  refine ⟨C, A, hCpos, hApos, ?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hfacpos : (0 : ℝ) < (n ! : ℝ) ^ r := factorial_rpow_pos n r
    have hApown : (0 : ℝ) < A ^ n := pow_pos hApos n
    have hnn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    by_cases hnN : n < N
    · have hmem : n ∈ Finset.range N := Finset.mem_range.mpr hnN
      have hterm : ‖PowerSeries.coeff n F‖ / (A ^ n * (n ! : ℝ) ^ r)
          ≤ ∑ k ∈ Finset.range N, ‖PowerSeries.coeff k F‖ / (A ^ k * (k ! : ℝ) ^ r) :=
        Finset.single_le_sum
          (f := fun k : ℕ => ‖PowerSeries.coeff k F‖ / (A ^ k * (k ! : ℝ) ^ r))
          (fun k _ => by positivity) hmem
      have hle : ‖PowerSeries.coeff n F‖ / (A ^ n * (n ! : ℝ) ^ r) ≤ C := by
        rw [hCdef]; linarith
      rw [div_le_iff₀ (by positivity)] at hle
      calc ‖PowerSeries.coeff n F‖ ≤ C * (A ^ n * (n ! : ℝ) ^ r) := hle
        _ = C * A ^ n * (n ! : ℝ) ^ r := by ring
    · push Not at hnN
      have hn1 : 1 ≤ n := le_trans (le_max_right N₀ 1) hnN
      have hN₀n : N₀ ≤ n := le_trans (le_max_left N₀ 1) hnN
      have hΦlow : c * ((n : ℝ) + 1) ^ d ≤ ‖(shiftPolynomial B 0).eval ((n : ℕ) : ℂ)‖ :=
        hlow n hN₀n
      have hpowd : (0 : ℝ) < ((n : ℝ) + 1) ^ d := by positivity
      have hΦpos : (0 : ℝ) < c * ((n : ℝ) + 1) ^ d := mul_pos hc hpowd
      have hrec := shiftPolynomial_zero_mul_coeff B F n
      rw [hsol] at hrec
      have hnormrec : ‖(shiftPolynomial B 0).eval ((n : ℕ) : ℂ)‖ * ‖PowerSeries.coeff n F‖
          ≤ ‖PowerSeries.coeff n G‖
            + ∑ k ∈ Finset.range n,
                ‖(shiftPolynomial B (n - k)).eval ((k : ℕ) : ℂ)‖ * ‖PowerSeries.coeff k F‖ := by
        have hleft : ‖(shiftPolynomial B 0).eval ((n : ℕ) : ℂ) * PowerSeries.coeff n F‖
            = ‖(shiftPolynomial B 0).eval ((n : ℕ) : ℂ)‖ * ‖PowerSeries.coeff n F‖ := norm_mul _ _
        have hA' : ‖(shiftPolynomial B 0).eval ((n : ℕ) : ℂ) * PowerSeries.coeff n F‖
            ≤ ‖PowerSeries.coeff n G‖
              + ‖∑ k ∈ Finset.range n,
                  (shiftPolynomial B (n - k)).eval ((k : ℕ) : ℂ) * PowerSeries.coeff k F‖ := by
          rw [hrec]
          exact norm_sub_le _ _
        have hB' : ‖∑ k ∈ Finset.range n,
              (shiftPolynomial B (n - k)).eval ((k : ℕ) : ℂ) * PowerSeries.coeff k F‖
            ≤ ∑ k ∈ Finset.range n,
                ‖(shiftPolynomial B (n - k)).eval ((k : ℕ) : ℂ)‖ * ‖PowerSeries.coeff k F‖ := by
          refine le_trans (norm_sum_le _ _) ?_
          exact le_of_eq (Finset.sum_congr rfl fun k _ => norm_mul _ _)
        rw [hleft] at hA'
        linarith
      have h3 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ d := one_le_pow₀ (by linarith)
      have h4 : (1 : ℝ) ≤ (n ! : ℝ) ^ r := by
        have := Real.rpow_le_rpow_of_exponent_le (one_le_factorial_cast n) hr0
        simpa using this
      have hGterm : ‖PowerSeries.coeff n G‖
          ≤ c / 2 * ((n : ℝ) + 1) ^ d * (C * A ^ n * (n ! : ℝ) ^ r) := by
        have h1 : ‖PowerSeries.coeff n G‖ ≤ Cg * γ ^ n := by
          have := hgb n
          simpa using this
        have h2 : γ ^ n ≤ A ^ n := pow_le_pow_left₀ (le_of_lt hγ) hγA n
        have h5 : Cg * γ ^ n ≤ (c / 2 * C) * A ^ n :=
          mul_le_mul hCg' h2 (pow_nonneg (le_of_lt hγ) n)
            (mul_nonneg (by linarith) hC0)
        have hbase : (0 : ℝ) ≤ c / 2 * C * A ^ n :=
          mul_nonneg (mul_nonneg (by linarith) hC0) (le_of_lt hApown)
        have hchain : (c / 2 * C) * A ^ n
            ≤ c / 2 * ((n : ℝ) + 1) ^ d * (C * A ^ n * (n ! : ℝ) ^ r) := by
          calc (c / 2 * C) * A ^ n = (c / 2 * C * A ^ n) * 1 := by ring
            _ ≤ (c / 2 * C * A ^ n) * (((n : ℝ) + 1) ^ d * (n ! : ℝ) ^ r) := by
                refine mul_le_mul_of_nonneg_left ?_ hbase
                nlinarith [h3, h4]
            _ = c / 2 * ((n : ℝ) + 1) ^ d * (C * A ^ n * (n ! : ℝ) ^ r) := by ring
        linarith
      have hconv : ∑ k ∈ Finset.range n,
            ‖(shiftPolynomial B (n - k)).eval ((k : ℕ) : ℂ)‖ * ‖PowerSeries.coeff k F‖
          ≤ c / 2 * ((n : ℝ) + 1) ^ d * (C * A ^ n * (n ! : ℝ) ^ r) := by
        have hbig0 : (0 : ℝ) ≤ Cb * (C * A ^ n * (n ! : ℝ) ^ r) * ((n : ℝ) + 1) ^ d :=
          mul_nonneg (mul_nonneg hCb0
            (mul_nonneg (mul_nonneg hC0 (le_of_lt hApown)) (le_of_lt hfacpos)))
            (le_of_lt hpowd)
        have hstep : ∀ k ∈ Finset.range n,
            ‖(shiftPolynomial B (n - k)).eval ((k : ℕ) : ℂ)‖ * ‖PowerSeries.coeff k F‖
              ≤ (Cb * (C * A ^ n * (n ! : ℝ) ^ r) * ((n : ℝ) + 1) ^ d) * q ^ (n - k) := by
          intro k hk
          have hkn : k < n := Finset.mem_range.mp hk
          have h1 : ‖(shiftPolynomial B (n - k)).eval ((k : ℕ) : ℂ)‖
              ≤ Cb * ρ ^ (n - k) * ((k : ℝ) + 1) ^ ((d : ℝ) + r * (((n - k : ℕ)) : ℝ)) :=
            hshift (n - k) k (by omega)
          have h2 : ‖PowerSeries.coeff k F‖ ≤ C * A ^ k * (k ! : ℝ) ^ r := ih k hkn
          have hfack : (0 : ℝ) < (k ! : ℝ) ^ r := factorial_rpow_pos k r
          have hk0 : (0 : ℝ)
              ≤ Cb * ρ ^ (n - k) * ((k : ℝ) + 1) ^ ((d : ℝ) + r * (((n - k : ℕ)) : ℝ)) :=
            mul_nonneg (mul_nonneg hCb0 (pow_nonneg hρ0 _))
              (le_of_lt (Real.rpow_pos_of_pos (by positivity) _))
          have hprod : (Cb * ρ ^ (n - k)
                * ((k : ℝ) + 1) ^ ((d : ℝ) + r * (((n - k : ℕ)) : ℝ)))
              * (C * A ^ k * (k ! : ℝ) ^ r)
              = (Cb * (C * A ^ n * (n ! : ℝ) ^ r)) * (q ^ (n - k)
                  * (((k : ℝ) + 1) ^ ((d : ℝ) + r * (((n - k : ℕ)) : ℝ))
                      * ((k ! : ℝ) ^ r / (n ! : ℝ) ^ r))) := by
            rw [hqdef, div_pow]
            have hApow : A ^ n = A ^ (n - k) * A ^ k := by
              rw [← pow_add]
              congr 1
              omega
            rw [hApow]
            field_simp
          have hfactor : ((k : ℝ) + 1) ^ ((d : ℝ) + r * (((n - k : ℕ)) : ℝ))
                * ((k ! : ℝ) ^ r / (n ! : ℝ) ^ r)
              ≤ ((n : ℝ) + 1) ^ d := shiftFactor_newton_le hr hkn
          have hqk0 : (0 : ℝ) ≤ q ^ (n - k) := pow_nonneg hq0 _
          have hleft0 : (0 : ℝ) ≤ Cb * (C * A ^ n * (n ! : ℝ) ^ r) :=
            mul_nonneg hCb0 (mul_nonneg (mul_nonneg hC0 (le_of_lt hApown)) (le_of_lt hfacpos))
          calc ‖(shiftPolynomial B (n - k)).eval ((k : ℕ) : ℂ)‖ * ‖PowerSeries.coeff k F‖
              ≤ (Cb * ρ ^ (n - k)
                    * ((k : ℝ) + 1) ^ ((d : ℝ) + r * (((n - k : ℕ)) : ℝ)))
                  * (C * A ^ k * (k ! : ℝ) ^ r) :=
                mul_le_mul h1 h2 (norm_nonneg _) hk0
            _ = (Cb * (C * A ^ n * (n ! : ℝ) ^ r)) * (q ^ (n - k)
                  * (((k : ℝ) + 1) ^ ((d : ℝ) + r * (((n - k : ℕ)) : ℝ))
                      * ((k ! : ℝ) ^ r / (n ! : ℝ) ^ r))) := hprod
            _ ≤ (Cb * (C * A ^ n * (n ! : ℝ) ^ r)) * (q ^ (n - k) * ((n : ℝ) + 1) ^ d) := by
                refine mul_le_mul_of_nonneg_left ?_ hleft0
                exact mul_le_mul_of_nonneg_left hfactor hqk0
            _ = (Cb * (C * A ^ n * (n ! : ℝ) ^ r) * ((n : ℝ) + 1) ^ d) * q ^ (n - k) := by ring
        calc ∑ k ∈ Finset.range n,
              ‖(shiftPolynomial B (n - k)).eval ((k : ℕ) : ℂ)‖ * ‖PowerSeries.coeff k F‖
            ≤ ∑ k ∈ Finset.range n,
                (Cb * (C * A ^ n * (n ! : ℝ) ^ r) * ((n : ℝ) + 1) ^ d) * q ^ (n - k) :=
              Finset.sum_le_sum hstep
          _ = (Cb * (C * A ^ n * (n ! : ℝ) ^ r) * ((n : ℝ) + 1) ^ d)
                * ∑ k ∈ Finset.range n, q ^ (n - k) := by
              rw [Finset.mul_sum]
          _ ≤ (Cb * (C * A ^ n * (n ! : ℝ) ^ r) * ((n : ℝ) + 1) ^ d) * (q / (1 - q)) :=
              mul_le_mul_of_nonneg_left (geom_shift_sum_le hq0 hq1 n) hbig0
          _ = (Cb * (q / (1 - q)))
                * ((C * A ^ n * (n ! : ℝ) ^ r) * ((n : ℝ) + 1) ^ d) := by ring
          _ ≤ (c / 2) * ((C * A ^ n * (n ! : ℝ) ^ r) * ((n : ℝ) + 1) ^ d) := by
              refine mul_le_mul_of_nonneg_right hqbound ?_
              exact mul_nonneg (mul_nonneg (mul_nonneg hC0 (le_of_lt hApown)) (le_of_lt hfacpos))
                (le_of_lt hpowd)
          _ = c / 2 * ((n : ℝ) + 1) ^ d * (C * A ^ n * (n ! : ℝ) ^ r) := by ring
      have hmid : c * ((n : ℝ) + 1) ^ d * ‖PowerSeries.coeff n F‖
          ≤ ‖(shiftPolynomial B 0).eval ((n : ℕ) : ℂ)‖ * ‖PowerSeries.coeff n F‖ :=
        mul_le_mul_of_nonneg_right hΦlow (norm_nonneg _)
      have hsum2 : ‖PowerSeries.coeff n G‖
            + ∑ k ∈ Finset.range n,
                ‖(shiftPolynomial B (n - k)).eval ((k : ℕ) : ℂ)‖ * ‖PowerSeries.coeff k F‖
          ≤ c * ((n : ℝ) + 1) ^ d * (C * A ^ n * (n ! : ℝ) ^ r) := by
        have hadd := add_le_add hGterm hconv
        have heq : c / 2 * ((n : ℝ) + 1) ^ d * (C * A ^ n * (n ! : ℝ) ^ r)
            + c / 2 * ((n : ℝ) + 1) ^ d * (C * A ^ n * (n ! : ℝ) ^ r)
            = c * ((n : ℝ) + 1) ^ d * (C * A ^ n * (n ! : ℝ) ^ r) := by ring
        linarith [hadd, heq]
      have hfinal : c * ((n : ℝ) + 1) ^ d * ‖PowerSeries.coeff n F‖
          ≤ c * ((n : ℝ) + 1) ^ d * (C * A ^ n * (n ! : ℝ) ^ r) :=
        le_trans (le_trans hmid hnormrec) hsum2
      exact le_of_mul_le_mul_left hfinal hΦpos


/-- **A linear equation whose Newton polygon has no positive slope has only convergent formal
solutions.**  This is the `r = 0` case of the Newton form: if every coefficient present at a
positive shift has index at most `deg Φ_0`, the solution is analytic. -/
theorem isGevreySeries_zero_of_eulerLinearOp_eq {m : ℕ} (B : Fin (m + 1) → PowerSeries ℂ)
    (hB : ∀ j, IsGevreySeries 0 (B j)) (hΦ : shiftPolynomial B 0 ≠ 0)
    (hdeg : ∀ (μ : ℕ) (j : Fin (m + 1)), 1 ≤ μ → PowerSeries.coeff μ (B j) ≠ 0 →
      ((j : ℕ) : ℝ) ≤ (((shiftPolynomial B 0).natDegree : ℕ) : ℝ))
    {F G : PowerSeries ℂ} (hG : IsGevreySeries 0 G)
    (hsol : eulerLinearOp B F = G) :
    IsGevreySeries 0 F := by
  refine isGevreySeries_of_eulerLinearOp_eq_newton le_rfl B hB hΦ ?_ hG hsol
  intro μ j hμ hz
  have := hdeg μ j hμ hz
  simpa using this

end GaloisForLFunctions.HTGeometry
