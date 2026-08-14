import GaloisForLFunctions.HTGeometry.GevreyFormalSeries

/-!
# A submultiplicative Gevrey bound

The plain Gevrey bound `‖aₙ‖ ≤ C Aⁿ (n!)^r` is not submultiplicative: a Cauchy product picks up the
factor `n+1` from the size of the antidiagonal, which forces the geometric base to grow at every
multiplication.  Weighting by `(n+1)²` repairs this, because

```text
(n+1)² ∑_{i+j=n} 1/((i+1)²(j+1)²) ≤ 16 ,
```

so the weighted bounds multiply with a fixed constant and a fixed base.  That is what lets a
nonlinear recursion see the **square** of the size of a perturbation rather than merely its first
power.

The displayed inequality comes from `(a+b)² ≤ 4(a²+b²)` together with `1/min² ≤ 1/a² + 1/b²` and the
elementary bound `∑_{k<n} 1/(k+1)² ≤ 2`.
-/

open PowerSeries
open scoped Nat

namespace GaloisForLFunctions.HTGeometry

/-! ### The convolution weight -/

theorem sum_inv_sq_le_two (n : ℕ) :
    ∑ k ∈ Finset.range n, (1 : ℝ) / ((k : ℝ) + 1) ^ 2 ≤ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        norm_num
      · -- the stronger telescoping bound is not needed: reuse the tail estimate
        have hstrong : ∀ k : ℕ, 1 ≤ k →
            ∑ j ∈ Finset.range k, (1 : ℝ) / ((j : ℝ) + 1) ^ 2 ≤ 2 - 1 / (k : ℝ) := by
          intro k hk
          induction k with
          | zero => omega
          | succ k ihk =>
              rcases Nat.eq_zero_or_pos k with hk0 | hk0
              · subst hk0
                norm_num
              · have hk1 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
                have hprev := ihk hk0
                have hstep' : (1 : ℝ) / ((k : ℝ) + 1) ^ 2 ≤ 1 / (k : ℝ) - 1 / ((k : ℝ) + 1) := by
                  rw [div_sub_div _ _ (ne_of_gt hk1) (by positivity),
                    div_le_div_iff₀ (by positivity) (by positivity)]
                  ring_nf
                  nlinarith [hk1]
                rw [Finset.sum_range_succ]
                have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
                rw [hcast]
                linarith
        have hres := hstrong (n + 1) (by omega)
        have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
        have hinv : (0 : ℝ) < 1 / ((n + 1 : ℕ) : ℝ) := by positivity
        linarith

/-- **The convolution weight is bounded.**  The antidiagonal sum of the inverse squares is
`O(1/(n+1)²)`. -/
theorem antidiagonal_inv_sq_le (n : ℕ) :
    ((n : ℝ) + 1) ^ 2 * ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
        (1 : ℝ) / (((p.1 : ℝ) + 1) ^ 2 * ((p.2 : ℝ) + 1) ^ 2) ≤ 16 := by
  classical
  have hterm : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal n,
      (1 : ℝ) / (((p.1 : ℝ) + 1) ^ 2 * ((p.2 : ℝ) + 1) ^ 2)
        ≤ (4 / ((n : ℝ) + 1) ^ 2)
          * ((1 : ℝ) / ((p.1 : ℝ) + 1) ^ 2 + (1 : ℝ) / ((p.2 : ℝ) + 1) ^ 2) := by
    intro p hp
    have hsum : p.1 + p.2 = n := List.Nat.mem_antidiagonal.mp hp
    have ha : (0 : ℝ) < (p.1 : ℝ) + 1 := by positivity
    have hb : (0 : ℝ) < (p.2 : ℝ) + 1 := by positivity
    have hn : ((n : ℝ) + 1) ≤ ((p.1 : ℝ) + 1) + ((p.2 : ℝ) + 1) := by
      have : ((p.1 + p.2 : ℕ) : ℝ) = (n : ℝ) := by exact_mod_cast hsum
      push_cast at this ⊢
      linarith
    have hkey : ((n : ℝ) + 1) ^ 2 ≤ 4 * (((p.1 : ℝ) + 1) ^ 2 + ((p.2 : ℝ) + 1) ^ 2) := by
      nlinarith [hn, ha, hb, sq_nonneg (((p.1 : ℝ) + 1) - ((p.2 : ℝ) + 1))]
    rw [div_le_iff₀ (by positivity)]
    have hexp : (4 / ((n : ℝ) + 1) ^ 2)
          * ((1 : ℝ) / ((p.1 : ℝ) + 1) ^ 2 + (1 : ℝ) / ((p.2 : ℝ) + 1) ^ 2)
          * (((p.1 : ℝ) + 1) ^ 2 * ((p.2 : ℝ) + 1) ^ 2)
        = 4 * (((p.2 : ℝ) + 1) ^ 2 + ((p.1 : ℝ) + 1) ^ 2) / ((n : ℝ) + 1) ^ 2 := by
      field_simp
    rw [hexp, le_div_iff₀ (by positivity)]
    nlinarith [hkey]
  have hsplit : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
      (4 / ((n : ℝ) + 1) ^ 2)
        * ((1 : ℝ) / ((p.1 : ℝ) + 1) ^ 2 + (1 : ℝ) / ((p.2 : ℝ) + 1) ^ 2)
      = (4 / ((n : ℝ) + 1) ^ 2)
        * ((∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, (1 : ℝ) / ((p.1 : ℝ) + 1) ^ 2)
          + ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, (1 : ℝ) / ((p.2 : ℝ) + 1) ^ 2) := by
    rw [← Finset.mul_sum, ← Finset.sum_add_distrib]
  have hfirst : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, (1 : ℝ) / ((p.1 : ℝ) + 1) ^ 2 ≤ 2 := by
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
      (fun p : ℕ × ℕ => (1 : ℝ) / ((p.1 : ℝ) + 1) ^ 2) n]
    exact sum_inv_sq_le_two (n + 1)
  have hsecond : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
      (1 : ℝ) / ((p.2 : ℝ) + 1) ^ 2 ≤ 2 := by
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
      (fun p : ℕ × ℕ => (1 : ℝ) / ((p.2 : ℝ) + 1) ^ 2) n]
    have hrefl := Finset.sum_range_reflect (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1) ^ 2) (n + 1)
    have heq : ∑ k ∈ Finset.range (n + 1), (1 : ℝ) / (((n - k : ℕ) : ℝ) + 1) ^ 2
        = ∑ k ∈ Finset.range (n + 1), (1 : ℝ) / ((k : ℝ) + 1) ^ 2 := by
      rw [← hrefl]
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 3
    rw [heq]
    exact sum_inv_sq_le_two (n + 1)
  have hbound : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
      (1 : ℝ) / (((p.1 : ℝ) + 1) ^ 2 * ((p.2 : ℝ) + 1) ^ 2)
      ≤ (4 / ((n : ℝ) + 1) ^ 2) * 4 := by
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [hsplit]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    linarith
  calc ((n : ℝ) + 1) ^ 2 * ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
        (1 : ℝ) / (((p.1 : ℝ) + 1) ^ 2 * ((p.2 : ℝ) + 1) ^ 2)
      ≤ ((n : ℝ) + 1) ^ 2 * ((4 / ((n : ℝ) + 1) ^ 2) * 4) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = 16 := by
        field_simp
        norm_num

/-! ### The submultiplicative bound -/

/-- A Gevrey bound weighted by `(n+1)²`.  Under this normalization Cauchy products multiply the
constants, with one fixed factor and no change of the geometric base. -/
def GevreyNormBound (C A r : ℝ) (F : PowerSeries ℂ) : Prop :=
  ∀ n : ℕ, ‖PowerSeries.coeff n F‖ * ((n : ℝ) + 1) ^ 2 ≤ C * A ^ n * (n ! : ℝ) ^ r

theorem GevreyNormBound.add {C₁ C₂ A r : ℝ} {F G : PowerSeries ℂ}
    (hF : GevreyNormBound C₁ A r F) (hG : GevreyNormBound C₂ A r G) :
    GevreyNormBound (C₁ + C₂) A r (F + G) := by
  intro n
  have h1 := hF n
  have h2 := hG n
  have hnorm : ‖PowerSeries.coeff n (F + G)‖ ≤ ‖PowerSeries.coeff n F‖ + ‖PowerSeries.coeff n G‖ := by
    rw [map_add]
    exact norm_add_le _ _
  have hw : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by positivity
  nlinarith [hnorm, h1, h2, hw]

/-- **The weighted bound is submultiplicative.** -/
theorem GevreyNormBound.mul {C₁ C₂ A r : ℝ} (hr : 0 ≤ r) (hA : 0 < A)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) {F G : PowerSeries ℂ}
    (hF : GevreyNormBound C₁ A r F) (hG : GevreyNormBound C₂ A r G) :
    GevreyNormBound (16 * C₁ * C₂) A r (F * G) := by
  classical
  intro n
  have hfacpos : (0 : ℝ) < (n ! : ℝ) ^ r := factorial_rpow_pos n r
  have hterm : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal n,
      ‖PowerSeries.coeff p.1 F * PowerSeries.coeff p.2 G‖
        ≤ (C₁ * C₂ * A ^ n * (n ! : ℝ) ^ r)
          * ((1 : ℝ) / (((p.1 : ℝ) + 1) ^ 2 * ((p.2 : ℝ) + 1) ^ 2)) := by
    intro p hp
    have hpn : p.1 + p.2 = n := List.Nat.mem_antidiagonal.mp hp
    have ha : (0 : ℝ) < ((p.1 : ℝ) + 1) ^ 2 := by positivity
    have hb : (0 : ℝ) < ((p.2 : ℝ) + 1) ^ 2 := by positivity
    have h1 : ‖PowerSeries.coeff p.1 F‖ * ((p.1 : ℝ) + 1) ^ 2
        ≤ C₁ * A ^ p.1 * ((p.1 ! : ℝ)) ^ r := hF p.1
    have h2 : ‖PowerSeries.coeff p.2 G‖ * ((p.2 : ℝ) + 1) ^ 2
        ≤ C₂ * A ^ p.2 * ((p.2 ! : ℝ)) ^ r := hG p.2
    have hfac : ((p.1 ! : ℝ)) ^ r * ((p.2 ! : ℝ)) ^ r ≤ (n ! : ℝ) ^ r := by
      have hle : p.1 ! * p.2 ! ≤ (p.1 + p.2)! :=
        Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add p.1 p.2)
      rw [hpn] at hle
      have hcast : ((p.1 ! * p.2 ! : ℕ) : ℝ) ≤ (n ! : ℝ) := by exact_mod_cast hle
      have hmul : ((p.1 ! : ℝ)) ^ r * ((p.2 ! : ℝ)) ^ r = ((p.1 ! * p.2 ! : ℕ) : ℝ) ^ r := by
        push_cast
        rw [Real.mul_rpow (by positivity) (by positivity)]
      rw [hmul]
      exact Real.rpow_le_rpow (by positivity) hcast hr
    have hApow : A ^ p.1 * A ^ p.2 = A ^ n := by rw [← pow_add, hpn]
    have hprod : (‖PowerSeries.coeff p.1 F‖ * ((p.1 : ℝ) + 1) ^ 2)
          * (‖PowerSeries.coeff p.2 G‖ * ((p.2 : ℝ) + 1) ^ 2)
        ≤ (C₁ * A ^ p.1 * ((p.1 ! : ℝ)) ^ r) * (C₂ * A ^ p.2 * ((p.2 ! : ℝ)) ^ r) := by
      refine mul_le_mul h1 h2 (by positivity) ?_
      exact mul_nonneg (mul_nonneg hC₁ (le_of_lt (pow_pos hA _)))
        (le_of_lt (factorial_rpow_pos p.1 r))
    have hright : (C₁ * A ^ p.1 * ((p.1 ! : ℝ)) ^ r) * (C₂ * A ^ p.2 * ((p.2 ! : ℝ)) ^ r)
        ≤ C₁ * C₂ * A ^ n * (n ! : ℝ) ^ r := by
      have hstep : (C₁ * A ^ p.1 * ((p.1 ! : ℝ)) ^ r) * (C₂ * A ^ p.2 * ((p.2 ! : ℝ)) ^ r)
          = (C₁ * C₂ * A ^ n) * (((p.1 ! : ℝ)) ^ r * ((p.2 ! : ℝ)) ^ r) := by
        rw [← hApow]
        ring
      rw [hstep]
      refine mul_le_mul_of_nonneg_left hfac ?_
      exact mul_nonneg (mul_nonneg hC₁ hC₂) (le_of_lt (pow_pos hA n))
    have hle : ‖PowerSeries.coeff p.1 F‖ * ‖PowerSeries.coeff p.2 G‖
        * (((p.1 : ℝ) + 1) ^ 2 * ((p.2 : ℝ) + 1) ^ 2)
        ≤ C₁ * C₂ * A ^ n * (n ! : ℝ) ^ r := by
      calc ‖PowerSeries.coeff p.1 F‖ * ‖PowerSeries.coeff p.2 G‖
            * (((p.1 : ℝ) + 1) ^ 2 * ((p.2 : ℝ) + 1) ^ 2)
          = (‖PowerSeries.coeff p.1 F‖ * ((p.1 : ℝ) + 1) ^ 2)
              * (‖PowerSeries.coeff p.2 G‖ * ((p.2 : ℝ) + 1) ^ 2) := by ring
        _ ≤ (C₁ * A ^ p.1 * ((p.1 ! : ℝ)) ^ r) * (C₂ * A ^ p.2 * ((p.2 ! : ℝ)) ^ r) := hprod
        _ ≤ C₁ * C₂ * A ^ n * (n ! : ℝ) ^ r := hright
    rw [norm_mul, mul_one_div, le_div_iff₀ (by positivity)]
    exact hle
  have hsum : ‖PowerSeries.coeff n (F * G)‖
      ≤ (C₁ * C₂ * A ^ n * (n ! : ℝ) ^ r)
        * ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
            (1 : ℝ) / (((p.1 : ℝ) + 1) ^ 2 * ((p.2 : ℝ) + 1) ^ 2) := by
    rw [PowerSeries.coeff_mul, Finset.mul_sum]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum hterm)
  have hweight := antidiagonal_inv_sq_le n
  have hbase : (0 : ℝ) ≤ C₁ * C₂ * A ^ n * (n ! : ℝ) ^ r :=
    mul_nonneg (mul_nonneg (mul_nonneg hC₁ hC₂) (le_of_lt (pow_pos hA n))) (le_of_lt hfacpos)
  calc ‖PowerSeries.coeff n (F * G)‖ * ((n : ℝ) + 1) ^ 2
      ≤ ((C₁ * C₂ * A ^ n * (n ! : ℝ) ^ r)
          * ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
              (1 : ℝ) / (((p.1 : ℝ) + 1) ^ 2 * ((p.2 : ℝ) + 1) ^ 2)) * ((n : ℝ) + 1) ^ 2 :=
        mul_le_mul_of_nonneg_right hsum (by positivity)
    _ = (C₁ * C₂ * A ^ n * (n ! : ℝ) ^ r)
          * (((n : ℝ) + 1) ^ 2 * ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
              (1 : ℝ) / (((p.1 : ℝ) + 1) ^ 2 * ((p.2 : ℝ) + 1) ^ 2)) := by ring
    _ ≤ (C₁ * C₂ * A ^ n * (n ! : ℝ) ^ r) * 16 := mul_le_mul_of_nonneg_left hweight hbase
    _ = 16 * C₁ * C₂ * A ^ n * (n ! : ℝ) ^ r := by ring

/-- The weighted bound implies the plain one. -/
theorem GevreyNormBound.isGevreySeries {C A r : ℝ} (hC : 0 < C) (hA : 0 < A)
    {F : PowerSeries ℂ} (h : GevreyNormBound C A r F) : IsGevreySeries r F := by
  refine ⟨C, A, hC, hA, fun n => ?_⟩
  have hw : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
    have : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    nlinarith
  have := h n
  nlinarith [norm_nonneg (PowerSeries.coeff n F), this, hw]

/-- Conversely every Gevrey series satisfies a weighted bound, after enlarging the base. -/
theorem IsGevreySeries.exists_gevreyNormBound {r : ℝ} {F : PowerSeries ℂ}
    (hF : IsGevreySeries r F) : ∃ C A : ℝ, 0 < C ∧ 0 < A ∧ GevreyNormBound C A r F := by
  obtain ⟨C, A, hC, hA, hbound⟩ := hF
  obtain ⟨C₃, hC₃1, hC₃⟩ := exists_succ_pow_le_const_mul_pow 2 (by norm_num : (1 : ℝ) < 2)
  refine ⟨C * C₃, 2 * A, by positivity, by positivity, fun n => ?_⟩
  have hfacpos : (0 : ℝ) < (n ! : ℝ) ^ r := factorial_rpow_pos n r
  have hpoly := hC₃ n
  calc ‖PowerSeries.coeff n F‖ * ((n : ℝ) + 1) ^ 2
      ≤ (C * A ^ n * (n ! : ℝ) ^ r) * (C₃ * 2 ^ n) := by
        refine mul_le_mul (hbound n) hpoly (by positivity) ?_
        exact mul_nonneg (mul_nonneg (le_of_lt hC) (le_of_lt (pow_pos hA n))) (le_of_lt hfacpos)
    _ = C * C₃ * (2 * A) ^ n * (n ! : ℝ) ^ r := by
        rw [mul_pow]
        ring

end GaloisForLFunctions.HTGeometry
