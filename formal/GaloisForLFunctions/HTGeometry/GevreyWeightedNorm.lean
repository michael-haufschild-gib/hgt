import GaloisForLFunctions.HTGeometry.GevreyBanachNorm
import GaloisForLFunctions.HTGeometry.MailletLinearGevrey

/-!
# Weighted Gevrey bounds, and the gain of a common vanishing order

A Gevrey bound weighted by `(n+1)^a` is submultiplicative for every `a ≥ 2`, because

```text
(n+1)^a ∑_{i+j=n} 1/((i+1)^a (j+1)^a) ≤ 2^{a+2} .
```

Two further features are what a nonlinear recursion needs.

* The Euler operator costs exactly one unit of weight, since it multiplies the `n`-th coefficient
  by `n`.
* A product of two series both divisible by `t^M` **gains** `M r` units of weight, because the two
  factorials in the Cauchy product are then separated from the total factorial by a binomial
  coefficient of size `((n+1)/2)^M / M!`.

The second point is the mechanism by which a truncation of high order makes a quadratic defect
negligible: the gain `M r` can be made larger than any prescribed polynomial loss by taking the
truncation order `M` large.
-/

open PowerSeries
open scoped Nat

namespace GaloisForLFunctions.HTGeometry

/-! ### The weighted convolution constant -/

theorem sum_inv_pow_le_two {a : ℕ} (ha : 2 ≤ a) (n : ℕ) :
    ∑ k ∈ Finset.range n, (1 : ℝ) / ((k : ℝ) + 1) ^ a ≤ 2 := by
  refine le_trans (Finset.sum_le_sum ?_) (sum_inv_sq_le_two n)
  intro k _
  have h1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) k
    linarith
  have hpow : ((k : ℝ) + 1) ^ 2 ≤ ((k : ℝ) + 1) ^ a := pow_le_pow_right₀ h1 ha
  have hpos : (0 : ℝ) < ((k : ℝ) + 1) ^ 2 := by positivity
  exact one_div_le_one_div_of_le hpos hpow

/-- **The weighted convolution weight is bounded**, for every exponent at least two. -/
theorem antidiagonal_inv_pow_le {a : ℕ} (ha : 2 ≤ a) (n : ℕ) :
    ((n : ℝ) + 1) ^ a * ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
        (1 : ℝ) / (((p.1 : ℝ) + 1) ^ a * ((p.2 : ℝ) + 1) ^ a) ≤ 2 ^ (a + 2) := by
  classical
  have hterm : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal n,
      (1 : ℝ) / (((p.1 : ℝ) + 1) ^ a * ((p.2 : ℝ) + 1) ^ a)
        ≤ (2 ^ a / ((n : ℝ) + 1) ^ a)
          * ((1 : ℝ) / ((p.1 : ℝ) + 1) ^ a + (1 : ℝ) / ((p.2 : ℝ) + 1) ^ a) := by
    intro p hp
    have hsum : p.1 + p.2 = n := List.Nat.mem_antidiagonal.mp hp
    have ha1 : (0 : ℝ) < (p.1 : ℝ) + 1 := by positivity
    have hb1 : (0 : ℝ) < (p.2 : ℝ) + 1 := by positivity
    have hn : ((n : ℝ) + 1) ≤ ((p.1 : ℝ) + 1) + ((p.2 : ℝ) + 1) := by
      have hc : ((p.1 + p.2 : ℕ) : ℝ) = (n : ℝ) := by exact_mod_cast hsum
      push_cast at hc ⊢
      linarith
    have hkey : ((n : ℝ) + 1) ^ a ≤ 2 ^ a * (((p.1 : ℝ) + 1) ^ a + ((p.2 : ℝ) + 1) ^ a) := by
      rcases le_total ((p.1 : ℝ) + 1) ((p.2 : ℝ) + 1) with hle | hle
      · have hmax : ((n : ℝ) + 1) ≤ 2 * ((p.2 : ℝ) + 1) := by linarith
        calc ((n : ℝ) + 1) ^ a ≤ (2 * ((p.2 : ℝ) + 1)) ^ a :=
              pow_le_pow_left₀ (by positivity) hmax a
          _ = 2 ^ a * ((p.2 : ℝ) + 1) ^ a := by rw [mul_pow]
          _ ≤ 2 ^ a * (((p.1 : ℝ) + 1) ^ a + ((p.2 : ℝ) + 1) ^ a) := by
              have : (0 : ℝ) ≤ ((p.1 : ℝ) + 1) ^ a := by positivity
              nlinarith [this, pow_pos (show (0:ℝ) < 2 by norm_num) a]
      · have hmax : ((n : ℝ) + 1) ≤ 2 * ((p.1 : ℝ) + 1) := by linarith
        calc ((n : ℝ) + 1) ^ a ≤ (2 * ((p.1 : ℝ) + 1)) ^ a :=
              pow_le_pow_left₀ (by positivity) hmax a
          _ = 2 ^ a * ((p.1 : ℝ) + 1) ^ a := by rw [mul_pow]
          _ ≤ 2 ^ a * (((p.1 : ℝ) + 1) ^ a + ((p.2 : ℝ) + 1) ^ a) := by
              have : (0 : ℝ) ≤ ((p.2 : ℝ) + 1) ^ a := by positivity
              nlinarith [this, pow_pos (show (0:ℝ) < 2 by norm_num) a]
    rw [div_le_iff₀ (by positivity)]
    have hexp : (2 ^ a / ((n : ℝ) + 1) ^ a)
          * ((1 : ℝ) / ((p.1 : ℝ) + 1) ^ a + (1 : ℝ) / ((p.2 : ℝ) + 1) ^ a)
          * (((p.1 : ℝ) + 1) ^ a * ((p.2 : ℝ) + 1) ^ a)
        = 2 ^ a * (((p.2 : ℝ) + 1) ^ a + ((p.1 : ℝ) + 1) ^ a) / ((n : ℝ) + 1) ^ a := by
      field_simp
    rw [hexp, le_div_iff₀ (by positivity)]
    nlinarith [hkey]
  have hsplit : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
      (2 ^ a / ((n : ℝ) + 1) ^ a)
        * ((1 : ℝ) / ((p.1 : ℝ) + 1) ^ a + (1 : ℝ) / ((p.2 : ℝ) + 1) ^ a)
      = (2 ^ a / ((n : ℝ) + 1) ^ a)
        * ((∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, (1 : ℝ) / ((p.1 : ℝ) + 1) ^ a)
          + ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, (1 : ℝ) / ((p.2 : ℝ) + 1) ^ a) := by
    rw [← Finset.mul_sum, ← Finset.sum_add_distrib]
  have hfirst : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
      (1 : ℝ) / ((p.1 : ℝ) + 1) ^ a ≤ 2 := by
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
      (fun p : ℕ × ℕ => (1 : ℝ) / ((p.1 : ℝ) + 1) ^ a) n]
    exact sum_inv_pow_le_two ha (n + 1)
  have hsecond : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
      (1 : ℝ) / ((p.2 : ℝ) + 1) ^ a ≤ 2 := by
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
      (fun p : ℕ × ℕ => (1 : ℝ) / ((p.2 : ℝ) + 1) ^ a) n]
    have hrefl := Finset.sum_range_reflect (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1) ^ a) (n + 1)
    have heq : ∑ k ∈ Finset.range (n + 1), (1 : ℝ) / (((n - k : ℕ) : ℝ) + 1) ^ a
        = ∑ k ∈ Finset.range (n + 1), (1 : ℝ) / ((k : ℝ) + 1) ^ a := by
      rw [← hrefl]
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 3
    rw [heq]
    exact sum_inv_pow_le_two ha (n + 1)
  have hbound : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
      (1 : ℝ) / (((p.1 : ℝ) + 1) ^ a * ((p.2 : ℝ) + 1) ^ a)
      ≤ (2 ^ a / ((n : ℝ) + 1) ^ a) * 4 := by
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [hsplit]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    linarith
  calc ((n : ℝ) + 1) ^ a * ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
        (1 : ℝ) / (((p.1 : ℝ) + 1) ^ a * ((p.2 : ℝ) + 1) ^ a)
      ≤ ((n : ℝ) + 1) ^ a * ((2 ^ a / ((n : ℝ) + 1) ^ a) * 4) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = 2 ^ a * 4 := by
        field_simp
    _ = 2 ^ (a + 2) := by
        rw [pow_add]
        norm_num

/-! ### The weighted bound -/

/-- A Gevrey bound of integral order `r` weighted by `(n+1)^w`. -/
def GevreyWeightBound (w : ℕ) (C A : ℝ) (r : ℕ) (F : PowerSeries ℂ) : Prop :=
  ∀ n : ℕ, ‖PowerSeries.coeff n F‖ * ((n : ℝ) + 1) ^ w ≤ C * A ^ n * ((n ! : ℝ)) ^ r

theorem GevreyWeightBound.mono_weight {w w' : ℕ} (hw : w' ≤ w) {C A : ℝ} {r : ℕ}
    {F : PowerSeries ℂ} (h : GevreyWeightBound w C A r F) : GevreyWeightBound w' C A r F := by
  intro n
  have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hpow : ((n : ℝ) + 1) ^ w' ≤ ((n : ℝ) + 1) ^ w := pow_le_pow_right₀ h1 hw
  refine le_trans (mul_le_mul_of_nonneg_left hpow (norm_nonneg _)) (h n)

theorem GevreyWeightBound.mono_const {w : ℕ} {C C' A : ℝ} (hCC : C ≤ C') (hA : 0 < A) {r : ℕ}
    {F : PowerSeries ℂ} (h : GevreyWeightBound w C A r F) : GevreyWeightBound w C' A r F := by
  intro n
  refine le_trans (h n) ?_
  have hpos : (0 : ℝ) ≤ A ^ n * ((n ! : ℝ)) ^ r := by positivity
  nlinarith [hCC, hpos]

theorem GevreyWeightBound.mono_base {w : ℕ} {C A A' : ℝ} (hA : 0 < A) (hAA : A ≤ A')
    (hC : 0 ≤ C) {r : ℕ} {F : PowerSeries ℂ} (h : GevreyWeightBound w C A r F) :
    GevreyWeightBound w C A' r F := by
  intro n
  refine le_trans (h n) ?_
  have hpow : A ^ n ≤ A' ^ n := pow_le_pow_left₀ (le_of_lt hA) hAA n
  have hfac : (0 : ℝ) ≤ ((n ! : ℝ)) ^ r := by positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC) hfac

theorem GevreyWeightBound.mono_order {w : ℕ} {C A : ℝ} {r r' : ℕ} (hr : r ≤ r') (hC : 0 ≤ C)
    (hA : 0 < A) {F : PowerSeries ℂ} (h : GevreyWeightBound w C A r F) :
    GevreyWeightBound w C A r' F := by
  intro n
  refine le_trans (h n) ?_
  have hfac : ((n ! : ℝ)) ^ r ≤ ((n ! : ℝ)) ^ r' :=
    pow_le_pow_right₀ (one_le_factorial_cast n) hr
  have hpos : (0 : ℝ) ≤ C * A ^ n := by positivity
  nlinarith [hfac, hpos]

/-! ### The Euler operator costs one unit of weight -/

theorem GevreyWeightBound.eulerOp {w : ℕ} {C A : ℝ} {r : ℕ} {F : PowerSeries ℂ}
    (h : GevreyWeightBound (w + 1) C A r F) :
    GevreyWeightBound w C A r (GaloisForLFunctions.HTGeometry.eulerOp F) := by
  intro n
  have hnorm : ‖PowerSeries.coeff n (GaloisForLFunctions.HTGeometry.eulerOp F)‖
      = (n : ℝ) * ‖PowerSeries.coeff n F‖ := by
    rw [coeff_eulerOp, norm_mul, Complex.norm_natCast]
  have hle : (n : ℝ) * ‖PowerSeries.coeff n F‖ * ((n : ℝ) + 1) ^ w
      ≤ ‖PowerSeries.coeff n F‖ * ((n : ℝ) + 1) ^ (w + 1) := by
    have hn : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
    have hw : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ w := by positivity
    have hnn : (0 : ℝ) ≤ ‖PowerSeries.coeff n F‖ := norm_nonneg _
    rw [pow_succ]
    nlinarith [hn, hw, hnn]
  rw [hnorm]
  exact le_trans hle (h n)

theorem GevreyWeightBound.eulerOp_iterate {j : ℕ} :
    ∀ {w : ℕ} {C A : ℝ} {r : ℕ} {F : PowerSeries ℂ},
      GevreyWeightBound (w + j) C A r F →
      GevreyWeightBound w C A r (GaloisForLFunctions.HTGeometry.eulerOp^[j] F) := by
  induction j with
  | zero => intro w C A r F h; simpa using h
  | succ j ih =>
      intro w C A r F h
      rw [Function.iterate_succ_apply]
      refine ih ?_
      refine GevreyWeightBound.eulerOp ?_
      have hEq : w + j + 1 = w + (j + 1) := by omega
      rw [hEq]
      exact h

/-! ### Submultiplicativity -/

/-- **The weighted bound is submultiplicative** for every exponent at least two. -/
theorem GevreyWeightBound.mul {a : ℕ} (ha : 2 ≤ a) {C₁ C₂ A : ℝ} (hA : 0 < A)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) {r : ℕ} {F G : PowerSeries ℂ}
    (hF : GevreyWeightBound a C₁ A r F) (hG : GevreyWeightBound a C₂ A r G) :
    GevreyWeightBound a (2 ^ (a + 2) * C₁ * C₂) A r (F * G) := by
  classical
  intro n
  have hterm : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal n,
      ‖PowerSeries.coeff p.1 F * PowerSeries.coeff p.2 G‖
        ≤ (C₁ * C₂ * A ^ n * ((n ! : ℝ)) ^ r)
          * ((1 : ℝ) / (((p.1 : ℝ) + 1) ^ a * ((p.2 : ℝ) + 1) ^ a)) := by
    intro p hp
    have hpn : p.1 + p.2 = n := List.Nat.mem_antidiagonal.mp hp
    have h1 := hF p.1
    have h2 := hG p.2
    have hfac : ((p.1 ! : ℝ)) ^ r * ((p.2 ! : ℝ)) ^ r ≤ ((n ! : ℝ)) ^ r := by
      have hle : p.1 ! * p.2 ! ≤ (p.1 + p.2)! :=
        Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add p.1 p.2)
      rw [hpn] at hle
      have hcast : ((p.1 ! : ℝ)) * ((p.2 ! : ℝ)) ≤ (n ! : ℝ) := by exact_mod_cast hle
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) hcast r
    have hApow : A ^ p.1 * A ^ p.2 = A ^ n := by rw [← pow_add, hpn]
    have hprod : (‖PowerSeries.coeff p.1 F‖ * ((p.1 : ℝ) + 1) ^ a)
          * (‖PowerSeries.coeff p.2 G‖ * ((p.2 : ℝ) + 1) ^ a)
        ≤ (C₁ * A ^ p.1 * ((p.1 ! : ℝ)) ^ r) * (C₂ * A ^ p.2 * ((p.2 ! : ℝ)) ^ r) := by
      refine mul_le_mul h1 h2 (by positivity) ?_
      have : (0 : ℝ) ≤ C₁ * A ^ p.1 := by positivity
      positivity
    have hright : (C₁ * A ^ p.1 * ((p.1 ! : ℝ)) ^ r) * (C₂ * A ^ p.2 * ((p.2 ! : ℝ)) ^ r)
        ≤ C₁ * C₂ * A ^ n * ((n ! : ℝ)) ^ r := by
      have hstep : (C₁ * A ^ p.1 * ((p.1 ! : ℝ)) ^ r) * (C₂ * A ^ p.2 * ((p.2 ! : ℝ)) ^ r)
          = (C₁ * C₂ * A ^ n) * (((p.1 ! : ℝ)) ^ r * ((p.2 ! : ℝ)) ^ r) := by
        rw [← hApow]
        ring
      rw [hstep]
      refine mul_le_mul_of_nonneg_left hfac ?_
      positivity
    have hle : ‖PowerSeries.coeff p.1 F‖ * ‖PowerSeries.coeff p.2 G‖
        * (((p.1 : ℝ) + 1) ^ a * ((p.2 : ℝ) + 1) ^ a)
        ≤ C₁ * C₂ * A ^ n * ((n ! : ℝ)) ^ r := by
      calc ‖PowerSeries.coeff p.1 F‖ * ‖PowerSeries.coeff p.2 G‖
            * (((p.1 : ℝ) + 1) ^ a * ((p.2 : ℝ) + 1) ^ a)
          = (‖PowerSeries.coeff p.1 F‖ * ((p.1 : ℝ) + 1) ^ a)
              * (‖PowerSeries.coeff p.2 G‖ * ((p.2 : ℝ) + 1) ^ a) := by ring
        _ ≤ (C₁ * A ^ p.1 * ((p.1 ! : ℝ)) ^ r) * (C₂ * A ^ p.2 * ((p.2 ! : ℝ)) ^ r) := hprod
        _ ≤ C₁ * C₂ * A ^ n * ((n ! : ℝ)) ^ r := hright
    rw [norm_mul, mul_one_div, le_div_iff₀ (by positivity)]
    exact hle
  have hsum : ‖PowerSeries.coeff n (F * G)‖
      ≤ (C₁ * C₂ * A ^ n * ((n ! : ℝ)) ^ r)
        * ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
            (1 : ℝ) / (((p.1 : ℝ) + 1) ^ a * ((p.2 : ℝ) + 1) ^ a) := by
    rw [PowerSeries.coeff_mul, Finset.mul_sum]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum hterm)
  have hweight := antidiagonal_inv_pow_le ha n
  have hbase : (0 : ℝ) ≤ C₁ * C₂ * A ^ n * ((n ! : ℝ)) ^ r := by positivity
  calc ‖PowerSeries.coeff n (F * G)‖ * ((n : ℝ) + 1) ^ a
      ≤ ((C₁ * C₂ * A ^ n * ((n ! : ℝ)) ^ r)
          * ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
              (1 : ℝ) / (((p.1 : ℝ) + 1) ^ a * ((p.2 : ℝ) + 1) ^ a)) * ((n : ℝ) + 1) ^ a :=
        mul_le_mul_of_nonneg_right hsum (by positivity)
    _ = (C₁ * C₂ * A ^ n * ((n ! : ℝ)) ^ r)
          * (((n : ℝ) + 1) ^ a * ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
              (1 : ℝ) / (((p.1 : ℝ) + 1) ^ a * ((p.2 : ℝ) + 1) ^ a)) := by ring
    _ ≤ (C₁ * C₂ * A ^ n * ((n ! : ℝ)) ^ r) * 2 ^ (a + 2) :=
        mul_le_mul_of_nonneg_left hweight hbase
    _ = 2 ^ (a + 2) * C₁ * C₂ * A ^ n * ((n ! : ℝ)) ^ r := by ring

/-! ### Passing between the weighted bound and the Gevrey class -/

theorem GevreyWeightBound.isGevreySeries {w : ℕ} {C A : ℝ} (hC : 0 < C) (hA : 0 < A) {r : ℕ}
    {F : PowerSeries ℂ} (h : GevreyWeightBound w C A r F) : IsGevreySeries (r : ℝ) F := by
  refine ⟨C, A, hC, hA, fun n => ?_⟩
  have hw : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ w := by
    refine one_le_pow₀ ?_
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hb := h n
  have hcast : ((n ! : ℝ)) ^ (r : ℝ) = ((n ! : ℝ)) ^ r := Real.rpow_natCast _ _
  rw [hcast]
  nlinarith [norm_nonneg (PowerSeries.coeff n F), hb, hw]

theorem exists_gevreyWeightBound {r : ℕ} {F : PowerSeries ℂ} (hF : IsGevreySeries (r : ℝ) F)
    (w : ℕ) : ∃ C A : ℝ, 0 < C ∧ 0 < A ∧ GevreyWeightBound w C A r F := by
  obtain ⟨C, A, hC, hA, hbound⟩ := hF
  obtain ⟨C₃, hC₃1, hC₃⟩ := exists_succ_pow_le_const_mul_pow w (by norm_num : (1 : ℝ) < 2)
  refine ⟨C * C₃, 2 * A, by positivity, by positivity, fun n => ?_⟩
  have hcast : ((n ! : ℝ)) ^ (r : ℝ) = ((n ! : ℝ)) ^ r := Real.rpow_natCast _ _
  have hb := hbound n
  rw [hcast] at hb
  calc ‖PowerSeries.coeff n F‖ * ((n : ℝ) + 1) ^ w
      ≤ (C * A ^ n * ((n ! : ℝ)) ^ r) * (C₃ * 2 ^ n) := by
        refine mul_le_mul hb (hC₃ n) (by positivity) ?_
        positivity
    _ = C * C₃ * (2 * A) ^ n * ((n ! : ℝ)) ^ r := by
        rw [mul_pow]
        ring

/-! ### The gain of a common vanishing order -/

/-- Two factorials whose arguments both exceed `M` are separated from their sum. -/
theorem factorial_mul_factorial_le_of_le (M : ℕ) :
    ∀ i, M ≤ i → ∀ j, M ≤ j → i ! * j ! ≤ M ! * (i + j - M)! := by
  intro i hi
  refine Nat.le_induction ?_ ?_ i hi
  · intro j _
    simp
  · intro i hi ih j hj
    have hprev := ih j hj
    have hstep : (i + 1)! * j ! = (i + 1) * (i ! * j !) := by
      rw [Nat.factorial_succ]
      ring
    have hidx : i + 1 + j - M = (i + j - M) + 1 := by omega
    rw [hstep, hidx, Nat.factorial_succ]
    calc (i + 1) * (i ! * j !) ≤ (i + 1) * (M ! * (i + j - M)!) :=
          Nat.mul_le_mul_left _ hprev
      _ ≤ (i + j - M + 1) * (M ! * (i + j - M)!) := by
          refine Nat.mul_le_mul_right _ ?_
          omega
      _ = (i + j - M + 1) * M ! * (i + j - M)! := by ring
      _ = M ! * ((i + j - M + 1) * (i + j - M)!) := by ring

/-- The factorial gain of a Cauchy product whose factors both vanish to order `M`. -/
theorem factorial_prod_le_of_dvd_order {M n i j : ℕ} (hM : M ≤ i) (hMj : M ≤ j)
    (hij : i + j = n) :
    ((i ! : ℝ)) * ((j ! : ℝ)) * ((n : ℝ) + 1) ^ M ≤ ((M ! : ℝ)) * 2 ^ M * (n ! : ℝ) := by
  have hMn : M ≤ n := by omega
  have h1 : i ! * j ! ≤ M ! * (n - M)! := by
    have := factorial_mul_factorial_le_of_le M i hM j hMj
    rwa [hij] at this
  have h2 : ((n - M) + 1) ^ (n - (n - M)) * (n - M)! ≤ n ! :=
    pow_succ_mul_factorial_le_factorial (n - M) n (by omega)
  have hidx : n - (n - M) = M := by omega
  rw [hidx] at h2
  have hhalf : ((n : ℝ) + 1) ≤ 2 * (((n - M : ℕ) : ℝ) + 1) := by
    have hcast : ((n - M : ℕ) : ℝ) = (n : ℝ) - (M : ℝ) := by
      have : (M : ℝ) ≤ (n : ℝ) := by exact_mod_cast hMn
      push_cast [Nat.cast_sub hMn]
      ring
    have hMi : (M : ℝ) ≤ (i : ℝ) := by exact_mod_cast hM
    have hMj' : (M : ℝ) ≤ (j : ℝ) := by exact_mod_cast hMj
    have hn : (n : ℝ) = (i : ℝ) + (j : ℝ) := by exact_mod_cast hij.symm
    rw [hcast]
    linarith
  have h1' : ((i ! : ℝ)) * ((j ! : ℝ)) ≤ ((M ! : ℝ)) * (((n - M : ℕ)! : ℝ)) := by
    exact_mod_cast h1
  have h2' : ((((n - M : ℕ) : ℝ)) + 1) ^ M * (((n - M : ℕ)! : ℝ)) ≤ (n ! : ℝ) := by
    exact_mod_cast h2
  have hpow : ((n : ℝ) + 1) ^ M ≤ 2 ^ M * ((((n - M : ℕ) : ℝ)) + 1) ^ M := by
    calc ((n : ℝ) + 1) ^ M ≤ (2 * ((((n - M : ℕ) : ℝ)) + 1)) ^ M :=
          pow_le_pow_left₀ (by positivity) hhalf M
      _ = 2 ^ M * ((((n - M : ℕ) : ℝ)) + 1) ^ M := by rw [mul_pow]
  have hfacpos : (0 : ℝ) ≤ ((M ! : ℝ)) := by positivity
  have hprodpos : (0 : ℝ) ≤ ((i ! : ℝ)) * ((j ! : ℝ)) := by positivity
  calc ((i ! : ℝ)) * ((j ! : ℝ)) * ((n : ℝ) + 1) ^ M
      ≤ (((M ! : ℝ)) * (((n - M : ℕ)! : ℝ)))
          * (2 ^ M * ((((n - M : ℕ) : ℝ)) + 1) ^ M) := by
        refine mul_le_mul h1' hpow (by positivity) (by positivity)
    _ = ((M ! : ℝ)) * 2 ^ M
          * (((((n - M : ℕ) : ℝ)) + 1) ^ M * (((n - M : ℕ)! : ℝ))) := by ring
    _ ≤ ((M ! : ℝ)) * 2 ^ M * (n ! : ℝ) := by
        refine mul_le_mul_of_nonneg_left h2' (by positivity)

/-- **A product of two series vanishing to order `M` gains `M r` units of weight.** -/
theorem GevreyWeightBound.mul_of_dvd {a M : ℕ} (ha : 2 ≤ a) {C₁ C₂ A : ℝ} (hA : 0 < A)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) {r : ℕ} {F G : PowerSeries ℂ}
    (hFdvd : (PowerSeries.X : PowerSeries ℂ) ^ M ∣ F)
    (hGdvd : (PowerSeries.X : PowerSeries ℂ) ^ M ∣ G)
    (hF : GevreyWeightBound a C₁ A r F) (hG : GevreyWeightBound a C₂ A r G) :
    GevreyWeightBound (a + M * r) (2 ^ (a + 2) * ((M ! : ℝ)) ^ r * 2 ^ (M * r) * C₁ * C₂) A r
      (F * G) := by
  classical
  intro n
  have hFz : ∀ k : ℕ, k < M → PowerSeries.coeff k F = 0 := by
    intro k hk
    exact (PowerSeries.X_pow_dvd_iff.mp hFdvd) k hk
  have hGz : ∀ k : ℕ, k < M → PowerSeries.coeff k G = 0 := by
    intro k hk
    exact (PowerSeries.X_pow_dvd_iff.mp hGdvd) k hk
  have hterm : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal n,
      ‖PowerSeries.coeff p.1 F * PowerSeries.coeff p.2 G‖ * ((n : ℝ) + 1) ^ (M * r)
        ≤ (((M ! : ℝ)) ^ r * 2 ^ (M * r) * C₁ * C₂ * A ^ n * ((n ! : ℝ)) ^ r)
          * ((1 : ℝ) / (((p.1 : ℝ) + 1) ^ a * ((p.2 : ℝ) + 1) ^ a)) := by
    intro p hp
    have hpn : p.1 + p.2 = n := List.Nat.mem_antidiagonal.mp hp
    by_cases hM1 : p.1 < M
    · rw [hFz p.1 hM1, zero_mul, norm_zero, zero_mul]
      positivity
    by_cases hM2 : p.2 < M
    · rw [hGz p.2 hM2, mul_zero, norm_zero, zero_mul]
      positivity
    push Not at hM1 hM2
    have h1 := hF p.1
    have h2 := hG p.2
    have hgain : ((p.1 ! : ℝ)) ^ r * ((p.2 ! : ℝ)) ^ r * ((n : ℝ) + 1) ^ (M * r)
        ≤ ((M ! : ℝ)) ^ r * 2 ^ (M * r) * ((n ! : ℝ)) ^ r := by
      have hbase := factorial_prod_le_of_dvd_order hM1 hM2 hpn
      have hpow := pow_le_pow_left₀
        (show (0:ℝ) ≤ ((p.1 ! : ℝ)) * ((p.2 ! : ℝ)) * ((n : ℝ) + 1) ^ M by positivity) hbase r
      calc ((p.1 ! : ℝ)) ^ r * ((p.2 ! : ℝ)) ^ r * ((n : ℝ) + 1) ^ (M * r)
          = (((p.1 ! : ℝ)) * ((p.2 ! : ℝ)) * ((n : ℝ) + 1) ^ M) ^ r := by
            rw [mul_pow, mul_pow, ← pow_mul]
        _ ≤ (((M ! : ℝ)) * 2 ^ M * (n ! : ℝ)) ^ r := hpow
        _ = ((M ! : ℝ)) ^ r * 2 ^ (M * r) * ((n ! : ℝ)) ^ r := by
            rw [mul_pow, mul_pow, ← pow_mul]
    have hApow : A ^ p.1 * A ^ p.2 = A ^ n := by rw [← pow_add, hpn]
    have hprod : (‖PowerSeries.coeff p.1 F‖ * ((p.1 : ℝ) + 1) ^ a)
          * (‖PowerSeries.coeff p.2 G‖ * ((p.2 : ℝ) + 1) ^ a)
        ≤ (C₁ * A ^ p.1 * ((p.1 ! : ℝ)) ^ r) * (C₂ * A ^ p.2 * ((p.2 ! : ℝ)) ^ r) := by
      refine mul_le_mul h1 h2 (by positivity) ?_
      positivity
    have hle : (‖PowerSeries.coeff p.1 F‖ * ‖PowerSeries.coeff p.2 G‖ * ((n : ℝ) + 1) ^ (M * r))
        * (((p.1 : ℝ) + 1) ^ a * ((p.2 : ℝ) + 1) ^ a)
        ≤ ((M ! : ℝ)) ^ r * 2 ^ (M * r) * C₁ * C₂ * A ^ n * ((n ! : ℝ)) ^ r := by
      have hstep : (‖PowerSeries.coeff p.1 F‖ * ‖PowerSeries.coeff p.2 G‖
              * ((n : ℝ) + 1) ^ (M * r))
          * (((p.1 : ℝ) + 1) ^ a * ((p.2 : ℝ) + 1) ^ a)
          = ((‖PowerSeries.coeff p.1 F‖ * ((p.1 : ℝ) + 1) ^ a)
              * (‖PowerSeries.coeff p.2 G‖ * ((p.2 : ℝ) + 1) ^ a)) * ((n : ℝ) + 1) ^ (M * r) := by
        ring
      rw [hstep]
      have hmid : ((‖PowerSeries.coeff p.1 F‖ * ((p.1 : ℝ) + 1) ^ a)
              * (‖PowerSeries.coeff p.2 G‖ * ((p.2 : ℝ) + 1) ^ a)) * ((n : ℝ) + 1) ^ (M * r)
          ≤ ((C₁ * A ^ p.1 * ((p.1 ! : ℝ)) ^ r) * (C₂ * A ^ p.2 * ((p.2 ! : ℝ)) ^ r))
              * ((n : ℝ) + 1) ^ (M * r) :=
        mul_le_mul_of_nonneg_right hprod (by positivity)
      refine le_trans hmid ?_
      have hrw : ((C₁ * A ^ p.1 * ((p.1 ! : ℝ)) ^ r) * (C₂ * A ^ p.2 * ((p.2 ! : ℝ)) ^ r))
              * ((n : ℝ) + 1) ^ (M * r)
          = (C₁ * C₂ * A ^ n)
              * (((p.1 ! : ℝ)) ^ r * ((p.2 ! : ℝ)) ^ r * ((n : ℝ) + 1) ^ (M * r)) := by
        rw [← hApow]
        ring
      rw [hrw]
      calc (C₁ * C₂ * A ^ n)
            * (((p.1 ! : ℝ)) ^ r * ((p.2 ! : ℝ)) ^ r * ((n : ℝ) + 1) ^ (M * r))
          ≤ (C₁ * C₂ * A ^ n) * (((M ! : ℝ)) ^ r * 2 ^ (M * r) * ((n ! : ℝ)) ^ r) :=
            mul_le_mul_of_nonneg_left hgain (by positivity)
        _ = ((M ! : ℝ)) ^ r * 2 ^ (M * r) * C₁ * C₂ * A ^ n * ((n ! : ℝ)) ^ r := by ring
    rw [norm_mul, mul_one_div, le_div_iff₀ (by positivity)]
    exact hle
  have hsum : ‖PowerSeries.coeff n (F * G)‖ * ((n : ℝ) + 1) ^ (M * r)
      ≤ (((M ! : ℝ)) ^ r * 2 ^ (M * r) * C₁ * C₂ * A ^ n * ((n ! : ℝ)) ^ r)
        * ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
            (1 : ℝ) / (((p.1 : ℝ) + 1) ^ a * ((p.2 : ℝ) + 1) ^ a) := by
    rw [PowerSeries.coeff_mul, Finset.mul_sum]
    refine le_trans (mul_le_mul_of_nonneg_right (norm_sum_le _ _) (by positivity)) ?_
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum hterm
  have hweight := antidiagonal_inv_pow_le ha n
  have hbase : (0 : ℝ) ≤ ((M ! : ℝ)) ^ r * 2 ^ (M * r) * C₁ * C₂ * A ^ n * ((n ! : ℝ)) ^ r := by
    positivity
  have hsplit : ‖PowerSeries.coeff n (F * G)‖ * ((n : ℝ) + 1) ^ (a + M * r)
      = (‖PowerSeries.coeff n (F * G)‖ * ((n : ℝ) + 1) ^ (M * r)) * ((n : ℝ) + 1) ^ a := by
    rw [pow_add]
    ring
  rw [hsplit]
  calc (‖PowerSeries.coeff n (F * G)‖ * ((n : ℝ) + 1) ^ (M * r)) * ((n : ℝ) + 1) ^ a
      ≤ ((((M ! : ℝ)) ^ r * 2 ^ (M * r) * C₁ * C₂ * A ^ n * ((n ! : ℝ)) ^ r)
          * ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
              (1 : ℝ) / (((p.1 : ℝ) + 1) ^ a * ((p.2 : ℝ) + 1) ^ a)) * ((n : ℝ) + 1) ^ a :=
        mul_le_mul_of_nonneg_right hsum (by positivity)
    _ = (((M ! : ℝ)) ^ r * 2 ^ (M * r) * C₁ * C₂ * A ^ n * ((n ! : ℝ)) ^ r)
          * (((n : ℝ) + 1) ^ a * ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
              (1 : ℝ) / (((p.1 : ℝ) + 1) ^ a * ((p.2 : ℝ) + 1) ^ a)) := by ring
    _ ≤ (((M ! : ℝ)) ^ r * 2 ^ (M * r) * C₁ * C₂ * A ^ n * ((n ! : ℝ)) ^ r) * 2 ^ (a + 2) :=
        mul_le_mul_of_nonneg_left hweight hbase
    _ = 2 ^ (a + 2) * ((M ! : ℝ)) ^ r * 2 ^ (M * r) * C₁ * C₂ * A ^ n * ((n ! : ℝ)) ^ r := by ring

end GaloisForLFunctions.HTGeometry
