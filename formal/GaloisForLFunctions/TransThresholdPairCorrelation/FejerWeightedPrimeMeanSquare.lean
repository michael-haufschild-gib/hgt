import GaloisForLFunctions.RHTower.ZetaFejerWeight
import Zeta23.PrimeSideB.PPKernel

/-!
# Fejér- and Lorentz-Weighted Mean Squares of the Prime Polynomial

The prime polynomial `P_X(τ) = −π⁻¹ Σ_{n≤X} a_n cos(τ log n)` has a mean square against the Fejér
profile `F_b` that is an exact positive pair sum, because `∫ F_b(v) e^{−iyv} dv = 2π Λ_b(y)`:

`∫ F_b(τ − c) P_X(τ)² dτ = π⁻¹ Σ_{n,m} a_n a_m (Λ_b(y_n − y_m) cos((y_n − y_m)c)
                                               + Λ_b(y_n + y_m) cos((y_n + y_m)c))`
(`integral_fejer_mul_PX_sq`).

For `b ≤ 1` the sum frequencies drop out and only pairs `|log(n/m)| < b` remain; counting them gives
`∫ F_b(τ − c) P_X² ≤ π⁻¹ √e log X (3b ψ(X) + Σ_{n≤X} Λ(n)/n)` (`integral_fejer_mul_PX_sq_le`).

Two Fejér profiles half a period apart dominate a Lorentzian of width `R = 1/b`
(`lorentz_le_fejer_add_fejer`), hence the **Lorentz-weighted mean value**
`∫ P_X(τ)² / (1 + ((τ − c)/R)²) dτ ≤ π √e log X (3ψ(X) + R Σ_{n≤X} Λ(n)/n)`
(`integral_lorentz_mul_PX_sq_le`), the `(R + X)`-shape of the Montgomery–Vaughan mean value theorem
on a window of length `R`, without the Hilbert inequality.
-/

open Complex MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction
open Zeta23 Zeta23.PrimeSide RHTower.FejerWeight GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.TransThresholdPairCorrelation

variable {b : ℝ}

/-! ## 1. The Fejér profile against a cosine -/

/-- `∫ F_b(τ − c) cos(θτ) dτ = 2π Λ_b(θ) cos(θc)`. -/
theorem integral_fejer_shift_mul_cos (hb : 0 < b) (c θ : ℝ) :
    ∫ τ, fejerBandProfile b (τ - c) * Real.cos (θ * τ) = 2 * π * triangleFn b θ * Real.cos (θ * c) := by
  have hF := integral_fejerBandProfile_mul_cexp hb θ
  have hint : Integrable fun v : ℝ => ((fejerBandProfile b v : ℝ) : ℂ) * cexp (-(I * θ * v)) := by
    refine ((integrable_fejerBandProfile hb).ofReal).mul_bdd (c := 1)
      (by fun_prop) (Filter.Eventually.of_forall fun v => ?_)
    rw [show -(I * θ * v) = ((-(θ * v) : ℝ) : ℂ) * I by push_cast; ring, Complex.norm_exp_ofReal_mul_I]
  -- shift the complex identity by `c`
  have hshift : ∫ τ, ((fejerBandProfile b (τ - c) : ℝ) : ℂ) * cexp (-(I * θ * τ))
      = cexp (-(I * θ * c)) * (2 * π * ((triangleFn b θ : ℝ) : ℂ)) := by
    rw [← hF, ← integral_const_mul,
      ← integral_add_right_eq_self
        (fun τ : ℝ => ((fejerBandProfile b (τ - c) : ℝ) : ℂ) * cexp (-(I * θ * τ))) c]
    refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
    simp only [add_sub_cancel_right]
    rw [show -(I * θ * ((τ + c : ℝ) : ℂ)) = -(I * θ * τ) + -(I * θ * c) by push_cast; ring,
      Complex.exp_add]
    ring
  have hre := congrArg Complex.re hshift
  have hint' : Integrable fun τ : ℝ => ((fejerBandProfile b (τ - c) : ℝ) : ℂ) * cexp (-(I * θ * τ)) := by
    refine ((integrable_fejerBandProfile hb).comp_sub_right c).ofReal.mul_bdd (c := 1)
      (by fun_prop) (Filter.Eventually.of_forall fun τ => ?_)
    rw [show -(I * θ * τ) = ((-(θ * τ) : ℝ) : ℂ) * I by push_cast; ring, Complex.norm_exp_ofReal_mul_I]
  have hre0 := integral_re hint'
  simp only [RCLike.re_to_complex] at hre0
  rw [← hre0] at hre
  have hl : ∀ τ : ℝ, (((fejerBandProfile b (τ - c) : ℝ) : ℂ) * cexp (-(I * θ * τ))).re
      = fejerBandProfile b (τ - c) * Real.cos (θ * τ) := by
    intro τ
    rw [show -(I * θ * τ) = ((-(θ * τ) : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.add_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, Complex.ofReal_re, Complex.ofReal_im]
    rw [Real.cos_neg]; ring
  simp_rw [hl] at hre
  rw [hre, show -(I * θ * c) = ((-(θ * c) : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I]
  simp only [Complex.mul_re, Complex.add_re, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.mul_im,
    Complex.add_im, Complex.re_ofNat, Complex.im_ofNat]
  rw [Real.cos_neg, Real.sin_neg]
  ring

/-! ## 2. The Fejér-weighted mean square of `P_X` -/

theorem PX_sq_eq (X τ : ℝ) :
    Zeta23.PX X τ ^ 2 = (1 / (2 * π ^ 2)) * ∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
      acoef n * acoef m * (Real.cos ((Real.log n - Real.log m) * τ)
        + Real.cos ((Real.log n + Real.log m) * τ)) := by
  have hS : Zeta23.PX X τ = -(1 / π) * ∑ n ∈ primeRange X, acoef n * Real.cos (τ * Real.log n) :=
    PX_eq X τ
  rw [hS, mul_pow, neg_sq, sq (∑ n ∈ primeRange X, acoef n * Real.cos (τ * Real.log n)),
    Finset.sum_mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have h1 : Real.cos ((Real.log n - Real.log m) * τ) + Real.cos ((Real.log n + Real.log m) * τ)
      = 2 * (Real.cos (τ * Real.log n) * Real.cos (τ * Real.log m)) := by
    rw [show (Real.log n - Real.log m) * τ = τ * Real.log n - τ * Real.log m by ring,
      show (Real.log n + Real.log m) * τ = τ * Real.log n + τ * Real.log m by ring,
      Real.cos_sub, Real.cos_add]; ring
  rw [h1]
  field_simp

theorem integrable_fejer_shift_mul_cos (hb : 0 < b) (c θ : ℝ) :
    Integrable fun τ => fejerBandProfile b (τ - c) * Real.cos (θ * τ) :=
  ((integrable_fejerBandProfile hb).comp_sub_right c).mul_bdd (c := 1) (by fun_prop)
    (Filter.Eventually.of_forall fun τ => by simpa using Real.abs_cos_le_one (θ * τ))

/-- **The Fejér-weighted mean square of the prime polynomial is an exact pair sum.** -/
theorem integral_fejer_mul_PX_sq (hb : 0 < b) (c X : ℝ) :
    ∫ τ, fejerBandProfile b (τ - c) * Zeta23.PX X τ ^ 2
      = (1 / π) * ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, acoef n * acoef m
          * (triangleFn b (Real.log n - Real.log m) * Real.cos ((Real.log n - Real.log m) * c)
            + triangleFn b (Real.log n + Real.log m) * Real.cos ((Real.log n + Real.log m) * c)) := by
  have hpt : ∀ τ, fejerBandProfile b (τ - c) * Zeta23.PX X τ ^ 2
      = ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, (1 / (2 * π ^ 2)) * (acoef n * acoef m)
        * (fejerBandProfile b (τ - c) * Real.cos ((Real.log n - Real.log m) * τ)
          + fejerBandProfile b (τ - c) * Real.cos ((Real.log n + Real.log m) * τ)) := by
    intro τ
    rw [PX_sq_eq]
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => by ring
  have hint : ∀ n m : ℕ, Integrable fun τ => (1 / (2 * π ^ 2)) * (acoef n * acoef m)
      * (fejerBandProfile b (τ - c) * Real.cos ((Real.log n - Real.log m) * τ)
        + fejerBandProfile b (τ - c) * Real.cos ((Real.log n + Real.log m) * τ)) := fun n m =>
    ((integrable_fejer_shift_mul_cos hb c _).add (integrable_fejer_shift_mul_cos hb c _)).const_mul _
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_finsetSum _ fun n _ => integrable_finsetSum _ fun m _ => hint n m, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [integral_finsetSum _ fun m _ => hint n m, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [integral_const_mul, integral_add (integrable_fejer_shift_mul_cos hb c _)
    (integrable_fejer_shift_mul_cos hb c _), integral_fejer_shift_mul_cos hb,
    integral_fejer_shift_mul_cos hb]
  field_simp

/-! ## 3. Counting the coalescent pairs -/

theorem acoef_le_log_div_sqrt {X : ℝ} (hX : 1 ≤ X) {m : ℕ} (hm : m ∈ primeRange X) :
    acoef m ≤ Real.log X / Real.sqrt m := by
  unfold acoef
  have hm1 := one_le_of_mem_primeRange hm
  have hsq : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by exact_mod_cast hm1)
  refine div_le_div_of_nonneg_right ?_ hsq.le
  exact ArithmeticFunction.vonMangoldt_le_log.trans (log_le_of_mem_primeRange hX hm)

/-- `e^b − e^{−b} ≤ 3b` for `0 ≤ b ≤ 1`. -/
theorem exp_sub_exp_neg_le {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    Real.exp b - Real.exp (-b) ≤ 3 * b := by
  have h1 := Real.exp_bound (x := b) (by rw [abs_of_nonneg hb0]; exact hb1) one_pos
  simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, pow_one,
    Nat.succ_eq_add_one, Nat.reduceAdd, mul_one] at h1
  have h2 : Real.exp b ≤ 1 + 2 * b := by
    have := (abs_le.mp h1).2; rw [abs_of_nonneg hb0] at this; norm_num at this; linarith
  have h3 : 1 - b ≤ Real.exp (-b) := by linarith [Real.add_one_le_exp (-b)]
  linarith

/-- Integers in an open real interval: `#{m : A < m < B} ≤ B − A + 1`. -/
theorem card_filter_Ioo_le (s : Finset ℕ) {A B : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B) :
    ((s.filter fun m : ℕ => A < m ∧ (m : ℝ) < B).card : ℝ) ≤ B - A + 1 := by
  have hsub : s.filter (fun m : ℕ => A < m ∧ (m : ℝ) < B) ⊆ Finset.Icc ⌈A⌉₊ ⌊B⌋₊ := by
    intro m hm
    rw [Finset.mem_filter] at hm
    rw [Finset.mem_Icc]
    exact ⟨Nat.ceil_le.mpr hm.2.1.le, Nat.le_floor hm.2.2.le⟩
  have hc := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hc
  have h1 : ((⌊B⌋₊ + 1 - ⌈A⌉₊ : ℕ) : ℝ) ≤ B - A + 1 := by
    rcases le_or_gt ⌈A⌉₊ (⌊B⌋₊ + 1) with h | h
    · rw [Nat.cast_sub h, Nat.cast_add, Nat.cast_one]
      have := Nat.floor_le (hA.trans hAB)
      have := Nat.le_ceil A
      linarith
    · rw [Nat.sub_eq_zero_of_le h.le, Nat.cast_zero]; linarith
  exact (Nat.cast_le.mpr hc).trans h1

/-- For a fixed `n ≥ 1` and `0 < b ≤ 1`, the partners `m` with `|log n − log m| < b` carry
`Σ_m a_m Λ_b(log n − log m) ≤ √e log X (3bn + 1)/√n`. -/
theorem sum_acoef_triangle_le {X : ℝ} (hX : 1 ≤ X) (hb : 0 < b) (hb1 : b ≤ 1) {n : ℕ}
    (hn : 1 ≤ n) :
    ∑ m ∈ primeRange X, acoef m * triangleFn b (Real.log n - Real.log m)
      ≤ Real.sqrt (Real.exp 1) * Real.log X * (3 * b * n + 1) / Real.sqrt n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX
  set S := (primeRange X).filter fun m : ℕ => n * Real.exp (-b) < m ∧ (m : ℝ) < n * Real.exp b
  -- terms outside the window vanish; inside, `a_m ≤ log X / √m ≤ √e log X / √n`
  have hterm : ∀ m ∈ primeRange X, acoef m * triangleFn b (Real.log n - Real.log m)
      ≤ if m ∈ S then Real.sqrt (Real.exp 1) * Real.log X / Real.sqrt n else 0 := by
    intro m hm
    have hm1 := one_le_of_mem_primeRange hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    have ha0 := acoef_nonneg m
    have ht1 := triangleFn_le_one hb (Real.log n - Real.log m)
    have ht0 := triangleFn_nonneg b (Real.log n - Real.log m)
    split_ifs with hS
    · have hmS := (Finset.mem_filter.mp hS).2
      have hsqm : Real.sqrt n / Real.sqrt (Real.exp 1) ≤ Real.sqrt m := by
        rw [div_le_iff₀ (Real.sqrt_pos.mpr (Real.exp_pos 1)), ← Real.sqrt_mul hm0.le]
        refine Real.sqrt_le_sqrt ?_
        have h1 : (n : ℝ) * Real.exp (-1) ≤ n * Real.exp (-b) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hn0.le
        have h2 : (n : ℝ) = n * Real.exp (-1) * Real.exp 1 := by
          rw [mul_assoc, ← Real.exp_add]; simp
        nlinarith [hmS.1, Real.exp_pos 1]
      have ham : acoef m ≤ Real.sqrt (Real.exp 1) * Real.log X / Real.sqrt n := by
        have hse : 0 < Real.sqrt (Real.exp 1) := Real.sqrt_pos.mpr (Real.exp_pos 1)
        refine (acoef_le_log_div_sqrt hX hm).trans ?_
        calc Real.log X / Real.sqrt m ≤ Real.log X / (Real.sqrt n / Real.sqrt (Real.exp 1)) :=
              div_le_div_of_nonneg_left hlogX (by positivity) hsqm
          _ = _ := by field_simp
      calc acoef m * triangleFn b (Real.log n - Real.log m) ≤ acoef m * 1 :=
            mul_le_mul_of_nonneg_left ht1 ha0
        _ ≤ _ := by rw [mul_one]; exact ham
    · -- outside the window `|log n − log m| ≥ b`
      have hout : b ≤ |Real.log n - Real.log m| := by
        have hnot : ¬ (n * Real.exp (-b) < m ∧ (m : ℝ) < n * Real.exp b) := fun h =>
          hS (Finset.mem_filter.mpr ⟨hm, h⟩)
        rcases not_and_or.mp hnot with h | h
        · replace h := not_lt.mp h
          have : Real.log m ≤ Real.log n - b := by
            rw [← Real.log_exp (Real.log n - b), Real.exp_sub, Real.exp_log hn0, div_eq_mul_inv,
              ← Real.exp_neg]
            exact Real.log_le_log hm0 h
          rw [abs_of_nonneg (by linarith)]; linarith
        · replace h := not_lt.mp h
          have : Real.log n + b ≤ Real.log m := by
            rw [← Real.log_exp (Real.log n + b), Real.exp_add, Real.exp_log hn0]
            exact Real.log_le_log (by positivity) h
          rw [abs_of_nonpos (by linarith)]; linarith
      rw [triangleFn_eq_zero hb hout, mul_zero]
  calc ∑ m ∈ primeRange X, acoef m * triangleFn b (Real.log n - Real.log m)
      ≤ ∑ m ∈ primeRange X, if m ∈ S then Real.sqrt (Real.exp 1) * Real.log X / Real.sqrt n else 0 :=
        Finset.sum_le_sum hterm
    _ = (S.card : ℝ) * (Real.sqrt (Real.exp 1) * Real.log X / Real.sqrt n) := by
        rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr (Finset.filter_subset _ _),
          Finset.sum_const, nsmul_eq_mul]
    _ ≤ (3 * b * n + 1) * (Real.sqrt (Real.exp 1) * Real.log X / Real.sqrt n) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have hc := card_filter_Ioo_le (primeRange X) (A := n * Real.exp (-b)) (B := n * Real.exp b)
          (by positivity) (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hn0.le)
        have he := exp_sub_exp_neg_le hb.le hb1
        nlinarith
    _ = Real.sqrt (Real.exp 1) * Real.log X * (3 * b * n + 1) / Real.sqrt n := by ring

/-- **The coalescent pair count.** For `0 < b ≤ 1`:
`Σ_{n,m≤X} a_n a_m Λ_b(log n − log m) ≤ √e log X (3b ψ(X) + Σ_{n≤X} Λ(n)/n)`. -/
theorem sum_sum_acoef_triangle_le {X : ℝ} (hX : 1 ≤ X) (hb : 0 < b) (hb1 : b ≤ 1) :
    ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, acoef n * acoef m * triangleFn b (Real.log n - Real.log m)
      ≤ Real.sqrt (Real.exp 1) * Real.log X
        * (3 * b * ∑ n ∈ primeRange X, (Λ n : ℝ) + ∑ n ∈ primeRange X, (Λ n : ℝ) / n) := by
  have hstep : ∀ n ∈ primeRange X, ∑ m ∈ primeRange X, acoef n * acoef m
      * triangleFn b (Real.log n - Real.log m)
      ≤ Real.sqrt (Real.exp 1) * Real.log X * (3 * b * (Λ n : ℝ) + (Λ n : ℝ) / n) := by
    intro n hn
    have hn1 := one_le_of_mem_primeRange hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
    have h := sum_acoef_triangle_le hX hb hb1 hn1
    simp_rw [mul_assoc (acoef n)]
    rw [← Finset.mul_sum]
    calc acoef n * ∑ m ∈ primeRange X, acoef m * triangleFn b (Real.log n - Real.log m)
        ≤ acoef n * (Real.sqrt (Real.exp 1) * Real.log X * (3 * b * n + 1) / Real.sqrt n) :=
          mul_le_mul_of_nonneg_left h (acoef_nonneg n)
      _ = Real.sqrt (Real.exp 1) * Real.log X * (3 * b * (Λ n : ℝ) + (Λ n : ℝ) / n) := by
          unfold acoef
          have hss : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
          field_simp
          rw [show Real.sqrt n ^ 2 = n by rw [sq, hss]]
          ring
  refine (Finset.sum_le_sum hstep).trans (le_of_eq ?_)
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]

/-- **Fejér-weighted mean square of `P_X`.** For `0 < b ≤ 1` and `X ≥ 1`:
`∫ F_b(τ − c) P_X(τ)² dτ ≤ π⁻¹ √e log X (3b ψ(X) + Σ_{n≤X} Λ(n)/n)`. -/
theorem integral_fejer_mul_PX_sq_le (hb : 0 < b) (hb1 : b ≤ 1) (c : ℝ) {X : ℝ} (hX : 1 ≤ X) :
    ∫ τ, fejerBandProfile b (τ - c) * Zeta23.PX X τ ^ 2
      ≤ (1 / π) * (Real.sqrt (Real.exp 1) * Real.log X
        * (3 * b * ∑ n ∈ primeRange X, (Λ n : ℝ) + ∑ n ∈ primeRange X, (Λ n : ℝ) / n)) := by
  rw [integral_fejer_mul_PX_sq hb]
  refine mul_le_mul_of_nonneg_left ((Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun m hm => ?_).trans
    (sum_sum_acoef_triangle_le hX hb hb1)) (by positivity)
  have hab := mul_nonneg (acoef_nonneg n) (acoef_nonneg m)
  -- the sum frequency is invisible: `log n + log m ≥ 2 log 2 > 1 ≥ b` whenever `a_n a_m ≠ 0`
  rcases acoef_eq_zero_or_two_le hn with hn0 | hn2
  · simp [hn0]
  rcases acoef_eq_zero_or_two_le hm with hm0 | hm2
  · simp [hm0]
  have hplus : triangleFn b (Real.log n + Real.log m) = 0 := by
    apply triangleFn_eq_zero hb
    have := Real.log_two_gt_d9
    have hn' : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn2)
    have hm' : Real.log 2 ≤ Real.log m := Real.log_le_log (by norm_num) (by exact_mod_cast hm2)
    rw [abs_of_pos (by linarith)]; linarith
  rw [hplus, zero_mul, add_zero]
  exact mul_le_mul_of_nonneg_left
    (mul_le_of_le_one_right (triangleFn_nonneg _ _) (Real.cos_le_one _)) hab

/-! ## 4. Lorentz weights -/

/-- The Lorentz weight `(1 + ((τ − c)/R)²)⁻¹` of width `R` centred at `c`. -/
def lorentzW (R c τ : ℝ) : ℝ := (1 + ((τ - c) / R) ^ 2)⁻¹

theorem lorentzW_nonneg (R c τ : ℝ) : 0 ≤ lorentzW R c τ := by unfold lorentzW; positivity

theorem lorentzW_le_one (R c τ : ℝ) : lorentzW R c τ ≤ 1 := by
  unfold lorentzW; exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg ((τ - c) / R)])

/-- A Fejér value bounded below by its numerator over any `D ≥ (vb + s)²`. -/
theorem fejer_ge_num_div (hb : 0 < b) (v s : ℝ) {D : ℝ} (hvD : (v * b + s) ^ 2 ≤ D) :
    b * (2 - 2 * Real.cos (v * b + s)) / D ≤ fejerBandProfile b (v + s / b) := by
  unfold fejerBandProfile
  split_ifs with h0
  · have hz : v * b + s = 0 := by
      have h := congrArg (· * b) h0
      simp only [zero_mul, add_mul, div_mul_cancel₀ s hb.ne'] at h
      exact h
    rw [hz, Real.cos_zero]; simp only [mul_one, sub_self, mul_zero, zero_div]; exact hb.le
  · have hu : (v + s / b) * b = v * b + s := by field_simp
    have hne : v * b + s ≠ 0 := by rw [← hu]; exact mul_ne_zero h0 hb.ne'
    have hE : 0 < (v * b + s) ^ 2 := by positivity
    have heq : (2 - 2 * Real.cos ((v + s / b) * b)) / ((v + s / b) ^ 2 * b)
        = b * (2 - 2 * Real.cos (v * b + s)) / (v * b + s) ^ 2 := by
      rw [hu]; field_simp
    rw [heq]
    have hnum : 0 ≤ b * (2 - 2 * Real.cos (v * b + s)) :=
      mul_nonneg hb.le (by linarith [Real.cos_le_one (v * b + s)])
    exact div_le_div_of_nonneg_left hnum hE hvD

/-- **Two Fejér profiles half a period apart dominate the Lorentz weight.**
`(1 + ((τ − c)/R)²)⁻¹ ≤ 2π² R (F_{1/R}(τ − c) + F_{1/R}(τ − c + πR))`. -/
theorem lorentz_le_fejer_add_fejer {R : ℝ} (hR : 0 < R) (c τ : ℝ) :
    lorentzW R c τ ≤ 2 * π ^ 2 * R
      * (fejerBandProfile (1 / R) (τ - c) + fejerBandProfile (1 / R) (τ - c + π * R)) := by
  have hb : 0 < 1 / R := by positivity
  set u := (τ - c) * (1 / R) with hu
  set D := (|u| + 2 * π) ^ 2 with hDdef
  have hπ := Real.pi_pos
  have hD : 0 < D := by positivity
  have h1 : ((τ - c) * (1 / R) + 0) ^ 2 ≤ D := by
    rw [add_zero, ← hu, hDdef, ← sq_abs u]
    exact pow_le_pow_left₀ (abs_nonneg _) (by linarith) 2
  have h2 : ((τ - c) * (1 / R) + π) ^ 2 ≤ D := by
    rw [← hu, hDdef, ← sq_abs (u + π)]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
    have := abs_add_le u π
    rw [abs_of_pos hπ] at this; linarith
  have f1 := fejer_ge_num_div hb (τ - c) 0 h1
  have f2 := fejer_ge_num_div hb (τ - c) π h2
  rw [zero_div, add_zero, add_zero, ← hu] at f1
  rw [show π / (1 / R) = π * R by field_simp, ← hu, Real.cos_add_pi] at f2
  have hsum : 4 * (1 / R) / D
      ≤ fejerBandProfile (1 / R) (τ - c) + fejerBandProfile (1 / R) (τ - c + π * R) := by
    have e : 4 * (1 / R) / D = (1 / R) * (2 - 2 * Real.cos u) / D
        + (1 / R) * (2 - 2 * -Real.cos u) / D := by field_simp; ring
    rw [e]; exact add_le_add f1 f2
  have hDle : D ≤ 8 * π ^ 2 * (1 + u ^ 2) := by
    rw [hDdef]
    have h3 : (|u| + 2 * π) ^ 2 ≤ 2 * u ^ 2 + 8 * π ^ 2 := by
      nlinarith [sq_nonneg (|u| - 2 * π), sq_abs u]
    have h4 : (2 : ℝ) ≤ 8 * π ^ 2 := by nlinarith [Real.pi_gt_three]
    nlinarith [sq_nonneg u]
  have hlor : lorentzW R c τ = (1 + u ^ 2)⁻¹ := by
    unfold lorentzW; rw [hu]; congr 2; ring
  rw [hlor]
  have hpos : 0 < 1 + u ^ 2 := by positivity
  calc (1 + u ^ 2)⁻¹ = 2 * π ^ 2 * R * (4 * (1 / R) / (8 * π ^ 2 * (1 + u ^ 2))) := by
        field_simp; ring
    _ ≤ 2 * π ^ 2 * R * (4 * (1 / R) / D) := by
        gcongr
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)

theorem integrable_lorentzW {R : ℝ} (hR : 0 < R) (c : ℝ) : Integrable (lorentzW R c) := by
  have h := (integrable_inv_one_add_sq.comp_div (ne_of_gt hR)).comp_sub_right c
  refine h.congr (Filter.Eventually.of_forall fun τ => ?_)
  simp [lorentzW]

theorem continuous_PX' (X : ℝ) : Continuous (Zeta23.PX X) := by
  unfold Zeta23.PX; fun_prop

theorem abs_PX_le' (X τ : ℝ) : |Zeta23.PX X τ| ≤ (1 / π) * ∑ n ∈ primeRange X, acoef n := by
  rw [PX_eq, abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 1 / π)]
  refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun n _ => ?_)) (by positivity)
  rw [abs_mul, abs_of_nonneg (acoef_nonneg n)]
  exact mul_le_of_le_one_right (acoef_nonneg n) (Real.abs_cos_le_one _)

/-- **Lorentz-weighted mean value of the prime polynomial.** For `R ≥ 1`, `X ≥ 1`:
`∫ P_X(τ)² (1 + ((τ − c)/R)²)⁻¹ dτ ≤ 4π √e log X (3ψ(X) + R Σ_{n≤X} Λ(n)/n)`. -/
theorem integral_lorentz_mul_PX_sq_le {R : ℝ} (hR : 1 ≤ R) (c : ℝ) {X : ℝ} (hX : 1 ≤ X) :
    ∫ τ, lorentzW R c τ * Zeta23.PX X τ ^ 2
      ≤ 4 * π * Real.sqrt (Real.exp 1) * Real.log X
        * (3 * ∑ n ∈ primeRange X, (Λ n : ℝ) + R * ∑ n ∈ primeRange X, (Λ n : ℝ) / n) := by
  have hR0 : 0 < R := by linarith
  have hb : 0 < 1 / R := by positivity
  have hb1 : 1 / R ≤ 1 := by rw [div_le_one hR0]; exact hR
  set M := (1 / π) * ∑ n ∈ primeRange X, acoef n
  have hPb : ∀ τ, Zeta23.PX X τ ^ 2 ≤ M ^ 2 := fun τ => by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_PX_le' X τ) 2
  have hPc := continuous_PX' X
  have hbdd : ∀ g : ℝ → ℝ, Integrable g → Integrable fun τ => g τ * Zeta23.PX X τ ^ 2 :=
    fun g hg => hg.mul_bdd (c := M ^ 2) ((hPc.pow 2).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun τ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hPb τ)
  have hF1 : Integrable fun τ => fejerBandProfile (1 / R) (τ - c) :=
    (integrable_fejerBandProfile hb).comp_sub_right c
  have hF2 : Integrable fun τ => fejerBandProfile (1 / R) (τ - c + π * R) := by
    have := (integrable_fejerBandProfile hb).comp_sub_right (c - π * R)
    refine this.congr (Filter.Eventually.of_forall fun τ => ?_)
    simp only; congr 1; ring
  have hmono : ∫ τ, lorentzW R c τ * Zeta23.PX X τ ^ 2
      ≤ ∫ τ, 2 * π ^ 2 * R * (fejerBandProfile (1 / R) (τ - c) * Zeta23.PX X τ ^ 2
          + fejerBandProfile (1 / R) (τ - (c - π * R)) * Zeta23.PX X τ ^ 2) := by
    refine integral_mono (hbdd _ (integrable_lorentzW hR0 c)) ?_ fun τ => ?_
    · refine (((hbdd _ hF1).add (hbdd _ ((integrable_fejerBandProfile hb).comp_sub_right
        (c - π * R)))).const_mul _)
    · have h := lorentz_le_fejer_add_fejer hR0 c τ
      rw [show τ - (c - π * R) = τ - c + π * R by ring]
      have hP0 := sq_nonneg (Zeta23.PX X τ)
      nlinarith [mul_le_mul_of_nonneg_right h hP0]
  refine hmono.trans ?_
  rw [integral_const_mul, integral_add (hbdd _ hF1)
    (hbdd _ ((integrable_fejerBandProfile hb).comp_sub_right (c - π * R)))]
  have e1 := integral_fejer_mul_PX_sq_le hb hb1 c hX
  have e2 := integral_fejer_mul_PX_sq_le hb hb1 (c - π * R) hX
  have hπ := Real.pi_pos
  calc 2 * π ^ 2 * R * ((∫ τ, fejerBandProfile (1 / R) (τ - c) * Zeta23.PX X τ ^ 2)
        + ∫ τ, fejerBandProfile (1 / R) (τ - (c - π * R)) * Zeta23.PX X τ ^ 2)
      ≤ 2 * π ^ 2 * R * (2 * ((1 / π) * (Real.sqrt (Real.exp 1) * Real.log X
          * (3 * (1 / R) * ∑ n ∈ primeRange X, (Λ n : ℝ) + ∑ n ∈ primeRange X, (Λ n : ℝ) / n)))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith
    _ = 4 * π * Real.sqrt (Real.exp 1) * Real.log X
        * (3 * ∑ n ∈ primeRange X, (Λ n : ℝ) + R * ∑ n ∈ primeRange X, (Λ n : ℝ) / n) := by
        field_simp; ring

end GaloisForLFunctions.TransThresholdPairCorrelation
