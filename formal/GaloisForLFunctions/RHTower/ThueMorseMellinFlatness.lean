import Mathlib

/-!
# Thue--Morse radial flatness discharges the entire Mellin interface

The signed Thue--Morse generating product

`prod_{k >= 0} (1 - q^(2^k))`

is the counterexample carrier in
`thue-morse-entire-dirichlet-order-two.md`.  Its decisive local property is not merely that each
finite binary product vanishes to high order at `q = 1`: every requested finite order is available
from an initial segment of the *same* infinite product.

This module formalizes the reusable analytic handoff.

* `HasAllOrderZeroBound` packages concrete bounds `|f x| <= C_m x^m` on `(0,1]`.
* `HasAllOrderZeroBound.superpolynomialDecayAtZero` changes the natural-order quantifier into every
  real Mellin exponent, discharging the zero-side big-O hypothesis at an arbitrary `s`.
* `IsMellinFlatKernel` combines that zero-side condition with local integrability and exponential
  decay.  Its Mellin transform is convergent and analytic on the whole plane.
* `thueMorseFiniteKernel_flat_bound` proves the exact finite binary-product estimate
  `exp(-x) prod_{k<m}(1-exp(-2^k x)) <= 2^(m(m-1)/2) x^m`.
* `IsThueMorseKernelBound` is the limit-facing interface: any kernel dominated by every finite
  binary product has all-order zero bounds.  The capstone
  `mellin_analyticOnNhd_of_thueMorseKernelBound` discharges the Mellin interface directly.
* `thueMorseKernel` constructs the positive infinite product itself.  Its finite-prefix domination,
  local integrability, and exponential tail instantiate the capstone, proving that its Mellin
  transform is analytic on the whole plane.

The infinite product is identified with its signed coefficient series and, on `Re s > 1`, its
Mellin transform is identified with `Gamma(s)` times the corresponding shifted `LSeries`.  Its
matching quadratic radial lower bound is also formalized.  The remaining exact-order work is the
global upper maximum-modulus estimate for the entire Dirichlet continuation.
-/

noncomputable section

namespace RHTower

open MeasureTheory Set Filter Asymptotics Polynomial
open scoped Topology BigOperators

/-! ### §1 All-order radial decay and the Mellin interface -/

/-- **Superpolynomial decay at the positive side of zero.**  The kernel satisfies every real-power
big-O bound needed by the Mellin strip theorem. -/
def SuperpolynomialDecayAtZero {E : Type*} [NormedAddCommGroup E] (f : ℝ → E) : Prop :=
  ∀ b : ℝ, f =O[𝓝[>] 0] (fun x : ℝ => x ^ (-b))

/-- **Concrete all-order zero bounds.**  For every natural order `m`, the kernel is bounded by
`C_m x^m` throughout `(0,1]`.  This is the form supplied by finite Prouhet products. -/
def HasAllOrderZeroBound {E : Type*} [NormedAddCommGroup E] (f : ℝ → E) : Prop :=
  ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → x ≤ 1 → ‖f x‖ ≤ C * x ^ m

/-- **Natural all-order bounds discharge every real Mellin exponent.**  Given a requested real
exponent `-b`, choose a natural `m >= -b`; on `(0,1]`, increasing the exponent decreases the power.
Thus `|f x| <= C_m x^m <= C_m x^(-b)`. -/
theorem HasAllOrderZeroBound.superpolynomialDecayAtZero
    {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    (hf : HasAllOrderZeroBound f) : SuperpolynomialDecayAtZero f := by
  intro b
  obtain ⟨m, hm⟩ := exists_nat_ge (-b)
  obtain ⟨C, hC, hbound⟩ := hf m
  rw [Asymptotics.isBigO_iff]
  refine ⟨C, ?_⟩
  have hlt : ∀ᶠ x : ℝ in 𝓝[>] 0, x < 1 :=
    (eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hlt] with x hx hlt
  have hx0 : 0 < x := hx
  have hx1 : x ≤ 1 := hlt.le
  calc
    ‖f x‖ ≤ C * x ^ m := hbound x hx0 hx1
    _ = C * x ^ (m : ℝ) := by rw [Real.rpow_natCast]
    _ ≤ C * x ^ (-b) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge hx0 hx1 hm) hC
    _ = C * ‖x ^ (-b)‖ := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx0 _)]

/-- **A globally Mellin-flat kernel.**  It is locally integrable on `(0,infinity)`, decays
exponentially at infinity, and faster than every power at zero. -/
def IsMellinFlatKernel {E : Type*} [NormedAddCommGroup E] (f : ℝ → E) : Prop :=
  LocallyIntegrableOn f (Ioi 0) ∧
    (∃ a : ℝ, 0 < a ∧ f =O[atTop] (fun x : ℝ => Real.exp (-a * x))) ∧
    SuperpolynomialDecayAtZero f

/-- **A Mellin-flat kernel is Mellin-convergent at every complex parameter.**  At `s`, take the
zero exponent `b = Re(s)-1`; superpolynomial decay supplies the strict inequality required by
mathlib's exponential-tail Mellin theorem. -/
theorem IsMellinFlatKernel.mellinConvergent {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f : ℝ → E} (hf : IsMellinFlatKernel f) (s : ℂ) :
    MellinConvergent f s := by
  rcases hf with ⟨hloc, ⟨a, ha, htop⟩, hzero⟩
  exact mellinConvergent_of_isBigO_rpow_exp ha hloc htop (hzero (s.re - 1)) (by linarith)

/-- **The Mellin transform of a Mellin-flat kernel is differentiable on the whole plane.**  This
removes the pointwise strip hypotheses from `mellin_differentiableAt_of_isBigO_rpow_exp`. -/
theorem IsMellinFlatKernel.mellin_differentiable {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f : ℝ → E} (hf : IsMellinFlatKernel f) :
    Differentiable ℂ (mellin f) := by
  intro s
  rcases hf with ⟨hloc, ⟨a, ha, htop⟩, hzero⟩
  exact mellin_differentiableAt_of_isBigO_rpow_exp ha hloc htop
    (hzero (s.re - 1)) (by linarith)

/-- **Analytic form of the entire Mellin conclusion.** -/
theorem IsMellinFlatKernel.mellin_analyticOnNhd {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {f : ℝ → E} (hf : IsMellinFlatKernel f) :
    AnalyticOnNhd ℂ (mellin f) Set.univ :=
  hf.mellin_differentiable.differentiableOn.analyticOnNhd isOpen_univ

/-- **Uniform boundedness on finite Mellin strips.**  A Mellin-flat kernel has a bounded Mellin
transform on every closed vertical strip.  The norm of the integrand at an intermediate real part
is dominated pointwise by the sum of the two endpoint integrands: below `1` use the left endpoint,
above `1` use the right endpoint.  Both endpoint majorants are integrable by Mellin convergence. -/
theorem IsMellinFlatKernel.exists_mellin_vertical_strip_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℝ → E} (hf : IsMellinFlatKernel f) (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖mellin f s‖ ≤ C := by
  let ga : ℝ → ℝ := fun t => ‖(t : ℂ) ^ ((a : ℂ) - 1) • f t‖
  let gb : ℝ → ℝ := fun t => ‖(t : ℂ) ^ ((b : ℂ) - 1) • f t‖
  let C : ℝ := ∫ t in Ioi (0 : ℝ), ga t + gb t
  have hga : IntegrableOn ga (Ioi (0 : ℝ)) :=
    (hf.mellinConvergent (a : ℂ)).norm
  have hgb : IntegrableOn gb (Ioi (0 : ℝ)) :=
    (hf.mellinConvergent (b : ℂ)).norm
  have hgab : IntegrableOn (fun t => ga t + gb t) (Ioi (0 : ℝ)) := hga.add hgb
  have hC : 0 ≤ C := by
    dsimp [C]
    exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun t => by positivity)
  refine ⟨C, hC, fun s has hsb => ?_⟩
  have hsint : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • f t) (Ioi 0) :=
    hf.mellinConvergent s
  calc
    ‖mellin f s‖
        ≤ ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) • f t‖ := by
          rw [mellin]
          exact norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi (0 : ℝ), ga t + gb t := by
      apply setIntegral_mono_on hsint.norm hgab measurableSet_Ioi
      intro t ht
      have ht0 : 0 < t := ht
      have hpow : t ^ (s.re - 1) ≤ t ^ (a - 1) + t ^ (b - 1) := by
        rcases le_or_gt 1 t with ht1 | ht1
        · exact (Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)).trans
            (le_add_of_nonneg_left (Real.rpow_nonneg ht0.le _))
        · exact (Real.rpow_le_rpow_of_exponent_ge ht0 ht1.le (by linarith)).trans
            (le_add_of_nonneg_right (Real.rpow_nonneg ht0.le _))
      rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.sub_re,
        Complex.one_re]
      have hgaeq : ga t = t ^ (a - 1) * ‖f t‖ := by
        simp only [ga, norm_smul]
        rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.sub_re, Complex.ofReal_re,
          Complex.one_re]
      have hgbeq : gb t = t ^ (b - 1) * ‖f t‖ := by
        simp only [gb, norm_smul]
        rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.sub_re, Complex.ofReal_re,
          Complex.one_re]
      rw [hgaeq, hgbeq]
      nlinarith [norm_nonneg (f t)]
    _ = C := rfl

/-! ### §2 The finite binary product and its exact all-order bound -/

/-- The finite Thue--Morse Mellin kernel
`exp(-x) * prod_{k<m}(1-exp(-2^k x))`. -/
def thueMorseFiniteKernel (m : ℕ) (x : ℝ) : ℝ :=
  Real.exp (-x) * ∏ k ∈ Finset.range m, (1 - Real.exp (-((2 : ℝ) ^ k * x)))

/-! ### The finite integer product polynomial -/

/-- The integer polynomial whose radial evaluation is the finite Thue--Morse product.  Its exact
degree `2^m-1` records that the first `m` binary factors occupy precisely one coefficient block of
length `2^m`; the signed coefficient expansion is the next bridge to the Dirichlet carrier. -/
def thueMorsePolynomial (m : ℕ) : ℤ[X] :=
  ∏ k ∈ Finset.range m, (1 - X ^ (2 ^ k))

/-- The signed Thue--Morse coefficient, defined by binary even/odd recursion.  Appending a zero bit
preserves the sign and appending a one bit reverses it. -/
def thueMorseSign (n : ℕ) : ℤ :=
  Nat.evenOddRec 1 (fun _ a => a) (fun _ a => -a) n

@[simp] theorem thueMorseSign_zero : thueMorseSign 0 = 1 := by
  simp [thueMorseSign]

@[simp] theorem thueMorseSign_even (n : ℕ) :
    thueMorseSign (2 * n) = thueMorseSign n := by
  simp [thueMorseSign]

@[simp] theorem thueMorseSign_odd (n : ℕ) :
    thueMorseSign (2 * n + 1) = -thueMorseSign n := by
  simp [thueMorseSign]

/-- Every signed Thue--Morse coefficient is a unit of square one. -/
theorem thueMorseSign_sq (n : ℕ) : thueMorseSign n ^ 2 = 1 := by
  induction n using Nat.evenOddRec with
  | h0 => simp
  | h_even n ih => simpa using ih
  | h_odd n ih => simp [ih]

@[simp] theorem thueMorseSign_abs (n : ℕ) : |thueMorseSign n| = 1 := by
  have hsq := thueMorseSign_sq n
  nlinarith [abs_nonneg (thueMorseSign n), sq_abs (thueMorseSign n)]

/-- Adding a new leading binary digit reverses the Thue--Morse sign. -/
theorem thueMorseSign_add_two_pow {m n : ℕ} (hn : n < 2 ^ m) :
    thueMorseSign (n + 2 ^ m) = -thueMorseSign n := by
  induction m generalizing n with
  | zero =>
      have hn0 : n = 0 := by omega
      subst n
      rw [show 0 + 2 ^ 0 = 2 * 0 + 1 by norm_num,
        thueMorseSign_odd, thueMorseSign_zero]
  | succ m ih =>
      obtain ⟨q, hq | hq⟩ := Nat.even_or_odd' n
      · subst n
        have hqbound : q < 2 ^ m := by
          rw [pow_succ] at hn
          omega
        rw [pow_succ]
        have harg : 2 * q + 2 ^ m * 2 = 2 * (q + 2 ^ m) := by omega
        rw [harg, thueMorseSign_even, thueMorseSign_even, ih hqbound]
      · subst n
        have hqbound : q < 2 ^ m := by
          rw [pow_succ] at hn
          omega
        rw [pow_succ]
        have harg : 2 * q + 1 + 2 ^ m * 2 = 2 * (q + 2 ^ m) + 1 := by omega
        rw [harg, thueMorseSign_odd, thueMorseSign_odd, ih hqbound]

@[simp] theorem thueMorsePolynomial_zero : thueMorsePolynomial 0 = 1 := by
  simp [thueMorsePolynomial]

/-- Adding one binary scale appends the factor `1-X^(2^m)`. -/
theorem thueMorsePolynomial_succ (m : ℕ) :
    thueMorsePolynomial (m + 1) =
      thueMorsePolynomial m * (1 - X ^ (2 ^ m)) := by
  simp [thueMorsePolynomial, Finset.prod_range_succ]

/-- Radial evaluation of the integer polynomial is exactly the finite binary product. -/
theorem eval₂_thueMorsePolynomial_exp_neg (m : ℕ) (x : ℝ) :
    (thueMorsePolynomial m).eval₂ (Int.castRingHom ℝ) (Real.exp (-x)) =
      ∏ k ∈ Finset.range m, (1 - Real.exp (-((2 : ℝ) ^ k * x))) := by
  rw [thueMorsePolynomial, eval₂_finsetProd]
  apply Finset.prod_congr rfl
  intro k hk
  simp only [eval₂_sub, eval₂_one, eval₂_pow, eval₂_X]
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring_nf

/-- Each binary factor has its displayed power as exact degree. -/
theorem thueMorsePolynomial_factor_natDegree (k : ℕ) :
    (1 - (X : ℤ[X]) ^ (2 ^ k)).natDegree = 2 ^ k := by
  rw [show 1 - (X : ℤ[X]) ^ (2 ^ k) = -((X : ℤ[X]) ^ (2 ^ k) - C 1) by
      simp only [C_1]
      ring_nf,
    natDegree_neg, natDegree_X_pow_sub_C]

/-- The sum of the first `m` binary place values is `2^m-1`. -/
theorem sum_two_pow_range (m : ℕ) :
    ∑ k ∈ Finset.range m, 2 ^ k = 2 ^ m - 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      omega

/-- The finite Thue--Morse product has exact degree `2^m-1`. -/
theorem thueMorsePolynomial_natDegree (m : ℕ) :
    (thueMorsePolynomial m).natDegree = 2 ^ m - 1 := by
  rw [thueMorsePolynomial, natDegree_prod]
  · calc
      ∑ i ∈ Finset.range m, (1 - (X : ℤ[X]) ^ (2 ^ i)).natDegree =
          ∑ i ∈ Finset.range m, 2 ^ i := by
            apply Finset.sum_congr rfl
            intro k hk
            exact thueMorsePolynomial_factor_natDegree k
      _ = 2 ^ m - 1 := sum_two_pow_range m
  · intro k hk hzero
    have heval := congrArg (fun P : ℤ[X] => P.eval 0) hzero
    simp at heval

/-- **Exact finite Thue--Morse coefficient identity.**  The depth-`m` binary product has coefficient
`thueMorseSign n` throughout the complete block `0 ≤ n < 2^m`, and vanishes beyond it.  The proof
uses the disjoint block recursion `P_{m+1}=P_m-X^(2^m)P_m`; adding the new leading binary digit
reverses every sign in the translated block. -/
theorem coeff_thueMorsePolynomial (m n : ℕ) :
    (thueMorsePolynomial m).coeff n = if n < 2 ^ m then thueMorseSign n else 0 := by
  induction m generalizing n with
  | zero =>
      by_cases hn : n = 0
      · subst n
        simp
      · simp [thueMorsePolynomial_zero, Polynomial.coeff_one, hn]
  | succ m ih =>
      rw [thueMorsePolynomial_succ, mul_sub, mul_one, coeff_sub, coeff_mul_X_pow']
      rw [ih]
      by_cases hlow : n < 2 ^ m
      · have hnot : ¬2 ^ m ≤ n := Nat.not_le.mpr hlow
        have hsucc : n < 2 ^ (m + 1) := by
          rw [pow_succ]
          omega
        simp [hnot, hlow, hsucc]
      · have hge : 2 ^ m ≤ n := Nat.le_of_not_gt hlow
        by_cases hhigh : n < 2 ^ (m + 1)
        · let d := n - 2 ^ m
          have hd : d < 2 ^ m := by
            dsimp [d]
            rw [pow_succ] at hhigh
            omega
          have hn : d + 2 ^ m = n := Nat.sub_add_cancel hge
          have hsign : thueMorseSign n = -thueMorseSign d := by
            rw [← hn]
            exact thueMorseSign_add_two_pow hd
          simp only [if_neg hlow, zero_sub, if_pos hge, if_pos hhigh]
          rw [show n - 2 ^ m = d by rfl, ih d, if_pos hd, hsign]
        · have hge2 : 2 ^ (m + 1) ≤ n := Nat.le_of_not_gt hhigh
          have hdge : 2 ^ m ≤ n - 2 ^ m := by
            rw [pow_succ] at hge2
            omega
          simp only [if_neg hlow, zero_sub, if_pos hge, if_neg hhigh]
          rw [ih (n - 2 ^ m), if_neg (Nat.not_lt.mpr hdge)]
          simp

/-- **Finite signed-product expansion.**  The binary product is exactly the polynomial whose first
`2^m` coefficients are the signed Thue--Morse sequence. -/
theorem thueMorsePolynomial_eq_sum (m : ℕ) :
    thueMorsePolynomial m =
      ∑ n ∈ Finset.range (2 ^ m), monomial n (thueMorseSign n) := by
  ext n
  rw [coeff_thueMorsePolynomial]
  by_cases hn : n < 2 ^ m
  · rw [if_pos hn]
    simp [coeff_monomial, hn]
  · rw [if_neg hn]
    simp [coeff_monomial, hn]

/-- The analytic finite kernel is `exp(-x)` times the radial evaluation of the integer polynomial. -/
theorem thueMorseFiniteKernel_eq_polynomial (m : ℕ) (x : ℝ) :
    thueMorseFiniteKernel m x = Real.exp (-x) *
      (thueMorsePolynomial m).eval₂ (Int.castRingHom ℝ) (Real.exp (-x)) := by
  rw [thueMorseFiniteKernel, eval₂_thueMorsePolynomial_exp_neg]

/-- **Finite radial coefficient expansion.**  The depth-`m` analytic kernel is the first `2^m`
terms of the shifted signed Thue--Morse exponential series.  This is the exact finite bridge from
the binary product carrier to its future Dirichlet coefficients. -/
theorem thueMorseFiniteKernel_eq_sum (m : ℕ) (x : ℝ) :
    thueMorseFiniteKernel m x =
      ∑ n ∈ Finset.range (2 ^ m),
        (thueMorseSign n : ℝ) * Real.exp (-(((n + 1 : ℕ) : ℝ) * x)) := by
  rw [thueMorseFiniteKernel_eq_polynomial, thueMorsePolynomial_eq_sum,
    eval₂_finsetSum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [eval₂_monomial]
  rw [show (Int.castRingHom ℝ) (thueMorseSign n) = (thueMorseSign n : ℝ) by rfl]
  rw [← Real.exp_nat_mul]
  calc
    Real.exp (-x) * ((thueMorseSign n : ℝ) * Real.exp ((n : ℝ) * -x)) =
        (thueMorseSign n : ℝ) * (Real.exp (-x) * Real.exp ((n : ℝ) * -x)) := by ring
    _ = (thueMorseSign n : ℝ) * Real.exp (-x + (n : ℝ) * -x) := by
      rw [Real.exp_add]
    _ = (thueMorseSign n : ℝ) * Real.exp (-(((n + 1 : ℕ) : ℝ) * x)) := by
      congr 2
      push_cast
      ring

/-- The exact coefficient accumulated by the first `m` binary scales:
`prod_{k<m} 2^k = 2^(m(m-1)/2)`. -/
def thueMorseFlatConstant (m : ℕ) : ℝ :=
  (2 : ℝ) ^ (m * (m - 1) / 2)

/-- Each finite binary factor is nonnegative on the positive real axis. -/
lemma one_sub_exp_neg_mul_nonneg {a x : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x) :
    0 ≤ 1 - Real.exp (-(a * x)) := by
  have hax : 0 ≤ a * x := mul_nonneg ha hx
  have : Real.exp (-(a * x)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hax)
  linarith

/-- The elementary flatness inequality `1-exp(-a*x) <= a*x` for `a,x >= 0`. -/
lemma one_sub_exp_neg_mul_le (a x : ℝ) :
    1 - Real.exp (-(a * x)) ≤ a * x := by
  have h := Real.add_one_le_exp (-(a * x))
  linarith

/-- On the unit interval the elementary exponential defect retains at least half of its linear
size.  The proof uses `exp u ≥ 1+u`, hence `exp(-u) ≤ (1+u)⁻¹`. -/
lemma half_le_one_sub_exp_neg {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    u / 2 ≤ 1 - Real.exp (-u) := by
  have hden : 0 < 1 + u := by linarith
  have hexp : 1 + u ≤ Real.exp u := by simpa [add_comm] using Real.add_one_le_exp u
  have hinv : (Real.exp u)⁻¹ ≤ (1 + u)⁻¹ :=
    (inv_le_inv₀ (Real.exp_pos u) hden).2 hexp
  rw [← Real.exp_neg] at hinv
  calc
    u / 2 ≤ u / (1 + u) := div_le_div_of_nonneg_left hu0 hden (by linarith)
    _ = 1 - (1 + u)⁻¹ := by field_simp; ring
    _ ≤ 1 - Real.exp (-u) := by linarith

/-- The finite Thue--Morse kernel is nonnegative on the positive real axis. -/
theorem thueMorseFiniteKernel_nonneg (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ thueMorseFiniteKernel m x := by
  apply mul_nonneg (Real.exp_pos _).le
  exact Finset.prod_nonneg fun k _ =>
    one_sub_exp_neg_mul_nonneg (by positivity : 0 ≤ (2 : ℝ) ^ k) hx

/-- Every finite binary kernel is uniformly dominated by the first exponential factor.  This is
the common integrable majorant used to pass its Mellin transform to the infinite product. -/
theorem thueMorseFiniteKernel_le_exp_neg (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    thueMorseFiniteKernel m x ≤ Real.exp (-x) := by
  rw [thueMorseFiniteKernel]
  nth_rewrite 2 [← mul_one (Real.exp (-x))]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  calc
    (∏ k ∈ Finset.range m, (1 - Real.exp (-((2 : ℝ) ^ k * x)))) ≤
        ∏ k ∈ Finset.range m, (1 : ℝ) := by
          apply Finset.prod_le_prod
          · intro k hk
            exact one_sub_exp_neg_mul_nonneg (by positivity) hx
          · intro k hk
            exact sub_le_self _ (Real.exp_pos _).le
    _ = 1 := by simp

/-- The product of the binary linear bounds has the exact closed form
`prod_{k<m}(2^k*x) = 2^(m(m-1)/2)*x^m`. -/
theorem prod_two_pow_mul (m : ℕ) (x : ℝ) :
    (∏ k ∈ Finset.range m, (2 : ℝ) ^ k * x) = thueMorseFlatConstant m * x ^ m := by
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.sum_range_id,
    Finset.prod_const, Finset.card_range, thueMorseFlatConstant]

/-- Closed form of the lower linear-factor product. -/
theorem prod_two_pow_mul_div_two (m : ℕ) (x : ℝ) :
    (∏ k ∈ Finset.range m, ((2 : ℝ) ^ k * x) / 2) =
      thueMorseFlatConstant m * x ^ m / (2 : ℝ) ^ m := by
  simp_rw [div_eq_mul_inv]
  rw [Finset.prod_mul_distrib, prod_two_pow_mul, Finset.prod_const,
    Finset.card_range]
  simp

/-- **Exact finite binary-product flatness.**  Every initial segment of length `m` contributes one
power of `x`, and the accumulated scale is exactly `2^(m(m-1)/2)`. -/
theorem thueMorseFiniteKernel_flat_bound (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    thueMorseFiniteKernel m x ≤ thueMorseFlatConstant m * x ^ m := by
  have hfactor0 : ∀ k ∈ Finset.range m,
      0 ≤ 1 - Real.exp (-((2 : ℝ) ^ k * x)) := fun k _ =>
    one_sub_exp_neg_mul_nonneg (by positivity) hx
  have hprod0 : 0 ≤ ∏ k ∈ Finset.range m, (1 - Real.exp (-((2 : ℝ) ^ k * x))) :=
    Finset.prod_nonneg hfactor0
  calc
    thueMorseFiniteKernel m x
        ≤ 1 * ∏ k ∈ Finset.range m, (1 - Real.exp (-((2 : ℝ) ^ k * x))) := by
          rw [thueMorseFiniteKernel]
          exact mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.mpr (by linarith)) hprod0
    _ = ∏ k ∈ Finset.range m, (1 - Real.exp (-((2 : ℝ) ^ k * x))) := one_mul _
    _ ≤ ∏ k ∈ Finset.range m, ((2 : ℝ) ^ k * x) :=
      Finset.prod_le_prod hfactor0 fun k _ =>
        one_sub_exp_neg_mul_le ((2 : ℝ) ^ k) x
    _ = thueMorseFlatConstant m * x ^ m := prod_two_pow_mul m x

/-! ### §3 Limit-facing interface and capstone -/

/-- **Binary-product domination interface.**  A candidate infinite kernel `K` is bounded in modulus
by every finite Thue--Morse product on `(0,1]`.  The actual positive infinite product has this
property because every omitted factor lies in `[0,1]`. -/
def IsThueMorseKernelBound {E : Type*} [NormedAddCommGroup E] (K : ℝ → E) : Prop :=
  ∀ (m : ℕ) (x : ℝ), 0 < x → x ≤ 1 → ‖K x‖ ≤ thueMorseFiniteKernel m x

/-- **Binary-product domination supplies natural bounds of every order.** -/
theorem IsThueMorseKernelBound.hasAllOrderZeroBound
    {E : Type*} [NormedAddCommGroup E] {K : ℝ → E}
    (hK : IsThueMorseKernelBound K) : HasAllOrderZeroBound K := by
  intro m
  refine ⟨thueMorseFlatConstant m, pow_nonneg (by norm_num) _, fun x hx hx1 => ?_⟩
  exact (hK m x hx hx1).trans (thueMorseFiniteKernel_flat_bound m hx.le)

/-- **Binary-product domination discharges every real zero-side Mellin exponent.** -/
theorem IsThueMorseKernelBound.superpolynomialDecayAtZero
    {E : Type*} [NormedAddCommGroup E] {K : ℝ → E}
    (hK : IsThueMorseKernelBound K) : SuperpolynomialDecayAtZero K :=
  hK.hasAllOrderZeroBound.superpolynomialDecayAtZero

/-- **Binary-product domination plus the two ordinary analytic side conditions constructs a
Mellin-flat kernel.**  The all-real-exponent hypothesis is derived, not supplied by the caller. -/
theorem IsThueMorseKernelBound.isMellinFlatKernel
    {E : Type*} [NormedAddCommGroup E] {K : ℝ → E}
    (hK : IsThueMorseKernelBound K) (hloc : LocallyIntegrableOn K (Ioi 0))
    {a : ℝ} (ha : 0 < a) (htop : K =O[atTop] (fun x : ℝ => Real.exp (-a * x))) :
    IsMellinFlatKernel K :=
  ⟨hloc, ⟨a, ha, htop⟩, hK.superpolynomialDecayAtZero⟩

/-- **Capstone: the binary constraint makes the Mellin transform analytic on the whole plane.**
The caller supplies only local integrability and one exponential tail; the entire zero-side family
of Mellin strip hypotheses is discharged by finite Thue--Morse product domination. -/
theorem mellin_analyticOnNhd_of_thueMorseKernelBound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {K : ℝ → E}
    (hK : IsThueMorseKernelBound K) (hloc : LocallyIntegrableOn K (Ioi 0))
    {a : ℝ} (ha : 0 < a) (htop : K =O[atTop] (fun x : ℝ => Real.exp (-a * x))) :
    AnalyticOnNhd ℂ (mellin K) Set.univ :=
  (hK.isMellinFlatKernel hloc ha htop).mellin_analyticOnNhd

/-! ### §4 The concrete infinite product -/

/-- The `k`-th positive radial factor `1 - exp (-2^k x)`. -/
def thueMorseFactor (k : ℕ) (x : ℝ) : ℝ :=
  1 - Real.exp (-((2 : ℝ) ^ k * x))

/-- For each `x > 0`, the exponential defects of the binary factors are summable.  Comparison with
the geometric series of ratio `exp (-x)` is enough because `k <= 2^k`. -/
lemma summable_exp_neg_two_pow_mul {x : ℝ} (hx : 0 < x) :
    Summable (fun k : ℕ => Real.exp (-((2 : ℝ) ^ k * x))) := by
  have hr0 : 0 ≤ Real.exp (-x) := (Real.exp_pos _).le
  have hr1 : Real.exp (-x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  refine (summable_geometric_of_lt_one hr0 hr1).of_nonneg_of_le (fun _ => (Real.exp_pos _).le) ?_
  intro k
  have hk_nat : k ≤ 2 ^ k := Nat.lt_two_pow_self.le
  have hk : (k : ℝ) ≤ (2 : ℝ) ^ k := by exact_mod_cast hk_nat
  calc
    Real.exp (-((2 : ℝ) ^ k * x)) ≤ Real.exp (-((k : ℝ) * x)) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    _ = Real.exp (-x) ^ k := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- The radial factor family has a convergent infinite product at every `x > 0`. -/
lemma thueMorseFactor_multipliable {x : ℝ} (hx : 0 < x) :
    Multipliable (fun k : ℕ => thueMorseFactor k x) := by
  have hsum := (summable_exp_neg_two_pow_mul hx).neg
  simpa [thueMorseFactor, sub_eq_add_neg] using
    Real.multipliable_one_add_of_summable hsum

/-- Every shifted tail of the radial factor family remains multipliable. -/
lemma thueMorseFactor_tail_multipliable {x : ℝ} (hx : 0 < x) (K : ℕ) :
    Multipliable (fun j : ℕ => thueMorseFactor (j + K) x) := by
  have hinj : Function.Injective (fun j : ℕ => j + K) := fun a b hab =>
    Nat.add_right_cancel hab
  have hsumtail : Summable (fun j : ℕ =>
      -Real.exp (-((2 : ℝ) ^ (j + K) * x))) :=
    (summable_exp_neg_two_pow_mul hx).neg.comp_injective hinj
  simpa [thueMorseFactor, sub_eq_add_neg] using
    Real.multipliable_one_add_of_summable hsumtail

/-- Every radial factor is nonnegative when `x` is nonnegative. -/
lemma thueMorseFactor_nonneg {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    0 ≤ thueMorseFactor k x := by
  exact one_sub_exp_neg_mul_nonneg (by positivity) hx

/-- Every radial factor is at most one. -/
lemma thueMorseFactor_le_one (x : ℝ) (k : ℕ) : thueMorseFactor k x ≤ 1 := by
  dsimp [thueMorseFactor]
  exact sub_le_self _ (Real.exp_pos _).le

/-- The concrete infinite radial product is nonnegative at every `x > 0`. -/
lemma thueMorse_tprod_nonneg {x : ℝ} (hx : 0 < x) :
    0 ≤ ∏' k : ℕ, thueMorseFactor k x := by
  exact ge_of_tendsto' (thueMorseFactor_multipliable hx).hasProd.tendsto_prod_nat
    (fun n => Finset.prod_nonneg fun k _ => thueMorseFactor_nonneg hx.le k)

/-- The concrete radial infinite product is strictly positive at every positive radius. -/
lemma thueMorse_tprod_pos {x : ℝ} (hx : 0 < x) :
    0 < ∏' k : ℕ, thueMorseFactor k x := by
  have hne : (∏' k : ℕ, thueMorseFactor k x) ≠ 0 := by
    refine tprod_one_add_ne_zero_of_summable
      (f := fun k : ℕ => -Real.exp (-((2 : ℝ) ^ k * x))) ?_ ?_
    · intro k
      dsimp
      have hpos : 0 < (2 : ℝ) ^ k * x := mul_pos (by positivity) hx
      exact sub_ne_zero.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hpos)).ne'
    · simpa only [norm_neg, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
        summable_exp_neg_two_pow_mul hx
  exact lt_of_le_of_ne (thueMorse_tprod_nonneg hx) (Ne.symm hne)

/-- The fixed positive tail product used in the matching lower-flatness bound. -/
def thueMorseTailConstant : ℝ :=
  ∏' j : ℕ, thueMorseFactor j 1

theorem thueMorseTailConstant_pos : 0 < thueMorseTailConstant :=
  thueMorse_tprod_pos one_pos

/-- Once the first omitted binary scale has crossed one, the remaining product is bounded below by
the fixed tail at radius one. -/
theorem thueMorse_tail_tprod_lower {J : ℕ} {x : ℝ} (hx : 0 < x)
    (hscale : 1 ≤ (2 : ℝ) ^ (J + 1) * x) :
    thueMorseTailConstant ≤
      ∏' j : ℕ, thueMorseFactor (j + (J + 1)) x := by
  have hbase : Multipliable (fun j : ℕ => thueMorseFactor j 1) :=
    thueMorseFactor_multipliable one_pos
  have htail : Multipliable (fun j : ℕ => thueMorseFactor (j + (J + 1)) x) :=
    thueMorseFactor_tail_multipliable hx (J + 1)
  rw [thueMorseTailConstant]
  apply le_of_tendsto_of_tendsto'
    hbase.hasProd.tendsto_prod_nat htail.hasProd.tendsto_prod_nat
  intro n
  apply Finset.prod_le_prod
  · intro j hj
    exact thueMorseFactor_nonneg zero_le_one j
  · intro j hj
    have hpow : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ (j + (J + 1)) * x := by
      calc
        (2 : ℝ) ^ j = (2 : ℝ) ^ j * 1 := by ring
        _ ≤ (2 : ℝ) ^ j * ((2 : ℝ) ^ (J + 1) * x) :=
          mul_le_mul_of_nonneg_left hscale (by positivity)
        _ = (2 : ℝ) ^ (j + (J + 1)) * x := by rw [pow_add]; ring
    unfold thueMorseFactor
    simpa using sub_le_sub_left (Real.exp_le_exp.mpr (neg_le_neg hpow)) 1

/-- The concrete infinite radial product is at most one. -/
lemma thueMorse_tprod_le_one {x : ℝ} (hx : 0 < x) :
    (∏' k : ℕ, thueMorseFactor k x) ≤ 1 := by
  let P : ℕ → ℝ := fun n => ∏ k ∈ Finset.range n, thueMorseFactor k x
  have hanti : Antitone P := antitone_nat_of_succ_le fun n => by
    rw [show P (n + 1) = P n * thueMorseFactor n x by simp [P, Finset.prod_range_succ]]
    exact mul_le_of_le_one_right
      (Finset.prod_nonneg fun k _ => thueMorseFactor_nonneg hx.le k)
      (thueMorseFactor_le_one x n)
  exact le_of_tendsto
    (show Tendsto P atTop (𝓝 (∏' k : ℕ, thueMorseFactor k x)) from
      (thueMorseFactor_multipliable hx).hasProd.tendsto_prod_nat)
    (Eventually.of_forall fun n => by simpa [P] using hanti (Nat.zero_le n))

/-- Every finite prefix dominates the concrete infinite radial product. -/
lemma thueMorse_tprod_le_prefix {x : ℝ} (hx : 0 < x) (m : ℕ) :
    (∏' k : ℕ, thueMorseFactor k x) ≤ ∏ k ∈ Finset.range m, thueMorseFactor k x := by
  let P : ℕ → ℝ := fun n => ∏ k ∈ Finset.range n, thueMorseFactor k x
  have hanti : Antitone P := antitone_nat_of_succ_le fun n => by
    rw [show P (n + 1) = P n * thueMorseFactor n x by simp [P, Finset.prod_range_succ]]
    exact mul_le_of_le_one_right
      (Finset.prod_nonneg fun k _ => thueMorseFactor_nonneg hx.le k)
      (thueMorseFactor_le_one x n)
  exact le_of_tendsto
    (show Tendsto P atTop (𝓝 (∏' k : ℕ, thueMorseFactor k x)) from
      (thueMorseFactor_multipliable hx).hasProd.tendsto_prod_nat)
    ((eventually_ge_atTop m).mono fun n hn => hanti hn)

/-- The concrete real Thue--Morse Mellin kernel, extended by zero off the positive axis. -/
def thueMorseKernel (x : ℝ) : ℝ :=
  if 0 < x then Real.exp (-x) * ∏' k : ℕ, thueMorseFactor k x else 0

/-- Every radius in `(0,1]` lies between two consecutive binary scales. -/
theorem exists_thueMorse_dyadic_bracket {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    ∃ J : ℕ, (2 : ℝ) ^ J * x ≤ 1 ∧ 1 ≤ (2 : ℝ) ^ (J + 1) * x := by
  have hexists : ∃ J : ℕ, 1 ≤ (2 : ℝ) ^ (J + 1) * x := by
    obtain ⟨n : ℕ, hn⟩ := exists_nat_gt (1 / x)
    refine ⟨n, ?_⟩
    have hncast : 1 / x < (n : ℝ) := hn
    have hnpow_nat : n ≤ 2 ^ n := Nat.lt_two_pow_self.le
    have hnpow : (n : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast hnpow_nat
    have hone0 : 1 < (n : ℝ) * x := (div_lt_iff₀ hx).mp hncast
    have hone : 1 < (2 : ℝ) ^ n * x := by
      nlinarith [mul_le_mul_of_nonneg_right hnpow hx.le]
    exact hone.le.trans (by
      rw [pow_succ]
      nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n])
  let J := Nat.find hexists
  refine ⟨J, ?_, Nat.find_spec hexists⟩
  by_cases hJ : J = 0
  · rw [hJ]
    simpa using hx1
  · have hpred : J - 1 < J := Nat.sub_one_lt hJ
    have hnot := Nat.find_min hexists hpred
    have hsucc : J - 1 + 1 = J := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hJ)
    rw [hsucc] at hnot
    exact le_of_not_ge hnot

/-- **Matching dyadic lower bound.**  If `x` lies between the binary scales `J` and `J+1`, the
initial factors retain half their linear size and the entire omitted tail retains the fixed positive
constant `thueMorseTailConstant`. -/
theorem thueMorseKernel_lower_of_dyadic_bracket {J : ℕ} {x : ℝ} (hx : 0 < x)
    (hsmall : (2 : ℝ) ^ J * x ≤ 1)
    (hlarge : 1 ≤ (2 : ℝ) ^ (J + 1) * x) :
    Real.exp (-x) *
        (thueMorseFlatConstant (J + 1) * x ^ (J + 1) / (2 : ℝ) ^ (J + 1)) *
          thueMorseTailConstant ≤ thueMorseKernel x := by
  have hprefix :
      (∏ k ∈ Finset.range (J + 1), ((2 : ℝ) ^ k * x) / 2) ≤
        ∏ k ∈ Finset.range (J + 1), thueMorseFactor k x := by
    apply Finset.prod_le_prod
    · intro k hk
      positivity
    · intro k hk
      have hkJ : k ≤ J := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      have hpow : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ J := by
        gcongr
        norm_num
      have hu0 : 0 ≤ (2 : ℝ) ^ k * x := mul_nonneg (by positivity) hx.le
      have hu1 : (2 : ℝ) ^ k * x ≤ 1 :=
        (mul_le_mul_of_nonneg_right hpow hx.le).trans hsmall
      unfold thueMorseFactor
      exact half_le_one_sub_exp_neg hu0 hu1
  have htail := thueMorse_tail_tprod_lower hx hlarge
  have htailMult := thueMorseFactor_tail_multipliable hx (J + 1)
  have hsplit := htailMult.prod_mul_tprod_nat_mul'
    (f := fun k : ℕ => thueMorseFactor k x)
  have hprefix0 : 0 ≤ ∏ k ∈ Finset.range (J + 1), ((2 : ℝ) ^ k * x) / 2 :=
    Finset.prod_nonneg fun k hk => by positivity
  have htail0 : 0 ≤ thueMorseTailConstant := thueMorseTailConstant_pos.le
  have hprod :
      (∏ k ∈ Finset.range (J + 1), ((2 : ℝ) ^ k * x) / 2) *
          thueMorseTailConstant ≤
        (∏ k ∈ Finset.range (J + 1), thueMorseFactor k x) *
          ∏' j : ℕ, thueMorseFactor (j + (J + 1)) x := by
    exact mul_le_mul hprefix htail htail0
      (Finset.prod_nonneg fun k hk => thueMorseFactor_nonneg hx.le k)
  rw [prod_two_pow_mul_div_two] at hprod
  rw [thueMorseKernel, if_pos hx, ← hsplit]
  simpa [mul_assoc] using
    mul_le_mul_of_nonneg_left hprod (Real.exp_pos (-x)).le

/-- Existential form of the matching lower bound, with the correct binary scale constructed from
the radius rather than supplied by the caller. -/
theorem thueMorseKernel_exists_dyadic_lower {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    ∃ J : ℕ,
      (2 : ℝ) ^ J * x ≤ 1 ∧ 1 ≤ (2 : ℝ) ^ (J + 1) * x ∧
      Real.exp (-x) *
          (thueMorseFlatConstant (J + 1) * x ^ (J + 1) / (2 : ℝ) ^ (J + 1)) *
            thueMorseTailConstant ≤ thueMorseKernel x := by
  obtain ⟨J, hsmall, hlarge⟩ := exists_thueMorse_dyadic_bracket hx hx1
  exact ⟨J, hsmall, hlarge, thueMorseKernel_lower_of_dyadic_bracket hx hsmall hlarge⟩

private theorem two_pow_eq_exp_nat_mul_log (n : ℕ) :
    (2 : ℝ) ^ n = Real.exp ((n : ℝ) * Real.log 2) := by
  calc
    (2 : ℝ) ^ n = Real.exp (Real.log 2) ^ n := by rw [Real.exp_log (by norm_num)]
    _ = Real.exp ((n : ℝ) * Real.log 2) := by rw [Real.exp_nat_mul]

private theorem thueMorse_dyadic_bracket_log_bounds {J : ℕ} {y : ℝ}
    (hsmall : (2 : ℝ) ^ J * Real.exp (-y) ≤ 1)
    (hlarge : 1 ≤ (2 : ℝ) ^ (J + 1) * Real.exp (-y)) :
    ((J : ℝ) + 1 - 1) * Real.log 2 ≤ y ∧
      y ≤ ((J : ℝ) + 1) * Real.log 2 := by
  have hs : Real.exp ((J : ℝ) * Real.log 2 - y) ≤ Real.exp 0 := by
    simpa [two_pow_eq_exp_nat_mul_log, ← Real.exp_add] using hsmall
  have hl : Real.exp 0 ≤ Real.exp (((J + 1 : ℕ) : ℝ) * Real.log 2 - y) := by
    simpa [two_pow_eq_exp_nat_mul_log, ← Real.exp_add] using hlarge
  have hs' := Real.exp_le_exp.mp hs
  have hl' := Real.exp_le_exp.mp hl
  push_cast at hl'
  constructor <;> linarith

private theorem natCast_triangular (m : ℕ) :
    ((m * (m - 1) / 2 : ℕ) : ℝ) = (m : ℝ) * ((m : ℝ) - 1) / 2 := by
  by_cases hm : m = 0
  · subst m
    norm_num
  · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
    have hnat := Finset.sum_range_id_mul_two m
    have hcast :
        ((∑ i ∈ Finset.range m, i : ℕ) : ℝ) * 2 =
          (m : ℝ) * ((m : ℝ) - 1) := by
      exact_mod_cast hnat
    rw [Finset.sum_range_id] at hcast
    nlinarith

/-- Logarithmic form of the exact binary-prefix flatness constant. -/
theorem thueMorseFlatConstant_eq_exp (m : ℕ) :
    thueMorseFlatConstant m =
      Real.exp (((m : ℝ) * ((m : ℝ) - 1) / 2) * Real.log 2) := by
  rw [thueMorseFlatConstant, two_pow_eq_exp_nat_mul_log, natCast_triangular]

private theorem dyadic_quadratic_exponent_lower {L y m : ℝ}
    (hL : 0 < L) (hlow : (m - 1) * L ≤ y) (hhigh : y ≤ m * L) :
    m * (m - 1) / 2 * L - m * L - m * y ≥
      -y ^ 2 / (2 * L) - 3 * y / 2 - L := by
  let d := m * L - y
  have hd0 : 0 ≤ d := by dsimp [d]; linarith
  have hdL : d ≤ L := by dsimp [d]; nlinarith
  have hprod : 0 ≤ (d - L) * (d - 2 * L) :=
    mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  have hden : 0 < 2 * L := by positivity
  have heq : -y ^ 2 / (2 * L) - 3 * y / 2 - L =
      (-y ^ 2 - 3 * L * y - 2 * L ^ 2) / (2 * L) := by
    field_simp
  rw [heq]
  apply (div_le_iff₀ hden).2
  dsimp [d] at hprod
  nlinarith

/-- The explicit positive constant in the quadratic radial lower bound. -/
def thueMorseRadialLowerConstant : ℝ :=
  thueMorseTailConstant * Real.exp (-1 - Real.log 2)

theorem thueMorseRadialLowerConstant_pos : 0 < thueMorseRadialLowerConstant :=
  mul_pos thueMorseTailConstant_pos (Real.exp_pos _)

private theorem thueMorse_explicit_lower_eq_exp (J : ℕ) (y : ℝ) :
    Real.exp (-Real.exp (-y)) *
        (thueMorseFlatConstant (J + 1) * Real.exp (-y) ^ (J + 1) /
          (2 : ℝ) ^ (J + 1)) * thueMorseTailConstant =
      thueMorseTailConstant * Real.exp
        (-Real.exp (-y) +
          (((J : ℝ) + 1) * (((J : ℝ) + 1) - 1) / 2 * Real.log 2 -
            ((J : ℝ) + 1) * Real.log 2 -
            ((J : ℝ) + 1) * y)) := by
  let m : ℝ := (J : ℝ) + 1
  rw [thueMorseFlatConstant_eq_exp, two_pow_eq_exp_nat_mul_log]
  rw [← Real.exp_nat_mul]
  push_cast
  change Real.exp (-Real.exp (-y)) *
      (Real.exp (m * (m - 1) / 2 * Real.log 2) *
        Real.exp (m * -y) / Real.exp (m * Real.log 2)) * thueMorseTailConstant =
    thueMorseTailConstant * Real.exp
      (-Real.exp (-y) + (m * (m - 1) / 2 * Real.log 2 -
        m * Real.log 2 - m * y))
  rw [div_eq_mul_inv, ← Real.exp_neg]
  calc
    Real.exp (-Real.exp (-y)) *
          (Real.exp (m * (m - 1) / 2 * Real.log 2) *
            Real.exp (m * -y) * Real.exp (-(m * Real.log 2))) *
          thueMorseTailConstant =
        thueMorseTailConstant *
          (Real.exp (-Real.exp (-y)) *
            Real.exp (m * (m - 1) / 2 * Real.log 2) *
            Real.exp (m * -y) * Real.exp (-(m * Real.log 2))) := by ring
    _ = thueMorseTailConstant * Real.exp
        (-Real.exp (-y) + m * (m - 1) / 2 * Real.log 2 + m * -y -
          m * Real.log 2) := by
            have harg :
                -Real.exp (-y) + m * (m - 1) / 2 * Real.log 2 + m * -y -
                    m * Real.log 2 =
                  ((-Real.exp (-y) + m * (m - 1) / 2 * Real.log 2) + m * -y) +
                    (-(m * Real.log 2)) := by ring
            rw [harg, Real.exp_add, Real.exp_add, Real.exp_add]
    _ = thueMorseTailConstant * Real.exp
        (-Real.exp (-y) + (m * (m - 1) / 2 * Real.log 2 -
          m * Real.log 2 - m * y)) := by
            congr 2
            ring

/-- **Matching quadratic radial flatness.**  In logarithmic radius `x=exp(-y)`, the concrete
Thue--Morse product is bounded below by a positive constant times
`exp(-y²/(2 log 2) - 3y/2)`.  Together with the finite-prefix upper bounds, this is the sharp
quadratic lower half of the paper's two-sided flatness law. -/
theorem thueMorseKernel_radial_quadratic_lower {y : ℝ} (hy : 0 ≤ y) :
    thueMorseRadialLowerConstant *
        Real.exp (-y ^ 2 / (2 * Real.log 2) - 3 * y / 2) ≤
      thueMorseKernel (Real.exp (-y)) := by
  have hx : 0 < Real.exp (-y) := Real.exp_pos _
  have hx1 : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  obtain ⟨J, hsmall, hlarge⟩ := exists_thueMorse_dyadic_bracket hx hx1
  have hkernel := thueMorseKernel_lower_of_dyadic_bracket hx hsmall hlarge
  rw [thueMorse_explicit_lower_eq_exp] at hkernel
  have hlogs := thueMorse_dyadic_bracket_log_bounds hsmall hlarge
  let m : ℝ := ((J + 1 : ℕ) : ℝ)
  have hquad := dyadic_quadratic_exponent_lower
    (L := Real.log 2) (y := y) (m := m) (Real.log_pos (by norm_num))
    (by simpa [m] using hlogs.1) (by simpa [m] using hlogs.2)
  apply le_trans ?_ hkernel
  rw [thueMorseRadialLowerConstant]
  have hxneg : -1 ≤ -Real.exp (-y) := by linarith [hx1]
  rw [mul_assoc, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ thueMorseTailConstant_pos.le
  apply Real.exp_le_exp.mpr
  dsimp [m] at hquad
  push_cast at hquad
  nlinarith

/-- The concrete real kernel is nonnegative. -/
theorem thueMorseKernel_nonneg (x : ℝ) : 0 ≤ thueMorseKernel x := by
  by_cases hx : 0 < x
  · rw [thueMorseKernel, if_pos hx]
    exact mul_nonneg (Real.exp_pos _).le (thueMorse_tprod_nonneg hx)
  · simp [thueMorseKernel, hx]

/-- The shifted signed radial Thue--Morse series is absolutely summable at every positive radius. -/
theorem thueMorseRadialSeries_summable {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ =>
      (thueMorseSign n : ℝ) * Real.exp (-(((n + 1 : ℕ) : ℝ) * x))) := by
  let r : ℝ := Real.exp (-x)
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hgeom : Summable (fun n : ℕ => r ^ (n + 1)) := by
    have h := (summable_geometric_of_norm_lt_one hr1).mul_left r
    simpa [pow_succ, mul_comm] using h
  apply Summable.of_norm_bounded hgeom
  intro n
  have hsign : ‖(thueMorseSign n : ℝ)‖ = 1 := by
    rw [Real.norm_eq_abs, ← Int.cast_abs, thueMorseSign_abs]
    norm_num
  have hexp : Real.exp (-(((n + 1 : ℕ) : ℝ) * x)) = r ^ (n + 1) := by
    change Real.exp (-(((n + 1 : ℕ) : ℝ) * x)) = Real.exp (-x) ^ (n + 1)
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [norm_mul, hsign, one_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hexp]

/-- Finite binary kernels converge pointwise to the concrete infinite-product kernel. -/
theorem thueMorseFiniteKernel_tendsto {x : ℝ} (hx : 0 < x) :
    Tendsto (fun m : ℕ => thueMorseFiniteKernel m x) atTop (𝓝 (thueMorseKernel x)) := by
  have hprod := (thueMorseFactor_multipliable hx).hasProd.tendsto_prod_nat
  have hmul := hprod.const_mul (Real.exp (-x))
  simpa only [thueMorseFiniteKernel, thueMorseFactor, thueMorseKernel, if_pos hx] using hmul

/-- **Infinite product-to-series identity.**  For every positive radius, the concrete binary
infinite product kernel is exactly the shifted signed Thue--Morse exponential series.  This closes
the product/series half of the remaining Dirichlet-carrier bridge. -/
theorem thueMorseKernel_eq_tsum {x : ℝ} (hx : 0 < x) :
    thueMorseKernel x = ∑' n : ℕ,
      (thueMorseSign n : ℝ) * Real.exp (-(((n + 1 : ℕ) : ℝ) * x)) := by
  let f : ℕ → ℝ := fun n =>
    (thueMorseSign n : ℝ) * Real.exp (-(((n + 1 : ℕ) : ℝ) * x))
  have hf : Summable f := thueMorseRadialSeries_summable hx
  have hpartial : Tendsto (fun m : ℕ => ∑ n ∈ Finset.range (2 ^ m), f n)
      atTop (𝓝 (∑' n, f n)) := by
    have htwo : Tendsto (fun m : ℕ => 2 ^ m) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2)
    exact hf.hasSum.tendsto_sum_nat.comp htwo
  have hkernel := thueMorseFiniteKernel_tendsto hx
  have heq : (fun m : ℕ => thueMorseFiniteKernel m x) =
      fun m : ℕ => ∑ n ∈ Finset.range (2 ^ m), f n := by
    funext m
    exact thueMorseFiniteKernel_eq_sum m x
  rw [heq] at hkernel
  exact tendsto_nhds_unique hkernel hpartial

/-! ### The shifted signed Dirichlet carrier -/

/-- The shifted signed Thue--Morse coefficient sequence.  Index zero is set to zero to match
mathlib's `LSeries` convention; index `n+1` carries `thueMorseSign n`. -/
def thueMorseDirichletCoeff (n : ℕ) : ℂ :=
  if n = 0 then 0 else (thueMorseSign (n - 1) : ℤ)

@[simp] theorem thueMorseDirichletCoeff_zero : thueMorseDirichletCoeff 0 = 0 := by
  simp [thueMorseDirichletCoeff]

@[simp] theorem thueMorseDirichletCoeff_succ (n : ℕ) :
    thueMorseDirichletCoeff (n + 1) = (thueMorseSign n : ℂ) := by
  simp [thueMorseDirichletCoeff]

theorem thueMorseDirichletCoeff_norm_le_one (n : ℕ) :
    ‖thueMorseDirichletCoeff n‖ ≤ 1 := by
  by_cases hn : n = 0
  · subst n
    simp
  · rw [thueMorseDirichletCoeff, if_neg hn, Complex.norm_intCast,
      ← Int.cast_abs, thueMorseSign_abs]
    norm_num

/-- The shifted signed coefficient sequence has an absolutely convergent `LSeries` on `Re s>1`. -/
theorem thueMorseDirichletCoeff_lseriesSummable {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable thueMorseDirichletCoeff s :=
  LSeriesSummable_of_bounded_of_one_lt_re
    (fun n _ => thueMorseDirichletCoeff_norm_le_one n) hs

/-- The mathlib `LSeries` is the naturally shifted signed Dirichlet sum. -/
theorem LSeries_thueMorseDirichletCoeff_eq_tsum {s : ℂ} (hs : 1 < s.re) :
    LSeries thueMorseDirichletCoeff s =
      ∑' n : ℕ, (thueMorseSign n : ℂ) * ((n + 1 : ℕ) : ℂ) ^ (-s) := by
  have hsum : Summable (fun n => LSeries.term thueMorseDirichletCoeff s n) :=
    thueMorseDirichletCoeff_lseriesSummable hs
  have hshift := hsum.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, LSeries.term_zero, zero_add] at hshift
  rw [LSeries, ← hshift]
  apply tsum_congr
  intro n
  rw [LSeries.term_def₀ thueMorseDirichletCoeff_zero,
    thueMorseDirichletCoeff_succ]

/-- The weighted coefficient norms required by Mellin--Dirichlet interchange are summable on
`Re s > 1`. -/
theorem thueMorseMellin_weight_summable {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ =>
      ‖(thueMorseSign n : ℂ)‖ / (((n + 1 : ℕ) : ℝ) ^ s.re)) := by
  have h := (Real.summable_one_div_nat_add_rpow 1 s.re).mpr hs
  refine h.congr fun n => ?_
  rw [Complex.norm_intCast, ← Int.cast_abs, thueMorseSign_abs]
  norm_num
  rw [abs_of_pos (by positivity : 0 < (n : ℝ) + 1)]

/-- The infinite product does not weaken the kernel's exponential tail. -/
theorem thueMorseKernel_le_exp_neg {x : ℝ} (hx : 0 < x) :
    thueMorseKernel x ≤ Real.exp (-x) := by
  rw [thueMorseKernel, if_pos hx]
  nth_rewrite 2 [← mul_one (Real.exp (-x))]
  exact mul_le_mul_of_nonneg_left (thueMorse_tprod_le_one hx) (Real.exp_pos _).le

/-- Every finite binary kernel dominates the concrete infinite kernel. -/
theorem thueMorseKernel_le_finite {x : ℝ} (hx : 0 < x) (m : ℕ) :
    thueMorseKernel x ≤ thueMorseFiniteKernel m x := by
  rw [thueMorseKernel, if_pos hx, thueMorseFiniteKernel]
  exact mul_le_mul_of_nonneg_left (thueMorse_tprod_le_prefix hx m) (Real.exp_pos _).le

/-- The complex-valued form of the concrete real kernel used by the Mellin transform. -/
def thueMorseMellinKernel (x : ℝ) : ℂ := (thueMorseKernel x : ℝ)

/-- On the negative real axis the Mellin transform is the bilateral Laplace transform of the
positive logarithmic radial source. -/
theorem mellin_thueMorse_neg_real_eq_integral (r : ℝ) :
    mellin thueMorseMellinKernel ((-r : ℝ) : ℂ) =
      ∫ y : ℝ, Real.exp (r * y) • thueMorseMellinKernel (Real.exp (-y)) := by
  rw [mellin_eq_fourier]
  simp [Real.fourier_eq', mul_comm]

/-- Real-valued form of the negative-axis logarithmic Mellin integral. -/
theorem mellin_thueMorse_neg_real_eq_realIntegral (r : ℝ) :
    mellin thueMorseMellinKernel ((-r : ℝ) : ℂ) =
      ((∫ y : ℝ, Real.exp (r * y) * thueMorseKernel (Real.exp (-y))) : ℝ) := by
  rw [mellin_thueMorse_neg_real_eq_integral]
  rw [← integral_complex_ofReal]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with y
  simp [thueMorseMellinKernel, Complex.real_smul]

/-- The signed exponential series converges to the complex Mellin kernel at every positive
radius.  This is the exact `HasSum` interface consumed by Mellin--Dirichlet interchange. -/
theorem thueMorseRadialSeries_hasSum_complex {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ =>
      (thueMorseSign n : ℂ) * Real.exp (-(((n + 1 : ℕ) : ℝ) * x)))
      (thueMorseMellinKernel x) := by
  have hreal := (thueMorseRadialSeries_summable hx).hasSum
  have hcomplex := Complex.hasSum_ofReal.mpr hreal
  simpa [thueMorseMellinKernel, thueMorseKernel_eq_tsum hx,
    Complex.ofReal_mul] using hcomplex

/-- **Unconditional Mellin--Dirichlet bridge.**  On the half-plane of absolute Dirichlet
convergence, the concrete infinite-product carrier has Mellin transform exactly equal to its
shifted Thue--Morse `LSeries` times the Gamma factor. -/
theorem mellin_thueMorseMellinKernel_eq_gamma_mul_LSeries
    {s : ℂ} (hs : 1 < s.re) :
    mellin thueMorseMellinKernel s =
      Complex.Gamma s * LSeries thueMorseDirichletCoeff s := by
  let a : ℕ → ℂ := fun n => (thueMorseSign n : ℂ)
  let p : ℕ → ℝ := fun n => ((n + 1 : ℕ) : ℝ)
  have hp : ∀ n, a n = 0 ∨ 0 < p n := fun n => Or.inr (by
    dsimp [p]
    exact_mod_cast Nat.succ_pos n)
  have hs0 : 0 < s.re := by linarith
  have hF : ∀ t ∈ Set.Ioi (0 : ℝ),
      HasSum (fun n => a n * Real.exp (-p n * t)) (thueMorseMellinKernel t) := by
    intro t ht
    convert thueMorseRadialSeries_hasSum_complex (x := t) ht using 1 with n
    funext n
    dsimp only [a, p]
    congr 2
    ring_nf
  have hweight : Summable (fun n => ‖a n‖ / p n ^ s.re) := by
    simpa [a, p] using thueMorseMellin_weight_summable hs
  have hmellin : HasSum (fun n => Complex.Gamma s * a n / (p n : ℂ) ^ s)
      (mellin thueMorseMellinKernel s) :=
    hasSum_mellin hp hs0 hF hweight
  rw [← hmellin.tsum_eq, LSeries_thueMorseDirichletCoeff_eq_tsum hs,
    ← tsum_mul_left]
  apply tsum_congr
  intro n
  dsimp [a, p]
  rw [div_eq_mul_inv, Complex.cpow_neg]
  ring

/-- The concrete infinite product discharges the finite-prefix domination interface. -/
theorem thueMorseMellinKernel_bound : IsThueMorseKernelBound thueMorseMellinKernel := by
  intro m x hx hx1
  rw [thueMorseMellinKernel, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (thueMorseKernel_nonneg x)]
  exact thueMorseKernel_le_finite hx m

/-- The concrete infinite product has a zero-side bound of every natural order. -/
theorem thueMorseMellinKernel_hasAllOrderZeroBound :
    HasAllOrderZeroBound thueMorseMellinKernel :=
  thueMorseMellinKernel_bound.hasAllOrderZeroBound

/-- The concrete real infinite-product kernel is measurable. -/
theorem thueMorseKernel_measurable : Measurable thueMorseKernel := by
  have hfac : ∀ k : ℕ, Measurable (fun x : ℝ => thueMorseFactor k x) := by
    intro k
    unfold thueMorseFactor
    fun_prop
  have hprod : Measurable (fun x : ℝ => ∏' k : ℕ, thueMorseFactor k x) :=
    Measurable.tprod hfac
  have hexp : Measurable (fun x : ℝ => Real.exp (-x)) := by fun_prop
  unfold thueMorseKernel
  exact Measurable.ite measurableSet_Ioi (hexp.mul hprod) measurable_const

/-- The complex-valued concrete kernel is measurable. -/
theorem thueMorseMellinKernel_measurable : Measurable thueMorseMellinKernel := by
  unfold thueMorseMellinKernel
  exact Complex.measurable_ofReal.comp thueMorseKernel_measurable

/-- The concrete complex-valued kernel has norm at most one on the whole real line. -/
theorem thueMorseMellinKernel_norm_le_one (x : ℝ) : ‖thueMorseMellinKernel x‖ ≤ 1 := by
  rw [thueMorseMellinKernel, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (thueMorseKernel_nonneg x)]
  by_cases hx : 0 < x
  · exact (thueMorseKernel_le_exp_neg hx).trans
      (Real.exp_le_one_iff.mpr (by linarith))
  · simp [thueMorseKernel, hx]

/-- Measurability and the uniform norm bound give local integrability on the positive axis. -/
theorem thueMorseMellinKernel_locallyIntegrableOn :
    LocallyIntegrableOn thueMorseMellinKernel (Ioi 0) := by
  have hconst : LocallyIntegrableOn (fun _ : ℝ => (1 : ℂ)) (Ioi 0) :=
    ContinuousOn.locallyIntegrableOn continuousOn_const measurableSet_Ioi
  exact hconst.mono thueMorseMellinKernel_measurable.aestronglyMeasurable
    (Eventually.of_forall fun x => by simpa using thueMorseMellinKernel_norm_le_one x)

/-- The concrete complex-valued kernel is big-O of `exp (-x)` at infinity. -/
theorem thueMorseMellinKernel_isBigO_exp :
    thueMorseMellinKernel =O[atTop] (fun x : ℝ => Real.exp (-1 * x)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [one_mul, neg_one_mul]
  calc
    ‖thueMorseMellinKernel x‖ = thueMorseKernel x := by
      rw [thueMorseMellinKernel, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (thueMorseKernel_nonneg x)]
    _ ≤ Real.exp (-x) := thueMorseKernel_le_exp_neg hx
    _ = ‖Real.exp (-x)‖ := by rw [Real.norm_of_nonneg (Real.exp_pos _).le]

/-- The concrete infinite product itself inhabits the full Mellin-flat-kernel interface. -/
theorem thueMorseMellinKernel_isMellinFlatKernel :
    IsMellinFlatKernel thueMorseMellinKernel :=
  thueMorseMellinKernel_bound.isMellinFlatKernel
    thueMorseMellinKernel_locallyIntegrableOn one_pos thueMorseMellinKernel_isBigO_exp

/-- **Concrete capstone.**  The Mellin transform of the positive Thue--Morse infinite product is
analytic on the whole complex plane. -/
theorem thueMorseMellinKernel_mellin_analyticOnNhd :
    AnalyticOnNhd ℂ (mellin thueMorseMellinKernel) Set.univ :=
  thueMorseMellinKernel_isMellinFlatKernel.mellin_analyticOnNhd

end RHTower
