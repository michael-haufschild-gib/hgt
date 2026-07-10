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

What is not formalized here: identification of the infinite product with the signed coefficient
series, its matching lower bound, or the exact Hadamard order-two type `(log 2)/2`.
-/

noncomputable section

namespace RHTower

open MeasureTheory Set Filter Asymptotics
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

/-! ### §2 The finite binary product and its exact all-order bound -/

/-- The finite Thue--Morse Mellin kernel
`exp(-x) * prod_{k<m}(1-exp(-2^k x))`. -/
def thueMorseFiniteKernel (m : ℕ) (x : ℝ) : ℝ :=
  Real.exp (-x) * ∏ k ∈ Finset.range m, (1 - Real.exp (-((2 : ℝ) ^ k * x)))

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

/-- The finite Thue--Morse kernel is nonnegative on the positive real axis. -/
theorem thueMorseFiniteKernel_nonneg (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ thueMorseFiniteKernel m x := by
  apply mul_nonneg (Real.exp_pos _).le
  exact Finset.prod_nonneg fun k _ =>
    one_sub_exp_neg_mul_nonneg (by positivity : 0 ≤ (2 : ℝ) ^ k) hx

/-- The product of the binary linear bounds has the exact closed form
`prod_{k<m}(2^k*x) = 2^(m(m-1)/2)*x^m`. -/
theorem prod_two_pow_mul (m : ℕ) (x : ℝ) :
    (∏ k ∈ Finset.range m, (2 : ℝ) ^ k * x) = thueMorseFlatConstant m * x ^ m := by
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.sum_range_id,
    Finset.prod_const, Finset.card_range, thueMorseFlatConstant]

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

/-- The concrete real kernel is nonnegative. -/
theorem thueMorseKernel_nonneg (x : ℝ) : 0 ≤ thueMorseKernel x := by
  by_cases hx : 0 < x
  · rw [thueMorseKernel, if_pos hx]
    exact mul_nonneg (Real.exp_pos _).le (thueMorse_tprod_nonneg hx)
  · simp [thueMorseKernel, hx]

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
