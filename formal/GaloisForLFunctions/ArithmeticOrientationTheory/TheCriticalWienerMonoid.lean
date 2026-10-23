import GaloisForLFunctions.TransHorizonIncidenceMechanics.CriticalWienerConvolutionsPreserveTheReceiver
import Mathlib.NumberTheory.LSeries.Convolution

/-!
# The critical Wiener monoid

The **critical Wiener algebra** of Trans-Horizon Incidence Mechanics is the class of kernels
`g : ℕ → ℝ` with `Σ_q |g(q)| q^{−1/2} < ∞` (`CriticalWiener`); its convolutions preserve paid
receivers (`receiverBounded_dirichletConv`).  This module proves that the class is what its name
says.

* **Closure** (`criticalWiener_dirichletConv`): the Dirichlet convolution of two critical Wiener
  kernels is critical Wiener, with the **submultiplicative norm**
  `Σ |g ⋆ h| q^{−1/2} ≤ (Σ |g| q^{−1/2}) (Σ |h| q^{−1/2})` (`tsum_abs_dirichletConv_le`).  The
  proof reads the absolute kernels as complex sequences and uses the L-series of their
  convolution at `s = ½`.
* **Unit and associativity** (`dirichletConv_unitKernel`, `dirichletConv_assoc`): the kernel
  `δ₁` is the unit away from `0` and convolution is associative, so the critical Wiener kernels
  form a monoid acting on weights.
* **Orbits** (`receiverBounded_orbit`): the paid class is a union of orbits of this monoid — the
  stability group of the orientation class "paid".

The field reads this as an index structure: "paid" is invariant under a monoid of compact-type
perturbations, exactly as a Fredholm index is; what is missing is the formula computing it.
-/

open Finset
open scoped LSeries.notation

namespace GaloisForLFunctions.ArithmeticOrientationTheory

open TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### Absolute kernels as complex sequences -/

/-- The absolute kernel `|g|` as a complex sequence. -/
def absWeight (g : ℕ → ℝ) : ℕ → ℂ := fun n => ((|g n| : ℝ) : ℂ)

/-- The critical point `s = ½` as a complex number. -/
def halfPoint : ℂ := ((1 / 2 : ℝ) : ℂ)

theorem halfPoint_re : halfPoint.re = 1 / 2 := by simp [halfPoint]

/-- The L-series term of the absolute kernel at `½` is `|g n| n^{−1/2}`, as a real number. -/
theorem term_absWeight (g : ℕ → ℝ) (n : ℕ) :
    LSeries.term (absWeight g) halfPoint n = ((|g n| * (n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero hn, absWeight, halfPoint, ← Complex.ofReal_natCast,
      ← Complex.ofReal_cpow (Nat.cast_nonneg n), ← Complex.ofReal_div, Real.rpow_neg (Nat.cast_nonneg n),
      div_eq_mul_inv]

theorem norm_term_absWeight (g : ℕ → ℝ) (n : ℕ) :
    ‖LSeries.term (absWeight g) halfPoint n‖ = |g n| * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  rw [term_absWeight, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

theorem criticalWiener_iff_summable_norm_term (g : ℕ → ℝ) :
    CriticalWiener g ↔ Summable (fun n => ‖LSeries.term (absWeight g) halfPoint n‖) := by
  unfold CriticalWiener
  simp_rw [norm_term_absWeight]

theorem lSeriesSummable_absWeight {g : ℕ → ℝ} (hg : CriticalWiener g) :
    LSeriesSummable (absWeight g) halfPoint :=
  Summable.of_norm ((criticalWiener_iff_summable_norm_term g).1 hg)

/-- The L-series of the absolute kernel at `½` is the critical Wiener norm, as a real number. -/
theorem lSeries_absWeight (g : ℕ → ℝ) :
    LSeries (absWeight g) halfPoint = ((∑' n : ℕ, |g n| * (n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  unfold LSeries
  rw [Complex.ofReal_tsum]
  exact tsum_congr fun n => term_absWeight g n

/-! ### The absolute convolution -/

/-- The absolute Dirichlet convolution `Σ_{d ∣ n} |a(d)| |b(n/d)|`. -/
def absConv (a b : ℕ → ℝ) (n : ℕ) : ℝ := ∑ d ∈ n.divisors, |a d| * |b (n / d)|

theorem absConv_nonneg (a b : ℕ → ℝ) (n : ℕ) : 0 ≤ absConv a b n :=
  sum_nonneg fun _ _ => by positivity

/-- The convolution is dominated by the absolute convolution. -/
theorem abs_dirichletConv_le (a b : ℕ → ℝ) (n : ℕ) :
    |RHTower.dirichletConv a b n| ≤ absConv a b n := by
  unfold RHTower.dirichletConv absConv
  refine (abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  exact sum_congr rfl fun d _ => abs_mul _ _

/-- The complex convolution of the absolute kernels is the absolute convolution. -/
theorem convolution_absWeight (a b : ℕ → ℝ) (n : ℕ) :
    (absWeight a ⍟ absWeight b) n = ((absConv a b n : ℝ) : ℂ) := by
  unfold LSeries.convolution
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun i j =>
      toArithmeticFunction (absWeight a) i * toArithmeticFunction (absWeight b) j)]
  unfold absConv
  push_cast
  refine sum_congr rfl fun d hd => ?_
  have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hd
  have hnd : n / d ≠ 0 :=
    (Nat.div_pos (Nat.divisor_le hd) (Nat.pos_of_mem_divisors hd)).ne'
  simp [toArithmeticFunction, hd0, hnd, absWeight]

/-- The L-series term of the absolute convolution at `½`, as a real number. -/
theorem term_convolution_absWeight (a b : ℕ → ℝ) (n : ℕ) :
    LSeries.term (absWeight a ⍟ absWeight b) halfPoint n =
      ((absConv a b n * (n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero hn, convolution_absWeight, halfPoint, ← Complex.ofReal_natCast,
      ← Complex.ofReal_cpow (Nat.cast_nonneg n), ← Complex.ofReal_div,
      Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]

theorem norm_term_convolution_absWeight (a b : ℕ → ℝ) (n : ℕ) :
    ‖LSeries.term (absWeight a ⍟ absWeight b) halfPoint n‖ =
      absConv a b n * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  rw [term_convolution_absWeight, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (absConv_nonneg a b n) (by positivity))]

/-- The absolute convolution of two critical Wiener kernels is summable against `n^{−1/2}`. -/
theorem summable_absConv_mul_rpow {a b : ℕ → ℝ} (ha : CriticalWiener a) (hb : CriticalWiener b) :
    Summable (fun n : ℕ => absConv a b n * (n : ℝ) ^ (-(1 / 2 : ℝ))) := by
  have hs : LSeriesSummable (absWeight a ⍟ absWeight b) halfPoint :=
    (lSeriesSummable_absWeight ha).convolution (lSeriesSummable_absWeight hb)
  have hre := Complex.reCLM.summable hs
  refine hre.congr fun n => ?_
  rw [term_convolution_absWeight]
  simp

/-! ### Closure and the submultiplicative norm -/

/-- **Closure**: the Dirichlet convolution of two critical Wiener kernels is critical Wiener. -/
theorem criticalWiener_dirichletConv {a b : ℕ → ℝ} (ha : CriticalWiener a)
    (hb : CriticalWiener b) : CriticalWiener (RHTower.dirichletConv a b) := by
  unfold CriticalWiener
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (summable_absConv_mul_rpow ha hb)
  exact mul_le_mul_of_nonneg_right (abs_dirichletConv_le a b n) (by positivity)

/-- **The critical Wiener norm is submultiplicative.** -/
theorem tsum_abs_dirichletConv_le {a b : ℕ → ℝ} (ha : CriticalWiener a) (hb : CriticalWiener b) :
    ∑' n : ℕ, |RHTower.dirichletConv a b n| * (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤
      (∑' n : ℕ, |a n| * (n : ℝ) ^ (-(1 / 2 : ℝ))) * ∑' n : ℕ, |b n| * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hs : LSeriesSummable (absWeight a ⍟ absWeight b) halfPoint :=
    (lSeriesSummable_absWeight ha).convolution (lSeriesSummable_absWeight hb)
  have h1 : ∑' n : ℕ, |RHTower.dirichletConv a b n| * (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤
      ∑' n : ℕ, absConv a b n * (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Summable.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_right (abs_dirichletConv_le a b n)
      (by positivity)) (criticalWiener_dirichletConv ha hb) (summable_absConv_mul_rpow ha hb)
  have h2 : ∑' n : ℕ, absConv a b n * (n : ℝ) ^ (-(1 / 2 : ℝ)) =
      (LSeries (absWeight a ⍟ absWeight b) halfPoint).re := by
    unfold LSeries
    rw [Complex.re_tsum hs]
    exact tsum_congr fun n => by rw [term_convolution_absWeight]; simp
  have h3 : (LSeries (absWeight a ⍟ absWeight b) halfPoint).re =
      (∑' n : ℕ, |a n| * (n : ℝ) ^ (-(1 / 2 : ℝ))) * ∑' n : ℕ, |b n| * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [LSeries_convolution' (lSeriesSummable_absWeight ha) (lSeriesSummable_absWeight hb),
      lSeries_absWeight a, lSeries_absWeight b, ← Complex.ofReal_mul, Complex.ofReal_re]
  linarith

/-! ### Unit and associativity -/

/-- The unit kernel `δ₁`. -/
def unitKernel : ℕ → ℝ := fun n => if n = 1 then 1 else 0

theorem criticalWiener_unitKernel : CriticalWiener unitKernel := by
  unfold CriticalWiener
  refine summable_of_ne_finset_zero (s := {1}) fun n hn => ?_
  simp only [mem_singleton] at hn
  simp [unitKernel, hn]

/-- `δ₁` is a unit for convolution away from `0`. -/
theorem dirichletConv_unitKernel (c : ℕ → ℝ) {n : ℕ} (hn : n ≠ 0) :
    RHTower.dirichletConv unitKernel c n = c n := by
  unfold RHTower.dirichletConv
  rw [sum_eq_single 1]
  · simp [unitKernel]
  · intro d _ hd
    simp [unitKernel, hd]
  · intro h
    exact absurd (Nat.one_mem_divisors.2 hn) h

/-- Dirichlet convolution is the product of arithmetic functions. -/
theorem dirichletConv_eq_toArithmeticFunction (a b : ℕ → ℝ) :
    RHTower.dirichletConv a b = ⇑(toArithmeticFunction a * toArithmeticFunction b) := by
  funext n
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun i j => toArithmeticFunction a i * toArithmeticFunction b j)]
  unfold RHTower.dirichletConv
  refine sum_congr rfl fun d hd => ?_
  have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
  have hnd : n / d ≠ 0 :=
    (Nat.div_pos (Nat.divisor_le hd) (Nat.pos_of_mem_divisors hd)).ne'
  simp [toArithmeticFunction, hd0, hnd]

/-- **Associativity** of Dirichlet convolution. -/
theorem dirichletConv_assoc (a b c : ℕ → ℝ) :
    RHTower.dirichletConv (RHTower.dirichletConv a b) c =
      RHTower.dirichletConv a (RHTower.dirichletConv b c) := by
  rw [dirichletConv_eq_toArithmeticFunction a b, dirichletConv_eq_toArithmeticFunction b c,
    dirichletConv_eq_toArithmeticFunction, dirichletConv_eq_toArithmeticFunction,
    ArithmeticFunction.toArithmeticFunction_eq_self, ArithmeticFunction.toArithmeticFunction_eq_self,
    mul_assoc]

/-! ### Orbits of the paid class -/

/-- **The paid class is a union of monoid orbits**: a paid weight with summable mean stays paid
under every critical Wiener kernel, and so under every finite product of them. -/
theorem receiverBounded_orbit {c : ℕ → ℝ} (hc : Summable (fun d : ℕ => |c d / d|))
    (hcB : ReceiverBounded c) {g h : ℕ → ℝ} (hg : CriticalWiener g) (hh : CriticalWiener h) :
    ReceiverBounded (RHTower.dirichletConv (RHTower.dirichletConv g h) c) :=
  receiverBounded_dirichletConv (criticalWiener_dirichletConv hg hh) hc hcB

end

end GaloisForLFunctions.ArithmeticOrientationTheory
