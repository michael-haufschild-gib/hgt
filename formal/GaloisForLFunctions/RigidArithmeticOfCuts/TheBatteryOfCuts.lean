import GaloisForLFunctions.RigidArithmeticOfCuts.TheCutSystemOverACurve
import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheBatteryOfAuxiliaryDynamics
import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheLocalFactorTricklesDownByRamanujan

/-!
# The battery of cuts

In degree two the language of cuts reads Weil's bound as one statement. Take the numerator `P(u) = 1 − t u + q u²` of a genus
one datum with real trace `t`. Its kernel is pure when every power-law kernel vector has exact decay `q^{-r/2}`.

**The kernel is pure iff `t² ≤ 4q`** (`isPureKernel_iff`).

So the tests separate as follows.

* **Kloosterman data pass.** `1 + K u + p u²` has a pure kernel, and the input is Weil's bound `|K| ≤ 2√p`. The linear
  stencil window `|K| ≤ p + 1` does not reach purity: only a statement about the kernel does.
* **The golden fake fails.** `1 − 5u + 5u²` has trace above `2√5`. Its zeros return exactly, along a full progression of shifts,
  and its kernel is impure, with a mode at the deep zero of `Re s ≈ 0.8`. So transport does not imply purity.
* **Quantized norms have no kernel** (`eq_zero_of_isCurveKernel_one`), and split hyperelliptic curves have a pure
  kernel by Stepanov (`isCurveKernel_lRoots_of_stepanov`).
* **A continuous count has no multiplicity** (`continuous_multiplicity_eq_zero`), so a statement read through the carry of the floor is
  false for it.
-/

open Polynomial
open GaloisForLFunctions.ArithmeticAuxiliaryDynamics
open GaloisForLFunctions.RHTower.WeilKloosterman

noncomputable section

namespace GaloisForLFunctions.RigidArithmeticOfCuts

/-- The numerator `1 − t u + q u²` of a genus-one datum. -/
def traceNumerator (t q : ℝ) : ℂ[X] := 1 - C (t : ℂ) * X + C (q : ℂ) * X ^ 2

theorem eval_traceNumerator (t q : ℝ) (u : ℂ) :
    (traceNumerator t q).eval u = 1 - t * u + q * u ^ 2 := by
  simp [traceNumerator]

/-- The kernel of a genus-one datum is pure: every power-law kernel vector decays at exactly `q^{-r/2}`. -/
def IsPureKernel (t q : ℝ) : Prop :=
  ∀ u : ℂ, IsCurveKernel (traceNumerator t q) (fun r => u ^ r) → Complex.normSq u = 1 / q

/-- Below the trace bound every root has modulus `q^{-1/2}`. -/
theorem normSq_of_root {t q : ℝ} (hq : 0 < q) (ht : t ^ 2 ≤ 4 * q) {u : ℂ}
    (hu : 1 - (t : ℂ) * u + (q : ℂ) * u ^ 2 = 0) : Complex.normSq u = 1 / q := by
  have hre := congrArg Complex.re hu
  have him := congrArg Complex.im hu
  simp only [pow_two, Complex.sub_re, Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_im, Complex.sub_im, Complex.add_im, Complex.one_im, Complex.zero_re,
    Complex.zero_im, zero_mul, sub_zero, add_zero] at hre him
  rw [Complex.normSq_apply, eq_div_iff hq.ne']
  by_cases hy : u.im = 0
  · rw [hy] at hre ⊢
    have h1 : (2 * q * u.re - t) ^ 2 ≤ 0 := by nlinarith
    have h2 : 2 * q * u.re - t = 0 := by
      have := sq_nonneg (2 * q * u.re - t)
      exact pow_eq_zero_iff (two_ne_zero) |>.mp (le_antisymm h1 this)
    have h3 : t = 2 * q * u.re := by linarith
    rw [h3] at hre
    nlinarith
  · have h1 : u.im * (2 * q * u.re - t) = 0 := by linarith
    have h2 : 2 * q * u.re - t = 0 := (mul_eq_zero.mp h1).resolve_left hy
    have h3 : t = 2 * q * u.re := by linarith
    rw [h3] at hre
    nlinarith

/-- **The kernel is pure iff the trace bound holds.** -/
theorem isPureKernel_iff {t q : ℝ} (hq : 0 < q) : IsPureKernel t q ↔ t ^ 2 ≤ 4 * q := by
  constructor
  · intro hpure
    by_contra hlt
    push Not at hlt
    set d : ℝ := Real.sqrt (t ^ 2 - 4 * q) with hd
    have hdpos : 0 < d := Real.sqrt_pos.mpr (by linarith)
    have hdsq : d ^ 2 = t ^ 2 - 4 * q := Real.sq_sqrt (by linarith)
    have hroot : ∀ x : ℝ, 2 * q * x - t = d ∨ 2 * q * x - t = -d →
        IsCurveKernel (traceNumerator t q) (fun r => ((x : ℂ)) ^ r) := by
      intro x hx
      rw [isCurveKernel_pow_iff, eval_traceNumerator]
      have hsq : (2 * q * x - t) ^ 2 = d ^ 2 := by
        rcases hx with h | h <;> rw [h]
        ring
      have hreal : 1 - t * x + q * x ^ 2 = 0 := by
        have h4 : 4 * q * (1 - t * x + q * x ^ 2) = 0 := by nlinarith
        have : (4 * q) ≠ 0 := by positivity
        exact (mul_eq_zero.mp h4).resolve_left this
      exact_mod_cast hreal
    set x₁ : ℝ := (t + d) / (2 * q) with hx₁
    set x₂ : ℝ := (t - d) / (2 * q) with hx₂
    have h2q : 2 * q ≠ 0 := by positivity
    have h1 : 2 * q * x₁ - t = d := by
      rw [hx₁]
      field_simp
      ring
    have h2 : 2 * q * x₂ - t = -d := by
      rw [hx₂]
      field_simp
      ring
    have hp1 := hpure _ (hroot x₁ (Or.inl h1))
    have hp2 := hpure _ (hroot x₂ (Or.inr h2))
    rw [Complex.normSq_ofReal] at hp1 hp2
    have hsub : x₁ - x₂ = d / q := by
      rw [hx₁, hx₂]
      field_simp
      ring
    have hprod : x₁ * x₂ = 1 / q := by
      rw [hx₁, hx₂, div_mul_div_comm, div_eq_div_iff (by positivity) hq.ne']
      nlinarith
    have hx0 : x₁ ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hp1
      have : (0 : ℝ) < 1 / q := by positivity
      linarith
    have hzero : x₁ * (x₁ - x₂) = 0 := by
      rw [mul_sub, hp1, hprod, sub_self]
    have hdiff : x₁ - x₂ = 0 := (mul_eq_zero.mp hzero).resolve_left hx0
    rw [hsub] at hdiff
    exact (div_pos hdpos hq).ne' hdiff
  · intro ht u hu
    rw [isCurveKernel_pow_iff, eval_traceNumerator] at hu
    exact normSq_of_root hq ht hu

/-! ### Kloosterman data -/

variable {p : ℕ} [Fact p.Prime]

/-- The numerator of the Kloosterman `L`-function is the genus-one numerator of trace `−K`. -/
theorem traceNumerator_kloosterman (ψ : AddChar (ZMod p) ℂ) (a : ZMod p) :
    traceNumerator (-(kloosterman ψ a).re) p =
      1 + C (kloosterman ψ a) * X + C (p : ℂ) * X ^ 2 := by
  have hK : (((kloosterman ψ a).re : ℝ) : ℂ) = kloosterman ψ a :=
    Complex.ext (by simp) (by simpa using (ArithmeticLorentzianGeometry.kloosterman_isReal ψ a).symm)
  have hC : C (((-(kloosterman ψ a).re : ℝ) : ℂ)) = -C (kloosterman ψ a) := by
    push_cast
    rw [hK, C_neg]
  rw [traceNumerator, hC]
  simp only [Complex.ofReal_natCast]
  ring

/-- **Kloosterman data pass.** Weil's bound is purity of the kernel of `1 + K u + p u²`. -/
theorem isPureKernel_kloosterman (hp2 : p ≠ 2) (ψ : AddChar (ZMod p) ℂ) (hψ : ψ.IsPrimitive) {a : ZMod p}
    (ha : a ≠ 0) : IsPureKernel (-(kloosterman ψ a).re) p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  rw [isPureKernel_iff hp0, neg_sq]
  have h1 := _root_.GaloisForLFunctions.RHTower.WeilKloosterman.kloosterman_weil_bound hp2 ψ hψ ha
  have h2 : |(kloosterman ψ a).re| ≤ 2 * Real.sqrt p := (Complex.abs_re_le_norm _).trans h1
  have h3 : (2 * Real.sqrt p) ^ 2 = 4 * p := by
    rw [mul_pow, Real.sq_sqrt hp0.le]
    norm_num
  rw [← sq_abs, ← h3]
  exact pow_le_pow_left₀ (abs_nonneg _) h2 2

/-! ### The golden fake -/

/-- The golden `L`-function is the genus-one numerator of trace `5` over `q = 5`, read at `5^{-s}`. -/
theorem goldenL_eq_eval (s : ℂ) : goldenL s = (traceNumerator 5 5).eval (((5 : ℝ) : ℂ) ^ (-s)) := by
  rw [goldenL, eval_traceNumerator]
  push_cast
  ring

/-- **The golden kernel is impure.** -/
theorem not_isPureKernel_golden : ¬ IsPureKernel 5 5 := by
  rw [isPureKernel_iff (by norm_num)]
  norm_num

/-- The deep golden zero is a mode of the kernel, and its decay differs from `5^{-r/2}`. -/
theorem golden_deep_mode :
    IsCurveKernel (traceNumerator 5 5) (fun r => (((5 : ℝ) : ℂ) ^ (-(goldenDeepZero : ℂ))) ^ r) ∧
      Complex.normSq (((5 : ℝ) : ℂ) ^ (-(goldenDeepZero : ℂ))) ≠ 1 / 5 := by
  obtain ⟨hzero, hhalf, -⟩ := goldenL_deepZero
  refine ⟨?_, ?_⟩
  · rw [isCurveKernel_pow_iff, ← goldenL_eq_eval]
    exact hzero
  · have hval : ((5 : ℝ) : ℂ) ^ (-(goldenDeepZero : ℂ)) = (((5 : ℝ) ^ (-goldenDeepZero) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow (by norm_num)]
      push_cast
      rfl
    rw [hval, Complex.normSq_ofReal, ← Real.rpow_add (by norm_num)]
    intro h
    have h1 : (5 : ℝ) ^ (-goldenDeepZero + -goldenDeepZero) < (5 : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
    rw [h, Real.rpow_neg_one] at h1
    norm_num at h1

/-- **The golden fake obeys transport and fails purity and the count.** -/
theorem golden_battery :
    (∀ (s : ℂ) (k : ℤ), goldenL (s + (k : ℂ) * (goldenPeriod : ℂ) * Complex.I) = goldenL s) ∧
      ¬ IsPureKernel 5 5 ∧
        ¬ ArithmeticOfSquareRootPrecision.CountAtPrecision
          ArithmeticCastelnuovoSeveri.goldenDatum (1 / 2) :=
  ⟨goldenL_shift, not_isPureKernel_golden, golden_fails_count⟩

end GaloisForLFunctions.RigidArithmeticOfCuts
