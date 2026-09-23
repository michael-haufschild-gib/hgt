import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic

/-!
# A real point-supported source can carry an off-axis quartet

For `a, b > 0` the polynomial

`F a b z = ((z - a) ^ (2 : ℕ) + b ^ (2 : ℕ)) * ((z + a) ^ (2 : ℕ) + b ^ (2 : ℕ))`

has real coefficients, is even, satisfies Schwarz symmetry, and its four simple zeros
`±a ± i b` all lie off the critical axis `Re z = 0`.

Its coefficient family is the bilateral Laplace transform datum of a real distribution supported at
the single real point `0`: pairing `∑ k, c k * (-1) ^ k * φ⁽ᵏ⁾(0)` against the exponential
`t ↦ exp (-(z t))` returns `F a b z`.

Multiplying any real even reporter by `F a b` keeps it real and even while inserting the off-axis
quartet.  Real source geometry with a reflection symmetry therefore does not force a critical
divisor.
-/

noncomputable section

namespace RHTower

open scoped BigOperators
open Complex

/-- The real quartet polynomial. -/
def quartetPoly_realSourceMicrolocalQuartet (a b : ℝ) : Polynomial ℝ :=
  ((Polynomial.X - Polynomial.C a) ^ (2 : ℕ) + Polynomial.C (b ^ (2 : ℕ))) *
    ((Polynomial.X + Polynomial.C a) ^ (2 : ℕ) + Polynomial.C (b ^ (2 : ℕ)))

/-- The complexified quartet reporter. -/
def quartetFun (a b : ℝ) (z : ℂ) : ℂ :=
  ((z - (a : ℂ)) ^ (2 : ℕ) + (b : ℂ) ^ (2 : ℕ)) * ((z + (a : ℂ)) ^ (2 : ℕ) + (b : ℂ) ^ (2 : ℕ))

theorem quartetPoly_eval_complex (a b : ℝ) (z : ℂ) :
    ((quartetPoly_realSourceMicrolocalQuartet a b).map (algebraMap ℝ ℂ)).eval z = quartetFun a b z := by
  simp [quartetPoly_realSourceMicrolocalQuartet, quartetFun]

theorem quartetPoly_natDegree (a b : ℝ) : (quartetPoly_realSourceMicrolocalQuartet a b).natDegree = 4 := by
  have h1 : ((Polynomial.X - Polynomial.C a) ^ (2 : ℕ) + Polynomial.C (b ^ (2 : ℕ))).natDegree = 2 := by
    compute_degree!
  have h2 : ((Polynomial.X + Polynomial.C a) ^ (2 : ℕ) + Polynomial.C (b ^ (2 : ℕ))).natDegree = 2 := by
    compute_degree!
  unfold quartetPoly_realSourceMicrolocalQuartet
  compute_degree!

/-- **Evenness.** -/
theorem quartetFun_neg (a b : ℝ) (z : ℂ) : quartetFun a b (-z) = quartetFun a b z := by
  unfold quartetFun
  ring

/-- **Schwarz symmetry.** -/
theorem quartetFun_conj (a b : ℝ) (z : ℂ) :
    quartetFun a b ((starRingEnd ℂ) z) = (starRingEnd ℂ) (quartetFun a b z) := by
  unfold quartetFun
  simp only [map_mul, map_add, map_sub, map_pow, Complex.conj_ofReal]

/-- Exact factorization into the four linear quartet factors. -/
theorem quartetFun_factor (a b : ℝ) (z : ℂ) :
    quartetFun a b z =
      (z - ((a : ℂ) + (b : ℂ) * I)) * (z - ((a : ℂ) - (b : ℂ) * I)) *
        (z - (-(a : ℂ) + (b : ℂ) * I)) * (z - (-(a : ℂ) - (b : ℂ) * I)) := by
  unfold quartetFun
  have hI : (I : ℂ) ^ (2 : ℕ) = -1 := Complex.I_sq
  linear_combination ((b : ℂ) ^ (2 : ℕ) * ((z - (a : ℂ)) ^ (2 : ℕ) + (z + (a : ℂ)) ^ (2 : ℕ)) -
      (b : ℂ) ^ (4 : ℕ) * ((I : ℂ) ^ (2 : ℕ) - 1)) * hI

/-- **The zero set is exactly the quartet.** -/
theorem quartetFun_eq_zero_iff (a b : ℝ) (z : ℂ) :
    quartetFun a b z = 0 ↔
      z = (a : ℂ) + (b : ℂ) * I ∨ z = (a : ℂ) - (b : ℂ) * I ∨
        z = -(a : ℂ) + (b : ℂ) * I ∨ z = -(a : ℂ) - (b : ℂ) * I := by
  rw [quartetFun_factor]
  simp only [mul_eq_zero, sub_eq_zero]
  tauto

/-- **Every quartet zero is off the critical axis.** -/
theorem quartetFun_zero_re_ne_zero {a b : ℝ} (ha : 0 < a) {z : ℂ} (hz : quartetFun a b z = 0) :
    z.re ≠ 0 := by
  rcases (quartetFun_eq_zero_iff a b z).mp hz with h | h | h | h <;> rw [h] <;>
    simp <;> linarith

/-- The four quartet zeros are pairwise distinct, so each is a simple zero. -/
theorem quartetZeros_pairwise_distinct {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ((a : ℂ) + (b : ℂ) * I ≠ (a : ℂ) - (b : ℂ) * I) ∧
      ((a : ℂ) + (b : ℂ) * I ≠ -(a : ℂ) + (b : ℂ) * I) ∧
      ((a : ℂ) + (b : ℂ) * I ≠ -(a : ℂ) - (b : ℂ) * I) ∧
      ((a : ℂ) - (b : ℂ) * I ≠ -(a : ℂ) + (b : ℂ) * I) ∧
      ((a : ℂ) - (b : ℂ) * I ≠ -(a : ℂ) - (b : ℂ) * I) ∧
      (-(a : ℂ) + (b : ℂ) * I ≠ -(a : ℂ) - (b : ℂ) * I) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;>
    [ (have := congrArg Complex.im h); (have := congrArg Complex.re h);
      (have := congrArg Complex.re h); (have := congrArg Complex.re h);
      (have := congrArg Complex.re h); (have := congrArg Complex.im h) ] <;>
    simp at this <;> linarith

/-! ### The point-supported real source -/

/-- Every iterated real derivative of a complex exponential. -/
theorem iteratedDeriv_cexp_linear (c : ℂ) (k : ℕ) :
    iteratedDeriv k (fun u : ℝ => Complex.exp (c * u)) =
      fun t : ℝ => c ^ k * Complex.exp (c * t) := by
  induction k with
  | zero => simp [iteratedDeriv_zero]
  | succ k ih =>
      funext t
      rw [iteratedDeriv_succ, ih]
      have hbase : HasDerivAt (fun u : ℝ => Complex.exp (c * u)) (c * Complex.exp (c * t)) t := by
        have h1 : HasDerivAt (fun u : ℝ => c * (u : ℂ)) c t := by
          simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul c
        simpa [mul_comm] using h1.cexp
      have hstep : HasDerivAt (fun u : ℝ => c ^ k * Complex.exp (c * u))
          (c ^ k * (c * Complex.exp (c * t))) t := hbase.const_mul _
      rw [hstep.deriv]
      ring

/-- The point-supported real source attached to a real polynomial: the pairing of
`∑ k, c k • δ₀⁽ᵏ⁾` with a smooth test function. -/
def pointSourcePairing (p : Polynomial ℝ) (φ : ℝ → ℂ) : ℂ :=
  ∑ k ∈ Finset.range (p.natDegree + 1),
    ((p.coeff k : ℝ) : ℂ) * (-1 : ℂ) ^ k * iteratedDeriv k φ 0

/-- **The Laplace transform of the point-supported source is the polynomial.** -/
theorem pointSourcePairing_exp (p : Polynomial ℝ) (z : ℂ) :
    pointSourcePairing p (fun t : ℝ => Complex.exp (-(z * t))) =
      ((p.map (algebraMap ℝ ℂ)).eval z) := by
  have hderiv : ∀ k : ℕ,
      iteratedDeriv k (fun t : ℝ => Complex.exp (-(z * t))) 0 = (-z) ^ k := by
    intro k
    have hrewrite : (fun t : ℝ => Complex.exp (-(z * t))) =
        fun t : ℝ => Complex.exp ((-z) * t) := by
      funext t
      ring_nf
    rw [hrewrite, iteratedDeriv_cexp_linear]
    simp
  have hterm : ∀ k ∈ Finset.range (p.natDegree + 1),
      ((p.coeff k : ℝ) : ℂ) * (-1 : ℂ) ^ k *
          iteratedDeriv k (fun t : ℝ => Complex.exp (-(z * t))) 0 =
        ((p.coeff k : ℝ) : ℂ) * z ^ k := by
    intro k _
    rw [hderiv k]
    have hmul : (-1 : ℂ) ^ k * (-z) ^ k = z ^ k := by
      rw [← mul_pow]
      congr 1
      ring
    calc ((p.coeff k : ℝ) : ℂ) * (-1 : ℂ) ^ k * (-z) ^ k
        = ((p.coeff k : ℝ) : ℂ) * ((-1 : ℂ) ^ k * (-z) ^ k) := by ring
      _ = ((p.coeff k : ℝ) : ℂ) * z ^ k := by rw [hmul]
  rw [pointSourcePairing, Finset.sum_congr rfl hterm]
  rw [Polynomial.eval_map, Polynomial.eval₂_eq_sum_range' (algebraMap ℝ ℂ)
    (Nat.lt_succ_self p.natDegree)]
  rfl

/-- **The countermodel.**  The point source of the quartet polynomial has the quartet reporter as
its bilateral Laplace transform. -/
theorem pointSourcePairing_quartet (a b : ℝ) (z : ℂ) :
    pointSourcePairing (quartetPoly_realSourceMicrolocalQuartet a b) (fun t : ℝ => Complex.exp (-(z * t))) =
      quartetFun a b z := by
  rw [pointSourcePairing_exp, quartetPoly_eval_complex]

/-- **Stronger source-reporter form.**  Multiplying a real even reporter by the quartet keeps it
real and even. -/
theorem quartetFun_mul_preserves_real_even (a b : ℝ) (X : ℂ → ℂ)
    (hEven : ∀ z, X (-z) = X z)
    (hReal : ∀ z, X ((starRingEnd ℂ) z) = (starRingEnd ℂ) (X z)) :
    (∀ z, (quartetFun a b * X) (-z) = (quartetFun a b * X) z) ∧
      (∀ z, (quartetFun a b * X) ((starRingEnd ℂ) z) =
        (starRingEnd ℂ) ((quartetFun a b * X) z)) := by
  refine ⟨fun z => ?_, fun z => ?_⟩
  · simp only [Pi.mul_apply, quartetFun_neg, hEven]
  · simp only [Pi.mul_apply, quartetFun_conj, hReal, map_mul]

end RHTower
