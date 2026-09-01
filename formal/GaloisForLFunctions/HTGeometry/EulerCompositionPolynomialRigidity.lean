import GaloisForLFunctions.HTGeometry.FirstOrderCompositionDefect
import GaloisForLFunctions.HTGeometry.WildCharacteristicCollapse
import GaloisForLFunctions.HTGeometry.EntireOrderTwoSeries

/-!
# The Euler relation, read after a substitution

The autonomous Euler relation `∑_{k ≤ m} C_k(f)·(z f′)^k = 0` forces an entire `f` to be a
polynomial (`eventually_taylorCoeff_eq_zero_of_euler_relation_general`).  This file makes that
conclusion available from the *substituted* form of the relation, which is how it arises in the
composition arguments: what the differential-algebra side produces is a vanishing polynomial
expression in the two meromorphic states `f ∘ g` and `g·(f′ ∘ g)`.

A nonzero entire function composed with a nonconstant entire function is nonzero, so a relation
holding after substitution already holds before it.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

/-! ### Finitely many Taylor coefficients means a polynomial -/

/-- An entire function whose Taylor coefficients eventually vanish is a polynomial. -/
theorem exists_polynomial_of_eventually_taylorCoeff_eq_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {M : ℕ} (hM : ∀ n : ℕ, M ≤ n → taylorCoeff f n = 0) :
    ∃ p : Polynomial ℂ, ∀ z : ℂ, f z = p.eval z := by
  classical
  refine ⟨∑ n ∈ Finset.range M, Polynomial.C (taylorCoeff f n) * Polynomial.X ^ n, fun z => ?_⟩
  have hsum := hasSum_taylorCoeff hf z
  have hfin : HasSum (fun n : ℕ => taylorCoeff f n * z ^ n)
      (∑ n ∈ Finset.range M, taylorCoeff f n * z ^ n) := by
    refine hasSum_sum_of_ne_finset_zero ?_
    intro n hn
    rw [hM n (by simpa using Finset.mem_range.not.mp hn), zero_mul]
  have := hsum.unique hfin
  rw [this, Polynomial.eval_finset_sum]
  exact Finset.sum_congr rfl fun n _ => by rw [Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]

/-! ### The substituted Euler expression -/

/-- The Euler expression `∑_{k ≤ m} C_k(f(w))·(w f′(w))^k`. -/
def eulerFun (f : ℂ → ℂ) (C : ℕ → Polynomial ℂ) (m : ℕ) : ℂ → ℂ :=
  fun w => ∑ k ∈ Finset.range (m + 1), (C k).eval (f w) * (w * deriv f w) ^ k

theorem analyticOnNhd_eulerTerm {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (C : ℕ → Polynomial ℂ) (k : ℕ) :
    AnalyticOnNhd ℂ (fun z : ℂ => (C k).eval (f (g z)) * (g z * deriv f (g z)) ^ k)
      (Set.univ : Set ℂ) := by
  have hcomp : Differentiable ℂ fun z : ℂ => f (g z) := fun z => (hf (g z)).comp z (hg z)
  have hgan : AnalyticOnNhd ℂ g (Set.univ : Set ℂ) :=
    hg.differentiableOn.analyticOnNhd isOpen_univ
  have hderivan : AnalyticOnNhd ℂ (fun z : ℂ => deriv f (g z)) (Set.univ : Set ℂ) :=
    analyticOnNhd_compDeriv hf hg
  exact (analyticOnNhd_polyComp (hcomp.differentiableOn.analyticOnNhd isOpen_univ) (C k)).mul
    ((hgan.mul hderivan).pow k)

theorem analyticOnNhd_eulerComp {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (C : ℕ → Polynomial ℂ) (m : ℕ) :
    AnalyticOnNhd ℂ (fun z : ℂ => eulerFun f C m (g z)) (Set.univ : Set ℂ) := by
  have hpi : (fun z : ℂ => eulerFun f C m (g z))
      = ∑ k ∈ Finset.range (m + 1),
        fun z : ℂ => (C k).eval (f (g z)) * (g z * deriv f (g z)) ^ k := by
    funext z
    rw [Finset.sum_apply, eulerFun]
  rw [hpi]
  exact Finset.sum_induction _ (fun h => AnalyticOnNhd ℂ h (Set.univ : Set ℂ))
    (fun a b ha hb => ha.add hb) analyticOnNhd_const
    (fun k _ => analyticOnNhd_eulerTerm hf hg C k)

/-- The substituted Euler expression, read in the meromorphic field. -/
theorem analyticMeroElement_eulerComp {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (hcomp : Differentiable ℂ fun w => f (g w))
    (C : ℕ → Polynomial ℂ) (m : ℕ) :
    analyticMeroElement (fun z : ℂ => eulerFun f C m (g z)) (analyticOnNhd_eulerComp hf hg C m)
      = ∑ k ∈ Finset.range (m + 1),
        Polynomial.aeval (jetElem hcomp 0) (C k)
          * (jetElem hg 0 * compJetElem hf hg 1) ^ k := by
  classical
  have hcompan : AnalyticOnNhd ℂ (fun w => f (g w)) (Set.univ : Set ℂ) :=
    hcomp.differentiableOn.analyticOnNhd isOpen_univ
  have hgan : AnalyticOnNhd ℂ g (Set.univ : Set ℂ) :=
    hg.differentiableOn.analyticOnNhd isOpen_univ
  have hderivan : AnalyticOnNhd ℂ (fun z : ℂ => deriv f (g z)) (Set.univ : Set ℂ) :=
    analyticOnNhd_compDeriv hf hg
  have hh : jetElem hcomp 0 = analyticMeroElement (fun w => f (g w)) hcompan := by
    rw [jetElem]
    exact analyticMeroElement_congr _ _ (by funext z; simp [iteratedDeriv_zero])
  have hG : jetElem hg 0 = analyticMeroElement g hgan := by
    rw [jetElem]
    exact analyticMeroElement_congr _ _ (by funext z; simp [iteratedDeriv_zero])
  have ha : compJetElem hf hg 1 = analyticMeroElement (fun z : ℂ => deriv f (g z)) hderivan := by
    rw [compJetElem]
    exact analyticMeroElement_congr _ _ (by funext z; simp [compJetFun, iteratedDeriv_one])
  have hterm : ∀ k : ℕ, AnalyticOnNhd ℂ
      (fun z : ℂ => (C k).eval (f (g z)) * (g z * deriv f (g z)) ^ k) (Set.univ : Set ℂ) :=
    fun k => analyticOnNhd_eulerTerm hf hg C k
  have hsum : AnalyticOnNhd ℂ (fun z : ℂ => ∑ k ∈ Finset.range (m + 1),
      (C k).eval (f (g z)) * (g z * deriv f (g z)) ^ k) (Set.univ : Set ℂ) := by
    have hpi : (fun z : ℂ => ∑ k ∈ Finset.range (m + 1),
        (C k).eval (f (g z)) * (g z * deriv f (g z)) ^ k)
        = ∑ k ∈ Finset.range (m + 1),
          fun z : ℂ => (C k).eval (f (g z)) * (g z * deriv f (g z)) ^ k := by
      funext z
      rw [Finset.sum_apply]
    rw [hpi]
    exact Finset.sum_induction _ (fun h => AnalyticOnNhd ℂ h (Set.univ : Set ℂ))
      (fun a b ha hb => ha.add hb) analyticOnNhd_const (fun k _ => hterm k)
  have hfirst : analyticMeroElement (fun z : ℂ => eulerFun f C m (g z))
      (analyticOnNhd_eulerComp hf hg C m)
      = analyticMeroElement (fun z : ℂ => ∑ k ∈ Finset.range (m + 1),
          (C k).eval (f (g z)) * (g z * deriv f (g z)) ^ k) hsum :=
    analyticMeroElement_congr _ _ (by funext z; rw [eulerFun])
  have hstep : analyticMeroElement (fun z : ℂ => ∑ k ∈ Finset.range (m + 1),
      (C k).eval (f (g z)) * (g z * deriv f (g z)) ^ k) hsum
      = ∑ k ∈ Finset.range (m + 1),
        analyticMeroElement (fun z : ℂ => (C k).eval (f (g z)) * (g z * deriv f (g z)) ^ k)
          (hterm k) := analyticMeroElement_finsetSum _ _ hterm hsum
  rw [hfirst, hstep]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hbasean : AnalyticOnNhd ℂ (fun z : ℂ => g z * deriv f (g z)) (Set.univ : Set ℂ) :=
    hgan.mul hderivan
  have hpowan : AnalyticOnNhd ℂ (fun z : ℂ => (g z * deriv f (g z)) ^ k) (Set.univ : Set ℂ) :=
    hbasean.pow k
  have hpolyan : AnalyticOnNhd ℂ (fun z : ℂ => (C k).eval (f (g z))) (Set.univ : Set ℂ) :=
    analyticOnNhd_polyComp hcompan (C k)
  have hmul : analyticMeroElement
      (fun z : ℂ => (C k).eval (f (g z)) * (g z * deriv f (g z)) ^ k) (hterm k)
      = analyticMeroElement (fun z : ℂ => (C k).eval (f (g z))) hpolyan
        * analyticMeroElement (fun z : ℂ => (g z * deriv f (g z)) ^ k) hpowan :=
    analyticMeroElement_mul hpolyan hpowan
  have hpow : analyticMeroElement (fun z : ℂ => (g z * deriv f (g z)) ^ k) hpowan
      = (analyticMeroElement (fun z : ℂ => g z * deriv f (g z)) hbasean) ^ k :=
    analyticMeroElement_pow hbasean k
  have hbase : analyticMeroElement (fun z : ℂ => g z * deriv f (g z)) hbasean
      = analyticMeroElement g hgan
        * analyticMeroElement (fun z : ℂ => deriv f (g z)) hderivan :=
    analyticMeroElement_mul hgan hderivan
  have hpoly : analyticMeroElement (fun z : ℂ => (C k).eval (f (g z))) hpolyan
      = Polynomial.aeval (analyticMeroElement (fun w : ℂ => f (g w)) hcompan) (C k) :=
    (aeval_analyticMeroElement hcompan (C k)).symm
  rw [hh, hG, ha, hmul, hpow, hbase, hpoly]

end

end GaloisForLFunctions.HTGeometry
