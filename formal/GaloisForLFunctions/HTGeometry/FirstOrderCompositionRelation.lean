import GaloisForLFunctions.HTGeometry.CompositionPairIndependence
import GaloisForLFunctions.HTGeometry.CompositionJetRing
import GaloisForLFunctions.HTGeometry.CascadeMeroField
import GaloisForLFunctions.HTGeometry.PolynomialDriftRationalOuterFactorRigidity

/-!
# A first-order equation for the outer factor, read after substitution

A first-order algebraic differential equation for `f`, written by the degree in the independent
variable,

`∑_i (∑_k c_{i,k}(f(w)) · f′(w)^k) · w^i = 0`,

becomes after the substitution `w = g(z)` a polynomial relation among the three meromorphic states
`g`, `h = f ∘ g` and `a = f′ ∘ g`.  If one of its rows does not vanish identically the relation is
nontrivial, and rows that do vanish identically are autonomous relations for `f`.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

/-- The `i`-th row of a first-order relation: the autonomous part attached to `w^i`. -/
def rowFun (f : ℂ → ℂ) (c : ℕ → ℕ → Polynomial ℂ) (m i : ℕ) : ℂ → ℂ :=
  fun w => ∑ k ∈ Finset.range (m + 1), (c i k).eval (f w) * (deriv f w) ^ k

/-- **A first-order algebraic differential equation**, possibly nonautonomous: a nonzero polynomial
relation among the independent variable, `f` and `f′`, arranged by the degree in the variable. -/
def FirstOrderDA (f : ℂ → ℂ) : Prop :=
  ∃ (d m : ℕ) (c : ℕ → ℕ → Polynomial ℂ), (∃ i ≤ d, ∃ k ≤ m, c i k ≠ 0) ∧
    ∀ w : ℂ, ∑ i ∈ Finset.range (d + 1), rowFun f c m i w * w ^ i = 0

/-- A row that vanishes identically is an autonomous relation. -/
theorem autonomousFirstOrder_of_rowFun_eq_zero {f : ℂ → ℂ} {c : ℕ → ℕ → Polynomial ℂ} {m i k₀ : ℕ}
    (hk₀ : k₀ ≤ m) (hne : c i k₀ ≠ 0) (hrow : ∀ w : ℂ, rowFun f c m i w = 0) :
    AutonomousFirstOrder f :=
  ⟨m, c i, ⟨k₀, hk₀, hne⟩, hrow⟩

/-! ### Analyticity of the substituted rows -/

theorem analyticOnNhd_rowComp {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (c : ℕ → ℕ → Polynomial ℂ) (m i : ℕ) :
    AnalyticOnNhd ℂ (fun z : ℂ => rowFun f c m i (g z)) (Set.univ : Set ℂ) := by
  have hcomp : Differentiable ℂ fun z : ℂ => f (g z) := fun z => (hf (g z)).comp z (hg z)
  have hfan : AnalyticOnNhd ℂ f (Set.univ : Set ℂ) :=
    hf.differentiableOn.analyticOnNhd isOpen_univ
  have hd : Differentiable ℂ (deriv f) := fun z => (hfan.deriv z (Set.mem_univ z)).differentiableAt
  have hderiv : Differentiable ℂ fun z : ℂ => deriv f (g z) := fun z => (hd (g z)).comp z (hg z)
  have hterm : ∀ k : ℕ, AnalyticOnNhd ℂ
      (fun z : ℂ => (c i k).eval (f (g z)) * (deriv f (g z)) ^ k) (Set.univ : Set ℂ) := by
    intro k
    have h1 : AnalyticOnNhd ℂ (fun z : ℂ => (c i k).eval (f (g z))) (Set.univ : Set ℂ) :=
      analyticOnNhd_polyComp (hcomp.differentiableOn.analyticOnNhd isOpen_univ) (c i k)
    exact h1.mul ((hderiv.differentiableOn.analyticOnNhd isOpen_univ).pow k)
  have hfun : (fun z : ℂ => rowFun f c m i (g z))
      = fun z : ℂ => ∑ k ∈ Finset.range (m + 1),
        (c i k).eval (f (g z)) * (deriv f (g z)) ^ k := by
    funext z
    rw [rowFun]
  rw [hfun]
  have hpi : (fun z : ℂ => ∑ k ∈ Finset.range (m + 1),
      (c i k).eval (f (g z)) * (deriv f (g z)) ^ k)
      = ∑ k ∈ Finset.range (m + 1),
        fun z : ℂ => (c i k).eval (f (g z)) * (deriv f (g z)) ^ k := by
    funext z
    rw [Finset.sum_apply]
  rw [hpi]
  exact Finset.sum_induction _ (fun h => AnalyticOnNhd ℂ h (Set.univ : Set ℂ))
    (fun a b ha hb => ha.add hb) analyticOnNhd_const (fun k _ => hterm k)

theorem analyticOnNhd_compDeriv {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) :
    AnalyticOnNhd ℂ (fun z : ℂ => deriv f (g z)) (Set.univ : Set ℂ) := by
  have hfan : AnalyticOnNhd ℂ f (Set.univ : Set ℂ) :=
    hf.differentiableOn.analyticOnNhd isOpen_univ
  have hd : Differentiable ℂ (deriv f) := fun z => (hfan.deriv z (Set.mem_univ z)).differentiableAt
  have hcd : Differentiable ℂ fun z : ℂ => deriv f (g z) := fun z => (hd (g z)).comp z (hg z)
  exact hcd.differentiableOn.analyticOnNhd isOpen_univ

/-! ### The substituted row in the meromorphic field -/

theorem analyticMeroElement_rowComp {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (hcomp : Differentiable ℂ fun w => f (g w))
    (c : ℕ → ℕ → Polynomial ℂ) (m i : ℕ) :
    analyticMeroElement (fun z : ℂ => rowFun f c m i (g z)) (analyticOnNhd_rowComp hf hg c m i)
      = ∑ k ∈ Finset.range (m + 1),
        Polynomial.aeval (jetElem hcomp 0) (c i k) * (compJetElem hf hg 1) ^ k := by
  classical
  have hcompan : AnalyticOnNhd ℂ (fun w => f (g w)) (Set.univ : Set ℂ) :=
    hcomp.differentiableOn.analyticOnNhd isOpen_univ
  have hderivan : AnalyticOnNhd ℂ (fun z : ℂ => deriv f (g z)) (Set.univ : Set ℂ) :=
    analyticOnNhd_compDeriv hf hg
  have hh : jetElem hcomp 0 = analyticMeroElement (fun w => f (g w)) hcompan := by
    rw [jetElem]
    exact analyticMeroElement_congr _ _ (by funext z; simp [iteratedDeriv_zero])
  have ha : compJetElem hf hg 1 = analyticMeroElement (fun z : ℂ => deriv f (g z)) hderivan := by
    rw [compJetElem]
    exact analyticMeroElement_congr _ _ (by funext z; simp [compJetFun, iteratedDeriv_one])
  have hterm : ∀ k : ℕ, AnalyticOnNhd ℂ
      (fun z : ℂ => (c i k).eval (f (g z)) * (deriv f (g z)) ^ k) (Set.univ : Set ℂ) := by
    intro k
    exact (analyticOnNhd_polyComp hcompan (c i k)).mul (hderivan.pow k)
  have hsum : AnalyticOnNhd ℂ (fun z : ℂ => ∑ k ∈ Finset.range (m + 1),
      (c i k).eval (f (g z)) * (deriv f (g z)) ^ k) (Set.univ : Set ℂ) := by
    have hpi : (fun z : ℂ => ∑ k ∈ Finset.range (m + 1),
        (c i k).eval (f (g z)) * (deriv f (g z)) ^ k)
        = ∑ k ∈ Finset.range (m + 1),
          fun z : ℂ => (c i k).eval (f (g z)) * (deriv f (g z)) ^ k := by
      funext z
      rw [Finset.sum_apply]
    rw [hpi]
    exact Finset.sum_induction _ (fun h => AnalyticOnNhd ℂ h (Set.univ : Set ℂ))
      (fun a b ha hb => ha.add hb) analyticOnNhd_const (fun k _ => hterm k)
  have hstep : analyticMeroElement (fun z : ℂ => ∑ k ∈ Finset.range (m + 1),
      (c i k).eval (f (g z)) * (deriv f (g z)) ^ k) hsum
      = ∑ k ∈ Finset.range (m + 1),
        analyticMeroElement (fun z : ℂ => (c i k).eval (f (g z)) * (deriv f (g z)) ^ k)
          (hterm k) := analyticMeroElement_finsetSum _ _ hterm hsum
  have hfirst : analyticMeroElement (fun z : ℂ => rowFun f c m i (g z))
      (analyticOnNhd_rowComp hf hg c m i)
      = analyticMeroElement (fun z : ℂ => ∑ k ∈ Finset.range (m + 1),
          (c i k).eval (f (g z)) * (deriv f (g z)) ^ k) hsum :=
    analyticMeroElement_congr _ _ (by funext z; rw [rowFun])
  rw [hfirst, hstep]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hpowan : AnalyticOnNhd ℂ (fun z : ℂ => deriv f (g z) ^ k) (Set.univ : Set ℂ) :=
    hderivan.pow k
  have hpolyan : AnalyticOnNhd ℂ (fun z : ℂ => (c i k).eval (f (g z))) (Set.univ : Set ℂ) :=
    analyticOnNhd_polyComp hcompan (c i k)
  have hmul : analyticMeroElement
      (fun z : ℂ => (c i k).eval (f (g z)) * deriv f (g z) ^ k) (hterm k)
      = analyticMeroElement (fun z : ℂ => (c i k).eval (f (g z))) hpolyan
        * analyticMeroElement (fun z : ℂ => deriv f (g z) ^ k) hpowan :=
    analyticMeroElement_mul hpolyan hpowan
  have hpow : analyticMeroElement (fun z : ℂ => deriv f (g z) ^ k) hpowan
      = (analyticMeroElement (fun z : ℂ => deriv f (g z)) hderivan) ^ k :=
    analyticMeroElement_pow hderivan k
  have hpoly : analyticMeroElement (fun z : ℂ => (c i k).eval (f (g z))) hpolyan
      = Polynomial.aeval (analyticMeroElement (fun w : ℂ => f (g w)) hcompan) (c i k) :=
    (aeval_analyticMeroElement hcompan (c i k)).symm
  rw [hh, ha, hmul, hpow, hpoly]

/-- **The substituted first-order relation.**  A first-order equation for `f` becomes a polynomial
relation among `g`, `f ∘ g` and `f′ ∘ g` in the meromorphic field. -/
theorem firstOrder_relation_mero {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hcomp : Differentiable ℂ fun w => f (g w)) {d m : ℕ} {c : ℕ → ℕ → Polynomial ℂ}
    (hrel : ∀ w : ℂ, ∑ i ∈ Finset.range (d + 1), rowFun f c m i w * w ^ i = 0) :
    ∑ i ∈ Finset.range (d + 1),
        (∑ k ∈ Finset.range (m + 1),
          Polynomial.aeval (jetElem hcomp 0) (c i k) * (compJetElem hf hg 1) ^ k)
        * (jetElem hg 0) ^ i = 0 := by
  classical
  have hgan : AnalyticOnNhd ℂ g (Set.univ : Set ℂ) :=
    hg.differentiableOn.analyticOnNhd isOpen_univ
  have hG : jetElem hg 0 = analyticMeroElement g hgan := by
    rw [jetElem]
    exact analyticMeroElement_congr _ _ (by funext z; simp [iteratedDeriv_zero])
  have hterm : ∀ i : ℕ, AnalyticOnNhd ℂ
      (fun z : ℂ => rowFun f c m i (g z) * g z ^ i) (Set.univ : Set ℂ) :=
    fun i => (analyticOnNhd_rowComp hf hg c m i).mul (hgan.pow i)
  have hzero : ∑ i ∈ Finset.range (d + 1),
      analyticMeroElement (fun z : ℂ => rowFun f c m i (g z) * g z ^ i) (hterm i) = 0 := by
    refine analyticMeroElement_sum_eq_zero _ _ hterm ?_
    intro z
    exact hrel (g z)
  rw [← hzero]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hpowan : AnalyticOnNhd ℂ (fun z : ℂ => g z ^ i) (Set.univ : Set ℂ) := hgan.pow i
  have hmul : analyticMeroElement (fun z : ℂ => rowFun f c m i (g z) * g z ^ i) (hterm i)
      = analyticMeroElement (fun z : ℂ => rowFun f c m i (g z))
          (analyticOnNhd_rowComp hf hg c m i)
        * analyticMeroElement (fun z : ℂ => g z ^ i) hpowan :=
    analyticMeroElement_mul (analyticOnNhd_rowComp hf hg c m i) hpowan
  have hpow : analyticMeroElement (fun z : ℂ => g z ^ i) hpowan
      = (analyticMeroElement g hgan) ^ i := analyticMeroElement_pow hgan i
  rw [hmul, hpow, analyticMeroElement_rowComp hf hg hcomp c m i, ← hG]

end

end GaloisForLFunctions.HTGeometry
