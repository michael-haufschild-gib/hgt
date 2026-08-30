import GaloisForLFunctions.HTGeometry.MeroTranscendentalConstants
import GaloisForLFunctions.HTGeometry.CompositionJetRing

/-!
# The autonomous cap: the composed derivative is algebraic over the composition

If `f′` is algebraic over `ℂ(f)` — an autonomous first-order relation — then composing that relation
with `g` shows that `f′ ∘ g` is algebraic over `ℂ(f ∘ g)`.  The only extra ingredient is that
`f ∘ g` is transcendental over the constants, which holds whenever it is nonconstant.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic

/-- **An autonomous first-order relation.**  `f′` is algebraic over `ℂ(f)`: there are polynomial
coefficients, not all zero, with `∑ c_k(f)·(f′)^k = 0`. -/
def AutonomousFirstOrder (f : ℂ → ℂ) : Prop :=
  ∃ (m : ℕ) (c : ℕ → Polynomial ℂ), (∃ k, k ≤ m ∧ c k ≠ 0) ∧
    ∀ w : ℂ, ∑ k ∈ Finset.range (m + 1), (c k).eval (f w) * (deriv f w) ^ k = 0

/-- **The composed derivative is algebraic over the composition.** -/
theorem isAlgebraic_compJetElem_one {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (haut : AutonomousFirstOrder f)
    (hcomp : Differentiable ℂ (fun w => f (g w)))
    (hnc : ¬ ∃ c : ℂ, ∀ z : ℂ, f (g z) = c) :
    IsAlgebraic ↥(Algebra.adjoin ℂ ({jetElem hcomp 0} : Set (meroField (Set.univ : Set ℂ))))
      (compJetElem hf hg 1) := by
  classical
  obtain ⟨m, c, ⟨k₀, hk₀m, hk₀⟩, hrel⟩ := haut
  set hElem : meroField (Set.univ : Set ℂ) := jetElem hcomp 0 with hhE
  set aElem : meroField (Set.univ : Set ℂ) := compJetElem hf hg 1 with haE
  have hhfun : hElem = analyticMeroElement (fun z => f (g z))
      (hcomp.differentiableOn.analyticOnNhd isOpen_univ) := by
    rw [hhE, jetElem]
    exact analyticMeroElement_congr _ _ (by funext z; simp [iteratedDeriv_zero])
  -- `f ∘ g` is transcendental over the constants
  have htrans : Transcendental ℂ hElem := by
    rw [hhfun]
    exact transcendental_analyticMeroElement_of_nonconstant hcomp _ hnc
  have hderivan : AnalyticOnNhd ℂ (fun z => deriv f (g z)) (Set.univ : Set ℂ) := by
    have hd : Differentiable ℂ (fun z => deriv f (g z)) := by
      have hfan : AnalyticOnNhd ℂ f (Set.univ : Set ℂ) :=
        hf.differentiableOn.analyticOnNhd isOpen_univ
      have h1 : Differentiable ℂ (deriv f) :=
        fun z => ((hfan.deriv) z (Set.mem_univ z)).differentiableAt
      exact fun z => (h1 (g z)).comp z (hg z)
    exact hd.differentiableOn.analyticOnNhd isOpen_univ
  have hpowan : ∀ k : ℕ, AnalyticOnNhd ℂ (fun z => (deriv f (g z)) ^ k) (Set.univ : Set ℂ) :=
    fun k x hx => (hderivan x hx).pow k
  -- the coefficients of the composed relation
  set C : ℕ → meroField (Set.univ : Set ℂ) := fun k => Polynomial.aeval hElem (c k) with hC
  have hCmem : ∀ k, C k ∈ Algebra.adjoin ℂ ({hElem} : Set (meroField (Set.univ : Set ℂ))) := by
    intro k
    rw [hC, Algebra.adjoin_singleton_eq_range_aeval]
    exact ⟨c k, rfl⟩
  have hCne : C k₀ ≠ 0 := by
    rw [hC]
    intro hcon
    exact hk₀ (by
      by_contra hne
      exact htrans ⟨c k₀, hne, hcon⟩)
  -- the relation in the field
  have hfieldrel : ∑ k ∈ Finset.range (m + 1), C k * aElem ^ k = 0 := by
    have hterm : ∀ k, C k * aElem ^ k
        = analyticMeroElement (fun z => (c k).eval (f (g z)) * (deriv f (g z)) ^ k)
            (((analyticOnNhd_eval_polynomial
              (hcomp.differentiableOn.analyticOnNhd isOpen_univ) (c k))).mul
              (hpowan k)) := by
      intro k
      simp only [hC, haE, hhfun]
      rw [aeval_analyticMeroElement_polynomial, compJetElem,
        ← analyticMeroElement_pow, ← analyticMeroElement_mul]
      refine analyticMeroElement_congr _ _ ?_
      funext z
      simp [compJetFun, iteratedDeriv_one]
    have hsumfun : AnalyticOnNhd ℂ (fun z => ∑ k ∈ Finset.range (m + 1),
        (c k).eval (f (g z)) * (deriv f (g z)) ^ k) (Set.univ : Set ℂ) := by
      have hpi : (fun z => ∑ k ∈ Finset.range (m + 1),
          (c k).eval (f (g z)) * (deriv f (g z)) ^ k)
          = ∑ k ∈ Finset.range (m + 1),
            fun z => (c k).eval (f (g z)) * (deriv f (g z)) ^ k := by
        funext z
        rw [Finset.sum_apply]
      rw [hpi]
      refine Finset.sum_induction _ (fun h => AnalyticOnNhd ℂ h (Set.univ : Set ℂ))
        (fun a b ha hb => ha.add hb) analyticOnNhd_const ?_
      intro k _
      exact ((analyticOnNhd_eval_polynomial
        (hcomp.differentiableOn.analyticOnNhd isOpen_univ) (c k))).mul (hpowan k)
    have hzero : analyticMeroElement (fun z => ∑ k ∈ Finset.range (m + 1),
        (c k).eval (f (g z)) * (deriv f (g z)) ^ k) hsumfun = 0 := by
      refine (analyticMeroElement_eq_zero_iff _).mpr ?_
      intro z _
      exact hrel (g z)
    rw [Finset.sum_congr rfl (fun k _ => hterm k),
      ← analyticMeroElement_finsetSum _ _ (fun k =>
        ((analyticOnNhd_eval_polynomial
          (hcomp.differentiableOn.analyticOnNhd isOpen_univ) (c k))).mul (hpowan k)) hsumfun]
    exact hzero
  -- assemble the algebraic relation
  refine ⟨∑ k ∈ Finset.range (m + 1),
    Polynomial.C (⟨C k, hCmem k⟩ :
      ↥(Algebra.adjoin ℂ ({hElem} : Set (meroField (Set.univ : Set ℂ))))) * Polynomial.X ^ k,
    ?_, ?_⟩
  · intro hzero
    have hcoeff := congrArg (fun p => p.coeff k₀) hzero
    simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_zero] at hcoeff
    rw [Finset.sum_eq_single k₀] at hcoeff
    · simp only [if_true, mul_one] at hcoeff
      exact hCne (congrArg Subtype.val hcoeff)
    · intro b _ hb
      simp [Ne.symm hb]
    · intro hcon
      exact absurd (Finset.mem_range.mpr (by omega)) hcon
  · rw [map_sum]
    simp only [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
    exact hfieldrel

end

end GaloisForLFunctions.HTGeometry
