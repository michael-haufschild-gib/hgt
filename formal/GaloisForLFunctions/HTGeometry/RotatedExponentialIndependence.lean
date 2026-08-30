import GaloisForLFunctions.HTGeometry.ExponentialCapNonAdditivity
import GaloisForLFunctions.HTGeometry.ExponentialLinearIndependence
import GaloisForLFunctions.HTGeometry.AlgebraAdjoinAlgebraic

/-!
# The two exponentials `exp z` and `exp (i z)` are algebraically independent over `ℂ(z)`

A polynomial relation between the two exponentials over the rational functions is, expanded in
monomials, a linear relation among the exponential-like elements `exp(z)^j exp(iz)^k`, whose
exponents `j + i k` are pairwise distinct.  Artin's shortening argument reduces such a relation to
the equation `c′ = λ c` for a nonzero complex constant `λ`, which no nonzero rational function
solves.  Hence all coefficients vanish and the relation was trivial.

The coordinate, `exp z` and `exp (i z)` therefore span three transcendence degrees over `ℂ`.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher
open scoped Differential

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

/-! ### The rotated exponential -/

theorem hasDerivAt_expI (z : ℂ) :
    HasDerivAt (fun w : ℂ => Complex.exp (Complex.I * w))
      (Complex.exp (Complex.I * z) * Complex.I) z := by
  have h : HasDerivAt (fun w : ℂ => Complex.I * w) Complex.I z := by
    simpa using (hasDerivAt_id z).const_mul Complex.I
  exact h.cexp

theorem differentiable_expI : Differentiable ℂ (fun z : ℂ => Complex.exp (Complex.I * z)) :=
  fun z => (hasDerivAt_expI z).differentiableAt

theorem analyticOnNhd_expI :
    AnalyticOnNhd ℂ (fun z : ℂ => Complex.exp (Complex.I * z)) (Set.univ : Set ℂ) :=
  differentiable_expI.differentiableOn.analyticOnNhd isOpen_univ

/-- The rotated exponential `exp (i z)` as an element of the meromorphic field. -/
def expIElem : meroField (Set.univ : Set ℂ) :=
  analyticMeroElement (fun z : ℂ => Complex.exp (Complex.I * z)) analyticOnNhd_expI

theorem deriv_expIElem :
    expIElem′ = algebraMap ℂ (meroField (Set.univ : Set ℂ)) Complex.I * expIElem := by
  rw [expIElem, deriv_analyticMeroElement', algebraMap_complex_eq_analyticMeroElement,
    ← analyticMeroElement_mul analyticOnNhd_const analyticOnNhd_expI]
  refine analyticMeroElement_congr _ _ ?_
  funext z
  rw [(hasDerivAt_expI z).deriv]
  ring

theorem expIElem_ne_zero : expIElem ≠ 0 := by
  rw [expIElem]
  intro h
  have := (analyticMeroElement_eq_zero_iff analyticOnNhd_expI).mp h 0 (Set.mem_univ 0)
  exact Complex.exp_ne_zero _ this

/-! ### The constant-coefficient rational obstruction -/

theorem algebraMap_complex_eq_ratFunc (c : ℂ) :
    algebraMap ℂ (meroField (Set.univ : Set ℂ)) c
      = algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) (RatFunc.C c) := by
  rw [algebraMap_ratFunc_C_eq, algebraMap_complex_eq_analyticMeroElement]

/-- **No nonzero rational function has a nonzero constant logarithmic derivative.** -/
theorem hker_const_ratField {lam : ℂ} (hlam : lam ≠ 0) (w : meroField (Set.univ : Set ℂ))
    (hw : w ∈ ratField) (h : w′ = algebraMap ℂ (meroField (Set.univ : Set ℂ)) lam * w) :
    w = 0 := by
  obtain ⟨r, rfl⟩ := hw
  rw [deriv_algebraMap r, algebraMap_complex_eq_ratFunc, ← map_mul] at h
  have hr : r′ = RatFunc.C lam * r := algebraMap_ratFunc_injective h
  have hzero : r = 0 := by
    refine GaloisForLFunctions.RationalShadow.eq_zero_of_deriv_eq_const_mul hlam ?_
    have hd : ratFuncCoordinateDerivation ℂ r = r′ := rfl
    rw [hd, hr, ← RatFunc.algebraMap_C]
  rw [hzero, map_zero]

/-! ### The exponential monomials -/

/-- The logarithmic derivatives of the two exponentials. -/
def expLam : Fin 2 → meroField (Set.univ : Set ℂ) :=
  ![1, algebraMap ℂ (meroField (Set.univ : Set ℂ)) Complex.I]

/-- The two exponentials. -/
def expPair : Fin 2 → meroField (Set.univ : Set ℂ) := ![expElem, expIElem]

theorem deriv_expPair (j : Fin 2) : (expPair j)′ = expLam j * expPair j := by
  fin_cases j
  · show expElem′ = (1 : meroField (Set.univ : Set ℂ)) * expElem
    rw [one_mul]
    exact deriv_expElem
  · show expIElem′ = algebraMap ℂ (meroField (Set.univ : Set ℂ)) Complex.I * expIElem
    exact deriv_expIElem

theorem expPair_ne_zero (j : Fin 2) : expPair j ≠ 0 := by
  fin_cases j
  · exact expElem_ne_zero
  · exact expIElem_ne_zero

theorem expLam_mem_ratField (j : Fin 2) : expLam j ∈ ratField := by
  fin_cases j
  · exact one_mem_ratField
  · exact IntermediateField.algebraMap_mem _ _

/-- The exponent attached to a monomial in the two exponentials. -/
def expExponent (m : Fin 2 →₀ ℕ) : ℂ := ((m 0 : ℕ) : ℂ) + Complex.I * ((m 1 : ℕ) : ℂ)

theorem expExponent_injective : Function.Injective expExponent := by
  intro m n h
  rw [expExponent, expExponent] at h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.natCast_re, Complex.natCast_im, zero_mul, one_mul, sub_zero,
    mul_zero, zero_add, add_zero] at hre him
  refine Finsupp.ext fun j => ?_
  fin_cases j
  · exact_mod_cast hre
  · exact_mod_cast him

theorem sum_expLam_eq (m : Fin 2 →₀ ℕ) :
    ∑ j : Fin 2, ((m j : ℕ) : meroField (Set.univ : Set ℂ)) * expLam j
      = algebraMap ℂ (meroField (Set.univ : Set ℂ)) (expExponent m) := by
  rw [Fin.sum_univ_two, expExponent, map_add, map_mul, map_natCast, map_natCast]
  show ((m 0 : ℕ) : meroField (Set.univ : Set ℂ)) * expLam 0
      + ((m 1 : ℕ) : meroField (Set.univ : Set ℂ)) * expLam 1 = _
  rw [show expLam 0 = 1 from rfl,
    show expLam 1 = algebraMap ℂ (meroField (Set.univ : Set ℂ)) Complex.I from rfl]
  ring

theorem sum_expLam_mem_ratField (m : Fin 2 →₀ ℕ) :
    ∑ j : Fin 2, ((m j : ℕ) : meroField (Set.univ : Set ℂ)) * expLam j ∈ ratField := by
  rw [sum_expLam_eq]
  exact IntermediateField.algebraMap_mem _ _

/-! ### Algebraic independence over the rational functions -/

/-- **The two exponentials are algebraically independent over the rational functions.** -/
theorem algebraicIndependent_expPair : AlgebraicIndependent ↥ratField expPair := by
  classical
  rw [algebraicIndependent_iff]
  intro P hP
  by_contra hP0
  obtain ⟨m₀, hm₀⟩ : P.support.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr fun h => hP0 (MvPolynomial.support_eq_empty.mp h)
  set Emon : ↥P.support → meroField (Set.univ : Set ℂ) :=
    fun m => ∏ j : Fin 2, expPair j ^ (m.1 j) with hEmon
  set tauf : ↥P.support → meroField (Set.univ : Set ℂ) :=
    fun m => ∑ j : Fin 2, ((m.1 j : ℕ) : meroField (Set.univ : Set ℂ)) * expLam j with htauf
  have hFd : ∀ a ∈ ratField.toSubfield, a′ ∈ ratField.toSubfield := fun a ha =>
    derivationClosed_ratField ha
  have hEne : ∀ m, Emon m ≠ 0 := by
    intro m
    rw [hEmon]
    refine Finset.prod_ne_zero_iff.mpr fun j _ => ?_
    exact pow_ne_zero _ (expPair_ne_zero j)
  have hEd : ∀ m, (Emon m)′ = tauf m * Emon m := fun m =>
    deriv_prod_pow Finset.univ expPair expLam (fun j _ => deriv_expPair j) (fun j => m.1 j)
  have htauF : ∀ m, tauf m ∈ ratField.toSubfield := fun m => sum_expLam_mem_ratField m.1
  have htau : ∀ m n : ↥P.support, m ≠ n → ∀ c ∈ ratField.toSubfield, c ≠ 0 →
      c′ ≠ (tauf m - tauf n) * c := by
    intro m n hmn c hc hc0 hrel
    have hne : expExponent m.1 - expExponent n.1 ≠ 0 := by
      intro h
      exact hmn (Subtype.ext (expExponent_injective (by linear_combination h)))
    have hdiff : tauf m - tauf n
        = algebraMap ℂ (meroField (Set.univ : Set ℂ)) (expExponent m.1 - expExponent n.1) := by
      have h1 : tauf m = algebraMap ℂ (meroField (Set.univ : Set ℂ)) (expExponent m.1) :=
        sum_expLam_eq m.1
      have h2 : tauf n = algebraMap ℂ (meroField (Set.univ : Set ℂ)) (expExponent n.1) :=
        sum_expLam_eq n.1
      rw [h1, h2, map_sub]
    rw [hdiff] at hrel
    exact hc0 (hker_const_ratField hne c hc hrel)
  have hsum : ∑ m : ↥P.support,
      ((P.coeff m.1 : ↥ratField) : meroField (Set.univ : Set ℂ)) * Emon m = 0 := by
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq'] at hP
    rw [← hP]
    exact (Finset.sum_subtype P.support (fun _ => Iff.rfl)
      (fun d => ((P.coeff d : ↥ratField) : meroField (Set.univ : Set ℂ))
        * ∏ j : Fin 2, expPair j ^ (d j))).symm
  have hall := eq_zero_of_sum_expLike_eq_zero ratField.toSubfield hFd Emon tauf hEne hEd htauF
    htau (fun m => ((P.coeff m.1 : ↥ratField) : meroField (Set.univ : Set ℂ)))
    (fun m => (P.coeff m.1).2) hsum
  have hz := hall ⟨m₀, hm₀⟩
  exact MvPolynomial.mem_support_iff.mp hm₀ (Subtype.ext hz)

/-! ### The three transcendence degrees -/

/-- **The rotated exponential is transcendental over the field of the coordinate and the
exponential.** -/
theorem not_isAlgebraic_expIElem :
    ¬ IsAlgebraic ↥(IntermediateField.adjoin ℂ
      (insert expElem ({coordElem} : Set (meroField (Set.univ : Set ℂ))))) expIElem := by
  intro halg
  have hle : IntermediateField.adjoin ℂ
      (insert expElem ({coordElem} : Set (meroField (Set.univ : Set ℂ))))
      ≤ (IntermediateField.adjoin ↥ratField
        ({expElem} : Set (meroField (Set.univ : Set ℂ)))).restrictScalars ℂ := by
    rw [IntermediateField.adjoin_le_iff]
    rintro y (rfl | rfl)
    · exact IntermediateField.subset_adjoin ↥ratField
        ({expElem} : Set (meroField (Set.univ : Set ℂ))) (Set.mem_singleton _)
    · exact IntermediateField.algebraMap_mem _ (⟨coordElem, coordElem_mem_ratField⟩ : ↥ratField)
  have h1 : IsAlgebraic ↥(IntermediateField.adjoin ↥ratField
      ({expElem} : Set (meroField (Set.univ : Set ℂ)))) expIElem := isAlgebraic_of_le hle halg
  have h2 : IsAlgebraic ↥(Algebra.adjoin ↥ratField
      ({expElem} : Set (meroField (Set.univ : Set ℂ)))) expIElem :=
    GaloisForLFunctions.isAlgebraic_algebraAdjoin_of_isAlgebraic_intermediateField _ h1
  have h3 := algebraicIndependent_expPair.transcendental_adjoin
    (s := ({0} : Set (Fin 2))) (i := 1) (by simp)
  have himg : expPair '' ({0} : Set (Fin 2)) = ({expElem} : Set (meroField (Set.univ : Set ℂ))) := by
    rw [Set.image_singleton]
    rfl
  rw [himg] at h3
  exact h3 h2

/-- **The coordinate and the two exponentials span three transcendence degrees.** -/
theorem trdeg_adjoin_coordElem_expElem_expIElem :
    Algebra.trdeg ℂ ↥(IntermediateField.adjoin ℂ
      (insert expIElem (insert expElem
        ({coordElem} : Set (meroField (Set.univ : Set ℂ)))))) = 3 := by
  have h1 := trdeg_adjoin_insert_eq_add_one not_isAlgebraic_expIElem
  exact h1.trans
    ((congrArg (fun c : Cardinal => c + 1) trdeg_adjoin_coordElem_expElem).trans (by norm_num))

end

end GaloisForLFunctions.HTGeometry
