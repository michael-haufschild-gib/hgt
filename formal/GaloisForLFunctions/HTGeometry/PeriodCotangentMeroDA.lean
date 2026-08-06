import GaloisForLFunctions.HTGeometry.RationalCorrectionDA
import GaloisForLFunctions.HTGeometry.AnalyticJetFieldBridge

/-!
# The cotangent of a complex period, inside the meromorphic field

The order-one boundary of the multiple sine hierarchy is a cotangent of the period,

```text
(π/w) cot(π z / w),
```

and this file builds it as an element of the global meromorphic field together with the two facts
the descent needs: it has that function as its punctured-local representative, and it is
differentially algebraic over `ℂ(z)`.

Both come from the harmonic equation.  The sine and the scaled cosine of the period are entire
solutions of `f'' = -(π/w)² f`, hence differentially algebraic; the global analytic-jet bridge turns
that into differential algebraicity of their meromorphic realizations, and the quotient of two
differentially algebraic elements is differentially algebraic.  The quotient's punctured
representative is the quotient of the two functions, which is the cotangent.
-/

open Filter Set Topology Complex
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic

/-! ### Second-order equations are algebraic differential equations -/

/-- **A constant-coefficient harmonic equation witnesses differential algebraicity.** -/
theorem differentiallyAlgebraic_of_secondOrder {f : ℂ → ℂ} {c : ℂ}
    (h : ∀ z, deriv (deriv f) z = c * f z) : DifferentiallyAlgebraic f := by
  refine ⟨2, MvPolynomial.X 3 - MvPolynomial.C c * MvPolynomial.X 1, ?_, ?_⟩
  · intro h0
    have hev := congrArg
      (MvPolynomial.eval (fun i : Fin 4 => if i = 3 then (1 : ℂ) else 0)) h0
    simp at hev
  · intro z
    have h0 : iteratedDeriv 0 f z = f z := by rw [iteratedDeriv_zero]
    have h2 : iteratedDeriv 2 f z = deriv (deriv f) z := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    have e1 : (Fin.cons z (fun j : Fin 3 => iteratedDeriv (j : ℕ) f z) : Fin 4 → ℂ) 1
        = f z := by
      show iteratedDeriv ((0 : Fin 3) : ℕ) f z = _
      exact h0
    have e3 : (Fin.cons z (fun j : Fin 3 => iteratedDeriv (j : ℕ) f z) : Fin 4 → ℂ) 3
        = deriv (deriv f) z := by
      show iteratedDeriv ((2 : Fin 3) : ℕ) f z = _
      exact h2
    simp only [map_sub, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C, e1, e3]
    rw [h z]
    ring

/-! ### The sine and cosine of a period -/

/-- The sine of the period `w`. -/
def periodSin (w : ℂ) : ℂ → ℂ := fun z => Complex.sin ((Real.pi : ℂ) * z / w)

/-- The scaled cosine of the period `w`: the derivative of `periodSin`. -/
def periodCosScaled (w : ℂ) : ℂ → ℂ :=
  fun z => ((Real.pi : ℂ) / w) * Complex.cos ((Real.pi : ℂ) * z / w)

theorem hasDerivAt_periodArgument (w z : ℂ) :
    HasDerivAt (fun x : ℂ => (Real.pi : ℂ) * x / w) ((Real.pi : ℂ) / w) z := by
  simpa [mul_comm, mul_div_assoc] using
    (((hasDerivAt_id z).const_mul (Real.pi : ℂ)).div_const w)

theorem hasDerivAt_periodSin (w z : ℂ) :
    HasDerivAt (periodSin w) (periodCosScaled w z) z := by
  have hsin := (Complex.hasDerivAt_sin ((Real.pi : ℂ) * z / w)).comp z
    (hasDerivAt_periodArgument w z)
  refine hsin.congr_deriv ?_
  unfold periodCosScaled
  ring

theorem deriv_periodSin (w : ℂ) : deriv (periodSin w) = periodCosScaled w :=
  funext fun z => (hasDerivAt_periodSin w z).deriv

theorem hasDerivAt_periodCosScaled (w z : ℂ) :
    HasDerivAt (periodCosScaled w)
      (-(((Real.pi : ℂ) / w) ^ 2) * periodSin w z) z := by
  have hcos := (Complex.hasDerivAt_cos ((Real.pi : ℂ) * z / w)).comp z
    (hasDerivAt_periodArgument w z)
  refine (hcos.const_mul ((Real.pi : ℂ) / w)).congr_deriv ?_
  unfold periodSin
  ring

theorem deriv_periodCosScaled (w : ℂ) :
    deriv (periodCosScaled w) = fun z => -(((Real.pi : ℂ) / w) ^ 2) * periodSin w z :=
  funext fun z => (hasDerivAt_periodCosScaled w z).deriv

theorem differentiable_periodSin (w : ℂ) : Differentiable ℂ (periodSin w) :=
  fun z => (hasDerivAt_periodSin w z).differentiableAt

theorem differentiable_periodCosScaled (w : ℂ) : Differentiable ℂ (periodCosScaled w) :=
  fun z => (hasDerivAt_periodCosScaled w z).differentiableAt

theorem analyticOnNhd_periodSin (w : ℂ) :
    AnalyticOnNhd ℂ (periodSin w) (Set.univ : Set ℂ) := by
  rw [Complex.analyticOnNhd_univ_iff_differentiable]
  exact differentiable_periodSin w

theorem analyticOnNhd_periodCosScaled (w : ℂ) :
    AnalyticOnNhd ℂ (periodCosScaled w) (Set.univ : Set ℂ) := by
  rw [Complex.analyticOnNhd_univ_iff_differentiable]
  exact differentiable_periodCosScaled w

/-! ### Both are differentially algebraic -/

theorem differentiallyAlgebraic_periodSin (w : ℂ) :
    DifferentiallyAlgebraic (periodSin w) := by
  refine differentiallyAlgebraic_of_secondOrder (c := -(((Real.pi : ℂ) / w) ^ 2)) ?_
  intro z
  rw [deriv_periodSin, deriv_periodCosScaled]

theorem differentiallyAlgebraic_periodCosScaled (w : ℂ) :
    DifferentiallyAlgebraic (periodCosScaled w) := by
  refine differentiallyAlgebraic_of_secondOrder (c := -(((Real.pi : ℂ) / w) ^ 2)) ?_
  intro z
  rw [deriv_periodCosScaled]
  have hderiv : HasDerivAt (fun x : ℂ => -(((Real.pi : ℂ) / w) ^ 2) * periodSin w x)
      (-(((Real.pi : ℂ) / w) ^ 2) * periodCosScaled w z) z :=
    (hasDerivAt_periodSin w z).const_mul _
  rw [hderiv.deriv]

/-! ### The cotangent element of the meromorphic field -/

/-- The period cotangent `(π/w) cot(π z/w)` as an element of the global meromorphic field. -/
def periodCotMero (w : ℂ) : meroField (Set.univ : Set ℂ) :=
  analyticMeroElement (periodCosScaled w) (analyticOnNhd_periodCosScaled w) /
    analyticMeroElement (periodSin w) (analyticOnNhd_periodSin w)

/-- The germ of the period sine is nonzero. -/
theorem analyticFunctionElement_periodSin_ne_zero {w : ℂ} (hw : w ≠ 0) :
    analyticFunctionElement (periodSin w) (analyticOnNhd_periodSin w) ≠ 0 := by
  intro h0
  have hgerm : ((periodSin w : ℂ → ℂ) : Germ (𝓟 (Set.univ : Set ℂ)) ℂ) = 0 :=
    congrArg Subtype.val h0
  have hall : ∀ z : ℂ, periodSin w z = 0 := by
    have := Germ.coe_eq.mp hgerm
    intro z
    exact (eventually_principal.mp this) z (Set.mem_univ z)
  have hval := hall (w / 2)
  rw [periodSin, show (Real.pi : ℂ) * (w / 2) / w = (Real.pi : ℂ) / 2 by
    field_simp, Complex.sin_pi_div_two] at hval
  exact one_ne_zero hval

/-- **The period cotangent has the cotangent as its punctured representative.** -/
theorem hasPuncturedMeromorphicRep_periodCotMero {w : ℂ} (hw : w ≠ 0) :
    HasPuncturedMeromorphicRep (periodCotMero w)
      (fun z => ((Real.pi : ℂ) / w) * Complex.cot ((Real.pi : ℂ) * z / w)) := by
  have hfrac := hasPuncturedMeromorphicRep_fraction
    (a := analyticFunctionElement (periodCosScaled w) (analyticOnNhd_periodCosScaled w))
    (b := analyticFunctionElement (periodSin w) (analyticOnNhd_periodSin w))
    (analyticFunctionElement_periodSin_ne_zero hw)
    (analyticOnNhd_periodCosScaled w) (analyticOnNhd_periodSin w) rfl rfl
  refine hfrac.congr_fun fun z => Filter.Eventually.of_forall fun x => ?_
  show periodCosScaled w x / periodSin w x
      = ((Real.pi : ℂ) / w) * Complex.cot ((Real.pi : ℂ) * x / w)
  rw [Complex.cot_eq_cos_div_sin]
  unfold periodCosScaled periodSin
  ring

/-- **The period cotangent is differentially algebraic over `ℂ(z)`.** -/
theorem differentialAlgebraicOver_periodCotMero (w : ℂ) :
    DifferentialAlgebraicOver (RatFunc ℂ) (periodCotMero w) := by
  refine differentialAlgebraicOver_div ?_ ?_
  · exact differentialAlgebraicOver_analyticMeroElement_of_differentiallyAlgebraic
      (analyticOnNhd_periodCosScaled w) (differentiallyAlgebraic_periodCosScaled w)
  · exact differentialAlgebraicOver_analyticMeroElement_of_differentiallyAlgebraic
      (analyticOnNhd_periodSin w) (differentiallyAlgebraic_periodSin w)

end

end GaloisForLFunctions.HTGeometry
