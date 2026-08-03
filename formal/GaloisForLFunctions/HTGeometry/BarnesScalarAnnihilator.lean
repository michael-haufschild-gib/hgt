import GaloisForLFunctions.HTGeometry.BarnesAnnihilatorTheorem

/-!
# The scalar annihilator of the Barnes source

A pure translation operator is a differential-translation operator whose coefficients are constants.
Evaluating the differential variable at zero retracts the constant embedding, so divisibility by
the ladder product descends from the operator ring with differential coefficients to the one with
complex coefficients.  The exact annihilator therefore reads, for translations alone,

```text
Q Ψ_N is DA over ℂ(z)   ↔   ∏_j (T_j - 1) ∣ Q     in ℂ[T₁,…,T_N].
```

This is the card's structural annihilator theorem, the degree-zero part of the
differential-translation one.
-/

open Filter Set Topology Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic zeroNomeScalarTower

variable {N : ℕ}

/-! ## Constant coefficients -/

/-- The constant embedding of a translation operator. -/
def constEmbed (Q : MvPolynomial (Fin N) ℂ) : MvPolynomial (Fin N) (Polynomial ℂ) :=
  MvPolynomial.map Polynomial.C Q

/-- Evaluation of the differential variable at zero retracts the constant embedding. -/
theorem map_evalZero_constEmbed (Q : MvPolynomial (Fin N) ℂ) :
    MvPolynomial.map (Polynomial.evalRingHom 0) (constEmbed Q) = Q := by
  rw [constEmbed, MvPolynomial.map_map]
  have hcomp : (Polynomial.evalRingHom (0 : ℂ)).comp Polynomial.C = RingHom.id ℂ := by
    ext a
    simp
  rw [hcomp, MvPolynomial.map_id]

theorem map_evalZero_fullLadder (N : ℕ) :
    MvPolynomial.map (Polynomial.evalRingHom 0) (fullLadder N)
      = ∏ j, (MvPolynomial.X j - 1 : MvPolynomial (Fin N) ℂ) := by
  rw [fullLadder, map_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [map_sub, MvPolynomial.map_X, map_one]

theorem constEmbed_prod (N : ℕ) :
    constEmbed (∏ j, (MvPolynomial.X j - 1 : MvPolynomial (Fin N) ℂ)) = fullLadder N := by
  rw [constEmbed, fullLadder, map_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [map_sub, MvPolynomial.map_X, map_one]

/-- **Divisibility by the ladder product descends to constant coefficients.** -/
theorem fullLadder_dvd_constEmbed_iff (Q : MvPolynomial (Fin N) ℂ) :
    fullLadder N ∣ constEmbed Q ↔ (∏ j, (MvPolynomial.X j - 1 : MvPolynomial (Fin N) ℂ)) ∣ Q := by
  constructor
  · rintro ⟨T, hT⟩
    refine ⟨MvPolynomial.map (Polynomial.evalRingHom 0) T, ?_⟩
    have h := congrArg (MvPolynomial.map (Polynomial.evalRingHom (0 : ℂ))) hT
    rw [map_evalZero_constEmbed, map_mul, map_evalZero_fullLadder] at h
    exact h
  · rintro ⟨T, rfl⟩
    exact ⟨constEmbed T, by rw [constEmbed, map_mul, ← constEmbed, ← constEmbed, constEmbed_prod]⟩

/-! ## The scalar action -/

/-- The action of a pure translation operator. -/
def transApply (ω : Fin N → ℂ) (Q : MvPolynomial (Fin N) ℂ)
    (y : meroField (Set.univ : Set ℂ)) : meroField (Set.univ : Set ℂ) :=
  ∑ n ∈ Q.support, algebraMap ℂ (meroField (Set.univ : Set ℂ)) (MvPolynomial.coeff n Q) *
    addTranslationMeroEquiv (monomialShift ω n) y

theorem differentialOperatorApply_polynomialC (a : ℂ) (y : meroField (Set.univ : Set ℂ)) :
    differentialOperatorApply (Polynomial.C a) y
      = algebraMap ℂ (meroField (Set.univ : Set ℂ)) a * y := by
  rw [show (Polynomial.C a : Polynomial ℂ) = Polynomial.monomial 0 a by simp,
    differentialOperatorApply_monomial, differentialJet_zero]

/-- The scalar action is the differential action of the constant embedding. -/
theorem transApply_eq_diffTranslateApply (ω : Fin N → ℂ) (Q : MvPolynomial (Fin N) ℂ)
    (y : meroField (Set.univ : Set ℂ)) :
    transApply ω Q y = diffTranslateApply ω (constEmbed Q) y := by
  have hsupp : (constEmbed Q).support = Q.support := by
    rw [constEmbed]
    exact MvPolynomial.support_map_of_injective Q Polynomial.C_injective
  rw [transApply, diffTranslateApply, hsupp]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hcoeff : MvPolynomial.coeff n (constEmbed Q) = Polynomial.C (MvPolynomial.coeff n Q) := by
    rw [constEmbed, MvPolynomial.coeff_map]
  rw [hcoeff, differentialOperatorApply_polynomialC]

/-! ## The scalar annihilator -/

/-- **The exact structural annihilator of the Barnes source.**  For rationally independent periods
in a common half-plane, a pure translation operator sends the Barnes source into the differentially
algebraic sector exactly when the full ladder product divides it. -/
theorem differentialAlgebraicOver_transApply_barnesSource_iff [NeZero N] (ω : Fin N → ℂ)
    (hω : ∀ i, 0 < (ω i).im)
    (hindep : ∀ n : Fin N → ℤ, ∑ k, (n k : ℂ) * ω k = 0 → ∀ k, n k = 0)
    (Q : MvPolynomial (Fin N) ℂ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
        (transApply ω Q (barnesSourceLogDerivMero ω hω))
      ↔ (∏ j, (MvPolynomial.X j - 1 : MvPolynomial (Fin N) ℂ)) ∣ Q := by
  rw [transApply_eq_diffTranslateApply,
    differentialAlgebraicOver_diffTranslateApply_barnesSource_iff ω hω hindep,
    fullLadder_dvd_constEmbed_iff]

end

end GaloisForLFunctions.HTGeometry
