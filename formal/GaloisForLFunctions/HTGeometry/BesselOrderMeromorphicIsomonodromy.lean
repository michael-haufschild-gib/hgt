import GaloisForLFunctions.HTGeometry.BesselOrderMeromorphic
import GaloisForLFunctions.HTGeometry.BesselOrderIsomonodromyObstruction
import GaloisForLFunctions.HTGeometry.BesselOrderRiccati
import GaloisForLFunctions.HTGeometry.MeromorphicRatFuncTranslation
import GaloisForLFunctions.HTGeometry.DeltaStructureCompatibility

/-!
# The order derivative of the modified Bessel function is not a Bessel combination

For `s > 0` the order function `ν ↦ K_ν(s)` is entire and satisfies the shift recurrence
`K_{ν+2}(s) = K_ν(s) + (2(ν+1)/s) K_{ν+1}(s)`.  This file proves that its order derivative is not
a rational-function combination of `K_ν(s)` and `K_{ν+1}(s)`: there are no `P, Q ∈ ℂ(ν)` with

`∂K_ν(s)/∂ν = P(ν) K_ν(s) + Q(ν) K_{ν+1}(s)`.

Equivalently, the rank-two order module carries no compatible derivation over `ℂ(ν)` — the
isomonodromy datum a parameterized Picard--Vessiot classification has to exclude.

The proof transports the hypothesis through the shift.  Because translation commutes with the
derivation and restricts to `X ↦ X + 1` on `ℂ(ν)`, the assumed formula propagates to the shifted
solution, and applying it twice expresses one meromorphic element in two ways.  The two solutions
`K_ν(s)` and `K_{ν+1}(s)` are linearly independent over `ℂ(ν)` — a dependence would be a rational
solution of the Bessel Riccati equation, which the tree excludes — so the coefficients agree, giving
the two rational compatibility identities that the degree count at infinity refutes.
-/

open Filter Set Topology
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic

/-- The unit translation restricts to the unit shift on the embedded rational functions. -/
theorem addTranslationMeroEquiv_one_algebraMap (r : RatFunc ℂ) :
    addTranslationMeroEquiv (1 : ℂ)
        (algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) r)
      = algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) (ratShift r) :=
  addTranslationMeroEquiv_ratfuncToMero r

/-- The order function is a nonzero meromorphic element. -/
theorem modifiedBesselKOrderMero_ne_zero {s : ℝ} (hs : 0 < s) :
    modifiedBesselKOrderMero s hs ≠ 0 := by
  rw [modifiedBesselKOrderMero, Ne, analyticMeroElement_eq_zero_iff]
  intro h
  have h0 := h 0 (Set.mem_univ 0)
  have hpos := modifiedBesselKOrder_real_pos hs 0
  rw [Complex.ofReal_zero, h0] at hpos
  simp at hpos

theorem addTranslationMeroEquiv_modifiedBesselKOrderMero_ne_zero {s : ℝ} (hs : 0 < s) :
    addTranslationMeroEquiv (1 : ℂ) (modifiedBesselKOrderMero s hs) ≠ 0 := fun h =>
  modifiedBesselKOrderMero_ne_zero hs
    ((addTranslationMeroEquiv (1 : ℂ)).injective (by rw [h, map_zero]))

/-- Translation moves the shifted order function one step further. -/
theorem addTranslationMeroEquiv_one_shift {s : ℝ} (hs : 0 < s) (q : ℂ) :
    addTranslationMeroEquiv (1 : ℂ) (modifiedBesselKOrderShiftMero s hs q)
      = modifiedBesselKOrderShiftMero s hs (q + 1) := by
  rw [modifiedBesselKOrderShiftMero, addTranslationMeroEquiv_analyticMeroElement,
    modifiedBesselKOrderShiftMero]
  exact analyticMeroElement_congr _ _ (by funext z; ring_nf)

/-- The order recurrence in the meromorphic field, with the rational shift coefficient. -/
theorem modifiedBesselKOrderMero_recurrence {s : ℝ} (hs : 0 < s) :
    addTranslationMeroEquiv (1 : ℂ)
        (addTranslationMeroEquiv (1 : ℂ) (modifiedBesselKOrderMero s hs))
      = modifiedBesselKOrderMero s hs
        + algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) (orderShiftCoeff (2 / (s : ℂ)))
          * addTranslationMeroEquiv (1 : ℂ) (modifiedBesselKOrderMero s hs) := by
  have h1 : addTranslationMeroEquiv (1 : ℂ) (modifiedBesselKOrderMero s hs)
      = modifiedBesselKOrderShiftMero s hs 1 :=
    addTranslationMeroEquiv_modifiedBesselKOrderMero s hs 1
  have h2 : addTranslationMeroEquiv (1 : ℂ) (modifiedBesselKOrderShiftMero s hs 1)
      = modifiedBesselKOrderShiftMero s hs 2 := by
    rw [addTranslationMeroEquiv_one_shift hs 1]
    norm_num
  have hrec := modifiedBesselKOrderShiftMero_recurrence s hs 1
  have hcoeff : besselOrderLinearCoeffShiftMero s 1
      = algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))
        (orderShiftCoeff (2 / (s : ℂ))) := by
    rw [besselOrderLinearCoeffShiftMero_eq_algebraMap]
    rfl
  rw [h1, h2]
  norm_num at hrec
  rw [hcoeff] at hrec
  exact hrec

/-- The derivative of the shift coefficient is the constant slope. -/
theorem deriv_orderShiftCoeff (c : ℂ) :
    Differential.deriv (orderShiftCoeff c) = algebraMap ℂ (RatFunc ℂ) c := by
  rw [orderShiftCoeff]
  show ratFuncCoordinateDerivation ℂ
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C c * (Polynomial.X + Polynomial.C 1)))
    = algebraMap ℂ (RatFunc ℂ) c
  rw [ratFuncCoordinateDerivation_algebraMap]
  simp

/-- **The two order solutions are linearly independent over `ℂ(ν)`.**  A dependence would be a
rational solution of the Bessel Riccati equation, which the tree excludes. -/
theorem besselMero_linearIndependent {s : ℝ} (hs : 0 < s) (α β : RatFunc ℂ)
    (h : algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) α * modifiedBesselKOrderMero s hs
        + algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) β
          * addTranslationMeroEquiv (1 : ℂ) (modifiedBesselKOrderMero s hs) = 0) :
    α = 0 ∧ β = 0 := by
  have hy0 : modifiedBesselKOrderMero s hs ≠ 0 := modifiedBesselKOrderMero_ne_zero hs
  have hinj : Function.Injective
      (algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))) :=
    (algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))).injective
  by_cases hβ : β = 0
  · subst hβ
    rw [map_zero, zero_mul, add_zero, mul_eq_zero] at h
    rcases h with h | h
    · exact ⟨hinj (by rw [h, map_zero]), rfl⟩
    · exact absurd h hy0
  · exfalso
    have hρβ : algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) β ≠ 0 := fun h0 =>
      hβ (hinj (by rw [h0, map_zero]))
    have huβ : (-α / β) * β = -α := by field_simp
    have hvu : algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) (-α / β)
          * modifiedBesselKOrderMero s hs
        = addTranslationMeroEquiv (1 : ℂ) (modifiedBesselKOrderMero s hs) := by
      apply mul_left_cancel₀ hρβ
      calc algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) β
              * (algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) (-α / β)
                * modifiedBesselKOrderMero s hs)
            = algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) ((-α / β) * β)
              * modifiedBesselKOrderMero s hs := by rw [map_mul]; ring
        _ = algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) (-α)
              * modifiedBesselKOrderMero s hs := by rw [huβ]
        _ = algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) β
              * addTranslationMeroEquiv (1 : ℂ) (modifiedBesselKOrderMero s hs) := by
              rw [map_neg]; linear_combination -h
    have hshift := congrArg (addTranslationMeroEquiv (1 : ℂ)) hvu
    rw [map_mul, addTranslationMeroEquiv_one_algebraMap] at hshift
    have hrec := modifiedBesselKOrderMero_recurrence hs
    rw [← hshift, ← hvu] at hrec
    have hric : (-α / β) * ratShift (-α / β)
        - orderShiftCoeff (2 / (s : ℂ)) * (-α / β) - 1 = 0 := by
      have h2 : algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))
          ((-α / β) * ratShift (-α / β)
            - orderShiftCoeff (2 / (s : ℂ)) * (-α / β) - 1)
          * modifiedBesselKOrderMero s hs = 0 := by
        simp only [map_sub, map_mul, map_one]
        linear_combination hrec
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact hinj (by rw [h3, map_zero])
      · exact absurd h3 hy0
    exact modifiedBesselOrderRiccati_no_ratFunc_solution hs ⟨-α / β, hric⟩

/-- **The order derivative of the modified Bessel function is not a rational Bessel combination.**
For `s > 0` there are no rational functions `P, Q` with
`∂K_ν(s)/∂ν = P(ν) K_ν(s) + Q(ν) K_{ν+1}(s)`. -/
theorem modifiedBesselKOrderMero_no_rational_delta_structure {s : ℝ} (hs : 0 < s) :
    ¬ ∃ P Q : RatFunc ℂ,
      Differential.deriv (modifiedBesselKOrderMero s hs)
        = algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) P * modifiedBesselKOrderMero s hs
          + algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) Q
            * addTranslationMeroEquiv (1 : ℂ) (modifiedBesselKOrderMero s hs) := by
  rintro ⟨P, Q, hδ⟩
  obtain ⟨hA, hB⟩ :=
    deltaStructure_compatibility
      (algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))) ratShift
      (addTranslationMeroEquiv (1 : ℂ))
      (fun x => addTranslationMeroEquiv_deriv 1 x)
      addTranslationMeroEquiv_one_algebraMap
      (fun r => deriv_algebraMap (A := RatFunc ℂ) (B := meroField (Set.univ : Set ℂ)) r)
      (modifiedBesselKOrderMero_recurrence hs)
      (besselMero_linearIndependent hs) hδ
  rw [deriv_orderShiftCoeff] at hB
  exact besselOrder_no_rational_delta_structure
    (div_ne_zero (by norm_num) (by exact_mod_cast ne_of_gt hs)) P Q hA hB

end

end GaloisForLFunctions.HTGeometry
