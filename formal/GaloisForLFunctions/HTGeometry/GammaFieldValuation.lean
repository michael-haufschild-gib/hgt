import GaloisForLFunctions.HTGeometry.GammaDatumUltrametric
import GaloisForLFunctions.HTGeometry.UniformGammaDatumHom

/-!
# The Gamma field carries a discrete valuation

The `Γ`-exponent of the boundary datum is multiplicative on products and cannot drop on a sum, so it
is a valuation of `K_Γ` with values in `ℤₘ₀`.  Its uniformizer is `Γ` and it is trivial on the digamma
field: adjoining `Γ` to `L` creates exactly one exponential direction.
-/

open Filter Set Topology Function
open scoped Differential
open scoped Classical

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

local instance gammaFieldValDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance gammaFieldValIntAlgebra : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _

local instance gammaFieldValDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance gammaFieldValComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance gammaFieldValRatAlgebra : Algebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncToMero.toAlgebra

local instance gammaFieldValRatFuncDifferential : Differential (RatFunc ℂ) :=
  ratFuncCoordinateDifferential

local instance gammaFieldValRatFuncDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncDifferentialAlgebra

/-- Every nonzero element of the Gamma field has a datum. -/
theorem exists_hasGammaTubeDatum_coe {x : gammaFieldK} (hx : x ≠ 0) :
    ∃ (k a b : ℤ) (c : ℂ), HasGammaTubeDatum 1 (x : upperEndMeroField) k a b c := by
  refine exists_hasGammaTubeDatum one_pos x.2 ?_
  intro h0
  exact hx (Subtype.ext (by simpa using h0))

/-- The `Γ`-exponent of an element of the Gamma field. -/
def gammaExponentK (x : gammaFieldK) : ℤ :=
  if h : x = 0 then 0 else (gammaUnitDatum (Units.mk0 x h)).1.1

/-- The `Γ`-exponent is read off any datum. -/
theorem gammaExponentK_eq_of {x : gammaFieldK} (hx : x ≠ 0) {k a b : ℤ} {c : ℂ}
    (h : HasGammaTubeDatum 1 (x : upperEndMeroField) k a b c) : gammaExponentK x = k := by
  rw [gammaExponentK, dif_neg hx]
  have hunit : gammaUnitDatum (Units.mk0 x hx) = ((k, a, b), Units.mk0 c h.1) :=
    gammaUnitDatum_eq_of h
  rw [hunit]

/-- **The Gamma field's exponential valuation.**  Its value group is `ℤ`, written multiplicatively;
`Γ` has value `ofAdd (-1)` and every element of the digamma field has value `1`. -/
def gammaValuation : Valuation gammaFieldK (WithZero (Multiplicative ℤ)) where
  toFun x := if x = 0 then (0 : WithZero (Multiplicative ℤ))
    else ((Multiplicative.ofAdd (-(gammaExponentK x)) : Multiplicative ℤ) :
      WithZero (Multiplicative ℤ))
  map_zero' := by
    rw [if_pos rfl]
  map_one' := by
    have hone : ((1 : gammaFieldK) : upperEndMeroField) = 1 := by simp
    have hdat : HasGammaTubeDatum 1 (((1 : gammaFieldK)) : upperEndMeroField) 0 0 0 1 := by
      rw [hone]
      exact hasGammaTubeDatum_one
    rw [if_neg (one_ne_zero : (1 : gammaFieldK) ≠ 0), gammaExponentK_eq_of one_ne_zero hdat]
    rfl
  map_mul' x y := by
    by_cases hx : x = 0
    · rw [hx, zero_mul, if_pos rfl, zero_mul]
    by_cases hy : y = 0
    · rw [hy, mul_zero, if_pos rfl, mul_zero]
    obtain ⟨k, a, b, c, hdx⟩ := exists_hasGammaTubeDatum_coe hx
    obtain ⟨k', a', b', c', hdy⟩ := exists_hasGammaTubeDatum_coe hy
    have hcoe : ((x * y : gammaFieldK) : upperEndMeroField)
        = (x : upperEndMeroField) * (y : upperEndMeroField) := by simp
    have hdxy : HasGammaTubeDatum 1 ((x * y : gammaFieldK) : upperEndMeroField)
        (k + k') (a + a') (b + b') (c * c') := by
      rw [hcoe]
      exact hdx.mul hdy
    rw [if_neg (mul_ne_zero hx hy), if_neg hx, if_neg hy, gammaExponentK_eq_of hx hdx,
      gammaExponentK_eq_of hy hdy, gammaExponentK_eq_of (mul_ne_zero hx hy) hdxy,
      ← WithZero.coe_mul, neg_add, ofAdd_add]
  map_add_le_max' x y := by
    by_cases hxy : x + y = 0
    · rw [hxy, if_pos rfl]
      exact zero_le
    by_cases hx : x = 0
    · rw [hx, zero_add, if_pos rfl]
      exact le_max_right _ _
    by_cases hy : y = 0
    · rw [hy, add_zero, if_pos rfl]
      exact le_max_left _ _
    obtain ⟨k, a, b, c, hdx⟩ := exists_hasGammaTubeDatum_coe hx
    obtain ⟨k', a', b', c', hdy⟩ := exists_hasGammaTubeDatum_coe hy
    obtain ⟨m, A, B, C, hdxy⟩ := exists_hasGammaTubeDatum_coe hxy
    have hcoe : ((x + y : gammaFieldK) : upperEndMeroField)
        = (x : upperEndMeroField) + (y : upperEndMeroField) := by simp
    rw [hcoe] at hdxy
    have hge : min k k' ≤ m := hasGammaTubeDatum_add_exponent_ge one_pos hdx hdy hdxy
    rw [if_neg hxy, if_neg hx, if_neg hy, gammaExponentK_eq_of hx hdx,
      gammaExponentK_eq_of hy hdy,
      gammaExponentK_eq_of hxy (by rw [hcoe]; exact hdxy)]
    rcases le_total k k' with hkk | hkk
    · rw [min_eq_left hkk] at hge
      have hle : (Multiplicative.ofAdd (-m) : Multiplicative ℤ)
          ≤ Multiplicative.ofAdd (-k) := (by omega : (-m : ℤ) ≤ -k)
      exact le_trans (WithZero.coe_le_coe.mpr hle) (le_max_left _ _)
    · rw [min_eq_right hkk] at hge
      have hle : (Multiplicative.ofAdd (-m) : Multiplicative ℤ)
          ≤ Multiplicative.ofAdd (-k') := (by omega : (-m : ℤ) ≤ -k')
      exact le_trans (WithZero.coe_le_coe.mpr hle) (le_max_right _ _)

theorem gammaValuation_apply_of_ne_zero {x : gammaFieldK} (hx : x ≠ 0) :
    gammaValuation x
      = ((Multiplicative.ofAdd (-(gammaExponentK x)) : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ)) := by
  show (if x = 0 then (0 : WithZero (Multiplicative ℤ)) else _) = _
  rw [if_neg hx]

/-- `Γ` is a uniformizer for the valuation. -/
theorem gammaValuation_gamma :
    gammaValuation (⟨gammaUpperMero,
        subset_differentialAdjoin (RatFunc ℂ) _ (Set.mem_singleton _)⟩ : gammaFieldK)
      = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  have hne : (⟨gammaUpperMero,
      subset_differentialAdjoin (RatFunc ℂ) _ (Set.mem_singleton _)⟩ : gammaFieldK) ≠ 0 := by
    intro h0
    exact gammaUpperMero_ne_zero (by simpa using congrArg Subtype.val h0)
  rw [gammaValuation_apply_of_ne_zero hne,
    gammaExponentK_eq_of hne (hasGammaTubeDatum_gammaUpperMero (M := 1))]

/-- The valuation is trivial on the digamma field. -/
theorem gammaValuation_eq_one_of_mem_digammaAdjoin {x : gammaFieldK} (hx : x ≠ 0)
    (hmem : (x : upperEndMeroField)
      ∈ differentialAdjoin (RatFunc ℂ) ({digammaMero} : Set upperEndMeroField)) :
    gammaValuation x = 1 := by
  have hx0 : (x : upperEndMeroField) ≠ 0 := by
    intro h0
    exact hx (Subtype.ext (by simpa using h0))
  obtain ⟨a, b, c, hdat⟩ := exists_hasGammaTubeDatum_digammaField one_pos hmem hx0
  rw [gammaValuation_apply_of_ne_zero hx, gammaExponentK_eq_of hx hdat]
  rfl

end

end GaloisForLFunctions.HTGeometry
