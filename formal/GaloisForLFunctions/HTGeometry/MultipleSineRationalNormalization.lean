import GaloisForLFunctions.HTGeometry.MultipleSineOrderOneSourceExact

/-!
# The rational normalization of the two-period multiple sine

The exact ladder defect and the exact order-one source are both rational, and their pole parts are
simple poles at

```text
-ω_k,   ω_1 + ω_2,   0,   ω_j.
```

These are two `ω_k`-orbit pairs, `{0, -ω_k}` and `{ω_j, ω_1 + ω_2}`, with opposite residues, so the
single symmetric rational function

```text
ρ = 1/z - 1/(z - (ω_1 + ω_2))
```

has exactly the required shift difference: adding `ρ` to the source cancels every pole of the
accumulated defect, and what remains is a polynomial.

The polynomial that remains is `P_k - P_k(ω_j - ·)`, the antisymmetrized ladder-correction
polynomial.  Discrete integration removes it up to a constant, which is what the cotangent-model
character obstruction tolerates.
-/

open Filter Set Topology Complex Polynomial
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic

/-! ### Simple poles in the coordinate field -/

/-- The simple pole `1/(X - a)`. -/
def linInv (a : ℂ) : RatFunc ℂ :=
  (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.X - Polynomial.C a))⁻¹

theorem linInv_ne_zero (a : ℂ) : linInv a ≠ 0 := by
  rw [linInv]
  refine inv_ne_zero (RatFunc.algebraMap_ne_zero ?_)
  exact Polynomial.X_sub_C_ne_zero a

theorem algebraMap_linear_ne_zero (a : ℂ) :
    algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.X - Polynomial.C a) ≠ 0 :=
  RatFunc.algebraMap_ne_zero (Polynomial.X_sub_C_ne_zero a)

theorem linInv_mul (a : ℂ) :
    linInv a * algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.X - Polynomial.C a) = 1 := by
  rw [linInv, inv_mul_cancel₀ (algebraMap_linear_ne_zero a)]

/-- Translating a simple pole moves its location. -/
theorem ratShiftBy_linInv (q a : ℂ) : ratShiftBy q (linInv a) = linInv (a - q) := by
  rw [linInv, linInv, map_inv₀, ratShiftBy_algebraMap]
  congr 2
  rw [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp, map_sub]
  ring

/-- Reflecting a simple pole reflects its location and flips its sign. -/
theorem ratReflectBy_linInv (c a : ℂ) : ratReflectBy c (linInv a) = -linInv (c - a) := by
  rw [linInv, linInv, map_inv₀, ratReflectBy_algebraMap]
  have h : (Polynomial.X - Polynomial.C a).comp (Polynomial.C c - Polynomial.X)
      = -(Polynomial.X - Polynomial.C (c - a)) := by
    rw [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp, map_sub]
    ring
  rw [h, map_neg]
  exact inv_neg

/-! ### The two rational data in partial fractions -/

/-- The order-one correction has two simple poles, at `0` and at the period. -/
theorem orderOneCorrection_eq (w : ℂ) :
    orderOneCorrection w = -linInv 0 - linInv w := by
  have hX : algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.X - Polynomial.C 0) ≠ 0 :=
    algebraMap_linear_ne_zero 0
  have hXw : algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.X - Polynomial.C w) ≠ 0 :=
    algebraMap_linear_ne_zero w
  have hden : algebraMap (Polynomial ℂ) (RatFunc ℂ) (orderOneDenominator w)
      = -(algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.X - Polynomial.C 0) *
          algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.X - Polynomial.C w)) := by
    rw [orderOneDenominator, ← map_mul, ← map_neg]
    congr 1
    simp only [map_zero]
    ring
  have hnum : algebraMap (Polynomial ℂ) (RatFunc ℂ) (orderOneNumerator w)
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.X - Polynomial.C 0)
          + algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.X - Polynomial.C w) := by
    rw [orderOneNumerator, ← map_add]
    congr 1
    simp only [map_zero, map_ofNat]
    ring
  rw [orderOneCorrection, hnum, hden, linInv, linInv]
  field_simp
  ring

/-- The ladder defect has a single simple pole at `-ω_k`. -/
theorem subframeLadderRat_eq {ι : Type} [Fintype ι] [DecidableEq ι] (ω : ι → ℂ)
    (S : Finset ι) (k : ι) (hk : k ∈ S) (hωk : ω k ≠ 0)
    [Nonempty {i : ι // i ∈ S}] :
    subframeLadderRat ω S k hk
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) (barnesLadderPolyPart (subframe ω S) ⟨k, hk⟩)
        - linInv (-(ω k)) := by
  have hval : subframe ω S ⟨k, hk⟩ = ω k := rfl
  have hkey := barnesLadderRatio_eq (subframe ω S) ⟨k, hk⟩ hωk
  rw [hval] at hkey
  rw [subframeLadderRat]
  have hXC : Polynomial.X + Polynomial.C (ω k)
      = Polynomial.X - Polynomial.C (-(ω k)) := by
    rw [map_neg, sub_neg_eq_add]
  rw [hkey, linInv, hXC, one_div]

/-! ### The normalization -/

/-- The rational normalization of the two-period source. -/
def normalizationRat (c : ℂ) : RatFunc ℂ := linInv 0 - linInv c

theorem shiftDiff_normalizationRat (q c : ℂ) :
    ratShiftBy q (normalizationRat c) - normalizationRat c
      = linInv (-q) - linInv (c - q) - linInv 0 + linInv c := by
  rw [normalizationRat, map_sub, ratShiftBy_linInv, ratShiftBy_linInv, zero_sub]
  ring

/-- **The normalized two-period defect is a polynomial.**  Adding the rational normalization to the
source cancels every pole of the exact ladder defect and of the order-one correction, leaving the
antisymmetrized ladder-correction polynomial. -/
theorem multipleSine_two_normalized_defect {ι : Type} [Fintype ι] [DecidableEq ι]
    (ω : ι → ℂ) (S : Finset ι) (k j : ι) (hk : k ∈ S) (herase : S.erase k = ({j} : Finset ι))
    (hcard : S.card = 2) (hωk : ω k ≠ 0) [Nonempty {i : ι // i ∈ S}] :
    (subframeLadderRat ω S k hk
        + (frameSignZ S : RatFunc ℂ) * ratReflectBy (frameReflectionPoint ω (S.erase k))
            (subframeLadderRat ω S k hk))
      - orderOneCorrection (ω j)
      + (ratShiftBy (ω k) (normalizationRat (ω k + ω j)) - normalizationRat (ω k + ω j))
    = algebraMap (Polynomial ℂ) (RatFunc ℂ)
        (barnesLadderPolyPart (subframe ω S) ⟨k, hk⟩
          - (barnesLadderPolyPart (subframe ω S) ⟨k, hk⟩).comp
              (Polynomial.C (ω j) - Polynomial.X)) := by
  classical
  set P : Polynomial ℂ := barnesLadderPolyPart (subframe ω S) ⟨k, hk⟩ with hP
  have hpoint : frameReflectionPoint ω (S.erase k) = ω j := by
    rw [herase, frameReflectionPoint, Finset.sum_singleton]
  have hsign : frameSignZ S = -1 := by
    rw [frameSignZ, hcard]
    norm_num
  have hR := subframeLadderRat_eq ω S k hk hωk
  rw [hpoint, hsign, hR, orderOneCorrection_eq (ω j), shiftDiff_normalizationRat]
  rw [map_sub, ratReflectBy_linInv, ratReflectBy_algebraMap]
  have hc1 : ω j - -(ω k) = ω k + ω j := by ring
  have hc2 : ω k + ω j - ω k = ω j := by ring
  rw [hc1, hc2]
  push_cast
  ring

end

end GaloisForLFunctions.HTGeometry
