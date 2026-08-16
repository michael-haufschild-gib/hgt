import GaloisForLFunctions.HTGeometry.RationalOrder

/-!
# The signed order is a valuation

Additivity of the order under multiplication was enough for the transport of an invariance relation
along a map, but a functional equation with an additive term needs the valuation inequality as well:
the order of a sum is at least the minimum of the orders, with equality when they differ.

Both come from the polynomial statement that a power of `X - c` dividing two polynomials divides
their sum, transported through the reduced representation of a rational function.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {K : Type*} [Field K]

/-- **Root multiplicity of a sum.** -/
theorem min_le_rootMultiplicity_add {p q : K[X]} (hp : p ≠ 0) (hq : q ≠ 0) (hpq : p + q ≠ 0)
    (c : K) :
    min (rootMultiplicity c p) (rootMultiplicity c q) ≤ rootMultiplicity c (p + q) := by
  classical
  set k : ℕ := min (rootMultiplicity c p) (rootMultiplicity c q) with hk
  have hdp : ((X - C c) ^ k : K[X]) ∣ p :=
    (le_rootMultiplicity_iff hp).mp (by rw [hk]; exact min_le_left _ _)
  have hdq : ((X - C c) ^ k : K[X]) ∣ q :=
    (le_rootMultiplicity_iff hq).mp (by rw [hk]; exact min_le_right _ _)
  exact (le_rootMultiplicity_iff hpq).mpr (dvd_add hdp hdq)

/-- The reduced representation of a rational function as a quotient of polynomials. -/
theorem eq_num_div_denom (f : RatFunc K) :
    f = algebraMap K[X] (RatFunc K) f.num * (algebraMap K[X] (RatFunc K) f.denom)⁻¹ := by
  rw [← div_eq_mul_inv]
  exact (RatFunc.num_div_denom f).symm

theorem algebraMap_ne_zero_of_ne_zero {p : K[X]} (hp : p ≠ 0) :
    algebraMap K[X] (RatFunc K) p ≠ 0 :=
  fun h => hp ((RatFunc.algebraMap_injective K) (by rw [h, map_zero]))

/-- **The order of a sum is at least the minimum of the orders.** -/
theorem min_le_ratOrder_add {f g : RatFunc K} (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f + g ≠ 0)
    (c : K) : min (ratOrder f c) (ratOrder g c) ≤ ratOrder (f + g) c := by
  classical
  have hfn : f.num ≠ 0 := RatFunc.num_ne_zero hf
  have hgn : g.num ≠ 0 := RatFunc.num_ne_zero hg
  have hfd : f.denom ≠ 0 := RatFunc.denom_ne_zero f
  have hgd : g.denom ≠ 0 := RatFunc.denom_ne_zero g
  set P : K[X] := f.num * g.denom + g.num * f.denom with hP
  have hPne : P ≠ 0 := by
    intro h
    refine hfg ?_
    have hAd : algebraMap K[X] (RatFunc K) f.denom ≠ 0 := algebraMap_ne_zero_of_ne_zero hfd
    have hBd : algebraMap K[X] (RatFunc K) g.denom ≠ 0 := algebraMap_ne_zero_of_ne_zero hgd
    have hsum : f + g = algebraMap K[X] (RatFunc K) P
        * (algebraMap K[X] (RatFunc K) (f.denom * g.denom))⁻¹ := by
      rw [hP, map_add, map_mul, map_mul, map_mul, mul_inv, mul_comm]
      conv_lhs => rw [eq_num_div_denom f, eq_num_div_denom g]
      field_simp
    rw [hsum, h, map_zero, zero_mul]
  have hDne : f.denom * g.denom ≠ 0 := mul_ne_zero hfd hgd
  have hsum : f + g = algebraMap K[X] (RatFunc K) P
      * (algebraMap K[X] (RatFunc K) (f.denom * g.denom))⁻¹ := by
    have hAd : algebraMap K[X] (RatFunc K) f.denom ≠ 0 := algebraMap_ne_zero_of_ne_zero hfd
    have hBd : algebraMap K[X] (RatFunc K) g.denom ≠ 0 := algebraMap_ne_zero_of_ne_zero hgd
    rw [hP, map_add, map_mul, map_mul, map_mul, mul_inv, mul_comm]
    conv_lhs => rw [eq_num_div_denom f, eq_num_div_denom g]
    field_simp
  have hAP : algebraMap K[X] (RatFunc K) P ≠ 0 := algebraMap_ne_zero_of_ne_zero hPne
  have hAD : algebraMap K[X] (RatFunc K) (f.denom * g.denom) ≠ 0 :=
    algebraMap_ne_zero_of_ne_zero hDne
  rw [hsum, ratOrder_mul hAP (inv_ne_zero hAD), ratOrder_inv hAD, ratOrder_algebraMap,
    ratOrder_algebraMap, rootMultiplicity_mul hDne]
  have hmul₁ : rootMultiplicity c (f.num * g.denom)
      = rootMultiplicity c f.num + rootMultiplicity c g.denom :=
    rootMultiplicity_mul (mul_ne_zero hfn hgd)
  have hmul₂ : rootMultiplicity c (g.num * f.denom)
      = rootMultiplicity c g.num + rootMultiplicity c f.denom :=
    rootMultiplicity_mul (mul_ne_zero hgn hfd)
  have hmin := min_le_rootMultiplicity_add (mul_ne_zero hfn hgd) (mul_ne_zero hgn hfd)
    (by rw [← hP]; exact hPne) c
  rw [hmul₁, hmul₂] at hmin
  have hmin' : min ((rootMultiplicity c f.num : ℤ) + (rootMultiplicity c g.denom : ℤ))
      ((rootMultiplicity c g.num : ℤ) + (rootMultiplicity c f.denom : ℤ))
      ≤ (rootMultiplicity c P : ℤ) := by
    exact_mod_cast hmin
  rw [ratOrder, ratOrder]
  omega

end GaloisForLFunctions.HTGeometry
