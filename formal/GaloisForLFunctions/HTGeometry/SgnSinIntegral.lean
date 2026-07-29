import GaloisForLFunctions.HTGeometry.AlternatingHarmonicPair
import GaloisForLFunctions.HTGeometry.SinSignIntervals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Data.Real.Sign
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The square wave against the inverse square

The set where `sin` is negative meets `[1,∞)` in the countable disjoint family of odd half-periods
`((2k+1)π, (2k+2)π)`, `k : ℕ`.  Integrating `x⁻²` over that family gives

```
∑_k (1/((2k+1)π) - 1/((2k+2)π)) = (log 2)/π,
```

by the grouped alternating harmonic value.  This is the mass that the square wave `sgn (sin x)`
removes from `∫₁^∞ x⁻² = 1`.
-/

open MeasureTheory Real Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- The `k`-th odd half-period, indexed by the naturals. -/
def oddHalfPeriod (k : ℕ) : Set ℝ := Ioo ((2 * (k : ℝ) + 1) * π) ((2 * (k : ℝ) + 2) * π)

theorem measurableSet_oddHalfPeriod (k : ℕ) : MeasurableSet (oddHalfPeriod k) :=
  measurableSet_Ioo

theorem one_lt_pi : (1 : ℝ) < π := by
  have := Real.two_le_pi
  linarith

theorem oddHalfPeriod_subset_Ici (k : ℕ) : oddHalfPeriod k ⊆ Ici (1 : ℝ) := by
  intro x hx
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hpi := one_lt_pi
  have : (1 : ℝ) ≤ (2 * (k : ℝ) + 1) * π := by nlinarith
  exact le_of_lt (lt_of_le_of_lt this hx.1)

theorem pairwise_disjoint_oddHalfPeriod :
    Pairwise (Function.onFun Disjoint oddHalfPeriod) := by
  intro i j hij
  have hij' : (i : ℤ) ≠ (j : ℤ) := by exact_mod_cast hij
  have h := pairwise_disjoint_oddInterval hij'
  simpa [Function.onFun, oddHalfPeriod] using h

/-- **The negativity set of the sine above `1`.** -/
theorem Ici_inter_sin_neg_eq_iUnion :
    Ici (1 : ℝ) ∩ {x : ℝ | Real.sin x < 0} = ⋃ k : ℕ, oddHalfPeriod k := by
  ext x
  constructor
  · rintro ⟨hx1, hxs⟩
    have hx1 : (1 : ℝ) ≤ x := hx1
    obtain ⟨k, hk⟩ := (sin_neg_iff x).mp hxs
    have hk0 : 0 ≤ k := zero_le_of_oddInterval_mem_Ici hx1 hk
    refine Set.mem_iUnion.mpr ⟨k.toNat, ?_⟩
    have hcast : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hk0]
    rw [oddHalfPeriod, hcast]
    exact hk
  · intro hx
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
    refine ⟨oddHalfPeriod_subset_Ici k hk, ?_⟩
    have hcast : ((k : ℕ) : ℝ) = (((k : ℕ) : ℤ) : ℝ) := by push_cast; ring
    refine sin_neg_of_mem_oddInterval (k := (k : ℤ)) ?_
    rw [← hcast]
    exact hk

/-- The inverse square integrates over an odd half-period to the difference of the endpoints'
reciprocals. -/
theorem integral_inv_sq_oddHalfPeriod (k : ℕ) :
    ∫ x in oddHalfPeriod k, (x ^ 2)⁻¹
      = 1 / ((2 * (k : ℝ) + 1) * π) - 1 / ((2 * (k : ℝ) + 2) * π) := by
  have hpi := Real.pi_pos
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have ha : (0 : ℝ) < (2 * (k : ℝ) + 1) * π := by positivity
  have hab : (2 * (k : ℝ) + 1) * π < (2 * (k : ℝ) + 2) * π := by nlinarith
  have hzero : (0 : ℝ) ∉ uIcc ((2 * (k : ℝ) + 1) * π) ((2 * (k : ℝ) + 2) * π) := by
    rw [Set.uIcc_of_le hab.le]
    rintro ⟨h1, -⟩
    linarith
  have hint : ∫ x in ((2 * (k : ℝ) + 1) * π)..((2 * (k : ℝ) + 2) * π), x ^ (-2 : ℤ)
      = 1 / ((2 * (k : ℝ) + 1) * π) - 1 / ((2 * (k : ℝ) + 2) * π) := by
    have hb : (0 : ℝ) < (2 * (k : ℝ) + 2) * π := by positivity
    rw [integral_zpow (Or.inr ⟨by norm_num, hzero⟩),
      show ((-2 : ℤ) + 1) = (-1 : ℤ) by norm_num, zpow_neg_one, zpow_neg_one,
      show (((-2 : ℤ) : ℝ) + 1) = -1 by norm_num]
    field_simp
    ring
  rw [← hint, intervalIntegral.integral_of_le hab.le,
    MeasureTheory.integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
  rw [show ((-2 : ℤ)) = -((2 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast]

/-- **The removed mass.**  Summing the odd half-periods gives `(log 2)/π`. -/
theorem tsum_integral_inv_sq_oddHalfPeriod :
    ∑' k : ℕ, (∫ x in oddHalfPeriod k, (x ^ 2)⁻¹) = Real.log 2 / π := by
  have hpi := Real.pi_pos
  have hterm : ∀ k : ℕ, (∫ x in oddHalfPeriod k, (x ^ 2)⁻¹)
      = π⁻¹ * alternatingHarmonicPair k := by
    intro k
    rw [integral_inv_sq_oddHalfPeriod k, alternatingHarmonicPair]
    have h1 : (0 : ℝ) < 2 * (k : ℝ) + 1 := by positivity
    have h2 : (0 : ℝ) < 2 * (k : ℝ) + 2 := by positivity
    field_simp
  rw [tsum_congr hterm, summable_alternatingHarmonicPair.tsum_mul_left,
    tsum_alternatingHarmonicPair, div_eq_inv_mul]

/-! ## The value of the square-wave integral -/

/-- The negativity set of the sine above `1`. -/
def sinNegAboveOne : Set ℝ := ⋃ k : ℕ, oddHalfPeriod k

theorem measurableSet_sinNegAboveOne : MeasurableSet sinNegAboveOne :=
  MeasurableSet.iUnion fun k => measurableSet_oddHalfPeriod k

theorem sinNegAboveOne_subset_Ici : sinNegAboveOne ⊆ Ici (1 : ℝ) :=
  Set.iUnion_subset fun k => oddHalfPeriod_subset_Ici k

/-- Every odd half-period starts at or beyond `π`. -/
theorem sinNegAboveOne_subset_Ici_of_le_pi {a : ℝ} (ha : a ≤ π) : sinNegAboveOne ⊆ Ici a := by
  refine Set.iUnion_subset fun k x hx => ?_
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hpi := Real.pi_pos
  have hlow : π ≤ (2 * (k : ℝ) + 1) * π := by nlinarith
  exact le_of_lt (lt_of_le_of_lt (le_trans ha hlow) hx.1)

theorem integrableOn_inv_sq_Ici {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => (x ^ 2)⁻¹) (Ici a) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  have hbase : IntegrableOn (fun t : ℝ => t ^ (-2 : ℝ)) (Ioi a) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) ha
  refine hbase.congr_fun (fun x hx => ?_) measurableSet_Ioi
  have hx0 : (0 : ℝ) < x := lt_trans ha hx
  change x ^ (-2 : ℝ) = (x ^ 2)⁻¹
  rw [Real.rpow_neg hx0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

theorem integral_inv_sq_Ici {a : ℝ} (ha : 0 < a) : ∫ x in Ici a, (x ^ 2)⁻¹ = 1 / a := by
  rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
  have hcongr : ∫ x in Ioi a, (x ^ 2)⁻¹ = ∫ x in Ioi a, x ^ (-2 : ℝ) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : (0 : ℝ) < x := lt_trans ha hx
    change (x ^ 2)⁻¹ = x ^ (-2 : ℝ)
    rw [Real.rpow_neg hx0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hcongr, integral_Ioi_rpow_of_lt (by norm_num) ha,
    show ((-2 : ℝ) + 1) = -1 by norm_num, Real.rpow_neg_one]
  field_simp

theorem integral_indicator_sinNegAboveOne {a : ℝ} (ha : 0 < a) (hapi : a ≤ π) :
    ∫ x in Ici a, sinNegAboveOne.indicator (fun x : ℝ => (x ^ 2)⁻¹) x
      = Real.log 2 / π := by
  have hsub := sinNegAboveOne_subset_Ici_of_le_pi hapi
  rw [setIntegral_indicator measurableSet_sinNegAboveOne,
    Set.inter_eq_self_of_subset_right hsub]
  have hInt : IntegrableOn (fun x : ℝ => (x ^ 2)⁻¹) sinNegAboveOne :=
    (integrableOn_inv_sq_Ici ha).mono_set hsub
  rw [sinNegAboveOne, MeasureTheory.integral_iUnion measurableSet_oddHalfPeriod
    pairwise_disjoint_oddHalfPeriod (by rwa [← sinNegAboveOne])]
  exact tsum_integral_inv_sq_oddHalfPeriod

theorem ae_sin_ne_zero : ∀ᵐ x : ℝ, Real.sin x ≠ 0 := by
  have hcount : {x : ℝ | Real.sin x = 0}.Countable := by
    have hset : {x : ℝ | Real.sin x = 0} = Set.range (fun n : ℤ => (n : ℝ) * π) := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_range, Real.sin_eq_zero_iff]
    rw [hset]
    exact Set.countable_range _
  rw [MeasureTheory.ae_iff]
  simpa using hcount.measure_zero volume

/-- **The square wave against the inverse square.**  For every base point between `1` and `π` the
tail integral is `1/a` minus the fixed square-wave defect `(2/π) log 2`. -/
theorem integral_sign_sin_mul_inv_sq_Ici {a : ℝ} (ha1 : 1 ≤ a) (hapi : a ≤ π) :
    ∫ x in Ici a, Real.sign (Real.sin x) * (x ^ 2)⁻¹ = 1 / a - 2 / π * Real.log 2 := by
  have ha : (0 : ℝ) < a := lt_of_lt_of_le zero_lt_one ha1
  have hsub := sinNegAboveOne_subset_Ici_of_le_pi hapi
  have hae : ∀ᵐ x : ℝ, x ∈ Ici a →
      Real.sign (Real.sin x) * (x ^ 2)⁻¹
        = (x ^ 2)⁻¹ - 2 * sinNegAboveOne.indicator (fun x : ℝ => (x ^ 2)⁻¹) x := by
    filter_upwards [ae_sin_ne_zero] with x hx0 hxa
    have hx1 : (1 : ℝ) ≤ x := le_trans ha1 hxa
    rcases lt_or_gt_of_ne hx0 with hneg | hpos
    · have hmem : x ∈ sinNegAboveOne := by
        rw [sinNegAboveOne, ← Ici_inter_sin_neg_eq_iUnion]
        exact ⟨hx1, hneg⟩
      rw [Real.sign_of_neg hneg, Set.indicator_of_mem hmem]
      ring
    · have hnot : x ∉ sinNegAboveOne := by
        intro hmem
        rw [sinNegAboveOne, ← Ici_inter_sin_neg_eq_iUnion] at hmem
        exact absurd hmem.2 (not_lt.mpr hpos.le)
      rw [Real.sign_of_pos hpos, Set.indicator_of_notMem hnot]
      ring
  rw [setIntegral_congr_ae measurableSet_Ici hae]
  have hInt1 : IntegrableOn (fun x : ℝ => (x ^ 2)⁻¹) (Ici a) := integrableOn_inv_sq_Ici ha
  have hInt2 : IntegrableOn
      (fun x : ℝ => 2 * sinNegAboveOne.indicator (fun x : ℝ => (x ^ 2)⁻¹) x)
      (Ici a) :=
    ((hInt1.indicator measurableSet_sinNegAboveOne).const_mul 2)
  rw [MeasureTheory.integral_sub hInt1 hInt2, MeasureTheory.integral_const_mul,
    integral_inv_sq_Ici ha, integral_indicator_sinNegAboveOne ha hapi]
  field_simp

/-- The base point `1`. -/
theorem integral_sign_sin_mul_inv_sq_Ici_one :
    ∫ x in Ici (1 : ℝ), Real.sign (Real.sin x) * (x ^ 2)⁻¹ = 1 - 2 / π * Real.log 2 := by
  have h := integral_sign_sin_mul_inv_sq_Ici (a := 1) le_rfl (by linarith [Real.two_le_pi])
  simpa using h

/-- The base point `2`, legitimate because `2 < π`. -/
theorem integral_sign_sin_mul_inv_sq_Ici_two :
    ∫ x in Ici (2 : ℝ), Real.sign (Real.sin x) * (x ^ 2)⁻¹ = 1 / 2 - 2 / π * Real.log 2 :=
  integral_sign_sin_mul_inv_sq_Ici (by norm_num) Real.two_le_pi

/-- **Equations (7)–(8) of the card.**  The endpoint difference `J(1) - J(2)` is exactly
`(2/π) log 2`, the coefficient that cancels the small-`n` Landau--Gonek term. -/
theorem sgnSin_endpoint_difference :
    1 * (∫ x in Ici (1 : ℝ), Real.sign (Real.sin x) * (x ^ 2)⁻¹)
        - 2 * (∫ x in Ici (2 : ℝ), Real.sign (Real.sin x) * (x ^ 2)⁻¹)
      = 2 / π * Real.log 2 := by
  rw [integral_sign_sin_mul_inv_sq_Ici_one, integral_sign_sin_mul_inv_sq_Ici_two]
  ring

end GaloisForLFunctions.HTGeometry
