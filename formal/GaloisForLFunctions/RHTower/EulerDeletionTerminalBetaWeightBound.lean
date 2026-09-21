import GaloisForLFunctions.RHTower.EulerDeletionChildFibreContrast

/-!
# Terminal EDQ beta-weight bound

The terminal Euler-deletion child kernel has exact beta weight

`∫₀¹ (1 - x) x^(A - 1) / (1 - x^C) dx`,

where its physical child condition gives `1 ≤ A ≤ C`.  This leaf proves its
unconditional positive harmonic bound `0 ≤ W ≤ 1 / A`.

Consequently beta transport attenuates a terminal source cell without changing
its sign.  It cannot supply the signed endpoint-cell cancellation required by
EDQ; that cancellation remains entirely in the Möbius source cells and their
pairwise contrasts.
-/

noncomputable section

open Finset MeasureTheory
open scoped BigOperators

namespace RHTower.DeletionResidueMartingale

private def geometricBetaKernel (A C : ℕ) (x : ℝ) : ℝ :=
  (1 - x) * x ^ (A - 1) * (1 - x ^ C)⁻¹

private def regularGeometricBetaKernel (A C : ℕ) (x : ℝ) : ℝ :=
  x ^ (A - 1) * (∑ i ∈ range C, x ^ i)⁻¹

private theorem geometricBetaKernel_eq_regular {A C : ℕ} (hC : 0 < C)
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    geometricBetaKernel A C x = regularGeometricBetaKernel A C x := by
  have hgeom : 1 - x ^ C = (1 - x) * ∑ i ∈ range C, x ^ i := by
    calc
      1 - x ^ C = -(x ^ C - 1) := by ring
      _ = -((∑ i ∈ range C, x ^ i) * (x - 1)) := by rw [geom_sum_mul]
      _ = (1 - x) * ∑ i ∈ range C, x ^ i := by ring
  have hsub : 1 - x ≠ 0 := ne_of_gt (sub_pos.mpr hx1)
  have hsum : ∑ i ∈ range C, x ^ i ≠ 0 := by
    apply ne_of_gt
    apply Finset.sum_pos'
    · intro i _
      exact pow_nonneg hx0.le _
    · refine ⟨0, Finset.mem_range.mpr hC, ?_⟩
      simp
  unfold geometricBetaKernel regularGeometricBetaKernel
  rw [hgeom]
  field_simp

private theorem regularGeometricBetaKernel_nonneg {A C : ℕ} {x : ℝ}
    (hx0 : 0 ≤ x) : 0 ≤ regularGeometricBetaKernel A C x := by
  unfold regularGeometricBetaKernel
  apply mul_nonneg
  · exact pow_nonneg hx0 _
  · apply inv_nonneg.mpr
    exact Finset.sum_nonneg fun i _ => pow_nonneg hx0 _

private theorem regularGeometricBetaKernel_le_inv {A C : ℕ} (hA : 0 < A) (hAC : A ≤ C)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    regularGeometricBetaKernel A C x ≤ 1 / (A : ℝ) := by
  have hsum_pos : 0 < ∑ i ∈ range C, x ^ i := by
    apply Finset.sum_pos'
    · intro i _
      exact pow_nonneg hx0 _
    · refine ⟨0, Finset.mem_range.mpr (lt_of_lt_of_le hA hAC), by simp⟩
  have hgeo := geometric_denominator_half_prefix_lower x hx0 hx1 A C hAC
  unfold regularGeometricBetaKernel
  rw [show x ^ (A - 1) * (∑ i ∈ range C, x ^ i)⁻¹ =
      x ^ (A - 1) / (∑ i ∈ range C, x ^ i) by ring]
  apply (div_le_iff₀ hsum_pos).2
  calc
    x ^ (A - 1) = (A : ℝ)⁻¹ * ((A : ℝ) * x ^ (A - 1)) := by
      field_simp [ne_of_gt (by exact_mod_cast hA : (A : ℝ) ≠ 0)]
    _ ≤ (A : ℝ)⁻¹ * (∑ i ∈ range C, x ^ i) :=
      mul_le_mul_of_nonneg_left hgeo (inv_nonneg.mpr (by positivity))
    _ = (1 / (A : ℝ)) * (∑ i ∈ range C, x ^ i) := by ring

private theorem continuousOn_regularGeometricBetaKernel {A C : ℕ} (hC : 0 < C) :
    ContinuousOn (regularGeometricBetaKernel A C) (Set.Icc (0 : ℝ) 1) := by
  have hsum_cont : Continuous (fun x : ℝ => ∑ i ∈ range C, x ^ i) :=
    continuous_finsetSum _ fun i _ => continuous_pow i
  have hsum_ne : ∀ x ∈ Set.Icc (0 : ℝ) 1, (∑ i ∈ range C, x ^ i) ≠ 0 := by
    intro x hx
    apply ne_of_gt
    apply Finset.sum_pos'
    · intro i _
      exact pow_nonneg hx.1 _
    · exact ⟨0, Finset.mem_range.mpr hC, by simp⟩
  exact ((continuous_pow (A - 1)).continuousOn).mul
    (hsum_cont.continuousOn.inv₀ hsum_ne)

private theorem intervalIntegrable_geometricBetaKernel {A C : ℕ} (hC : 0 < C) :
    IntervalIntegrable (geometricBetaKernel A C) volume 0 1 := by
  rw [intervalIntegrable_iff, Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  apply (integrableOn_Ioc_iff_integrableOn_Ioo).2
  change IntegrableOn (geometricBetaKernel A C) (Set.Ioo (0 : ℝ) 1) volume
  have hregularInt : IntervalIntegrable (regularGeometricBetaKernel A C) volume 0 1 :=
    (show ContinuousOn (regularGeometricBetaKernel A C) (Set.uIcc (0 : ℝ) 1) by
      simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
        (continuousOn_regularGeometricBetaKernel (A := A) hC)).intervalIntegrable
  have hregularIoc := intervalIntegrable_iff.mp hregularInt
  rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hregularIoc
  have hregular : IntegrableOn (regularGeometricBetaKernel A C) (Set.Ioo (0 : ℝ) 1) volume :=
    hregularIoc.mono_set (fun x hx => ⟨hx.1, hx.2.le⟩)
  refine hregular.congr_fun ?_ measurableSet_Ioo
  intro x hx
  exact (geometricBetaKernel_eq_regular hC hx.1 hx.2).symm

private theorem intervalIntegral_geometricBetaKernel_eq_regular {A C : ℕ} (hC : 0 < C) :
    (∫ x in (0 : ℝ)..1, geometricBetaKernel A C x) =
      ∫ x in (0 : ℝ)..1, regularGeometricBetaKernel A C x := by
  rw [intervalIntegral.integral_of_le (by norm_num),
    intervalIntegral.integral_of_le (by norm_num)]
  rw [integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact geometricBetaKernel_eq_regular hC hx.1 hx.2

private theorem intervalIntegral_geometricBetaKernel_bounds {A C : ℕ} (hA : 0 < A) (hAC : A ≤ C) :
    0 ≤ (∫ x in (0 : ℝ)..1, geometricBetaKernel A C x) ∧
      (∫ x in (0 : ℝ)..1, geometricBetaKernel A C x) ≤ 1 / (A : ℝ) := by
  have hC : 0 < C := lt_of_lt_of_le hA hAC
  have hregularInt : IntervalIntegrable (regularGeometricBetaKernel A C) volume 0 1 :=
    (show ContinuousOn (regularGeometricBetaKernel A C) (Set.uIcc (0 : ℝ) 1) by
      simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
        (continuousOn_regularGeometricBetaKernel (A := A) hC)).intervalIntegrable
  rw [intervalIntegral_geometricBetaKernel_eq_regular hC]
  constructor
  · exact intervalIntegral.integral_nonneg (by norm_num) fun x hx =>
      regularGeometricBetaKernel_nonneg hx.1
  · calc
      (∫ x in (0 : ℝ)..1, regularGeometricBetaKernel A C x) ≤
          ∫ _x in (0 : ℝ)..1, 1 / (A : ℝ) :=
        intervalIntegral.integral_mono_on (by norm_num) hregularInt intervalIntegrable_const
          fun x hx => regularGeometricBetaKernel_le_inv hA hAC hx.1 hx.2
      _ = 1 / (A : ℝ) := by simp

/-- Every admissible terminal EDQ beta weight is nonnegative and no larger than
the reciprocal of its literal chronological endpoint. -/
theorem terminalChildTailWeight_nonneg_and_le (n b : ℕ)
    (hb : b < clock (n + 1) / clock n) :
    0 ≤ terminalChildTailWeight n b ∧
      terminalChildTailWeight n b ≤ 1 / ((clock n * (b + 1) : ℕ) : ℝ) := by
  let A := clock n * (b + 1)
  let C := clock (n + 1)
  have hA : 0 < A := Nat.mul_pos (clock_pos n) (Nat.succ_pos b)
  have hAC : A ≤ C := by
    calc
      clock n * (b + 1) ≤ clock n * (clock (n + 1) / clock n) :=
        Nat.mul_le_mul_left _ (Nat.succ_le_iff.mpr hb)
      _ = clock (n + 1) := Nat.mul_div_cancel' (clock_dvd (Nat.le_succ n))
  have hbound := intervalIntegral_geometricBetaKernel_bounds hA hAC
  simpa only [terminalChildTailWeight, A, C, geometricBetaKernel] using hbound

end RHTower.DeletionResidueMartingale
