import Mathlib

/-!
# Centered aperture carrier norms

The critical-norm step of `(PFK16)/(PFK17)` in
`xi-physical-prime-log-aperture-fusion-cross-kernel` needs: every centered aperture feature has `L²`
norm at most `√A`, and any nonnegative-weighted aggregate of such features has norm at most `√A` times
its total weight.  This file proves both at the level of an arbitrary atom log-location `b`, so the
same bound applies to ordinary primes (`b = log p`) and to proper prime powers (`b = r log p`), which
is exactly the von Mangoldt completion input of `(PFK16)`.
-/

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

/-- **Centered-indicator norm bound.**  For a measurable `I ⊆ (0,A]`, the centered carrier
`1_I - (|I|/A)·1_{(0,A]}` has norm at most `√A`: its square is `|I|(1 - |I|/A) ≤ |I| ≤ A`. -/
theorem norm_centered_indicator_le_sqrt {A : ℝ} (hA : 0 < A) {I : Set ℝ}
    (hI : MeasurableSet I) (hfin : volume I ≠ ⊤) (hsub : I ⊆ Set.Ioc 0 A) :
    ‖indicatorConstLp 2 hI hfin (1 : ℝ)
        - (volume.real I / A) •
          indicatorConstLp (μ := (volume : Measure ℝ)) 2
            (measurableSet_Ioc (a := (0:ℝ)) (b := A)) measure_Ioc_lt_top.ne (1 : ℝ)‖
      ≤ Real.sqrt A := by
  set fI := indicatorConstLp 2 hI hfin (1 : ℝ) with hfI
  set fΩ := indicatorConstLp (μ := (volume : Measure ℝ)) 2
    (measurableSet_Ioc (a := (0:ℝ)) (b := A)) measure_Ioc_lt_top.ne (1 : ℝ) with hfΩ
  set ℓ := volume.real I with hℓ
  have hΩvol : volume.real (Set.Ioc (0:ℝ) A) = A := by
    rw [Measure.real, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal hA.le]
  have hℓnn : 0 ≤ ℓ := measureReal_nonneg
  have hℓA : ℓ ≤ A := by
    rw [hℓ, ← hΩvol]; exact measureReal_mono hsub measure_Ioc_lt_top.ne
  have hsq : ‖fI - (ℓ / A) • fΩ‖ ^ 2 = ℓ - ℓ ^ 2 / A := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      hfI, hfΩ, L2.real_inner_indicatorConstLp_one_indicatorConstLp_one,
      Set.inter_self, Set.inter_eq_left.mpr hsub, Set.inter_eq_right.mpr hsub, hΩvol]
    field_simp
    ring
  have hbound : ‖fI - (ℓ / A) • fΩ‖ ^ 2 ≤ A := by
    rw [hsq]
    have hdiv : 0 ≤ ℓ ^ 2 / A := by positivity
    linarith [hℓA, hdiv]
  rw [← Real.sqrt_sq (norm_nonneg (fI - (ℓ / A) • fΩ))]
  exact Real.sqrt_le_sqrt hbound

/-- Clipped aperture interval for an atom at log-location `b`. -/
def apertureSetAt (A m k b : ℝ) : Set ℝ := Ioc (max 0 (m - b)) (min A (k - b))

theorem apertureSetAt_subset (A m k b : ℝ) : apertureSetAt A m k b ⊆ Set.Ioc 0 A := by
  intro u hu
  rw [apertureSetAt, mem_Ioc] at hu
  rw [mem_Ioc]
  exact ⟨lt_of_le_of_lt (le_max_left _ _) hu.1, hu.2.trans (min_le_left _ _)⟩

theorem measurableSet_apertureSetAt (A m k b : ℝ) : MeasurableSet (apertureSetAt A m k b) := by
  rw [apertureSetAt]; exact measurableSet_Ioc

theorem apertureSetAt_measure_ne_top (A m k b : ℝ) : volume (apertureSetAt A m k b) ≠ ⊤ := by
  rw [apertureSetAt]; exact measure_Ioc_lt_top.ne

/-- Centered aperture carrier for an atom at log-location `b`: the clipped indicator projected off the
constant aperture direction. -/
noncomputable def centeredApertureCarrierAt (A m k b : ℝ) : Lp ℝ 2 (volume : Measure ℝ) :=
  indicatorConstLp 2 (measurableSet_apertureSetAt A m k b)
      (apertureSetAt_measure_ne_top A m k b) (1 : ℝ)
    - (volume.real (apertureSetAt A m k b) / A) •
      indicatorConstLp (μ := (volume : Measure ℝ)) 2
        (measurableSet_Ioc (a := (0:ℝ)) (b := A)) measure_Ioc_lt_top.ne (1 : ℝ)

theorem norm_centeredApertureCarrierAt_le {A : ℝ} (hA : 0 < A) (m k b : ℝ) :
    ‖centeredApertureCarrierAt A m k b‖ ≤ Real.sqrt A := by
  rw [centeredApertureCarrierAt]
  exact norm_centered_indicator_le_sqrt hA (measurableSet_apertureSetAt A m k b)
    (apertureSetAt_measure_ne_top A m k b) (apertureSetAt_subset A m k b)

/-- **`(PFK16)` general aggregate norm bound.**  Any nonnegative-weighted sum of centered aperture
carriers has norm at most `√A` times the total weight. -/
theorem norm_aggregate_centeredApertureCarrierAt_le {A : ℝ} (hA : 0 < A) (m k : ℝ)
    {ι : Type*} (S : Finset ι) (b : ι → ℝ) (w : ι → ℝ) (hw : ∀ i ∈ S, 0 ≤ w i) :
    ‖∑ i ∈ S, w i • centeredApertureCarrierAt A m k (b i)‖ ≤ Real.sqrt A * ∑ i ∈ S, w i := by
  calc ‖∑ i ∈ S, w i • centeredApertureCarrierAt A m k (b i)‖
      ≤ ∑ i ∈ S, ‖w i • centeredApertureCarrierAt A m k (b i)‖ := norm_sum_le _ _
    _ = ∑ i ∈ S, w i * ‖centeredApertureCarrierAt A m k (b i)‖ := by
        apply Finset.sum_congr rfl; intro i hi
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw i hi)]
    _ ≤ ∑ i ∈ S, w i * Real.sqrt A := by
        apply Finset.sum_le_sum; intro i hi
        exact mul_le_mul_of_nonneg_left (norm_centeredApertureCarrierAt_le hA m k (b i)) (hw i hi)
    _ = Real.sqrt A * ∑ i ∈ S, w i := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring

end GaloisForLFunctions.HTGeometry
