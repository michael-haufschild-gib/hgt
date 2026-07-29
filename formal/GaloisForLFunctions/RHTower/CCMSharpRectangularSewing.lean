import GaloisForLFunctions.RHTower.CCMSharpPrimeWindow
import Mathlib.MeasureTheory.Function.Floor

/-!
# Sharp-to-rectangular sewing

The completed adjacent-block coefficient is not an independent observable.  It is exactly the
one-aperture integral of the sharp prime--polar coefficient after restoring the explicit decaying
endpoint correction.  Thus the rectangular value is the additive sewing of local sharp values.
-/

open MeasureTheory Set

noncomputable section

namespace RHTower

theorem measurable_criticalMellinPrimeMass :
    Measurable criticalMellinPrimeMass := by
  let F : ℕ → ℝ := fun m =>
    ∑ k ∈ Finset.Icc 0 m,
      ((k : ℝ) ^ (-1 / 2 : ℝ)) * ArithmeticFunction.vonMangoldt k
  have hF : Measurable F := measurable_of_countable F
  have hfloor : Measurable (fun h : ℝ => ⌊Real.exp h⌋₊) :=
    Real.measurable_exp.nat_floor
  change Measurable (fun h : ℝ => F ⌊Real.exp h⌋₊)
  exact hF.comp hfloor

theorem criticalMellinPrimeMass_nonneg (h : ℝ) :
    0 ≤ criticalMellinPrimeMass h := by
  rw [criticalMellinPrimeMass]
  exact Finset.sum_nonneg fun k _ =>
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg k) _)
      ArithmeticFunction.vonMangoldt_nonneg

theorem criticalMellinPrimeMass_mono :
    Monotone criticalMellinPrimeMass := by
  intro a b hab
  rw [criticalMellinPrimeMass, criticalMellinPrimeMass]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    simp only [Finset.mem_Icc] at hk ⊢
    exact ⟨hk.1, hk.2.trans (Nat.floor_mono (Real.exp_le_exp.mpr hab))⟩
  · intro k _ _
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg k) _)
      ArithmeticFunction.vonMangoldt_nonneg

theorem integrableOn_criticalMellinPrimeMass_Ioc
    {a b : ℝ} :
    IntegrableOn criticalMellinPrimeMass (Ioc a b) := by
  have hg : Integrable (fun _ : ℝ => criticalMellinPrimeMass b)
      (volume.restrict (Ioc a b)) :=
    integrableOn_const (ne_of_lt measure_Ioc_lt_top)
  refine hg.mono' ?_ ?_
  · exact measurable_criticalMellinPrimeMass.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with h hh
    rw [Real.norm_eq_abs, abs_of_nonneg (criticalMellinPrimeMass_nonneg h)]
    exact criticalMellinPrimeMass_mono hh.2

private theorem integrableOn_criticalMellinCompletedError_Ioc
    {a b : ℝ} :
    IntegrableOn criticalMellinCompletedError (Ioc a b) := by
  rw [show criticalMellinCompletedError = fun h : ℝ =>
      4 * Real.sinh (h / 2) - criticalMellinPrimeMass h by
    funext h
    exact criticalMellinCompletedError_eq_polar_sub_primeMass h]
  apply IntegrableOn.sub
  · exact (continuous_const.mul
      (Real.continuous_sinh.comp
        (continuous_id.div_const 2))).continuousOn.integrableOn_Icc.mono_set
          (fun h hh => ⟨hh.1.le, hh.2⟩)
  · exact integrableOn_criticalMellinPrimeMass_Ioc

private theorem integrableOn_comp_sub_Ioc
    (f : ℝ → ℝ) (a b L : ℝ)
    (hf : IntegrableOn f (Ioc (a - L) (b - L))) :
    IntegrableOn (fun h => f (h - L)) (Ioc a b) := by
  have hmp := measurePreserving_add_right (volume : Measure ℝ) (-L)
  have hi := (hmp.integrableOn_comp_preimage
    (measurableEmbedding_addRight (-L))
    (f := f) (s := Ioc (a - L) (b - L))).mpr hf
  have hpre : (fun h : ℝ => h + -L) ⁻¹' Ioc (a - L) (b - L) = Ioc a b := by
    ext h
    simp only [mem_preimage, mem_Ioc]
    constructor <;> intro hh <;> constructor <;> linarith [hh.1, hh.2]
  rw [hpre] at hi
  rw [show (fun h => f (h - L)) = f ∘ fun h => h + -L by
    funext h
    rw [Function.comp_apply, sub_eq_add_neg]]
  exact hi

private theorem setIntegral_Ioc_comp_sub_eq
    (f : ℝ → ℝ) (a b L : ℝ) :
    (∫ h in Ioc a b, f (h - L)) =
      ∫ u in Ioc (a - L) (b - L), f u := by
  have hmp := measurePreserving_add_right (volume : Measure ℝ) (-L)
  have h := hmp.setIntegral_preimage_emb
    (measurableEmbedding_addRight (-L)) f (Ioc (a - L) (b - L))
  have hpre : (fun h : ℝ => h + -L) ⁻¹' Ioc (a - L) (b - L) = Ioc a b := by
    ext h
    simp only [mem_preimage, mem_Ioc]
    constructor <;> intro hh <;> constructor <;> linarith [hh.1, hh.2]
  rw [hpre] at h
  simpa only [sub_eq_add_neg] using h

/-- **Sharp-to-rectangular sewing law.**  The completed adjacent-block value is exactly one half
of the aperture integral of the sharp prime--polar values with their explicit endpoint correction
restored.  The identity is unconditional and valid at every real width and position. -/
theorem sharpPrimePolarIntegral_eq_twice_adjacentBlock
    (L x : ℝ) :
    (∫ h in Ioc (x - L) x,
        (sharpPrimePolarCoefficient L h +
          sharpPrimeWindowEndpointCorrection L h)) =
      2 * criticalMellinAdjacentBlock L x := by
  have hpoint : (fun h : ℝ =>
      sharpPrimePolarCoefficient L h +
        sharpPrimeWindowEndpointCorrection L h) =
      fun h : ℝ => 2 *
        (criticalMellinCompletedError h -
          criticalMellinCompletedError (h - L)) := by
    funext h
    rw [sharpPrimePolarCoefficient_eq_completedErrorIncrement]
    ring
  rw [hpoint]
  rw [MeasureTheory.integral_const_mul]
  rw [MeasureTheory.integral_sub
    integrableOn_criticalMellinCompletedError_Ioc
    (by
      apply integrableOn_comp_sub_Ioc
      exact integrableOn_criticalMellinCompletedError_Ioc)]
  rw [setIntegral_Ioc_comp_sub_eq]
  rw [criticalMellinAdjacentBlock]
  ring_nf

end RHTower
