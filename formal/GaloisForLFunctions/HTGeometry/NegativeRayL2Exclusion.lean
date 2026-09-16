import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! An eventual nonzero tail on an infinite negative ray is excluded from `L²`. -/

open Set Filter Topology MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A horizon coefficient whose norm is eventually at least one cannot belong to the native
negative-ray `L²` space. -/
theorem not_memLp_two_restrict_Iio_of_atBot_norm_ge_one
    {E : Type*} [NormedAddCommGroup E] (f : ℝ → E)
    (h : ∀ᶠ t in atBot, 1 ≤ ‖f t‖) :
    ¬ MemLp f 2 (volume.restrict (Iio 0)) := by
  intro hf
  have hwhole : MemLp ((Iio (0 : ℝ)).indicator f) 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_Iio).mpr hf
  have hint : Integrable (fun t : ℝ => ‖((Iio (0 : ℝ)).indicator f) t‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm hwhole.aestronglyMeasurable).mp hwhole
  obtain ⟨L, hL⟩ := (eventually_atBot.1 h)
  let M : ℝ := min L (-1)
  have hML : M ≤ L := by
    dsimp [M]
    exact min_le_left _ _
  have hM0 : M ≤ -1 := by
    dsimp [M]
    exact min_le_right _ _
  have hone : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Iio M) := by
    refine hint.integrableOn.mono' aestronglyMeasurable_const ?_
    refine (ae_restrict_iff' measurableSet_Iio).mpr
      (Filter.Eventually.of_forall fun t ht => ?_)
    have htL : t ≤ L := le_trans ht.le hML
    have ht0 : t < 0 := by
      have htM : t < M := ht
      linarith
    have hnorm : 1 ≤ ‖((Iio (0 : ℝ)).indicator f) t‖ := by
      rw [Set.indicator_of_mem (show t ∈ Iio (0 : ℝ) from ht0)]
      exact hL t htL
    rw [Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
    nlinarith [norm_nonneg (((Iio (0 : ℝ)).indicator f) t)]
  rw [integrableOn_const_iff, Real.volume_Iio] at hone
  simp at hone

end

end GaloisForLFunctions.HTGeometry
