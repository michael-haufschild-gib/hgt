import GaloisForLFunctions.HTGeometry.SzegoLowerBoundGeneral

/-!
# Reverse angular integrability bridge

Pulling an integrable function on normalized circle Haar measure back through the standard
angular parametrization gives interval integrability on one full period.  This is the converse
of the forward circle-integrability bridge needed by outer-function constructions.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

theorem intervalIntegrable_angularCircle_of_integrable_circleLebesgue
    (G : Circle → ℝ) (hGm : Measurable G)
    (hG : Integrable G circleLebesgue) :
    IntervalIntegrable (fun theta => G (AddCircle.toCircle
      (↑(theta / (2 * Real.pi)) : AddCircle (1 : ℝ))))
      volume 0 (2 * Real.pi) := by
  haveI : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩
  have hACm : Measurable (fun x : AddCircle (1 : ℝ) =>
      G (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero x)) :=
    hGm.comp (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).continuous.measurable
  have hAC : Integrable (fun x : AddCircle (1 : ℝ) =>
      G (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero x))
      AddCircle.haarAddCircle := by
    rw [circleLebesgue,
      integrable_map_measure hGm.aestronglyMeasurable
        (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).continuous.aemeasurable] at hG
    exact hG
  have hvh : (AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ))) = volume := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simp
  rw [hvh] at hAC
  have hstep : Integrable
      (fun a : ℝ => G ((AddCircle.toCircle (↑a : AddCircle (1 : ℝ)) : Circle)))
      (volume.restrict (Set.Ioc 0 1)) := by
    rw [← (AddCircle.measurePreserving_mk (1 : ℝ) 0).map_eq,
      integrable_map_measure hACm.aestronglyMeasurable
        AddCircle.measurable_mk'.aemeasurable] at hAC
    have h1 : (0 : ℝ) + 1 = 1 := by norm_num
    rw [h1] at hAC
    simpa only [Function.comp_apply, AddCircle.homeomorphCircle_apply] using! hAC
  have hstepII : IntervalIntegrable
      (fun a : ℝ => G ((AddCircle.toCircle (↑a : AddCircle (1 : ℝ)) : Circle)))
      volume 0 1 := by
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
  have h := hstepII.comp_mul_left (c := (2 * Real.pi)⁻¹)
    enorm_ne_top enorm_ne_top
  convert h using 1
  · funext theta
    congr 2
    field_simp [Real.pi_ne_zero]
  · norm_num
  · field_simp [Real.pi_ne_zero]


end GaloisForLFunctions.HTGeometry
