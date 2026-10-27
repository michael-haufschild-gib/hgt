import GaloisForLFunctions.RHTower.PrimeCirclePeriodization
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Lattice Fourier vanishing forces absolute continuity

A real measure whose image on an additive circle is absolutely continuous is
itself absolutely continuous: pull null sets back through a measurable section
on each fundamental interval, then use a countable cover. Consequently a finite
measure with characteristic function zero at every nonzero lattice frequency
is Lebesgue absolutely continuous, by Haar uniqueness of its periodization.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry


/-- Absolute continuity of a circle image lifts through the countable covering of ℝ. -/
theorem absolutelyContinuous_of_addCircle_map {T : ℝ} [hT : Fact (0 < T)] {μ : Measure ℝ}
    (hμ : μ.map (fun x : ℝ => (x : AddCircle T)) ≪ volume) : μ ≪ volume := by
  apply Measure.AbsolutelyContinuous.mk
  intro S hS hS0
  -- Each fundamental interval embeds in the circle through its measurable section.
  have hlocal (a : ℝ) : μ (S ∩ Ioc a (a + T)) = 0 := by
    let e := AddCircle.measurableEquivIoc T a
    let s : AddCircle T → ℝ := fun z => (e z : ℝ)
    have hs : Measurable s := measurable_subtype_coe.comp e.measurable
    have hmap : (volume : Measure (AddCircle T)).map s = volume.restrict (Ioc a (a + T)) := by
      calc (volume : Measure (AddCircle T)).map s
          = ((volume : Measure (AddCircle T)).map e).map Subtype.val :=
            (Measure.map_map measurable_subtype_coe e.measurable).symm
        _ = (Measure.comap Subtype.val (volume : Measure ℝ)).map Subtype.val := by
          rw [show (volume : Measure (AddCircle T)).map e =
            Measure.comap Subtype.val (volume : Measure ℝ) from
            (AddCircle.measurePreserving_equivIoc (T := T) (a := a)).map_eq]
        _ = volume.restrict (Ioc a (a + T)) := map_comap_subtype_coe measurableSet_Ioc _
    have hnull : (μ.map (fun x : ℝ => (x : AddCircle T))).map s S = 0 := by
      apply (hμ.map hs)
      rw [hmap, Measure.restrict_apply hS]
      exact measure_mono_null Set.inter_subset_left hS0
    rw [Measure.map_apply hs hS,
      Measure.map_apply AddCircle.measurable_mk' (hs hS)] at hnull
    apply measure_mono_null _ hnull
    intro x hx
    change (e (x : AddCircle T) : ℝ) ∈ S
    have he : (e (x : AddCircle T) : ℝ) = x := by
      exact congrArg Subtype.val (AddCircle.equivIoc_coe_eq hx.2)
    simpa only [he] using hx.1
  have hn (n : ℤ) : μ (S ∩ Ioc (n • T) ((n + 1) • T)) = 0 := by
    simpa only [add_smul, one_smul] using hlocal (n • T)
  have hcover : S = ⋃ n : ℤ, S ∩ Ioc (n • T) ((n + 1) • T) := by
    rw [← inter_iUnion, iUnion_Ioc_zsmul hT.out, inter_univ]
  rw [hcover]
  exact measure_iUnion_null hn


/-- Vanishing at all positive multiples of a nonzero frequency forces an absolutely
continuous real measure. Hermitian symmetry supplies the negative multiples. -/
theorem absolutelyContinuous_of_lattice_charFun_zero
    (μ : Measure ℝ) [IsFiniteMeasure μ] {ℓ : ℝ} (hℓ : ℓ ≠ 0)
    (hzero : ∀ j : ℕ, 1 ≤ j → charFun μ ((j : ℝ) * ℓ) = 0) : μ ≪ volume := by
  have hhaar : (AddCircle.haarAddCircle : Measure (AddCircle (2 * Real.pi))) ≪ volume := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    exact Measure.absolutelyContinuous_smul (by positivity)
  have hphase : μ.map (RHTower.PrimeCirclePeriodization.phase ℓ) ≪ volume := by
    rw [RHTower.PrimeCirclePeriodization.map_phase_eq_of_blind μ ℓ hzero]
    exact hhaar.smul_left _
  have hf : Measurable (fun x : ℝ => x * ℓ) := measurable_id.mul_const ℓ
  have hg : Measurable (fun x : ℝ => x * ℓ⁻¹) := measurable_id.mul_const ℓ⁻¹
  have hm : Measurable (fun x : ℝ => (x : AddCircle (2 * Real.pi))) :=
    AddCircle.measurable_mk'
  -- First pass to the scaled real measure, then undo the nonzero scaling.
  have hscaled : μ.map (fun x : ℝ => x * ℓ) ≪ volume := by
    apply absolutelyContinuous_of_addCircle_map (T := 2 * Real.pi)
    rw [Measure.map_map hm hf]
    exact hphase
  have hpull := hscaled.map hg
  rw [Measure.map_map hg hf] at hpull
  have hcomp : (fun x : ℝ => x * ℓ⁻¹) ∘ (fun x : ℝ => x * ℓ) = id := by
    funext x
    simp only [Function.comp_apply, id_eq, mul_assoc, mul_inv_cancel₀ hℓ, mul_one]
  rw [hcomp, Measure.map_id, Real.map_volume_mul_right (inv_ne_zero hℓ)] at hpull
  exact hpull.trans Measure.smul_absolutelyContinuous

#print axioms absolutelyContinuous_of_lattice_charFun_zero

end GaloisForLFunctions.HTGeometry
