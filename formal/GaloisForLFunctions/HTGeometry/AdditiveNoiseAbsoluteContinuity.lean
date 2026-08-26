import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Absolute continuity after independent additive noise

An absolutely continuous finite-dimensional complex packet remains absolutely continuous after
adding an arbitrary independent measurable noise packet.  The proof is a direct Fubini argument:
every tail section is a translate of the same Lebesgue-null target set.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Translating a finite-dimensional complex law preserves Lebesgue absolute continuity. -/
theorem map_add_const_absolutelyContinuous
    (N : ℕ) (μ : Measure (Fin N → ℂ))
    (hμ : μ ≪ (volume : Measure (Fin N → ℂ))) (c : Fin N → ℂ) :
    Measure.map (fun x => x + c) μ ≪ (volume : Measure (Fin N → ℂ)) := by
  have hmap : Measurable (fun x : Fin N → ℂ => x + c) := by fun_prop
  refine Measure.AbsolutelyContinuous.mk ?_
  intro s hs hnull
  rw [Measure.map_apply hmap hs]
  apply hμ
  have hpre : (fun x : Fin N → ℂ => x + c) ⁻¹' s =
      (fun x : Fin N → ℂ => c + x) ⁻¹' s := by
    ext x
    simp only [Set.mem_preimage]
    rw [add_comm]
  rw [hpre, measure_preimage_add]
  exact hnull

/-- Adding arbitrary independent measurable noise preserves Lebesgue absolute continuity of a
finite complex packet.  The product is ordered as `noise × packet` so Fubini exposes an absolutely
continuous packet section at each fixed noise value. -/
theorem map_snd_add_noise_prod_absolutelyContinuous
    {Y : Type*} [MeasurableSpace Y] (N : ℕ)
    (ν : Measure Y) (μ : Measure (Fin N → ℂ)) [SFinite μ]
    (hμ : μ ≪ (volume : Measure (Fin N → ℂ)))
    (g : Y → (Fin N → ℂ)) (hg : Measurable g) :
    Measure.map (fun p : Y × (Fin N → ℂ) => p.2 + g p.1) (ν.prod μ) ≪
      (volume : Measure (Fin N → ℂ)) := by
  let A : Y × (Fin N → ℂ) → (Fin N → ℂ) := fun p => p.2 + g p.1
  have hA : Measurable A := by
    exact measurable_snd.add (hg.comp measurable_fst)
  refine Measure.AbsolutelyContinuous.mk ?_
  intro s hs hnull
  rw [Measure.map_apply hA hs]
  have hpre : MeasurableSet (A ⁻¹' s) := hs.preimage hA
  apply (Measure.measure_prod_null hpre).2
  filter_upwards with y
  apply hμ
  have hsection : Prod.mk y ⁻¹' (A ⁻¹' s) =
      (fun x : Fin N → ℂ => g y + x) ⁻¹' s := by
    ext x
    simp only [Set.mem_preimage, A]
    rw [add_comm]
  rw [hsection, measure_preimage_add]
  exact hnull

end

end GaloisForLFunctions.HTGeometry
