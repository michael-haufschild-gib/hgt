import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real

/-! # Disjoint translated occupation windows -/
open MeasureTheory Set
namespace GaloisForLFunctions.HTGeometry

/-- If translates of a set of affordable times by shifts in [0,B] are
disjoint, each length-T interval contains at most (T+B)/card worth of them. -/
theorem occupation_mul_card_le_of_disjoint_shifts {ι : Type*} [Fintype ι]
    {A : Set ℝ} (hA : MeasurableSet A) (u : ι → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hu : ∀ i, u i ∈ Icc 0 B)
    (hsep : ∀ i j, i ≠ j → ∀ x : ℝ, x-u i ∈ A → x-u j ∉ A)
    (a T : ℝ) (hT : 0 ≤ T) :
    (Fintype.card ι:ℝ)*volume.real (A ∩ Icc a (a+T)) ≤ T+B := by
  let F := A ∩ Icc a (a+T)
  let G (i : ι) := (fun x : ℝ => x+(-u i)) ⁻¹' F
  have hm : MeasurableSet F := hA.inter measurableSet_Icc
  have hG (i : ι) : volume (G i) = volume F :=
    (measurePreserving_add_right volume (-u i)).measure_preimage hm.nullMeasurableSet
  have hGF (i : ι) : volume.real (G i) = volume.real F := congrArg ENNReal.toReal (hG i)
  have hfin : volume F ≠ ⊤ := measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne
  have hd : Pairwise (fun i j => Disjoint (G i) (G j)) := by
    intro i j hij
    exact Set.disjoint_left.mpr fun x hi hj => hsep i j hij x hi.1 hj.1
  have hsub : (⋃ i, G i) ⊆ Icc a (a+T+B) := by
    intro x hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    have hb : x+-u i ∈ Icc a (a+T) := hi.2
    exact ⟨by linarith only [hb.1,(hu i).1],by linarith only [hb.2,(hu i).2]⟩
  have hbound := measureReal_mono hsub measure_Icc_lt_top.ne
  rw [measureReal_iUnion_fintype hd (fun i => hm.preimage (measurable_id.add_const _))
    (fun i => (hG i).trans_ne hfin),Real.volume_real_Icc_of_le (by linarith only [hT,hB])] at hbound
  simpa only [hGF,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,add_sub_cancel_left,
    show a+T+B-a=T+B by ring] using hbound

end GaloisForLFunctions.HTGeometry
