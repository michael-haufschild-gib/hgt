import GaloisForLFunctions.HTGeometry.KantorovichRubinsteinDuality
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-! An essentially bounded source cannot be coupled at finite infinity cost
to a target whose identity is not essentially bounded. -/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

theorem eLpNorm_sub_top_eq_top_of_memLp_not_memLp
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {f g : α → E}
    (hf : MemLp f ⊤ μ) (hgm : AEStronglyMeasurable g μ) (hg : ¬ MemLp g ⊤ μ) :
    eLpNorm (fun x => f x - g x) ⊤ μ = ⊤ := by
  by_contra h
  have hd : MemLp (fun x => f x - g x) ⊤ μ :=
    ⟨hf.aestronglyMeasurable.sub hgm, lt_top_iff_ne_top.mpr h⟩
  apply hg
  convert hf.sub hd using 1
  ext x
  simp

theorem eLpNorm_coupling_top_eq_top_of_memLp_not_memLp
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] {μ ν : Measure E}
    (hμ : MemLp (fun x : E => x) ⊤ μ) (hν : ¬ MemLp (fun x : E => x) ⊤ ν)
    (π : {π : Measure (E × E) // IsCoupling μ ν π}) :
    eLpNorm (fun z : E × E => z.1 - z.2) ⊤ π.val = ⊤ := by
  have hfst : MemLp (fun z : E × E => z.1) ⊤ π.val := by
    have hmap := memLp_map_measure_iff (μ := π.val) (p := ⊤) (g := fun x : E => x)
      measurable_id.aestronglyMeasurable measurable_fst.aemeasurable
    rw [π.property.1] at hmap
    exact hmap.mp hμ
  have hsnd : ¬ MemLp (fun z : E × E => z.2) ⊤ π.val := by
    intro h
    apply hν
    have hmap := memLp_map_measure_iff (μ := π.val) (p := ⊤) (g := fun x : E => x)
      measurable_id.aestronglyMeasurable measurable_snd.aemeasurable
    rw [π.property.2] at hmap
    exact hmap.mpr h
  exact eLpNorm_sub_top_eq_top_of_memLp_not_memLp hfst
    measurable_snd.aestronglyMeasurable hsnd

end GaloisForLFunctions.HTGeometry
