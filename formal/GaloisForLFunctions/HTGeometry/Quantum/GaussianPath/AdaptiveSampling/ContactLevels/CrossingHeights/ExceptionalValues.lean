import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.Aliasing
import GaloisForLFunctions.HTGeometry.ConvolutionAtomBounds

/-! # Countably many deterministic heights can select a resonant wait -/

open Set MeasureTheory
namespace GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactLevels.CrossingHeights
noncomputable section

/-- For each endpoint, nonzero character and integer winding there is
only one possible resonant starting date. The atoms of the observable
at these countably many candidate dates exhaust the exceptional heights. -/
theorem exceptional_clock_heights {X J I : Type*} [MeasurableSpace X] [Countable J] [Fintype I]
    (μ : Measure X) [IsFiniteMeasure μ] (w : X → I → ℝ) (hw : Measurable w)
    (v : J → X → ℝ) (hv : ∀ j, Measurable (v j))
    (f : J → X × ℝ → ℝ) (hf : ∀ j, Measurable (f j)) :
    ∃ B : Set ℝ, B.Countable ∧ ∀ r ∉ B, ∀ᵐ x ∂μ,
      RationallyIndependentFrequency (w x) → ∀ j u,
        f j (x,u)=r → FreeAtStep (w x) (v j x-u) := by
  classical
  let V := J × (I → ℤ) × ℤ
  let d (m : I → ℤ) (x : X) := finiteTorusCharacterDetuning m (w x)
  have hd (m) : Measurable (d m) := by
    dsimp only [d,finiteTorusCharacterDetuning]
    fun_prop
  let F (b : V) (x : X) := f b.1 (x,v b.1 x-(b.2.2:ℝ)*(2*Real.pi)/d b.2.1 x)
  have hF (b) : Measurable (F b) := (hf b.1).comp
    (measurable_id.prodMk ((hv b.1).sub (measurable_const.div (hd b.2.1))))
  let B (b : V) := {r : ℝ | (μ.map (F b)) {r}≠0}
  refine ⟨⋃ b, B b,countable_iUnion fun b => countable_atoms _,?_⟩
  intro r hr
  have h (b : V) : ∀ᵐ x ∂μ, F b x≠r := by
    have hz : (μ.map (F b)) {r}=0 := by
      by_contra hn
      exact hr (mem_iUnion.mpr ⟨b,hn⟩)
    rw [Measure.map_apply (hF b) (measurableSet_singleton r)] at hz
    exact measure_eq_zero_iff_ae_notMem.mp hz
  filter_upwards [ae_all_iff.mpr h] with x hx hi j u hu m k hk
  by_contra hm
  have hn : d m x≠0 := fun h => hm (hi m h)
  have hstep := (eq_div_iff hn).mpr hk
  have he : v j x-(k:ℝ)*(2*Real.pi)/d m x=u := by linarith only [hstep]
  apply hx (j,m,k)
  change f j (x,v j x-(k:ℝ)*(2*Real.pi)/d m x)=r
  rwa [he]

#print axioms exceptional_clock_heights
end
end GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactLevels.CrossingHeights
