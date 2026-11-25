import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ForecastWindows.Conditioning.WindowMaximal
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ForecastWindows.Conditioning.WindowDensity

/-! # Averaged conditional window bounds for all resolutions at once -/

open Set MeasureTheory Metric
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ForecastWindows.Conditioning
noncomputable section
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- The conditional probability exceeds L times the radius at some
resolution. The background x and the forecast t can both vary. -/
def excessKernel (ν : Measure Y) (F : X×Y→ℝ) (L : ℝ) : Set (X×ℝ) :=
  {p | ∃ h> (0:ℝ), L*h<ν.real {y | |F (p.1,y)-p.2|<h}}

theorem measurableSet_excessKernel (ν : Measure Y) [IsProbabilityMeasure ν]
    {F : X×Y→ℝ} (hf : Measurable F) {L : ℝ} (hL : 0<L) :
    MeasurableSet (excessKernel ν F L) := by
  let B (q : ℚ) := {p : X×ℝ | 0<q ∧ L*(q:ℝ)<ν.real {y | |F (p.1,y)-p.2|<(q:ℝ)}}
  have hm (q : ℚ) : MeasurableSet (B q) := by
    by_cases hq : 0<q
    · simp only [B,hq,true_and]
      exact measurableSet_lt measurable_const (measurable_window_mass ν hf q)
    · simp [B,hq]
  have he : excessKernel ν F L=⋃ q : ℚ, B q := by
    ext p
    constructor
    · rintro ⟨h,hh,hbad⟩
      obtain ⟨q,hl,hu⟩ := exists_rat_btwn ((lt_div_iff₀ hL).mpr (by simpa only [mul_comm h L] using hbad))
      have hq : (0:ℚ)<q := by exact_mod_cast hh.trans hl
      have hlt := (lt_div_iff₀ hL).mp hu
      refine mem_iUnion.mpr ⟨q,hq,?_⟩
      apply (show L*(q:ℝ)<ν.real {y | |F (p.1,y)-p.2|<h} by rwa [mul_comm] at hlt).trans_le
      exact measureReal_mono (fun _ hy => hy.trans hl) (measure_ne_top _ _)
    · intro hp
      obtain ⟨q,hq,hh⟩ := mem_iUnion.mp hp
      exact ⟨q,by exact_mod_cast hq,hh⟩
  rw [he]
  exact MeasurableSet.iUnion hm

/-- Integrating over all forecast centers bounds the joint bad-set measure
by the one-dimensional maximal inequality, independently of the background. -/
theorem prod_excessKernel (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν]
    {F : X×Y→ℝ} (hf : Measurable F) {L : ℝ} (hL : 0<L) :
    μ.prod volume (excessKernel ν F L) ≤ ENNReal.ofReal (8/L) := by
  rw [Measure.prod_apply (measurableSet_excessKernel ν hf hL)]
  have hu (x : X) : volume (Prod.mk x ⁻¹' excessKernel ν F L)≤ENNReal.ofReal (8/L) := by
    let f (y : Y) := F (x,y)
    have hfx : Measurable f := hf.comp (measurable_const.prodMk measurable_id)
    let ρ := ν.map f
    letI : IsProbabilityMeasure ρ := Measure.isProbabilityMeasure_map hfx.aemeasurable
    have hs : Prod.mk x ⁻¹' excessKernel ν F L⊆excessCenters ρ L := by
      rintro t ⟨h,hh,hbad⟩
      refine ⟨h,hh,?_⟩
      rw [Measure.real,show ρ=ν.map f from rfl,Measure.map_apply hfx isOpen_ball.measurableSet]
      simpa only [Measure.real,Set.preimage,mem_ball,Real.dist_eq,f] using hbad
    exact (measure_mono hs).trans (volume_excessCenters ρ hL)
  exact (lintegral_mono hu).trans_eq (by simp)

#print axioms prod_excessKernel
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ForecastWindows.Conditioning
