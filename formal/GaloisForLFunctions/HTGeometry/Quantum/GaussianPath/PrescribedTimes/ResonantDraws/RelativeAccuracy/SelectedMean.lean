import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.FirstPassageSelection.RayBounds
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.PhysicalRays

/-! # Finite probability errors after selecting an expansion-closed event -/
open Set MeasureTheory ProbabilityTheory
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.RelativeAccuracy
noncomputable section
open FirstPassageSelection

/-- Uniform error on the good rays also controls every measurable
expansion-closed selection, with the Gaussian dilation cost paid once. -/
theorem selected_error {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (X : Ω → (ι → ℝ))
    (hX : MeasurePreserving X P (Measure.pi fun _ : ι => gaussianReal 0 1))
    (B E : Set (ι → ℝ)) (hm : MeasurableSet B) (he : MeasurableSet E) (hB : expansionClosed B)
    {b p r β : ℝ} (hb : 1<b) (hp : p ∈ Icc (0:ℝ) 1) (hr : 0≤r) (hβ : 0≤β)
    (A : Set Ω) (hA : P A ≤ ENNReal.ofReal β)
    (h : ∀ᵐ ω ∂P, ω ∉ A → |rayMass b E (X ω)/(b-1)-p|≤r) :
    let μ := Measure.pi fun _ : ι => gaussianReal 0 1
    |μ.real (B ∩ E)-μ.real B*p| ≤ r+β+2*(b^Fintype.card ι-1) := by
  classical
  intro μ
  let L := b-1
  let R (x : ι → ℝ) := rayMass b E x/L
  let g (x : ι → ℝ) := |R x-p|
  have hL : 0<L := sub_pos.mpr hb
  have hR : Measurable R := (measurable_rayMass b he).div_const _
  have hg : Measurable g := (hR.sub_const p).abs
  have hbound (x : ι → ℝ) : R x ∈ Icc (0:ℝ) 1 := by
    refine ⟨div_nonneg measureReal_nonneg hL.le,(div_le_one hL).mpr ?_⟩
    exact (measureReal_mono (subset_univ _)).trans_eq
      ((measureReal_restrict_apply_univ _).trans (Real.volume_real_Icc_of_le hb.le))
  have hgb (x) : g x≤1 := abs_le.mpr ⟨by linarith only [(hbound x).1,hp.2],
    by linarith only [(hbound x).2,hp.1]⟩
  have hgi : Integrable g μ := Integrable.of_bound hg.aestronglyMeasurable 1
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs,abs_of_nonneg (abs_nonneg _)] using hgb x)
  have hri : Integrable R μ := Integrable.of_bound hR.aestronglyMeasurable 1
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs,abs_of_nonneg (hbound x).1] using (hbound x).2)
  have hav := mean_of_exception P (fun ω => g (X ω)) (hg.comp hX.measurable)
    (fun _ => abs_nonneg _) (fun ω => hgb (X ω)) A hr hA hβ h
  have hpush : (∫ x, g x ∂μ)=(∫ ω, g (X ω) ∂P) := by
    change (∫ x, g x ∂(Measure.pi fun _ : ι => gaussianReal 0 1))=_
    rw [←hX.map_eq,integral_map hX.measurable.aemeasurable hg.aestronglyMeasurable]
  have hgmean := hpush.le.trans hav
  let d := fun x : ι → ℝ => B.indicator R x-B.indicator (fun _ => p) x
  have hdi : Integrable d μ := (hri.indicator hm).sub ((integrable_const p).indicator hm)
  have hpoint (x) : -g x≤d x ∧ d x≤g x := by
    by_cases hx : x∈B
    · simp only [d,g,indicator_of_mem hx]
      exact abs_le.mp (le_rfl : |R x-p|≤|R x-p|)
    · simp only [d,indicator_of_notMem hx,sub_self,g]
      exact ⟨neg_nonpos.mpr (abs_nonneg _),abs_nonneg _⟩
  have hl := integral_mono hgi.neg hdi (fun x => (hpoint x).1)
  have hu := integral_mono hdi hgi (fun x => (hpoint x).2)
  have hd : (∫ x, d x ∂μ)=(∫ x, B.indicator (rayMass b E) x ∂μ)/L-μ.real B*p := by
    rw [show (∫ x, d x ∂μ)=(∫ x, B.indicator R x ∂μ)-(∫ x, B.indicator (fun _ => p) x ∂μ) from
      integral_sub (hri.indicator hm) ((integrable_const p).indicator hm),integral_indicator hm,
      integral_indicator hm,integral_indicator hm,setIntegral_const,smul_eq_mul]
    unfold R
    rw [integral_div]
  simp only [Pi.neg_apply,integral_neg,hd] at hl hu
  have hs := abs_le.mp (selected_mean_error B E hm he hB hb)
  exact abs_le.mpr ⟨by linarith only [hl,hgmean,hs.2],by linarith only [hu,hgmean,hs.1]⟩

#print axioms selected_error
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.RelativeAccuracy
