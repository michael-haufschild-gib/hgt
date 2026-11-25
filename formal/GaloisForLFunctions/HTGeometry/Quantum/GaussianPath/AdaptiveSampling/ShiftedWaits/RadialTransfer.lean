import GaloisForLFunctions.HTGeometry.Quantum.MetricIntegerClock
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.GaussianDilation
import GaloisForLFunctions.HTGeometry.ShellSimpleSpectrum

/-! # A prescribed shift of a scale-covariant date preserves Gaussian null sets -/

open Set MeasureTheory Filter
namespace GaloisForLFunctions.HTGeometry.AdaptiveSampling.ShiftedWaits
noncomputable section

/-- A direction-dependent radial translation followed by a fixed nonzero
dilation preserves null preimages, including where the signed radius
becomes negative. No angular continuity of the translation is required. -/
theorem radial_shift_volume {m : ℕ} (o : (Fin m → ℝ) → ℝ) (ho : Measurable o)
    (hc : ∀ a > (0:ℝ), ∀ x, a*o (a • x)=o x) {h : ℝ} (hh : h≠0) :
    Measure.QuasiMeasurePreserving (fun x => (o x+h) • x) volume volume := by
  let X := Fin m → ℝ
  let F (x : X) := (o x+h) • x
  have hF : Measurable F := (ho.add measurable_const).smul measurable_id
  refine ⟨hF,Measure.AbsolutelyContinuous.mk fun B hB hnull => ?_⟩
  rw [Measure.map_apply hF hB,measure_eq_zero_iff_ae_notMem]
  have hcol : ∀ᵐ a ∂(volume : Measure ℝ), ∀ᵐ x ∂(volume : Measure X), a • x ∉ B := by
    filter_upwards [Measure.ae_ne volume (0:ℝ)] with a ha
    exact (Measure.quasiMeasurePreserving_smul (volume : Measure X) ha).ae
      (measure_eq_zero_iff_ae_notMem.mp hnull)
  have hm : MeasurableSet {p : X × ℝ | p.2 • p.1 ∉ B} :=
    hB.compl.preimage (measurable_snd.smul measurable_fst)
  have hrow := (Measure.ae_ae_comm (μ:=volume) (ν:=volume) hm).mpr hcol
  let G := F ⁻¹' Bᶜ
  have hG : MeasurableSet G := hB.compl.preimage hF
  let Q (x : X) (a : ℝ) := 0<a → a • x ∈ G
  have hmQ : MeasurableSet {p : X × ℝ | Q p.1 p.2} :=
    ((measurableSet_lt (show Measurable (fun _ : X × ℝ => (0:ℝ)) from measurable_const)
      measurable_snd).compl.union (hG.preimage (measurable_snd.smul measurable_fst))).congr
      (by ext; simp [Q,imp_iff_not_or])
  have hr : ∀ᵐ x ∂(volume : Measure X), ∀ᵐ a ∂(volume : Measure ℝ), Q x a := by
    filter_upwards [hrow] with x hx
    have haff : Measure.QuasiMeasurePreserving (fun a : ℝ => o x+h*a) volume volume :=
      (measurePreserving_add_left volume (o x)).quasiMeasurePreserving.comp
        (Measure.quasiMeasurePreserving_smul (volume : Measure ℝ) hh)
    filter_upwards [haff.ae hx] with a ha
    intro hp
    change (o (a • x)+h) • (a • x) ∉ B
    rwa [smul_smul,add_mul,mul_comm (o _) a,hc a hp x]
  have ht := (Measure.ae_ae_comm (μ:=volume) (ν:=volume) hmQ).mp hr
  obtain ⟨a,ha,hgood⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (by norm_num [Real.volume_Ioc] : volume (Ioc (0:ℝ) 1)≠0) (ae_restrict_of_ae ht)
  have ht' := (Measure.quasiMeasurePreserving_smul (volume : Measure X) (inv_ne_zero ha.1.ne')).ae hgood
  filter_upwards [ht'] with x hx
  have hx' : x ∈ G := by simpa only [smul_smul,mul_inv_cancel₀ ha.1.ne',one_smul] using hx ha.1
  exact hx'

/-- The shifted-date sample of a finite vector of independent standard
Gaussian couplings has a law absolutely continuous with respect to their
original Gaussian law. -/
theorem radial_shift_gaussian {m : ℕ} (o : (Fin m → ℝ) → ℝ) (ho : Measurable o)
    (hc : ∀ a > (0:ℝ), ∀ x, a*o (a • x)=o x) {h : ℝ} (hh : h≠0) :
    Measure.QuasiMeasurePreserving (fun x => (o x+h) • x)
      (centredProductGaussian (Fin m) 1) (centredProductGaussian (Fin m) 1) := by
  let μ := centredProductGaussian (Fin m) 1
  have hv : volume ≪ μ := volume_absolutelyContinuous_centredProductGaussian _ one_ne_zero
  have hg : μ ≪ volume := by
    simpa [μ,centredProductGaussian] using productGaussian_absolutelyContinuous m one_ne_zero (fun _ => 0)
  have hf := radial_shift_volume o ho hc hh
  refine ⟨hf.measurable,Measure.AbsolutelyContinuous.mk fun B hB hnull => ?_⟩
  rw [Measure.map_apply hf.measurable hB]
  apply hg
  exact measure_eq_zero_iff_ae_notMem.mpr (hf.ae (measure_eq_zero_iff_ae_notMem.mp (hv hnull)))

#print axioms radial_shift_gaussian
end
end GaloisForLFunctions.HTGeometry.AdaptiveSampling.ShiftedWaits
