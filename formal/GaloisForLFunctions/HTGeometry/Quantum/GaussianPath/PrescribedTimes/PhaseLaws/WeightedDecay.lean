import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.PhaseLaws.FrequencyDistribution
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Fourier decay after a phase offset depending on the same disorder -/

open Filter MeasureTheory Topology
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.PhaseLaws
noncomputable section
variable {X : Type*} [MeasurableSpace X]

def oscillation (a t : ℝ) := Complex.exp (-((t*a:ℝ):ℂ)*Complex.I)

theorem norm_oscillation (a t : ℝ) : ‖oscillation a t‖=1 := by
  simp [oscillation,Complex.norm_exp]

private theorem positive_weight_decay (μ : Measure X) [IsFiniteMeasure μ] (A : X→ℝ)
    (hA : Measurable A) (hac : μ.map A ≪ volume) (w : X→ℝ) (hw : Measurable w)
    (hb : ∀ x, 0≤w x ∧ w x≤2) :
    Tendsto (fun t : ℝ => ∫ x, (w x:ℂ)*oscillation (A x) t ∂μ) (cocompact ℝ) (𝓝 0) := by
  let d (x : X) := ENNReal.ofReal (w x)
  let ν := μ.withDensity d
  have hfinite : ∫⁻ x, d x ∂μ ≠ ⊤ := by
    apply ne_top_of_le_ne_top (b:=∫⁻ _x : X, (2:ℝ≥0∞) ∂μ)
      (by rw [lintegral_const]; exact ENNReal.mul_ne_top (by norm_num) (measure_ne_top μ Set.univ))
    exact lintegral_mono fun x => (ENNReal.ofReal_le_ofReal (hb x).2).trans_eq (by norm_num)
  letI : IsFiniteMeasure ν := isFiniteMeasure_withDensity hfinite
  have hν := ((withDensity_absolutelyContinuous μ d).map hA).trans hac
  have h := spectralDensityFourierAmplitude_tendsto_zero_cocompact (spectralMeasureDensity (ν.map A))
  apply h.congr
  intro t
  rw [spectralDensityFourierAmplitude_spectralMeasureDensity (ν.map A) hν,integral_map hA.aemeasurable (by fun_prop)]
  change (∫ x, oscillation (A x) t ∂μ.withDensity d)=_
  rw [integral_withDensity_eq_integral_toReal_smul hw.ennreal_ofReal
    (.of_forall fun _ => ENNReal.ofReal_lt_top)]
  exact integral_congr_ae (.of_forall fun x => by
    simp only [ENNReal.toReal_ofReal (hb x).1,Complex.real_smul])

/-- An arbitrary unit phase learned from the draw does not prevent the
oscillation of a real action with absolutely continuous law from averaging
to zero. No independence between the action and the offset is needed. -/
theorem phase_weight_decay (μ : Measure X) [IsFiniteMeasure μ] (A : X→ℝ) (hA : Measurable A)
    (hac : μ.map A ≪ volume) (g : X→ℂ) (hg : Measurable g) (hg₁ : ∀ x, ‖g x‖=1) :
    Tendsto (fun t : ℝ => ∫ x, g x*oscillation (A x) t ∂μ) (cocompact ℝ) (𝓝 0) := by
  let R (x : X) := (g x).re+1
  let I (x : X) := (g x).im+1
  have hR : Measurable R := (Complex.continuous_re.measurable.comp hg).add_const 1
  have hI : Measurable I := (Complex.continuous_im.measurable.comp hg).add_const 1
  have br (x : X) : 0≤R x ∧ R x≤2 := by
    have hh := abs_le.mp ((Complex.abs_re_le_norm (g x)).trans_eq (hg₁ x))
    dsimp only [R]; constructor <;> linarith only [hh.1,hh.2]
  have bi (x : X) : 0≤I x ∧ I x≤2 := by
    have hh := abs_le.mp ((Complex.abs_im_le_norm (g x)).trans_eq (hg₁ x))
    dsimp only [I]; constructor <;> linarith only [hh.1,hh.2]
  have hr := positive_weight_decay μ A hA hac R hR br
  have hi := positive_weight_decay μ A hA hac I hI bi
  have h1 := positive_weight_decay μ A hA hac (fun _ => 1) measurable_const (fun _ => by norm_num)
  have h := (hr.add (hi.const_mul Complex.I)).sub (h1.const_mul (1+Complex.I))
  simp only [mul_zero,add_zero,sub_zero] at h
  apply h.congr
  intro t
  let K (x : X) := oscillation (A x) t
  have hm : Measurable K := by unfold K oscillation; fun_prop
  have hk : Integrable K μ := (integrable_const (1:ℝ)).mono' hm.aestronglyMeasurable
    (.of_forall fun x => (norm_oscillation (A x) t).le)
  have wint (w : X→ℝ) (hw : Measurable w) (hb : ∀ x, 0≤w x ∧ w x≤2) :
      Integrable (fun x => (w x:ℂ)*K x) μ :=
    (integrable_const (2:ℝ)).mono' ((Complex.continuous_ofReal.measurable.comp hw).mul hm).aestronglyMeasurable
      (.of_forall fun x => by rw [norm_mul,norm_oscillation,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hb x).1]; exact (hb x).2)
  simp only [Complex.ofReal_one,one_mul]
  have hsum : Integrable (fun x => (R x:ℂ)*K x+Complex.I*((I x:ℂ)*K x)) μ :=
    (wint R hR br).add ((wint I hI bi).const_mul Complex.I)
  rw [←integral_const_mul,←integral_const_mul,←integral_add (wint R hR br) ((wint I hI bi).const_mul Complex.I)]
  rw [←integral_sub hsum (hk.const_mul (1+Complex.I))]
  apply integral_congr_ae
  filter_upwards with x
  change (R x:ℂ)*K x+Complex.I*((I x:ℂ)*K x)-(1+Complex.I)*K x=g x*K x
  conv_rhs => rw [←Complex.re_add_im (g x)]
  dsimp only [R,I]
  push_cast
  ring

#print axioms phase_weight_decay
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.PhaseLaws
