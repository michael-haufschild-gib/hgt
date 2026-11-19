import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.HaarCellProfiles
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Gaussian information projection of position inside a logarithmic cell

Corollary 2.20 of Darijani–Soufian–Beyerer, arXiv:2611.16022, gives a
dimension-dependent minimum for uniform laws. Here the source is normalized
Lebesgue measure on a physical logarithmic interval. Its forward KL is
finite, its reverse KL infinite, and its optimum is independent of width.
-/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
open BiarithmeticGaugeGeometry

/-- Position uniformly sampled on an interval with left endpoint t and log width w. -/
def positionLaw (t w : ℝ) := ProbabilityTheory.cond volume (Ioc t (t+Real.exp w))

private theorem vol_position (t w : ℝ) :
    volume (Ioc t (t+Real.exp w)) = ENNReal.ofReal (Real.exp w) := by
  rw [Real.volume_Ioc,add_sub_cancel_left]

instance position_probability (t w : ℝ) : IsProbabilityMeasure (positionLaw t w) :=
  cond_isProbabilityMeasure_of_finite (by rw [vol_position]; exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne')
    (by rw [vol_position]; exact ENNReal.ofReal_ne_top)

/-- Gaussian with its variance parametrized logarithmically. -/
def positionGaussian (m l : ℝ) := gaussianReal m (Real.toNNReal (Real.exp l))

instance positionGaussian_probability (m l : ℝ) : IsProbabilityMeasure (positionGaussian m l) :=
  inferInstanceAs (IsProbabilityMeasure (gaussianReal m (Real.toNNReal (Real.exp l))))

private theorem variance_ne (l : ℝ) : Real.toNNReal (Real.exp l) ≠ 0 :=
  (Real.toNNReal_pos.mpr (Real.exp_pos _)).ne'

private theorem target_ac (m l : ℝ) : positionGaussian m l ≪ volume :=
  gaussianReal_absolutelyContinuous _ (variance_ne _)

private theorem volume_ac_target (m l : ℝ) : volume ≪ positionGaussian m l :=
  gaussianReal_absolutelyContinuous' _ (variance_ne _)

/-- Gaussian log density in location and log-variance coordinates. -/
theorem gaussian_log_pdf (m l x : ℝ) :
    Real.log (gaussianPDFReal m (Real.toNNReal (Real.exp l)) x) =
      -(Real.log (2*Real.pi)+l)/2 - (x-m)^2/(2*Real.exp l) := by
  have h : 0 < 2*Real.pi := by positivity
  have h' : 0 < 2*Real.pi*Real.exp l := mul_pos h (Real.exp_pos l)
  simp only [gaussianPDFReal,Real.coe_toNNReal _ (Real.exp_pos _).le,
    Real.log_mul (inv_ne_zero (Real.sqrt_pos.mpr h').ne') (Real.exp_ne_zero _),
    Real.log_inv,Real.log_sqrt h'.le,Real.log_mul h.ne' (Real.exp_ne_zero _),Real.log_exp]
  ring

private def cellLogRatio (w m l x : ℝ) :=
  -w + (Real.log (2*Real.pi)+l)/2 + (1/(2*Real.exp l))*(x-m)^2

private theorem position_log_density (t w : ℝ) {Q : Measure ℝ} [IsProbabilityMeasure Q]
    {g : ℝ → ℝ} (hg : ∀ x, 0 < g x) (hQ : Q ≪ volume) (hvolQ : volume ≪ Q)
    (hd : Q.rnDeriv volume =ᵐ[volume] fun x => ENNReal.ofReal (g x)) :
    llr (positionLaw t w) Q =ᵐ[positionLaw t w] fun x => -w-Real.log (g x) := by
  let S := Ioc t (t+Real.exp w)
  let P := positionLaw t w
  have hP : P ≪ volume := cond_absolutelyContinuous
  have hPQ := hP.trans hvolQ
  have hvol : volume S = ENNReal.ofReal (Real.exp w) := vol_position t w
  have hv0 : volume S ≠ 0 := by
    rw [hvol]
    exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hm : MeasurableSet S := measurableSet_Ioc
  have hPdens : P.rnDeriv volume =ᵐ[volume] fun x => (volume S)⁻¹ * S.indicator 1 x := by
    have h := Measure.rnDeriv_smul_left_of_ne_top' (volume.restrict S) volume (ENNReal.inv_ne_top.mpr hv0)
    filter_upwards [h,Measure.rnDeriv_restrict_self volume hm] with x hx hy
    change ((volume S)⁻¹ • volume.restrict S).rnDeriv volume x = _ at hx ⊢
    rw [hx]
    change (volume S)⁻¹ * (volume.restrict S).rnDeriv volume x = _
    rw [hy]
  filter_upwards [hPQ.ae_le (Measure.rnDeriv_eq_div hP hQ),
    hP.ae_le hPdens,hP.ae_le hd,ae_cond_mem (μ := volume) hm] with x hRN hpx hqx hx
  change Real.log (P.rnDeriv Q x).toReal = _
  rw [hRN,hpx,hqx,indicator_of_mem hx,Pi.one_apply,mul_one,hvol,ENNReal.toReal_div,
    ENNReal.toReal_inv,ENNReal.toReal_ofReal (Real.exp_pos w).le,ENNReal.toReal_ofReal (hg x).le,
    Real.log_div (inv_ne_zero (Real.exp_ne_zero _)) (hg x).ne',Real.log_inv,Real.log_exp]

private theorem ratio_on_interval (t w m l : ℝ) :
    llr (positionLaw t w) (positionGaussian m l) =ᵐ[positionLaw t w] cellLogRatio w m l := by
  have h := position_log_density t w (Q := positionGaussian m l)
    (fun x => gaussianPDFReal_pos m _ x (variance_ne l)) (target_ac m l) (volume_ac_target m l)
    (rnDeriv_gaussianReal m (Real.toNNReal (Real.exp l)))
  filter_upwards [h] with x hx
  rw [hx,gaussian_log_pdf]
  unfold cellLogRatio
  ring

private theorem interval_integrable (t w : ℝ) {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable f (positionLaw t w) := by
  have he := (intervalIntegrable_iff_integrableOn_Ioc_of_le
    (show t ≤ t+Real.exp w by linarith only [Real.exp_pos w])).mp
      (hf.intervalIntegrable (μ := volume) t (t+Real.exp w))
  apply he.smul_measure
  rw [vol_position]
  exact ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'

/-- On a uniformly sampled interval the divergence against a positive
continuous probability density is its integrated log score minus log width. -/
theorem position_kl_from_density (t w : ℝ) {Q : Measure ℝ} [IsProbabilityMeasure Q]
    {g : ℝ → ℝ} (hc : Continuous g) (hg : ∀ x, 0 < g x) (hQ : Q ≪ volume) (hvolQ : volume ≪ Q)
    (hd : Q.rnDeriv volume =ᵐ[volume] fun x => ENNReal.ofReal (g x)) :
    klDiv (positionLaw t w) Q ≠ ⊤ ∧
      (klDiv (positionLaw t w) Q).toReal =
        (∫ x in t..t+Real.exp w, -w-Real.log (g x))/(Real.exp w) := by
  let f := fun x => -w-Real.log (g x)
  have hf : Continuous f := continuous_const.sub (hc.log fun x => (hg x).ne')
  have he := position_log_density t w hg hQ hvolQ hd
  have hi := (interval_integrable t w hf).congr he.symm
  have hac : positionLaw t w ≪ Q := cond_absolutelyContinuous.trans hvolQ
  refine ⟨klDiv_ne_top hac hi,?_⟩
  rw [toReal_klDiv_of_measure_eq hac (by simp),integral_congr_ae he,
    positionLaw,ProbabilityTheory.cond,integral_smul_measure,vol_position,ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (Real.exp_pos w).le,smul_eq_mul,
    intervalIntegral.integral_of_le (show t ≤ t+Real.exp w by linarith only [Real.exp_pos w])]
  ring

private theorem position_sq_integral (t w m : ℝ) :
    (∫ x, (x-m)^2 ∂positionLaw t w) = (Real.exp w)^2/12+(t+Real.exp w/2-m)^2 := by
  rw [positionLaw,ProbabilityTheory.cond,integral_smul_measure,vol_position,ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (Real.exp_pos w).le,smul_eq_mul,
    ← intervalIntegral.integral_of_le (show t ≤ t+Real.exp w by linarith only [Real.exp_pos w]),
    intervalIntegral.integral_comp_sub_right (fun x : ℝ => x^2) m,integral_pow]
  push_cast
  field_simp [Real.exp_ne_zero w]
  ring

/-- Exact finite KL loss and all location and scale penalties on a physical interval. -/
theorem position_gaussian_kl (t w m l : ℝ) :
    let D := klDiv (positionLaw t w) (positionGaussian m l)
    D ≠ ⊤ ∧ 2*D.toReal = Real.log (2*Real.pi)+l-2*w +
      ((Real.exp w)^2/12+(t+Real.exp w/2-m)^2)/Real.exp l := by
  have hAC : positionLaw t w ≪ positionGaussian m l := cond_absolutelyContinuous.trans (volume_ac_target m l)
  have hconst : Integrable (fun _ : ℝ => -w+(Real.log (2*Real.pi)+l)/2) (positionLaw t w) :=
    integrable_const _
  have hsq := interval_integrable t w (show Continuous (fun x : ℝ => (x-m)^2) by fun_prop)
  have he := ratio_on_interval t w m l
  have hi := (hconst.add (hsq.const_mul (1/(2*Real.exp l)))).congr he.symm
  refine ⟨klDiv_ne_top hAC hi,?_⟩
  rw [toReal_klDiv_of_measure_eq hAC (by change _ = gaussianReal _ _ univ; simp),
    integral_congr_ae he]
  unfold cellLogRatio
  rw [integral_add hconst (hsq.const_mul _),integral_const,integral_const_mul,position_sq_integral]
  simp only [probReal_univ,one_smul]
  ring

/-- Reverse divergence is infinite because Gaussian mass extends beyond every finite cell. -/
theorem position_reverse_kl (t w m l : ℝ) :
    klDiv (positionGaussian m l) (positionLaw t w) = ⊤ := by
  apply klDiv_of_not_ac
  intro h
  let b := t+Real.exp w
  have hz : positionLaw t w (Ioc b (b+1)) = 0 := by
    rw [positionLaw,ProbabilityTheory.cond,Measure.smul_apply,Measure.restrict_apply measurableSet_Ioc]
    have he : Ioc b (b+1) ∩ Ioc t (t+Real.exp w) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact (not_lt_of_ge hx.2.2) hx.1.1
    simp [he]
  have hv := (volume_ac_target m l).trans h hz
  rw [Real.volume_Ioc,add_sub_cancel_left,ENNReal.ofReal_one] at hv
  exact one_ne_zero hv

/-- Moment matching gives the same minimum on every logarithmic width.
The exact excess is the sum of a scale loss and a squared location loss. -/
theorem position_projection_gap (t w m l : ℝ) :
    let best := Real.log ((Real.exp w)^2/12)
    2*(klDiv (positionLaw t w) (positionGaussian m l)).toReal -
      (Real.log (2*Real.pi)-Real.log 12+1) =
        (Real.exp (best-l)-1-(best-l))+(t+Real.exp w/2-m)^2/Real.exp l := by
  have hv : 0 < (Real.exp w)^2/12 := by positivity
  rw [(position_gaussian_kl t w m l).2]
  dsimp only
  rw [Real.exp_sub,Real.exp_log hv,Real.log_div (pow_ne_zero _ (Real.exp_ne_zero _)) (by norm_num),
    Real.log_pow,Real.log_exp]
  ring

/-- Unique moment-matched projection. Both penalties vanish exactly at the
cell midpoint and its squared width divided by twelve. -/
theorem position_projection_exact (t w m l : ℝ) :
    let loss := 2*(klDiv (positionLaw t w) (positionGaussian m l)).toReal
    let best := Real.log (2*Real.pi)-Real.log 12+1
    best ≤ loss ∧ (loss = best ↔ m = t+Real.exp w/2 ∧ l = Real.log ((Real.exp w)^2/12)) := by
  let z := Real.log ((Real.exp w)^2/12)-l
  let b := t+Real.exp w/2
  have h := position_projection_gap t w m l
  have hx : 0 ≤ (b-m)^2/Real.exp l := div_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have hz : 0 ≤ Real.exp z-1-z := by linarith only [Real.add_one_le_exp z]
  change _ = (Real.exp z-1-z)+(b-m)^2/Real.exp l at h
  refine ⟨by linarith only [h,hx,hz],?_⟩
  constructor
  · intro he
    have ha : z = 0 := by
      by_contra hn
      linarith only [Real.add_one_lt_exp hn,h,he,hx]
    have hb : (b-m)^2/Real.exp l = 0 := by linarith only [h,he,hx,hz]
    exact ⟨(sub_eq_zero.mp (sq_eq_zero_iff.mp ((div_eq_zero_iff.mp hb).resolve_right
      (Real.exp_ne_zero _)))).symm,(sub_eq_zero.mp ha).symm⟩
  · rintro ⟨rfl,rfl⟩
    simp [z,b] at h
    linarith only [h]

/-- The original logarithmic position cell attains the universal minimum
at its geometric-endpoint midpoint in log coordinates. -/
theorem original_cell_projection (i : ℕ) :
    let a := i+1
    let L := Real.log (a:ℝ)
    let W := logCellWidth a
    let P := ProbabilityTheory.cond volume (Ioc L (Real.log ((a:ℝ)+1)))
    2*(klDiv P (positionGaussian (L+W/2) (Real.log (W^2/12)))).toReal =
      Real.log (2*Real.pi)-Real.log 12+1 := by
  let a := i+1
  have hw := logCellWidth_pos (show 1 ≤ a by omega)
  have h := (position_projection_exact (Real.log (a:ℝ)) (Real.log (logCellWidth a))
    (Real.log (a:ℝ)+logCellWidth a/2) (Real.log (logCellWidth a^2/12))).2
  rw [Real.exp_log hw] at h
  have hp : positionLaw (Real.log (a:ℝ)) (Real.log (logCellWidth a)) =
      ProbabilityTheory.cond volume (Ioc (Real.log (a:ℝ)) (Real.log ((a:ℝ)+1))) := by
    simp only [positionLaw,Real.exp_log hw]
    have he : Real.log (a:ℝ)+logCellWidth a = Real.log ((a:ℝ)+1) := by unfold logCellWidth; ring
    rw [he]
  rw [hp] at h
  exact h.mpr ⟨rfl,rfl⟩

#print axioms position_gaussian_kl
#print axioms position_kl_from_density
#print axioms position_reverse_kl
#print axioms position_projection_gap
#print axioms position_projection_exact
#print axioms original_cell_projection
end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
