import GaloisForLFunctions.RHTower.LiClockThetaScoreProfile
import GaloisForLFunctions.RHTower.LiEvenCrossActualClockHistoryBarrier
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Literal score correlation and signed history reserve

All profiles and source measures retain their complete theta rows and original
R0 normalizer. Compact product integrability precedes Fubini and signed algebra.
The reserve and budget statements keep the literal first-zero history guards.
The final decomposition retains its positive lower boundary and complete signed
primitive-history term; it supplies no M15, primitive-sign, or RH conclusion.
-/

open MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal Interval
namespace RHTower
noncomputable section
local notation "R0" => thetaCuspRawEvenMoment 0
local notation "B" => liEvenCrossActualClockBorelKernel
local notation "K" => deriv B
local notation "K1" => deriv K
local notation "P" => liEvenCrossActualClockPrimitive
local notation "D" => liEvenCrossActualClockLogHistory
local notation "ell" => liEvenCrossActualClockHistoryScale
local notation "Cout" => liEvenCrossActualClockHistoryOutsideCorrelation
local notation "T" => liClockThetaSmoothedBorelProfile
local notation "U" => liClockThetaScoreCostProfile
local notation "R" => liClockThetaScoreReserveProfile
local notation "Phi2" => liClockThetaFactorialSecondKernel

/-- The full outside cost integral against the canonical log history. -/
def liEvenCrossActualClockScoreCostIntegral (t : ℝ) : ℝ :=
  ∫ s in ell t..t, s*D s*(U ((t-s):ℂ)).re

/-- The full outside reserve integral against the canonical log history. -/
def liEvenCrossActualClockScoreReserveIntegral (t : ℝ) : ℝ :=
  ∫ s in ell t..t, s*D s*(R ((t-s):ℂ)).re

/-- The signed outside integral of the actual Borel derivative kernel. -/
def liEvenCrossActualClockScoreKernelIntegral (t : ℝ) : ℝ :=
  ∫ s in ell t..t, D s*K (t-s)

/-- The exact clock and early-history budget for the outside correlation. -/
def liEvenCrossActualClockScoreHistoryBudget (t : ℝ) : ℝ :=
  t*K t + (K t/2)*∫ s in 0..ell t, D s

/-- The genuine compact mixed source test, including the zero-lag endpoint. -/
def liEvenCrossActualClockScoreHistoryTest (t x : ℝ) : ℝ :=
  ∫ s in ell t..t, s*D s*(Phi2 (((t-s):ℂ)*(x:ℂ))).re

local notation "IU" => liEvenCrossActualClockScoreCostIntegral
local notation "IR" => liEvenCrossActualClockScoreReserveIntegral
local notation "IK" => liEvenCrossActualClockScoreKernelIntegral
local notation "V" => liEvenCrossActualClockScoreHistoryBudget
local notation "Psi" => liEvenCrossActualClockScoreHistoryTest

private def scPhi (r : ℝ) : ℝ := (Phi2 (r:ℂ)).re
private def scT (r : ℝ) : ℝ := (T (r:ℂ)).re
private def scU (r : ℝ) : ℝ := (U (r:ℂ)).re
private def scR (r : ℝ) : ℝ := (R (r:ℂ)).re

private theorem sc_D_cont : Continuous D :=
  continuous_iff_continuousAt.mpr fun t =>
    (hasDerivAt_liEvenCrossActualClockLogHistory t).continuousAt
private theorem sc_P_cont : Continuous P := contDiff_liEvenCrossActualClockPrimitive.continuous
private theorem sc_K_cont : Continuous K :=
  contDiff_liEvenCrossActualClockBorelKernel.continuous_deriv (by simp)
private theorem sc_K1_cont : Continuous K1 := by
  have hc : ContDiff ℝ (2:ℕ∞) B :=
    contDiff_liEvenCrossActualClockBorelKernel.of_le (by exact_mod_cast (le_top : (2:ℕ∞) ≤ ⊤))
  exact (show ContDiff ℝ (1:ℕ∞) K from hc.deriv').continuous_deriv_one
private theorem sc_complex_cont : Continuous Phi2 ∧ Continuous T ∧ Continuous U ∧ Continuous R := by
  refine ⟨?_,?_,?_,?_⟩ <;> apply continuous_iff_continuousAt.mpr
  · intro z; exact (liClockThetaScoreProfiles_analyticAt z).2.1.continuousAt
  · intro z; exact (liClockThetaScoreProfiles_analyticAt z).2.2.1.continuousAt
  · intro z; exact (liClockThetaScoreProfiles_analyticAt z).2.2.2.1.continuousAt
  · intro z; exact (liClockThetaScoreProfiles_analyticAt z).2.2.2.2.continuousAt
private theorem sc_real_cont : Continuous scPhi ∧ Continuous scT ∧ Continuous scU ∧ Continuous scR :=
  ⟨Complex.continuous_re.comp (sc_complex_cont.1.comp Complex.continuous_ofReal),
   Complex.continuous_re.comp (sc_complex_cont.2.1.comp Complex.continuous_ofReal),
   Complex.continuous_re.comp (sc_complex_cont.2.2.1.comp Complex.continuous_ofReal),
   Complex.continuous_re.comp (sc_complex_cont.2.2.2.comp Complex.continuous_ofReal)⟩
private theorem sc_geometry {t : ℝ} (ht : 0 < t) : 0 < ell t ∧ ell t<t := by
  have h := liEvenCrossActualClockHistory_geometry ht
  exact ⟨h.2.2.1,by linarith [h.2.2.2]⟩
private theorem sc_phi_sum (r : ℝ) :
    Summable (fun j : ℕ => r^(2*j)/(((2*j+2).factorial:ℝ)*((2*j).factorial:ℝ))) ∧
    scPhi r = ∑' j : ℕ, r^(2*j)/(((2*j+2).factorial:ℝ)*((2*j).factorial:ℝ)) := by
  have hc := (liClockThetaScoreProfiles_summable_norm (r:ℂ)).2.1.of_norm
  have he : (fun j : ℕ => (r:ℂ)^(2*j)/
      (((2*j+2).factorial:ℂ)*((2*j).factorial:ℂ))) =
      (fun j : ℕ => ((r^(2*j)/(((2*j+2).factorial:ℝ)*((2*j).factorial:ℝ)):ℝ):ℂ)) := by
    funext j; simp
  rw [he] at hc
  refine ⟨Complex.summable_ofReal.mp hc,?_⟩
  unfold scPhi liClockThetaFactorialSecondKernel
  rw [he,←Complex.ofReal_tsum]
  simp
private theorem sc_phi_nonneg (r : ℝ) : 0 ≤ scPhi r := by
  rw [(sc_phi_sum r).2]
  apply tsum_nonneg
  intro j
  exact div_nonneg (by simpa only [←pow_mul,Nat.mul_comm] using sq_nonneg (r^j)) (by positivity)
private theorem sc_phi_mono_mul {r t : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t) (x : ℝ) :
    scPhi (r*x)  ≤  scPhi (t*x) := by
  rw [(sc_phi_sum (r*x)).2,(sc_phi_sum (t*x)).2]
  apply Summable.tsum_le_tsum _ (sc_phi_sum (r*x)).1 (sc_phi_sum (t*x)).1
  intro j
  rw [mul_pow,mul_pow]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr hrt _) (by simpa only [←pow_mul,Nat.mul_comm] using sq_nonneg (x^j))) (by positivity)
private theorem sc_phi_arg (r x : ℝ) :
    (Phi2 ((r:ℂ)*(x:ℂ))).re=scPhi (r*x) := by simp [scPhi]
private theorem sc_clock_L1 (t : ℝ) :
    IntervalIntegrable (fun s => s*D s*scU (t-s)) volume (ell t) t ∧
    IntervalIntegrable (fun s => s*D s*scR (t-s)) volume (ell t) t ∧
    IntervalIntegrable (fun s => D s*K (t-s)) volume (ell t) t ∧
    IntervalIntegrable (fun s => P s*(t-s)*scT (t-s)) volume (ell t) t := by
  have hU : Continuous (fun s => scU (t-s)) := sc_real_cont.2.2.1.comp (continuous_const.sub continuous_id)
  have hR : Continuous (fun s => scR (t-s)) := sc_real_cont.2.2.2.comp (continuous_const.sub continuous_id)
  have hT : Continuous (fun s => scT (t-s)) := sc_real_cont.2.1.comp (continuous_const.sub continuous_id)
  have hK : Continuous (fun s => K (t-s)) := sc_K_cont.comp (continuous_const.sub continuous_id)
  exact ⟨((continuous_id.mul sc_D_cont).mul hU).intervalIntegrable _ _,
    ((continuous_id.mul sc_D_cont).mul hR).intervalIntegrable _ _,
    (sc_D_cont.mul hK).intervalIntegrable _ _,
    ((sc_P_cont.mul (continuous_const.sub continuous_id)).mul hT).intervalIntegrable _ _⟩

private theorem sc_product_L1 (μ : Measure ℝ) [SFinite μ] (q : ℝ → ℝ)
    (hq : Continuous q) (hq0 : ∀ x,0 ≤ q x) {t : ℝ} (ht : 0 < t)
    (hi : Integrable (fun x => q x*scPhi (t*x)) μ) :
    Integrable (fun p : ℝ×ℝ => p.1*D p.1*q p.2*scPhi ((t-p.1)*p.2))
      ((volume.restrict (Ioc (ell t) t)).prod μ) := by
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((continuous_id.mul sc_D_cont).continuousOn : ContinuousOn (fun s : ℝ => s*D s) (Icc (ell t) t))
  have he := sc_geometry ht
  have hM0 : 0 ≤ M := (norm_nonneg ((ell t)*D (ell t))).trans (hM _ ⟨le_rfl,he.2.le⟩)
  have hb : Integrable (fun p : ℝ×ℝ => M*(q p.2*scPhi (t*p.2)))
      ((volume.restrict (Ioc (ell t) t)).prod μ) := (integrable_const M).mul_prod hi
  have hf : Continuous (fun p : ℝ×ℝ => p.1*D p.1*q p.2*scPhi ((t-p.1)*p.2)) := by
    exact (((continuous_fst.mul (sc_D_cont.comp continuous_fst)).mul (hq.comp continuous_snd)).mul
      (sc_real_cont.1.comp ((continuous_const.sub continuous_fst).mul continuous_snd)))
  apply hb.mono' hf.aestronglyMeasurable
  apply (Measure.ae_prod_iff_ae_ae
    (isClosed_le hf.norm (continuous_const.mul ((hq.comp continuous_snd).mul (sc_real_cont.1.comp (continuous_const.mul continuous_snd))))).measurableSet).2
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  apply Filter.Eventually.of_forall
  intro x
  change ‖s*D s*q x*scPhi ((t-s)*x)‖ ≤ M*(q x*scPhi (t*x))
  have hr : 0 ≤ t-s := sub_nonneg.mpr hs.2
  have hrt : t-s ≤ t := sub_le_self t (he.1.le.trans hs.1.le)
  have hn := sc_phi_nonneg ((t-s)*x)
  have hb' := mul_le_mul (mul_le_mul_of_nonneg_right (hM s ⟨hs.1.le,hs.2⟩) (hq0 x))
    (sc_phi_mono_mul hr hrt x) hn (mul_nonneg hM0 (hq0 x))
  change ‖s*D s‖*q x*scPhi ((t-s)*x) ≤ M*q x*scPhi (t*x) at hb'
  simpa only [norm_mul,Real.norm_eq_abs,abs_of_nonneg (hq0 x),abs_of_nonneg hn,mul_assoc] using hb' 


private theorem sc_source_L1 {t : ℝ} (ht : 0 < t) :
    Integrable (Psi t) liClockThetaScoreMeasure ∧
    Integrable (fun x => (x-1)^2*Psi t x) liClockThetaRawSourceMeasure ∧
    Integrable (fun p : ℝ×ℝ => p.1*D p.1*scPhi ((t-p.1)*p.2))
      ((volume.restrict (Ioc (ell t) t)).prod liClockThetaScoreMeasure) ∧
    Integrable (fun p : ℝ×ℝ => p.1*D p.1*(p.2-1)^2*scPhi ((t-p.1)*p.2))
      ((volume.restrict (Ioc (ell t) t)).prod liClockThetaRawSourceMeasure) := by
  letI := liClockThetaScoreMeasure_admission.1
  letI := liClockThetaRawSourceMeasure_admission.1
  have hs : Integrable (fun x => scPhi (t*x)) liClockThetaScoreMeasure := by
    simpa only [RCLike.re_eq_complex_re,←Complex.ofReal_sub,sc_phi_arg,one_mul] using (liClockThetaScoreProfiles_source_integrals (t:ℂ)).2.1.re
  have hr : Integrable (fun x => (x-1)^2*scPhi (t*x)) liClockThetaRawSourceMeasure := by
    simpa only [←Complex.ofReal_sub,sc_phi_arg] using (liClockThetaScoreReserveProfile_square t).1
  have hpS := sc_product_L1 liClockThetaScoreMeasure (fun _ => 1) continuous_const (fun _ => zero_le_one) ht (by simpa using hs)
  simp only [mul_one] at hpS
  have hpR := sc_product_L1 liClockThetaRawSourceMeasure (fun x => (x-1)^2) (by fun_prop) (fun x => sq_nonneg (x-1)) ht hr
  have hiS := hpS.integral_prod_right
  have hiR := hpR.integral_prod_right
  have he := (sc_geometry ht).2.le
  refine ⟨?_,?_,hpS,hpR⟩
  · change Integrable (fun x => Psi t x) liClockThetaScoreMeasure
    simpa only [liEvenCrossActualClockScoreHistoryTest,scPhi,Complex.ofReal_mul,Complex.ofReal_sub,intervalIntegral.integral_of_le he] using hiS
  · apply hiR.congr
    filter_upwards [] with x
    simp only [liEvenCrossActualClockScoreHistoryTest,←Complex.ofReal_sub,sc_phi_arg,intervalIntegral.integral_of_le he]
    rw [←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with s
    ring

private def scWeight (n : ℕ) (x : ℝ) : ℝ :=
  liClockThetaScoreDefect (n+1) x*thetaCuspBornWittenAmplitude (n+1) x^2
private theorem sc_weight_measurable (n : ℕ) : Measurable (scWeight n) := by
  unfold scWeight liClockThetaScoreDefect thetaCuspBornWittenAmplitude
    thetaCuspBornWittenSuperpotential thetaCuspBornWittenWeight
    thetaCuspMorseSuperpotential thetaCuspMorseGroundState thetaCuspMorseZeroMode
    thetaCuspMorseScale
  fun_prop
private theorem sc_weight_nonneg (n : ℕ) :
    ∀ᵐ x ∂(volume.restrict (Ioi 0)),0 ≤ scWeight n x := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hd : 0 ≤ liClockThetaScoreDefect (n+1) x :=
    (sq_nonneg (x-1)).trans (thetaCuspBornWitten_scoreDefect_ge_square (by omega) hx.le)
  exact mul_nonneg hd (sq_nonneg _)
private theorem sc_density_integral (ρ : ℝ → ℝ) (hρ : Measurable ρ)
    (hn : ∀ᵐ x ∂(volume.restrict (Ioi 0)),0 ≤ ρ x) (f : ℝ → ℝ) :
    (∫ x,f x ∂(volume.restrict (Ioi 0)).withDensity (fun x => ENNReal.ofReal (ρ x)))=
      ∫ x : ℝ in Ioi 0,ρ x*f x := by
  rw [integral_withDensity_eq_integral_toReal_smul hρ.ennreal_ofReal
    (by simp : ∀ᵐ x ∂(volume.restrict (Ioi 0)),ENNReal.ofReal (ρ x)<∞)]
  apply integral_congr_ae
  filter_upwards [hn] with x hx
  simp only [ENNReal.toReal_ofReal hx,smul_eq_mul]
private theorem sc_density_L1 (ρ : ℝ → ℝ) (hρ : Measurable ρ)
    (hn : ∀ᵐ x ∂(volume.restrict (Ioi 0)),0 ≤ ρ x) (f : ℝ → ℝ)
    (hf : Integrable f ((volume.restrict (Ioi 0)).withDensity (fun x => ENNReal.ofReal (ρ x)))) :
    Integrable (fun x => ρ x*f x) (volume.restrict (Ioi 0)) := by
  have hi := (integrable_withDensity_iff_integrable_smul' hρ.ennreal_ofReal
    (by simp : ∀ᵐ x ∂(volume.restrict (Ioi 0)),ENNReal.ofReal (ρ x)<∞)).1 hf
  apply hi.congr
  filter_upwards [hn] with x hx
  simp only [ENNReal.toReal_ofReal hx,smul_eq_mul]
private theorem sc_rows (f : ℝ → ℝ) (hf : Integrable f liClockThetaScoreMeasure) :
    (∀ n : ℕ,IntegrableOn (fun x => scWeight n x*f x) (Ioi 0)) ∧
    Summable (fun n : ℕ => ∫ x : ℝ in Ioi 0,|scWeight n x*f x|) ∧
    (∫ x,f x ∂liClockThetaScoreMeasure)=(2*Real.pi/R0)*∑' n : ℕ,∫ x : ℝ in Ioi 0,scWeight n x*f x := by
  let κ : ℝ := 2*Real.pi/R0
  have hk : 0 < κ := div_pos (mul_pos (by norm_num) Real.pi_pos) (thetaCuspRawEvenMoment_pos 0)
  have htotal : Integrable f (Measure.sum liClockThetaScoreAtomMeasure) := hf
  have ha (n : ℕ) := htotal.mono_measure (Measure.le_sum _ n)
  have hm (n : ℕ) : Measurable (fun x => κ*scWeight n x) := (sc_weight_measurable n).const_mul κ
  have hn (n : ℕ) : ∀ᵐ x ∂(volume.restrict (Ioi 0)),0 ≤ κ*scWeight n x :=
    (sc_weight_nonneg n).mono (fun x hx => mul_nonneg hk.le hx)
  have had (n : ℕ) : Integrable f ((volume.restrict (Ioi 0)).withDensity (fun x => ENNReal.ofReal (κ*scWeight n x))) := by
    simpa only [liClockThetaScoreAtomMeasure,scWeight,κ,mul_assoc] using ha n
  have hi (n : ℕ) : Integrable (fun x => scWeight n x*f x) (volume.restrict (Ioi 0)) := by
    have h := sc_density_L1 _ (hm n) (hn n) f (had n)
    apply (h.const_mul κ⁻¹).congr
    filter_upwards [] with x
    field_simp [hk.ne']
  have he (n : ℕ) : (∫ x,f x ∂liClockThetaScoreAtomMeasure n)=κ*(∫ x : ℝ in Ioi 0,scWeight n x*f x) := by
    rw [show liClockThetaScoreAtomMeasure n=(volume.restrict (Ioi 0)).withDensity (fun x => ENNReal.ofReal (κ*scWeight n x)) by
      simp only [liClockThetaScoreAtomMeasure,scWeight,κ,mul_assoc],sc_density_integral _ (hm n) (hn n)]
    rw [←integral_const_mul]
    congr 1; ext x; ring
  have heN (n : ℕ) : (∫ x,‖f x‖ ∂liClockThetaScoreAtomMeasure n)=κ*(∫ x : ℝ in Ioi 0,|scWeight n x*f x|) := by
    rw [show liClockThetaScoreAtomMeasure n=(volume.restrict (Ioi 0)).withDensity (fun x => ENNReal.ofReal (κ*scWeight n x)) by
      simp only [liClockThetaScoreAtomMeasure,scWeight,κ,mul_assoc],sc_density_integral _ (hm n) (hn n)]
    rw [←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [sc_weight_nonneg n] with x hx
    simp only [Real.norm_eq_abs,abs_mul,abs_of_nonneg hx]
    ring
  have hs := htotal.summable_integral
  have hsrow : Summable (fun n : ℕ => ∫ x : ℝ in Ioi 0,|scWeight n x*f x|) := by
    exact (hs.mul_left κ⁻¹).congr (fun n => by rw [heN]; field_simp [hk.ne'])
  have hh := hasSum_integral_measure htotal
  have hh' := hh.congr_fun (fun n => (he n).symm)
  refine ⟨hi,hsrow,?_⟩
  simpa only [liClockThetaScoreMeasure,κ,tsum_mul_left] using hh'.tsum_eq.symm

private theorem sc_R_source (r : ℝ) : scR r=∫ x,scPhi (r*x) ∂liClockThetaScoreMeasure := by
  have hi := (liClockThetaScoreProfiles_source_integrals (r:ℂ)).2.1
  have he := integral_re hi
  simp only [RCLike.re_eq_complex_re] at he
  rw [←(liClockThetaScoreProfiles_source_integrals (r:ℂ)).2.2.2] at he
  simpa only [scR,sc_phi_arg] using he.symm
private theorem sc_Psi_measurable {t : ℝ} (ht : 0 < t) : Measurable (Psi t) := by
  have hc : Continuous (fun p : ℝ×ℝ => p.1*D p.1*scPhi ((t-p.1)*p.2)) :=
    (continuous_fst.mul (sc_D_cont.comp continuous_fst)).mul
      (sc_real_cont.1.comp ((continuous_const.sub continuous_fst).mul continuous_snd))
  have h := hc.stronglyMeasurable.integral_prod_left' (μ := volume.restrict (Ioc (ell t) t))
  change Measurable (fun x => Psi t x)
  simpa only [liEvenCrossActualClockScoreHistoryTest,scPhi,Complex.ofReal_mul,Complex.ofReal_sub,
    intervalIntegral.integral_of_le (sc_geometry ht).2.le] using h.measurable

/-- All signed compact, product, and full-row integrals are genuinely admitted. -/
theorem liEvenCrossActualClockScoreHistory_admission {t : ℝ} (ht : 0 < t) :
  IntervalIntegrable (fun s => s*D s*(U ((t-s):ℂ)).re) volume (ell t) t ∧
  IntervalIntegrable (fun s => s*D s*(R ((t-s):ℂ)).re) volume (ell t) t ∧
  IntervalIntegrable (fun s => D s*K (t-s)) volume (ell t) t ∧
  IntervalIntegrable (fun s => P s*(t-s)*(T ((t-s):ℂ)).re)
    volume (ell t) t ∧
  Integrable (Psi t) liClockThetaScoreMeasure ∧
  Integrable (fun x => (x-1)^2*Psi t x) liClockThetaRawSourceMeasure ∧
  Integrable (fun p : ℝ×ℝ => p.1*D p.1 *
    (Phi2 (((t-p.1):ℂ)*(p.2:ℂ))).re)
    ((volume.restrict (Ioc (ell t) t)).prod liClockThetaScoreMeasure) ∧
  Integrable (fun p : ℝ×ℝ => p.1*D p.1*(p.2-1)^2 *
    (Phi2 (((t-p.1):ℂ)*(p.2:ℂ))).re)
    ((volume.restrict (Ioc (ell t) t)).prod liClockThetaRawSourceMeasure) ∧
  Summable (fun n : ℕ => ∫ x : ℝ in Ioi 0,
    |liClockThetaScoreDefect (n+1) x *
      thetaCuspBornWittenAmplitude (n+1) x ^ 2 * Psi t x|) := by
  have hc := sc_clock_L1 t
  have hs := sc_source_L1 ht
  refine ⟨by simpa only [scU,Complex.ofReal_sub] using hc.1,by simpa only [scR,Complex.ofReal_sub] using hc.2.1,hc.2.2.1,by simpa only [scT,Complex.ofReal_sub] using hc.2.2.2,hs.1,hs.2.1,?_,?_,?_⟩
  · simpa only [←Complex.ofReal_sub,sc_phi_arg] using hs.2.2.1
  · simpa only [←Complex.ofReal_sub,sc_phi_arg] using hs.2.2.2
  · simpa only [scWeight] using (sc_rows (Psi t) hs.1).2.1

/-- The reserve equals the full source measure integral and every original score row. -/
theorem liEvenCrossActualClockScoreHistory_source_identity {t : ℝ} (ht : 0 < t) :
  IR t = (∫ x : ℝ, Psi t x ∂liClockThetaScoreMeasure) ∧
  IR t = (2*Real.pi/R0) * ∑' n : ℕ,
    ∫ x : ℝ in Ioi 0, liClockThetaScoreDefect (n+1) x *
      thetaCuspBornWittenAmplitude (n+1) x ^ 2 * Psi t x := by
  letI := liClockThetaScoreMeasure_admission.1
  have hp := (sc_source_L1 ht).2.2.1
  have hp' : Integrable (Function.uncurry (fun s x : ℝ => s*D s*scPhi ((t-s)*x)))
      ((volume.restrict (uIoc (ell t) t)).prod liClockThetaScoreMeasure) := by
    simpa only [uIoc_of_le (sc_geometry ht).2.le,Function.uncurry_def] using hp
  have hfub := intervalIntegral_integral_swap hp'
  have he : IR t=∫ x,Psi t x ∂liClockThetaScoreMeasure := by
    calc
      IR t=∫ s in ell t..t,∫ x,s*D s*scPhi ((t-s)*x) ∂liClockThetaScoreMeasure := by
        unfold liEvenCrossActualClockScoreReserveIntegral
        apply intervalIntegral.integral_congr
        intro s _
        simp only [←Complex.ofReal_sub]
        change s*D s*scR (t-s)=_
        rw [integral_const_mul,←sc_R_source]
      _ = _ := by simpa only [liEvenCrossActualClockScoreHistoryTest,scPhi,Complex.ofReal_mul,Complex.ofReal_sub] using hfub
  refine ⟨he,?_⟩
  rw [he]
  simpa only [scWeight] using (sc_rows (Psi t) (sc_source_L1 ht).1).2.2

private theorem sc_K_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ K r := by
  rcases hr.eq_or_lt with h|h
  · rw [←h,liEvenCrossActualClockHistory_origin.1]
  · exact (liEvenCrossActualClockBorel_deriv_pos h).le
private theorem sc_profiles_pos (r : ℝ) : 0 < scT r ∧ 0 < scU r ∧ 0 < scR r := by
  obtain ⟨θ,_,_,_,hθ⟩ := liClockThetaScoreProfiles_uniform_reserve
  exact ⟨(hθ r).1,(hθ r).2.1,(hθ r).2.2.1⟩
private theorem sc_hist_weight {t : ℝ} (ht : 0 < t) (hHist : ∀ s ∈ Icc 0 t,0 ≤ D s)
    {s : ℝ} (hs : s∈Icc (ell t) t) : 0 ≤ s*D s :=
  mul_nonneg (le_trans (sc_geometry ht).1.le hs.1) (hHist s ⟨le_trans (sc_geometry ht).1.le hs.1,hs.2⟩)
private theorem sc_Psi_nonneg {t : ℝ} (ht : 0 < t) (hHist : ∀ s ∈ Icc 0 t,0 ≤ D s) (x : ℝ) : 0 ≤ Psi t x := by
  unfold liEvenCrossActualClockScoreHistoryTest
  apply intervalIntegral.integral_nonneg (sc_geometry ht).2.le
  intro s hs
  simp only [←Complex.ofReal_sub,sc_phi_arg]
  exact mul_nonneg (sc_hist_weight ht hHist hs) (sc_phi_nonneg _)


/-- The literal outside correlation retains the exact factor 303 and signed kernel term. -/
theorem liEvenCrossActualClockScoreHistory_cost_identity {t : ℝ}
    (ht : 20 < t) (hz : D t = 0) (hHist : ∀ s ∈ Icc 0 t, 0  ≤  D s) :
  303*Cout t = IU t-IR t-303*IK t := by
  have _ := hz
  have _ := hHist
  have _ := ht
  have hi := sc_clock_L1 t
  unfold liEvenCrossActualClockHistoryOutsideCorrelation liEvenCrossActualClockScoreCostIntegral
    liEvenCrossActualClockScoreReserveIntegral liEvenCrossActualClockScoreKernelIntegral
  rw [←intervalIntegral.integral_const_mul]
  calc
    (∫ s in ell t..t,303*(D s*(s*K1 (t-s)-K (t-s)))) =
      ∫ s in ell t..t,(s*D s*scU (t-s)-s*D s*scR (t-s))-303*(D s*K (t-s)) := by
        apply intervalIntegral.integral_congr
        intro s _
        dsimp [scU,scR]
        rw [←liClockThetaScoreProfiles_cost_identity (t-s)]
        ring
    _ = _ := by
      rw [intervalIntegral.integral_sub (hi.1.sub hi.2.1) (hi.2.2.1.const_mul 303),
        intervalIntegral.integral_sub hi.1 hi.2.1,intervalIntegral.integral_const_mul]
      simp only [scU,scR,Complex.ofReal_sub]

/-- Guarded nonnegative histories transfer to the full reserve and square-source test. -/
theorem liEvenCrossActualClockScoreHistory_positive_reserve {t : ℝ}
    (ht : 20 < t) (hz : D t = 0) (hHist : ∀ s ∈ Icc 0 t, 0  ≤  D s) :
  0  ≤  IU t ∧ 0  ≤  IR t ∧ 0  ≤  IK t ∧ (∀ x : ℝ, 0  ≤  Psi t x) ∧
  (∫ s in ell t..t, ∫ x : ℝ,
    s*D s*(x-1)^2*(Phi2 (((t-s):ℂ)*(x:ℂ))).re
      ∂liClockThetaRawSourceMeasure)  ≤  IR t := by
  have _ := hz
  have ht0 : 0 < t := by linarith
  have he := (sc_geometry ht0).2.le
  have hi := sc_clock_L1 t
  have hIu : 0 ≤ IU t := by
    unfold liEvenCrossActualClockScoreCostIntegral
    simp only [←Complex.ofReal_sub]
    change 0 ≤ ∫ s in ell t..t,s*D s*scU (t-s)
    apply intervalIntegral.integral_nonneg he
    intro s hs
    exact mul_nonneg (sc_hist_weight ht0 hHist hs) (sc_profiles_pos (t-s)).2.1.le
  have hIr : 0 ≤ IR t := by
    unfold liEvenCrossActualClockScoreReserveIntegral
    simp only [←Complex.ofReal_sub]
    change 0 ≤ ∫ s in ell t..t,s*D s*scR (t-s)
    apply intervalIntegral.integral_nonneg he
    intro s hs
    exact mul_nonneg (sc_hist_weight ht0 hHist hs) (sc_profiles_pos (t-s)).2.2.le
  have hIk : 0 ≤ IK t := by
    change 0 ≤ ∫ s in ell t..t,D s*K (t-s)
    apply intervalIntegral.integral_nonneg he
    intro s hs
    exact mul_nonneg (hHist s ⟨le_trans (sc_geometry ht0).1.le hs.1,hs.2⟩)
      (sc_K_nonneg (sub_nonneg.mpr hs.2))
  have hPsi := sc_Psi_nonneg ht0 hHist
  have hh := liClockThetaScoreMeasure_nonnegative_test (Psi t) (sc_Psi_measurable ht0)
    hPsi (sc_source_L1 ht0).1
  letI := liClockThetaRawSourceMeasure_admission.1
  have hp := (sc_source_L1 ht0).2.2.2
  have hp' : Integrable (Function.uncurry (fun s x : ℝ => s*D s*(x-1)^2*scPhi ((t-s)*x)))
      ((volume.restrict (uIoc (ell t) t)).prod liClockThetaRawSourceMeasure) := by
    simpa only [uIoc_of_le he,Function.uncurry_def] using hp
  have hfub := intervalIntegral_integral_swap hp'
  have heq : (∫ s in ell t..t,∫ x : ℝ,s*D s*(x-1)^2*(Phi2 (((t-s):ℂ)*(x:ℂ))).re
      ∂liClockThetaRawSourceMeasure)=∫ x : ℝ,(x-1)^2*Psi t x ∂liClockThetaRawSourceMeasure := by
    simp only [←Complex.ofReal_sub,sc_phi_arg]
    rw [hfub]
    apply integral_congr_ae
    filter_upwards [] with x
    unfold liEvenCrossActualClockScoreHistoryTest
    rw [←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _
    simp only [←Complex.ofReal_sub,sc_phi_arg]
    ring
  refine ⟨hIu,hIr,hIk,hPsi,?_⟩
  rw [heq,(liEvenCrossActualClockScoreHistory_source_identity ht0).1]
  exact hh.2

/-- One coefficient ceiling gives a reserve and an explicit conditional budget estimate. -/
theorem liEvenCrossActualClockScoreHistory_uniform_reserve :
  ∃ theta : ℝ, 0 < theta ∧ theta < 1 ∧
    ∀ t : ℝ, 20 < t → D t = 0 → (∀ s ∈ Icc 0 t, 0  ≤  D s) →
      (1-theta)*IU t  ≤  IR t ∧
      Cout t  ≤  (theta/303)*IU t-IK t ∧
      (theta*IU t  ≤  303*(IK t+V t) → Cout t  ≤  V t) := by
  obtain ⟨theta,hθ0,hθ1,_,hθ⟩ := liClockThetaScoreProfiles_uniform_reserve
  refine ⟨theta,hθ0,hθ1,?_⟩
  intro t ht hz hHist
  have ht0 : 0 < t := by linarith
  have hi := sc_clock_L1 t
  have hb : (1-theta)*IU t ≤ IR t := by
    unfold liEvenCrossActualClockScoreCostIntegral liEvenCrossActualClockScoreReserveIntegral
    simp only [←Complex.ofReal_sub]
    change (1-theta)*(∫ s in ell t..t,s*D s*scU (t-s)) ≤ ∫ s in ell t..t,s*D s*scR (t-s)
    rw [←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on (sc_geometry ht0).2.le (hi.1.const_mul (1-theta)) hi.2.1
    intro s hs
    have h := mul_le_mul_of_nonneg_left (hθ (t-s)).2.2.2.1 (sc_hist_weight ht0 hHist hs)
    dsimp [scU,scR]
    simpa only [mul_assoc,mul_left_comm,mul_comm] using h
  have he := liEvenCrossActualClockScoreHistory_cost_identity ht hz hHist
  refine ⟨hb,by nlinarith,?_⟩
  intro hbudget
  nlinarith

/-- The outside budget is exactly equivalent to its full signed score inequality. -/
theorem liEvenCrossActualClockScoreHistory_budget_iff {t : ℝ}
    (ht : 20 < t) (hz : D t = 0) (hHist : ∀ s ∈ Icc 0 t, 0  ≤  D s) :
  Cout t  ≤  V t ↔ IU t-303*V t  ≤  IR t+303*IK t := by
  have he := liEvenCrossActualClockScoreHistory_cost_identity ht hz hHist
  constructor <;> intro h <;> nlinarith

private theorem sc_T_contDiff : ContDiff ℝ (⊤:ℕ∞) scT := by
  have hd : Differentiable ℂ T := fun z => (liClockThetaScoreProfiles_analyticAt z).2.2.1.differentiableAt
  exact hd.contDiff.real_of_complex
private theorem sc_T_deriv (r : ℝ) : HasDerivAt scT (deriv T (r:ℂ)).re r :=
  (liClockThetaScoreProfiles_analyticAt (r:ℂ)).2.2.1.differentiableAt.hasDerivAt.real_of_complex
private theorem sc_U_deriv (r : ℝ) : scU r=17*scT r+16*r*deriv scT r := by
  have h := congrArg Complex.re (liClockThetaScoreCostProfile_eq_derivative (r:ℂ))
  norm_num [Complex.add_re,Complex.mul_re] at h
  rw [←(sc_T_deriv r).deriv] at h
  exact h
private theorem sc_clock_product_deriv (t s : ℝ) (hs : 0 < s) :
    HasDerivAt (fun s => s*D s*(t-s)) ((t-2*s)*D s+(t-s)*P s) s := by
  have hD := hasDerivAt_liEvenCrossActualClockLogHistory s
  simp only [liEvenCrossActualClockLogHistoryDensity] at hD
  convert ((hasDerivAt_id s).mul hD).mul ((hasDerivAt_id s).const_sub t) using 1 <;>
    first | rfl | (simp only [id_eq,Pi.mul_apply];field_simp [hs.ne'];ring)
private theorem sc_smoothing_IBP {t : ℝ} (ht : 0 < t) :
    (∫ s in ell t..t,s*D s*(t-s)*deriv scT (t-s)) =
      ell t*D (ell t)*(t-ell t)*scT (t-ell t)+
        ∫ s in ell t..t,((t-2*s)*D s+(t-s)*P s)*scT (t-s) := by
  let u : ℝ → ℝ := fun s => s*D s*(t-s)
  let u' : ℝ → ℝ := fun s => (t-2*s)*D s+(t-s)*P s
  let v : ℝ → ℝ := fun s => scT (t-s)
  let v' : ℝ → ℝ := fun s => -deriv scT (t-s)
  have hu : Continuous u := by dsimp [u]; exact (continuous_id.mul sc_D_cont).mul (continuous_const.sub continuous_id)
  have hu' : Continuous u' := ((continuous_const.sub (continuous_const.mul continuous_id)).mul sc_D_cont).add ((continuous_const.sub continuous_id).mul sc_P_cont)
  have hv : Continuous v := sc_real_cont.2.1.comp (continuous_const.sub continuous_id)
  have hv' : Continuous v' := (sc_T_contDiff.continuous_deriv (by simp)).comp (continuous_const.sub continuous_id) |>.neg
  have he := sc_geometry ht
  have hh := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt hu.continuousOn hv.continuousOn
    (fun s hs => sc_clock_product_deriv t s (by
      simp only [min_eq_left he.2.le,max_eq_right he.2.le,mem_Ioo] at hs
      exact lt_trans he.1 hs.1))
    (fun s _ => by
      have h := (sc_T_contDiff.differentiable (by simp) (t-s)).hasDerivAt.comp s ((hasDerivAt_id s).const_sub t)
      simpa only [v,v',Function.comp_def,mul_neg_one] using h)
    (hu'.intervalIntegrable (ell t) t) (hv'.intervalIntegrable (ell t) t)
  have hneg : (∫ s in ell t..t,u s*v' s)=-(∫ s in ell t..t,s*D s*(t-s)*deriv scT (t-s)) := by
    rw [←intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro s _; dsimp [u,v']; ring
  rw [hneg] at hh
  dsimp [u,v,u'] at hh
  simp only [sub_self,mul_zero,zero_mul,zero_sub] at hh
  linarith

/-- Compact integration by parts retains the lower boundary and complete signed P term. -/
theorem liEvenCrossActualClockScoreHistory_signed_decomposition {t : ℝ}
    (ht : 20 < t) (hz : D t = 0) (hHist : ∀ s ∈ Icc 0 t, 0  ≤  D s) :
  IU t = 16*ell t*D (ell t)*(t-ell t)*(T ((t-ell t):ℂ)).re +
    (∫ s in ell t..t, D s*(16*t-15*s)*(T ((t-s):ℂ)).re) +
    16*(∫ s in ell t..t, P s*(t-s)*(T ((t-s):ℂ)).re) ∧
  0  ≤  16*ell t*D (ell t)*(t-ell t)*(T ((t-ell t):ℂ)).re ∧
  0  ≤  ∫ s in ell t..t, D s*(16*t-15*s)*(T ((t-s):ℂ)).re := by
  have _ := hz
  have ht0 : 0 < t := by linarith
  have he := sc_geometry ht0
  have hTr : Continuous (fun s : ℝ => scT (t-s)) := sc_real_cont.2.1.comp (continuous_const.sub continuous_id)
  have hTd : Continuous (fun s : ℝ => deriv scT (t-s)) := (sc_T_contDiff.continuous_deriv (by simp)).comp (continuous_const.sub continuous_id)
  have hA : IntervalIntegrable (fun s => s*D s*scT (t-s)) volume (ell t) t :=
    ((continuous_id.mul sc_D_cont).mul hTr).intervalIntegrable _ _
  have hJ : IntervalIntegrable (fun s => s*D s*(t-s)*deriv scT (t-s)) volume (ell t) t :=
    (((continuous_id.mul sc_D_cont).mul (continuous_const.sub continuous_id)).mul hTd).intervalIntegrable _ _
  have hL : IntervalIntegrable (fun s => ((t-2*s)*D s+(t-s)*P s)*scT (t-s)) volume (ell t) t := by
    have hc : Continuous (fun s => ((t-2*s)*D s+(t-s)*P s)*scT (t-s)) := (((continuous_const.sub (continuous_const.mul continuous_id)).mul sc_D_cont).add ((continuous_const.sub continuous_id).mul sc_P_cont)).mul hTr
    exact hc.intervalIntegrable _ _
  have hM : IntervalIntegrable (fun s => D s*(16*t-15*s)*scT (t-s)) volume (ell t) t :=
    ((sc_D_cont.mul (by fun_prop)).mul hTr).intervalIntegrable _ _
  have hP := (sc_clock_L1 t).2.2.2
  have hIU : IU t=17*(∫ s in ell t..t,s*D s*scT (t-s))+
      16*(∫ s in ell t..t,s*D s*(t-s)*deriv scT (t-s)) := by
    rw [←intervalIntegral.integral_const_mul,←intervalIntegral.integral_const_mul,
      ←intervalIntegral.integral_add (hA.const_mul 17) (hJ.const_mul 16)]
    unfold liEvenCrossActualClockScoreCostIntegral
    simp only [←Complex.ofReal_sub]
    apply intervalIntegral.integral_congr
    intro s _
    change s*D s*scU (t-s)=_
    rw [sc_U_deriv]
    ring
  have hlinear : 17*(∫ s in ell t..t,s*D s*scT (t-s))+
      16*(∫ s in ell t..t,((t-2*s)*D s+(t-s)*P s)*scT (t-s)) =
      (∫ s in ell t..t,D s*(16*t-15*s)*scT (t-s))+
      16*(∫ s in ell t..t,P s*(t-s)*scT (t-s)) := by
    rw [←intervalIntegral.integral_const_mul,←intervalIntegral.integral_const_mul,
      ←intervalIntegral.integral_const_mul,
      ←intervalIntegral.integral_add (hA.const_mul 17) (hL.const_mul 16),
      ←intervalIntegral.integral_add hM (hP.const_mul 16)]
    apply intervalIntegral.integral_congr
    intro s _; ring
  have hIBP := sc_smoothing_IBP ht0
  simp only [←Complex.ofReal_sub]
  refine ⟨?_,?_,?_⟩
  · change IU t=16*ell t*D (ell t)*(t-ell t)*scT (t-ell t)+
      (∫ s in ell t..t,D s*(16*t-15*s)*scT (t-s))+
      16*(∫ s in ell t..t,P s*(t-s)*scT (t-s))
    nlinarith
  · change 0 ≤ 16*ell t*D (ell t)*(t-ell t)*scT (t-ell t)
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) he.1.le)
      (hHist (ell t) ⟨he.1.le,he.2.le⟩)) (sub_nonneg.mpr he.2.le)) (sc_profiles_pos _).1.le
  · change 0 ≤ ∫ s in ell t..t,D s*(16*t-15*s)*scT (t-s)
    apply intervalIntegral.integral_nonneg he.2.le
    intro s hs
    exact mul_nonneg (mul_nonneg (hHist s ⟨he.1.le.trans hs.1,hs.2⟩)
      (by linarith [hs.2])) (sc_profiles_pos _).1.le

end
end RHTower
