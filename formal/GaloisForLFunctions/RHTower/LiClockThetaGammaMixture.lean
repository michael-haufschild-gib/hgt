import GaloisForLFunctions.RHTower.LiEvenCrossActualClockBorelCorrection
import GaloisForLFunctions.RHTower.PrimeArchThetaAllOrderCumulant
import GaloisForLFunctions.HTGeometry.LaplaceTransformConvolution
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Literal theta degree law and positive Gamma mixture

The single normalized Xi value supplies the complete positive degree weights.
Degree zero retains its Dirac row; positive degrees use Gamma shape `2*j` and
rate `p`. Their full countable mixture has the actual damped Borel-derivative
density, whose integrability follows from the complete probability mass.
Real MGF parameters below the rate and complex disks inside that range have
genuine integrability and the same source normalizer bound.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace RHTower
local notation "Lap" => GaloisForLFunctions.HTGeometry.laplace

/-- The real value of the single normalized Xi source at reciprocal imaginary argument. -/
def liClockThetaGammaNormalizer (p : ℝ) : ℝ :=
  (XiC (-Complex.I * (p : ℂ)⁻¹) / XiC 0).re

/-- The real logarithm of the literal source normalizer. -/
def liClockThetaReciprocalLog (p : ℝ) : ℝ :=
  Real.log (liClockThetaGammaNormalizer p)

/-- The normalized positive theta moment weight of each natural degree. -/
def liClockThetaDegreeWeight (p : ℝ) (j : ℕ) : ℝ :=
  thetaCuspNormalizedEvenMoment j /
    (((2*j).factorial : ℝ) * p^(2*j) * liClockThetaGammaNormalizer p)

/-- The complete degree law, retaining every natural atom including zero. -/
def liClockThetaDegreeLaw (p : ℝ) : Measure ℝ :=
  Measure.sum (fun j : ℕ =>
    ENNReal.ofReal (liClockThetaDegreeWeight p j) • Measure.dirac (j : ℝ))

/-- The positive-degree Gamma shape `2*j`, rate `p` density; the zero row has no density. -/
def liClockThetaGammaRowDensity (p : ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  if j = 0 then 0 else
    (Ioi (0 : ℝ)).indicator (fun t =>
      p^(2*j) * t^(2*j-1) * Real.exp (-(p*t)) /
        ((2*j-1).factorial : ℝ)) t

/-- The zero Dirac row and the literal positive-degree Gamma rows. -/
def liClockThetaGammaRowLaw (p : ℝ) (j : ℕ) : Measure ℝ :=
  if j = 0 then Measure.dirac 0
  else ProbabilityTheory.gammaMeasure (2*j : ℝ) p

/-- The full countable positive Gamma mixture weighted by the actual degree law. -/
def liClockThetaGammaMixture (p : ℝ) : Measure ℝ :=
  Measure.sum (fun j : ℕ =>
    ENNReal.ofReal (liClockThetaDegreeWeight p j) • liClockThetaGammaRowLaw p j)

private theorem gm_Xi_zero : XiC 0 = (thetaCuspRawEvenMoment 0 : ℂ) := by
  simpa [iteratedDeriv_zero] using iteratedDeriv_XiC_zero_eq_rawEvenMoment 0

private theorem gm_Xi_series (w : ℂ) :
    HasSum (fun j : ℕ => (thetaCuspNormalizedEvenMoment j : ℂ) * w^(2*j) /
      ((2*j).factorial : ℂ)) (XiC (-Complex.I*w) / XiC 0) := by
  let f : ℕ → ℂ := fun n => (n.factorial : ℂ)⁻¹ * (-Complex.I*w)^n *
    iteratedDeriv n XiC 0
  have hs : HasSum f (XiC (-Complex.I*w)) := by
    simpa only [f, sub_zero, smul_eq_mul, mul_assoc] using
      Complex.hasSum_taylorSeries_of_entire XiC_differentiable 0 (-Complex.I*w)
  have hzero : ∀ n, n ∉ Set.range (fun j : ℕ => 2*j) → f n = 0 := by
    intro n hn
    rcases Nat.even_or_odd n with ⟨j, hj⟩ | ho
    · exact (hn ⟨j, by dsimp; omega⟩).elim
    · simp [f, iteratedDeriv_XiC_odd_zero ho]
  have he := ((show Function.Injective (fun j : ℕ => 2*j) from by
    intro i j hij; dsimp at hij; omega).hasSum_iff hzero).mpr hs
  have hd := he.div_const (XiC 0)
  apply hd.congr_fun
  intro j
  symm
  dsimp [f, Function.comp_def]
  rw [iteratedDeriv_XiC_zero_eq_rawEvenMoment, gm_Xi_zero]
  have hi : (-Complex.I)^(2*j) = (-1 : ℂ)^j := by
    rw [pow_mul]
    norm_num
  rw [mul_pow, hi]
  simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_neg,
    Complex.ofReal_one, thetaCuspNormalizedEvenMoment, Complex.ofReal_div]
  have hsign : (-1 : ℂ)^j * (-1 : ℂ)^j = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    _ = ((-1:ℂ)^j*(-1:ℂ)^j) *
      ((thetaCuspRawEvenMoment j:ℂ) / (thetaCuspRawEvenMoment 0:ℂ) *
        w^(2*j) / ((2*j).factorial:ℂ)) := by ring
    _ = _ := by rw [hsign]; ring

private theorem gm_normalizer_hasSum (p : ℝ) :
    HasSum (fun j : ℕ => thetaCuspNormalizedEvenMoment j /
      (((2*j).factorial : ℝ)*p^(2*j))) (liClockThetaGammaNormalizer p) := by
  have hs := (gm_Xi_series ((p:ℂ)⁻¹)).map Complex.reCLM Complex.continuous_re
  change HasSum (fun j => ((thetaCuspNormalizedEvenMoment j:ℂ) *
    ((p:ℂ)⁻¹)^(2*j) / ((2*j).factorial:ℂ)).re)
    (liClockThetaGammaNormalizer p) at hs
  apply hs.congr_fun
  intro j
  have hh : (thetaCuspNormalizedEvenMoment j:ℂ) * ((p:ℂ)⁻¹)^(2*j) /
      ((2*j).factorial:ℂ) =
      (thetaCuspNormalizedEvenMoment j / (((2*j).factorial:ℝ)*p^(2*j)) : ℝ) := by
    push_cast
    rw [inv_pow]
    ring
  simpa only [Complex.ofReal_re] using (congrArg Complex.re hh).symm

private theorem gm_normalizer_complex (p : ℝ) :
    (liClockThetaGammaNormalizer p : ℂ) = XiC (-Complex.I*(p:ℂ)⁻¹)/XiC 0 := by
  have hh := Complex.hasSum_ofReal.mpr (gm_normalizer_hasSum p)
  have hs := gm_Xi_series ((p:ℂ)⁻¹)
  apply hh.unique
  convert hs using 1
  ext j
  push_cast
  rw [inv_pow]
  ring

private theorem gm_normalizer_gt_one {p : ℝ} (hp : 0 < p) :
    1 < liClockThetaGammaNormalizer p := by
  let f : ℕ → ℝ := fun j => thetaCuspNormalizedEvenMoment j /
    (((2*j).factorial:ℝ)*p^(2*j))
  have hf : ∀ j, 0 < f j := fun j => div_pos
    (thetaCuspNormalizedEvenMoment_pos j) (mul_pos (by positivity) (pow_pos hp _))
  have hs := gm_normalizer_hasSum p
  have hle := hs.summable.sum_le_tsum {0,1} (fun j _ => (hf j).le)
  rw [hs.tsum_eq] at hle
  have hz : f 0 = 1 := by simp [f]
  have hh : f 0 + f 1 ≤ liClockThetaGammaNormalizer p := by
    simpa only [Finset.sum_insert, Finset.mem_singleton, zero_ne_one, not_false_eq_true,
      Finset.sum_singleton, f] using hle
  linarith [hf 1]

/-- The complete positive theta moment series is the single normalized entire Xi value. -/
theorem liClockThetaGammaNormalizer_source {p : ℝ} (hp : 0 < p) :
    HasSum (fun j : ℕ => thetaCuspNormalizedEvenMoment j /
      (((2*j).factorial : ℝ) * p^(2*j))) (liClockThetaGammaNormalizer p) ∧
    (liClockThetaGammaNormalizer p : ℂ) = XiC (-Complex.I * (p : ℂ)⁻¹) / XiC 0 ∧
    1 < liClockThetaGammaNormalizer p :=
  ⟨gm_normalizer_hasSum p, gm_normalizer_complex p, gm_normalizer_gt_one hp⟩

private theorem gm_weights {p : ℝ} (hp : 0 < p) :
    (∀ j, 0 < liClockThetaDegreeWeight p j) ∧ HasSum (liClockThetaDegreeWeight p) 1 := by
  have hz : 0 < liClockThetaGammaNormalizer p := lt_trans zero_lt_one (gm_normalizer_gt_one hp)
  refine ⟨fun j => div_pos (thetaCuspNormalizedEvenMoment_pos j)
    (mul_pos (mul_pos (by positivity) (pow_pos hp _)) hz), ?_⟩
  have h := (gm_normalizer_hasSum p).div_const (liClockThetaGammaNormalizer p)
  rw [div_self hz.ne'] at h
  apply h.congr_fun
  intro j
  dsimp [liClockThetaDegreeWeight]
  ring

private theorem gm_degree_atoms {p : ℝ} (j : ℕ) :
    liClockThetaDegreeLaw p {(j:ℝ)} = ENNReal.ofReal (liClockThetaDegreeWeight p j) := by
  classical
  rw [liClockThetaDegreeLaw, Measure.sum_apply _ (measurableSet_singleton _)]
  have he (k : ℕ) :
      (ENNReal.ofReal (liClockThetaDegreeWeight p k) • Measure.dirac (k:ℝ)) {(j:ℝ)} =
      if k=j then ENNReal.ofReal (liClockThetaDegreeWeight p j) else 0 := by
    by_cases hk : k=j
    · simp [hk]
    · simp [Measure.smul_apply, hk]
  simp_rw [he]
  simp

private theorem gm_degree_support (p : ℝ) :
    ∀ᵐ t ∂liClockThetaDegreeLaw p, t ∈ Set.range (fun j : ℕ => (j:ℝ)) := by
  apply Measure.ae_sum_iff.mpr
  intro j
  apply Measure.ae_smul_measure
  apply (ae_dirac_iff (Set.countable_range (fun j : ℕ => (j:ℝ))).measurableSet).mpr
  exact ⟨j,rfl⟩

/-- Every natural degree has positive mass in the normalized complete degree law. -/
theorem liClockThetaDegreeLaw_admission {p : ℝ} (hp : 0 < p) :
    (∀ j : ℕ, 0 < liClockThetaDegreeWeight p j) ∧
    HasSum (liClockThetaDegreeWeight p) 1 ∧
    IsProbabilityMeasure (liClockThetaDegreeLaw p) ∧
    (∀ j : ℕ, liClockThetaDegreeLaw p { (j : ℝ) } =
      ENNReal.ofReal (liClockThetaDegreeWeight p j)) ∧
    (∀ᵐ t ∂liClockThetaDegreeLaw p, t ∈ Set.range (fun j : ℕ => (j : ℝ))) := by
  have hw := gm_weights hp
  exact ⟨hw.1, hw.2, hw.2.isProbabilityMeasure_sum_dirac (fun j => (hw.1 j).le),
    gm_degree_atoms, gm_degree_support p⟩

private theorem gm_power_integrable {r : ℝ} (hr : 0 < r) (m : ℕ) :
    IntegrableOn (fun t : ℝ => t^m * Real.exp (-(r*t))) (Ioi 0) := by
  have hm : (-1:ℝ)<(m:ℝ) := by
    have hm0 : 0≤(m:ℝ) := by positivity
    linarith
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p:=1) (s:=(m:ℝ))
    (b:=r) hm (by norm_num) hr
  simpa only [Real.rpow_one, Real.rpow_natCast, neg_mul] using h

private theorem gm_power_integral {r : ℝ} (hr : 0 < r) (m : ℕ) :
    (∫ t in Ioi 0, t^m * Real.exp (-(r*t))) = (m.factorial:ℝ)/r^(m+1) := by
  have hm : (-1:ℝ)<(m:ℝ) := by
    have hm0 : 0≤(m:ℝ) := by positivity
    linarith
  have hc : (m:ℝ)+1=((m+1:ℕ):ℝ) := by norm_num
  have h := integral_rpow_mul_exp_neg_mul_rpow
    (p:=1) (q:=(m:ℝ)) (b:=r) (by norm_num) hm hr
  calc
    _ = r^(-((m:ℝ)+1))*Real.Gamma ((m:ℝ)+1) := by
      simpa only [Real.rpow_one,Real.rpow_natCast,div_one,mul_one,neg_mul] using h
    _ = (r^(m+1))⁻¹*(m.factorial:ℝ) := by
      rw [Real.rpow_neg hr.le,Real.Gamma_nat_eq_factorial,hc,Real.rpow_natCast]
    _ = _ := by rw [div_eq_mul_inv]; ring

private theorem gm_density_measurable (p : ℝ) (j : ℕ) :
    Measurable (liClockThetaGammaRowDensity p j) := by
  unfold liClockThetaGammaRowDensity
  split_ifs
  · fun_prop
  · exact Measurable.indicator (by fun_prop) measurableSet_Ioi

private theorem gm_density_nonneg {p : ℝ} (hp : 0 < p) (j : ℕ) (t : ℝ) :
    0 ≤ liClockThetaGammaRowDensity p j t := by
  by_cases hj : j=0
  · simp [liClockThetaGammaRowDensity,hj]
  by_cases ht : 0<t
  · simp only [liClockThetaGammaRowDensity, if_neg hj, indicator_of_mem (show t∈Ioi (0:ℝ) from ht)]
    positivity
  · simp [liClockThetaGammaRowDensity,hj,ht]

private theorem gm_gamma_pdf {p : ℝ} {j : ℕ} (hj : 0<j) :
    ProbabilityTheory.gammaPDFReal (2*j:ℝ) p = liClockThetaGammaRowDensity p j := by
  have hs : (2*j:ℝ)=((2*j:ℕ):ℝ) := by norm_num
  have hn : 2*j-1+1=2*j := by omega
  have hc : ((2*j-1:ℕ):ℝ)+1=(2*j:ℝ) := by exact_mod_cast hn
  have he : (2*j:ℝ)-1=((2*j-1:ℕ):ℝ) := by linarith
  have hg : Real.Gamma (2*j:ℝ) = ((2*j-1).factorial:ℝ) := by
    rw [←hc,Real.Gamma_nat_eq_factorial]
  funext t
  by_cases ht : 0<t
  · simp only [ProbabilityTheory.gammaPDFReal,if_pos ht.le,liClockThetaGammaRowDensity,if_neg (by omega : j≠0),indicator_of_mem (show t∈Ioi (0:ℝ) from ht)]
    rw [he,hg,hs]
    simp only [Real.rpow_natCast]
    ring
  · have ht0 : t≤0 := le_of_not_gt ht
    rcases ht0.eq_or_lt with rfl | hneg
    · simp [ProbabilityTheory.gammaPDFReal,liClockThetaGammaRowDensity,hg,he,
        Real.rpow_natCast,show 2*j-1≠0 by omega]
    · simp [ProbabilityTheory.gammaPDFReal,liClockThetaGammaRowDensity,
        not_le.mpr hneg,not_lt_of_ge hneg.le]

private theorem gm_row_density {p : ℝ} {j : ℕ} (hj : 0<j) :
    liClockThetaGammaRowLaw p j =
      volume.withDensity (fun t => ENNReal.ofReal (liClockThetaGammaRowDensity p j t)) := by
  rw [liClockThetaGammaRowLaw,if_neg (by omega : j≠0),ProbabilityTheory.gammaMeasure]
  congr 1
  funext t
  change ENNReal.ofReal (ProbabilityTheory.gammaPDFReal (2*j:ℝ) p t) = _
  rw [gm_gamma_pdf hj]

private theorem gm_row_probability {p : ℝ} (hp : 0<p) (j : ℕ) :
    IsProbabilityMeasure (liClockThetaGammaRowLaw p j) := by
  by_cases hj : j=0
  · simp only [liClockThetaGammaRowLaw,if_pos hj]
    infer_instance
  · rw [liClockThetaGammaRowLaw,if_neg hj]
    exact ProbabilityTheory.isProbabilityMeasure_gammaMeasure (by positivity : 0<(2*j:ℝ)) hp

private theorem gm_row_support {p : ℝ} (j : ℕ) :
    ∀ᵐ t ∂liClockThetaGammaRowLaw p j, 0≤t := by
  by_cases hj : j=0
  · simp [liClockThetaGammaRowLaw,hj,ae_dirac_eq]
  · rw [gm_row_density (by omega : 0<j),ae_withDensity_iff
      (gm_density_measurable p j).ennreal_ofReal]
    apply ae_of_all
    intro t ht
    by_contra hneg
    apply ht
    simp [liClockThetaGammaRowDensity,hj,not_lt.mpr (le_of_not_ge hneg)]

private theorem gm_row_tilt_eq {p u : ℝ} {j : ℕ} (hj : 0<j) :
    (fun t => liClockThetaGammaRowDensity p j t * Real.exp (u*t)) =
    (fun t => (p^(2*j)/((2*j-1).factorial:ℝ)) *
      (Ioi (0:ℝ)).indicator (fun t => t^(2*j-1)*Real.exp (-((p-u)*t))) t) := by
  funext t
  by_cases ht : 0<t
  · simp only [liClockThetaGammaRowDensity,if_neg (by omega : j≠0),indicator_of_mem (show t∈Ioi (0:ℝ) from ht)]
    rw [show -((p-u)*t)=-(p*t)+u*t by ring,Real.exp_add]
    ring
  · simp [liClockThetaGammaRowDensity,show j≠0 by omega,ht]

private theorem gm_density_tilt {p u : ℝ} (hp : 0<p) (hu : u<p) (j : ℕ) :
    Integrable (fun t => liClockThetaGammaRowDensity p j t * Real.exp (u*t)) ∧
    (∫ t, liClockThetaGammaRowDensity p j t * Real.exp (u*t)) =
      if j=0 then 0 else (p/(p-u))^(2*j) := by
  by_cases hj : j=0
  · simp [liClockThetaGammaRowDensity,hj]
  · have hjpos : 0<j := by omega
    rw [gm_row_tilt_eq hjpos]
    have hr : 0<p-u := sub_pos.mpr hu
    have hg := (integrable_indicator_iff measurableSet_Ioi).mpr
      (gm_power_integrable hr (2*j-1))
    refine ⟨hg.const_mul _,?_⟩
    rw [integral_const_mul,integral_indicator measurableSet_Ioi,
      gm_power_integral hr,if_neg hj]
    have hn : 2*j-1+1=2*j := by omega
    rw [hn,div_pow]
    field_simp

private theorem gm_row_mgf {p u : ℝ} (hp : 0<p) (hu : u<p) (j : ℕ) :
    Integrable (fun t => Real.exp (u*t)) (liClockThetaGammaRowLaw p j) ∧
    (∫ t, Real.exp (u*t) ∂liClockThetaGammaRowLaw p j) = (p/(p-u))^(2*j) := by
  by_cases hj : j=0
  · subst j
    refine ⟨?_,?_⟩
    · exact integrable_dirac (by simp)
    · simp [liClockThetaGammaRowLaw]
  have hjpos : 0<j := by omega
  have hnn := gm_density_nonneg hp j
  have htop : ∀ᵐ t ∂(volume:Measure ℝ),
      ENNReal.ofReal (liClockThetaGammaRowDensity p j t)<∞ := by simp
  have he : (fun t => (ENNReal.ofReal (liClockThetaGammaRowDensity p j t)).toReal •
      Real.exp (u*t)) = (fun t => liClockThetaGammaRowDensity p j t*Real.exp (u*t)) := by
    funext t
    rw [ENNReal.toReal_ofReal (hnn t),smul_eq_mul]
  rw [gm_row_density hjpos]
  refine ⟨(integrable_withDensity_iff_integrable_smul'
    (gm_density_measurable p j).ennreal_ofReal htop).mpr ?_,?_⟩
  · rw [he]
    exact (gm_density_tilt hp hu j).1
  · rw [integral_withDensity_eq_integral_toReal_smul
      (gm_density_measurable p j).ennreal_ofReal htop,he,
      (gm_density_tilt hp hu j).2,if_neg hj]

/-- The zero row is a point mass; positive rows have their literal integer-shape Gamma density. -/
theorem liClockThetaGammaRowLaw_admission {p : ℝ} (hp : 0 < p) (j : ℕ) :
    IsProbabilityMeasure (liClockThetaGammaRowLaw p j) ∧
    (∀ᵐ t ∂liClockThetaGammaRowLaw p j, 0 ≤ t) ∧
    (∀ s : ℝ, 0 ≤ s →
      Integrable (fun t : ℝ => Real.exp (-(s*t))) (liClockThetaGammaRowLaw p j) ∧
      Lap (liClockThetaGammaRowLaw p j) s =
        ENNReal.ofReal ((p/(p+s))^(2*j))) ∧
    (0 < j → liClockThetaGammaRowLaw p j =
      volume.withDensity (fun t => ENNReal.ofReal (liClockThetaGammaRowDensity p j t))) := by
  refine ⟨gm_row_probability hp j,gm_row_support j,?_,fun hj => gm_row_density hj⟩
  intro s hs
  have h := gm_row_mgf hp (by linarith : -s<p) j
  have he : (fun t : ℝ => Real.exp (-(s*t))) = fun t => Real.exp ((-s)*t) := by
    ext t; rw [neg_mul]
  refine ⟨by rw [he]; exact h.1,?_⟩
  unfold GaloisForLFunctions.HTGeometry.laplace
  rw [← ofReal_integral_eq_lintegral_ofReal (by rw [he]; exact h.1)
    (ae_of_all _ (fun _ => (Real.exp_pos _).le)),he,h.2]
  simp only [sub_neg_eq_add]

private theorem gm_mixture_probability {p : ℝ} (hp : 0<p) :
    IsProbabilityMeasure (liClockThetaGammaMixture p) := by
  have hw := gm_weights hp
  refine ⟨?_⟩
  rw [liClockThetaGammaMixture,Measure.sum_apply _ MeasurableSet.univ]
  have he (j : ℕ) : liClockThetaGammaRowLaw p j Set.univ = 1 :=
    (gm_row_probability hp j).measure_univ
  simp_rw [Measure.smul_apply,he,smul_eq_mul,mul_one]
  rw [←ENNReal.ofReal_tsum_of_nonneg (fun j => (hw.1 j).le) hw.2.summable,
    hw.2.tsum_eq]
  simp

private theorem gm_mixture_support (p : ℝ) :
    ∀ᵐ t ∂liClockThetaGammaMixture p, 0≤t := by
  apply Measure.ae_sum_iff.mpr
  intro j
  exact Measure.ae_smul_measure (gm_row_support j) _

private theorem gm_weighted_tilt {p u : ℝ} (hp : 0<p) (hu : u<p) :
    HasSum (fun j : ℕ => liClockThetaDegreeWeight p j*(p/(p-u))^(2*j))
      (liClockThetaGammaNormalizer (p-u)/liClockThetaGammaNormalizer p) := by
  have hz : liClockThetaGammaNormalizer p ≠ 0 :=
    (lt_trans zero_lt_one (gm_normalizer_gt_one hp)).ne'
  have hr : p-u ≠ 0 := (sub_pos.mpr hu).ne'
  apply ((gm_normalizer_hasSum (p-u)).div_const (liClockThetaGammaNormalizer p)).congr_fun
  intro j
  simp only [liClockThetaDegreeWeight,div_pow]
  field_simp [hp.ne',hr,hz]

private theorem gm_mixture_mgf {p u : ℝ} (hp : 0<p) (hu : u<p) :
    Integrable (fun t => Real.exp (u*t)) (liClockThetaGammaMixture p) ∧
    (∫ t, Real.exp (u*t) ∂liClockThetaGammaMixture p) =
      liClockThetaGammaNormalizer (p-u)/liClockThetaGammaNormalizer p := by
  have hw := gm_weights hp
  have hs := gm_weighted_tilt hp hu
  have he (j : ℕ) :
      (∫ t, Real.exp (u*t) ∂(ENNReal.ofReal (liClockThetaDegreeWeight p j) •
        liClockThetaGammaRowLaw p j)) =
      liClockThetaDegreeWeight p j*(p/(p-u))^(2*j) := by
    rw [integral_smul_measure,ENNReal.toReal_ofReal (hw.1 j).le,
      (gm_row_mgf hp hu j).2,smul_eq_mul]
  have hn (j : ℕ) :
      (∫ t, ‖Real.exp (u*t)‖ ∂(ENNReal.ofReal (liClockThetaDegreeWeight p j) •
        liClockThetaGammaRowLaw p j)) =
      liClockThetaDegreeWeight p j*(p/(p-u))^(2*j) := by
    simp_rw [Real.norm_eq_abs,Real.abs_exp]
    exact he j
  have hi : Integrable (fun t => Real.exp (u*t)) (liClockThetaGammaMixture p) := by
    apply integrable_sum_measure
    · intro j
      exact (gm_row_mgf hp hu j).1.smul_measure (by simp)
    · simp_rw [hn]
      exact hs.summable
  refine ⟨hi,?_⟩
  have hh := hasSum_integral_measure hi
  simp_rw [he] at hh
  exact hh.unique hs

private def gm_damped_density (p : ℝ) : ℝ → ℝ :=
  (Ioi (0:ℝ)).indicator (fun t => Real.exp (-(p*t))*deriv liEvenCrossActualClockBorelKernel t)

private theorem gm_density_shift {p : ℝ} (hp : 0<p) {t : ℝ} (ht : 0<t) (r : ℕ) :
    liClockThetaDegreeWeight p (r+1)*liClockThetaGammaRowDensity p (r+1) t =
      (Real.exp (-(p*t))/liClockThetaGammaNormalizer p)*
        ((2*(r+1):ℝ)*liEvenCrossActualClockBorelCoefficient (r+1)*t^(2*r+1)) := by
  have hf : ((2*(r+1)).factorial:ℝ) =
      (2*(r+1):ℝ)*((2*r+1).factorial:ℝ) := by
    rw [show 2*(r+1)= (2*r+1)+1 by omega,Nat.factorial_succ]
    push_cast
    ring
  simp only [liClockThetaDegreeWeight,liClockThetaGammaRowDensity,
    if_neg (show r+1≠0 by omega),indicator_of_mem (show t∈Ioi (0:ℝ) from ht),
    liEvenCrossActualClockBorelCoefficient,show 2*(r+1)-1=2*r+1 by omega]
  have hz : liClockThetaGammaNormalizer p ≠ 0 :=
    (lt_trans zero_lt_one (gm_normalizer_gt_one hp)).ne'
  rw [hf]
  field_simp [hp.ne',hz]

private theorem gm_density_series {p : ℝ} (hp : 0<p) (t : ℝ) :
    HasSum (fun j : ℕ => liClockThetaDegreeWeight p j*liClockThetaGammaRowDensity p j t)
      (gm_damped_density p t/liClockThetaGammaNormalizer p) := by
  by_cases ht : 0<t
  · have hs := ((liEvenCrossActualClockBorel_deriv_series t).2).mul_left
      (Real.exp (-(p*t))/liClockThetaGammaNormalizer p)
    have he : (Real.exp (-(p*t))/liClockThetaGammaNormalizer p)*
        deriv liEvenCrossActualClockBorelKernel t =
        gm_damped_density p t/liClockThetaGammaNormalizer p := by
      simp only [gm_damped_density,indicator_of_mem (show t∈Ioi (0:ℝ) from ht)]
      ring
    rw [he] at hs
    have hh : HasSum (fun r : ℕ => liClockThetaDegreeWeight p (r+1)*
        liClockThetaGammaRowDensity p (r+1) t)
        (gm_damped_density p t/liClockThetaGammaNormalizer p) :=
      hs.congr_fun (gm_density_shift hp ht)
    let f : ℕ → ℝ := fun j => liClockThetaDegreeWeight p j*liClockThetaGammaRowDensity p j t
    have hzero : ∀ j, j∉Set.range Nat.succ → f j=0 := by
      intro j hj
      have hj0 : j=0 := by
        by_contra h
        exact hj ⟨j-1,by dsimp; omega⟩
      simp [f,hj0,liClockThetaGammaRowDensity]
    change HasSum (f∘Nat.succ) (gm_damped_density p t/liClockThetaGammaNormalizer p) at hh
    exact (Nat.succ_injective.hasSum_iff (f:=f) hzero).mp hh
  · simp [liClockThetaGammaRowDensity,gm_damped_density,ht]

private theorem gm_scaled_density_measurable {p : ℝ} (hp : 0<p) :
    Measurable (fun t => gm_damped_density p t/liClockThetaGammaNormalizer p) := by
  have h : Measurable (fun t : ℝ => ∑' j : ℕ,
      liClockThetaDegreeWeight p j*liClockThetaGammaRowDensity p j t) :=
    Measurable.tsum (fun j : ℕ =>
      (gm_density_measurable p j).const_mul (liClockThetaDegreeWeight p j))
  convert h using 1
  ext t
  exact (gm_density_series hp t).tsum_eq.symm

private theorem gm_scaled_density_nonneg {p : ℝ} (hp : 0<p) (t : ℝ) :
    0≤gm_damped_density p t/liClockThetaGammaNormalizer p := by
  rw [←(gm_density_series hp t).tsum_eq]
  exact tsum_nonneg (fun j => mul_nonneg ((gm_weights hp).1 j).le
    (gm_density_nonneg hp j t))

private theorem gm_mixture_scaled_density {p : ℝ} (hp : 0<p) :
    liClockThetaGammaMixture p =
      ENNReal.ofReal (1/liClockThetaGammaNormalizer p) • Measure.dirac 0 +
      volume.withDensity (fun t => ENNReal.ofReal
        (gm_damped_density p t/liClockThetaGammaNormalizer p)) := by
  let c : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal (liClockThetaDegreeWeight p j)
  let ν : ℕ → Measure ℝ := fun j => volume.withDensity
    (fun t => ENNReal.ofReal (liClockThetaDegreeWeight p j*liClockThetaGammaRowDensity p j t))
  have hw := gm_weights hp
  have hj (j : ℕ) : c j • liClockThetaGammaRowLaw p j =
      (if j=0 then c 0 • Measure.dirac 0 else 0) + ν j := by
    by_cases h : j=0
    · subst j
      simp [c,ν,liClockThetaGammaRowLaw,liClockThetaGammaRowDensity]
    · have he : ν j = c j • volume.withDensity
          (fun t : ℝ => ENNReal.ofReal (liClockThetaGammaRowDensity p j t)) := by
        change volume.withDensity (fun t : ℝ => ENNReal.ofReal
          (liClockThetaDegreeWeight p j*liClockThetaGammaRowDensity p j t)) = _
        calc
          _ = volume.withDensity (c j • (fun t : ℝ =>
              ENNReal.ofReal (liClockThetaGammaRowDensity p j t))) := by
            congr 1
            ext t
            dsimp [c]
            exact ENNReal.ofReal_mul (hw.1 j).le
          _ = _ := withDensity_smul (μ:=volume) (c j)
            (gm_density_measurable p j).ennreal_ofReal
      rw [if_neg h,zero_add,he,gm_row_density (by omega : 0<j)]
  have hatom : Measure.sum (fun j : ℕ => if j=0 then c 0 • Measure.dirac (0:ℝ) else 0) =
      c 0 • Measure.dirac (0:ℝ) := by
    ext s hs
    rw [Measure.sum_apply _ hs]
    have hh (j : ℕ) :
        (if j=0 then c 0 • Measure.dirac (0:ℝ) else (0:Measure ℝ)) s =
        if j=0 then (c 0 • Measure.dirac (0:ℝ)) s else 0 := by
      split_ifs <;> rfl
    simp_rw [hh]
    simp only [tsum_ite_eq]
  have hdens : Measure.sum ν = volume.withDensity
      (fun t => ENNReal.ofReal (gm_damped_density p t/liClockThetaGammaNormalizer p)) := by
    have hm (j : ℕ) : Measurable (fun t => ENNReal.ofReal
        (liClockThetaDegreeWeight p j*liClockThetaGammaRowDensity p j t)) :=
      ((gm_density_measurable p j).const_mul _).ennreal_ofReal
    change Measure.sum (fun j : ℕ => volume.withDensity (fun t : ℝ =>
      ENNReal.ofReal (liClockThetaDegreeWeight p j*liClockThetaGammaRowDensity p j t))) = _
    rw [←withDensity_tsum (μ:=volume) hm]
    congr 1
    ext t
    rw [tsum_apply (Pi.summable.mpr (fun _ => ENNReal.summable)),
      ←ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg (hw.1 j).le
        (gm_density_nonneg hp j t)) (gm_density_series hp t).summable,
      (gm_density_series hp t).tsum_eq]
  change Measure.sum (fun j => c j • liClockThetaGammaRowLaw p j) = _
  rw [Measure.sum_congr hj,←Measure.sum_add_sum,hatom,hdens]
  simp [c,liClockThetaDegreeWeight]

private theorem gm_damped_admission {p : ℝ} (hp : 0<p) :
    Integrable (gm_damped_density p) ∧
      (∫ t, gm_damped_density p t) = liClockThetaGammaNormalizer p-1 := by
  let g : ℝ → ℝ := fun t => gm_damped_density p t/liClockThetaGammaNormalizer p
  have hgmeas : Measurable g := gm_scaled_density_measurable hp
  have hgnonneg : ∀ t, 0≤g t := gm_scaled_density_nonneg hp
  have hz : 0<liClockThetaGammaNormalizer p := lt_trans zero_lt_one (gm_normalizer_gt_one hp)
  have hmass : ENNReal.ofReal (1/liClockThetaGammaNormalizer p) +
      (∫⁻ t, ENNReal.ofReal (g t)) = 1 := by
    have h := (gm_mixture_probability hp).measure_univ
    rw [gm_mixture_scaled_density hp,Measure.add_apply,Measure.smul_apply,
      withDensity_apply _ MeasurableSet.univ] at h
    simpa only [Measure.dirac_apply_of_mem (mem_univ (0:ℝ)),smul_eq_mul,mul_one,
      Measure.restrict_univ] using h
  have hbound : (∫⁻ t, ENNReal.ofReal (g t))≤1 := by
    calc
      _ ≤ ENNReal.ofReal (1/liClockThetaGammaNormalizer p)+
        (∫⁻ t, ENNReal.ofReal (g t)) := le_add_left le_rfl
      _ = 1 := hmass
  have hgi : Integrable g := ⟨hgmeas.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ hgnonneg)).mpr
      (hbound.trans_lt (by simp))⟩
  have hgmass : (∫ t, g t) = 1-1/liClockThetaGammaNormalizer p := by
    rw [←ofReal_integral_eq_lintegral_ofReal hgi (ae_of_all _ hgnonneg)] at hmass
    have h := congrArg ENNReal.toReal hmass
    rw [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal (integral_nonneg hgnonneg),ENNReal.toReal_one] at h
    linarith
  have he : gm_damped_density p = fun t => liClockThetaGammaNormalizer p*g t := by
    ext t
    dsimp [g]
    field_simp
  refine ⟨(hgi.const_mul _).congr (ae_of_all _ (congrFun he.symm)),?_⟩
  rw [he,integral_const_mul,hgmass]
  field_simp

private theorem gm_damped_measurable {p : ℝ} (hp : 0<p) :
    Measurable (gm_damped_density p) := by
  have hz : liClockThetaGammaNormalizer p≠0 :=
    (lt_trans zero_lt_one (gm_normalizer_gt_one hp)).ne'
  have h := (gm_scaled_density_measurable hp).const_mul (liClockThetaGammaNormalizer p)
  convert h using 1
  ext t
  field_simp

/-- The full Gamma mixture has its atom and its genuinely integrable actual Borel-derivative density. -/
theorem liClockThetaGammaMixture_density {p : ℝ} (hp : 0 < p) :
    let f : ℝ → ℝ := (Ioi (0 : ℝ)).indicator (fun t =>
      Real.exp (-(p*t)) * deriv liEvenCrossActualClockBorelKernel t)
    Integrable f volume ∧
    (∫ t, f t) = liClockThetaGammaNormalizer p - 1 ∧
    liClockThetaGammaMixture p =
      ENNReal.ofReal (1 / liClockThetaGammaNormalizer p) •
        (Measure.dirac 0 + volume.withDensity (fun t => ENNReal.ofReal (f t))) := by
  change Integrable (gm_damped_density p) ∧
    (∫ t, gm_damped_density p t) = liClockThetaGammaNormalizer p-1 ∧
    liClockThetaGammaMixture p = ENNReal.ofReal (1/liClockThetaGammaNormalizer p) •
      (Measure.dirac 0 + volume.withDensity (fun t => ENNReal.ofReal (gm_damped_density p t)))
  refine ⟨(gm_damped_admission hp).1,(gm_damped_admission hp).2,?_⟩
  have hz : 0<liClockThetaGammaNormalizer p := lt_trans zero_lt_one (gm_normalizer_gt_one hp)
  have he : volume.withDensity (fun t => ENNReal.ofReal
      (gm_damped_density p t/liClockThetaGammaNormalizer p)) =
      ENNReal.ofReal (1/liClockThetaGammaNormalizer p) •
        volume.withDensity (fun t => ENNReal.ofReal (gm_damped_density p t)) := by
    rw [←withDensity_smul _ (gm_damped_measurable hp).ennreal_ofReal]
    congr 1
    ext t
    rw [Pi.smul_apply,smul_eq_mul,←ENNReal.ofReal_mul (by positivity : 0≤1/liClockThetaGammaNormalizer p)]
    congr 1
    ring
  rw [gm_mixture_scaled_density hp,he,smul_add]

/-- The complete mixture is a probability on the nonnegative halfline with its exact zero atom. -/
theorem liClockThetaGammaMixture_admission {p : ℝ} (hp : 0 < p) :
    IsProbabilityMeasure (liClockThetaGammaMixture p) ∧
    (∀ᵐ t ∂liClockThetaGammaMixture p, 0 ≤ t) ∧
    liClockThetaGammaMixture p {0} =
      ENNReal.ofReal (1 / liClockThetaGammaNormalizer p) := by
  refine ⟨gm_mixture_probability hp,gm_mixture_support p,?_⟩
  rw [(liClockThetaGammaMixture_density hp).2.2]
  simp

/-- The normalized reciprocal-source ratio is the Laplace transform of the literal mixture. -/
theorem liClockThetaGammaMixture_laplace {p : ℝ} (hp : 0 < p)
    {s : ℝ} (hs : 0 ≤ s) :
    Lap (liClockThetaGammaMixture p) s =
      ENNReal.ofReal (liClockThetaGammaNormalizer (p+s) /
        liClockThetaGammaNormalizer p) := by
  have h := gm_mixture_mgf hp (by linarith : -s<p)
  have he : (fun t : ℝ => Real.exp (-(s*t))) = fun t => Real.exp ((-s)*t) := by
    ext t; rw [neg_mul]
  unfold GaloisForLFunctions.HTGeometry.laplace
  rw [←ofReal_integral_eq_lintegral_ofReal (by rw [he]; exact h.1)
    (ae_of_all _ (fun _ => (Real.exp_pos _).le)),he,h.2]
  simp only [sub_neg_eq_add]

/-- Every real MGF parameter below the rate is admitted, with common domination on complex disks. -/
theorem liClockThetaGammaMixture_mgf {p : ℝ} (hp : 0 < p) :
    (∀ u : ℝ, u < p →
      Integrable (fun t : ℝ => Real.exp (u*t)) (liClockThetaGammaMixture p) ∧
      (∫ t, Real.exp (u*t) ∂liClockThetaGammaMixture p) =
        liClockThetaGammaNormalizer (p-u) / liClockThetaGammaNormalizer p) ∧
    (∀ ρ : ℝ, 0 ≤ ρ → ρ < p → ∀ u : ℂ, ‖u‖ ≤ ρ →
      Integrable (fun t : ℝ => Complex.exp (u*(t : ℂ))) (liClockThetaGammaMixture p) ∧
      ‖∫ t, Complex.exp (u*(t : ℂ)) ∂liClockThetaGammaMixture p‖ ≤
        liClockThetaGammaNormalizer (p-ρ) / liClockThetaGammaNormalizer p) := by
  refine ⟨fun u hu => gm_mixture_mgf hp hu,?_⟩
  intro ρ hρ hρp u hu
  have h := gm_mixture_mgf hp hρp
  have hdom : ∀ᵐ (t : ℝ) ∂liClockThetaGammaMixture p,
      ‖Complex.exp (u*(t:ℂ))‖ ≤ Real.exp (ρ*t) := by
    filter_upwards [gm_mixture_support p] with t ht
    rw [Complex.norm_exp,Complex.mul_re]
    simp only [Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ((Complex.re_le_norm u).trans hu) ht)
  have hi : Integrable (fun t : ℝ => Complex.exp (u*(t:ℂ)))
      (liClockThetaGammaMixture p) := h.1.mono' (by fun_prop) hdom
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ t, ‖Complex.exp (u*(t:ℂ))‖ ∂liClockThetaGammaMixture p :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t, Real.exp (ρ*t) ∂liClockThetaGammaMixture p := integral_mono_ae hi.norm h.1 hdom
    _ = _ := h.2

end RHTower
