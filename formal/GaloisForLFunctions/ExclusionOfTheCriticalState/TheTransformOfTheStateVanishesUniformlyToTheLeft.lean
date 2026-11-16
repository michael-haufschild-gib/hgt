import GaloisForLFunctions.ExclusionOfTheCriticalState.TheTransformOfTheStateIsMeromorphicInThePlane
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# The state vanishes uniformly to the left

In each head integral the exponential sees the nonnegative distance from the
moving endpoint. Dominated convergence first removes each head, then the Lévy
integral and prime sum. The two charges vanish as well. Thus the continuation
vanishes as its real part tends to minus infinity, uniformly in its imaginary part.
-/

noncomputable section
open MeasureTheory Set Filter Complex Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-- The exponential in a head reads distance from its left endpoint. -/
theorem cexp_mul_levyHead_eq_integral (F : ℝ → ℝ) (p : ℂ) (x : ℝ) :
    cexp (p*x)*levyHead F p x =
      ∫ u in Ioi (-x), cexp (p*((x+u : ℝ) : ℂ))*(F u : ℂ) := by
  rw [levyHead, ← integral_const_mul, integral_Ici_eq_integral_Ioi]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Each head vanishes uniformly in height when its exponent moves to the left. -/
theorem tendsto_cexp_mul_levyHead_left {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (x : ℝ) :
    Tendsto (fun p : ℂ => cexp (p*x)*levyHead F p x)
      (comap Complex.re atBot) (𝓝 0) := by
  have hre : Tendsto Complex.re (comap Complex.re atBot) atBot := tendsto_comap
  simp_rw [cexp_mul_levyHead_eq_integral]
  have h := tendsto_integral_filter_of_dominated_convergence
    (l := comap Complex.re atBot)
    (μ := volume.restrict (Ioi (-x))) (f := fun _ => (0 : ℂ))
    (F := fun (p : ℂ) (u : ℝ) => cexp (p*((x+u : ℝ) : ℂ))*(F u : ℂ))
    (fun u => |F u|) ?_ ?_ hF.integrable.abs.integrableOn ?_
  · simpa only [integral_zero] using h
  · exact Eventually.of_forall fun p =>
      ((by fun_prop : Continuous fun u : ℝ => cexp (p*((x+u : ℝ) : ℂ))).measurable.mul
        (Complex.measurable_ofReal.comp hF.meas)).aestronglyMeasurable
  · filter_upwards [hre.eventually (eventually_le_atBot 0)] with p hp
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
    rw [norm_mul,norm_cexp_mul_ofReal,Complex.norm_real,Real.norm_eq_abs]
    have he : Real.exp (p.re*(x+u)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg hp (by linarith only [mem_Ioi.mp hu]))
    simpa only [one_mul] using mul_le_mul_of_nonneg_right he (abs_nonneg (F u))
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
    have hxu : 0 < x+u := by linarith only [mem_Ioi.mp hu]
    have he : Tendsto (fun p : ℂ => cexp (p*((x+u : ℝ) : ℂ))) (comap Complex.re atBot) (𝓝 0) := by
      apply Complex.tendsto_exp_nhds_zero_iff.mpr
      simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,mul_comm]
        using hre.const_mul_atBot hxu
    simpa only [zero_mul] using he.mul_const (F u : ℂ)

/-- The full Lévy head tends to zero uniformly throughout far-left half-planes. -/
theorem tendsto_levyHeadTerm_left {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    Tendsto (levyHeadTerm F) (comap Complex.re atBot) (𝓝 0) := by
  have hre : Tendsto Complex.re (comap Complex.re atBot) atBot := tendsto_comap
  obtain ⟨g,hg,hgb⟩ := exists_levyHeadTerm_dominator hF (σ := 0) le_rfl (by norm_num)
  have h := tendsto_integral_filter_of_dominated_convergence
    (l := comap Complex.re atBot)
    (μ := volume.restrict (Ioi (0 : ℝ))) (f := fun _ => (0 : ℂ))
    (F := fun (p : ℂ) (x : ℝ) => (archLevyDensity x : ℂ)*(cexp (p*x)*levyHead F p x))
    g ?_ ?_ hg ?_
  · change Tendsto (fun p => levyHeadTerm F p) _ _
    simpa only [integral_zero,levyHeadTerm] using h
  · exact Eventually.of_forall fun p =>
      ((Complex.measurable_ofReal.comp measurable_archLevyDensity').stronglyMeasurable.mul
        ((by fun_prop : Continuous fun x : ℝ => cexp (p*x)).stronglyMeasurable.mul
          (stronglyMeasurable_levyHead hF.meas p))).aestronglyMeasurable
  · filter_upwards [hre.eventually (eventually_le_atBot 0)] with p hp
    exact (ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun x hx => hgb x hx p hp)
  · exact Eventually.of_forall fun x => by
      simpa only [mul_zero] using (tendsto_cexp_mul_levyHead_left hF x).const_mul
        (archLevyDensity x : ℂ)

/-- Confinement makes the vanishing of individual prime heads summable. -/
theorem tendsto_primeHead_left {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    Tendsto (primeHead F) (comap Complex.re atBot) (𝓝 0) := by
  have hre : Tendsto Complex.re (comap Complex.re atBot) atBot := tendsto_comap
  have h := tendsto_tsum_of_dominated_convergence
    (𝓕 := comap Complex.re atBot)
    (f := fun (p : ℂ) (n : ℕ) => (vonMangoldtAtom n : ℂ)*
      (cexp (p*Real.log n)*levyHead F p (Real.log n))) (g := fun _ => (0 : ℂ))
    (summable_primeHead_bound (F := F) (σ := -1) (by norm_num)) ?_ ?_
  · change Tendsto (fun p => primeHead F p) _ _
    simpa only [tsum_zero,primeHead] using h
  · intro n
    simpa only [mul_zero] using (tendsto_cexp_mul_levyHead_left hF (Real.log n)).const_mul
      (vonMangoldtAtom n : ℂ)
  · filter_upwards [hre.eventually (eventually_le_atBot (-1))] with p hp n
    exact norm_primeHead_term_le hF (by norm_num : (-4 : ℝ) < -1) hp n

/-- Moving left makes the norm of every fixed affine denominator diverge. -/
theorem tendsto_norm_sub_left (z : ℂ) :
    Tendsto (fun p : ℂ => ‖p-z‖) (comap Complex.re atBot) atTop := by
  have hre : Tendsto Complex.re (comap Complex.re atBot) atBot := tendsto_comap
  refine tendsto_atTop.mpr fun R => ?_
  filter_upwards [hre.eventually (eventually_le_atBot (z.re-R))] with p hp
  calc
    R ≤ z.re-p.re := by linarith
    _ ≤ |(p-z).re| := by
      rw [Complex.sub_re]
      simpa only [neg_sub] using neg_le_abs (p.re-z.re)
    _ ≤ ‖p-z‖ := Complex.abs_re_le_norm _

/-- Both wall charges vanish uniformly in imaginary part. -/
theorem tendsto_charge_left (C z : ℂ) :
    Tendsto (fun p : ℂ => C/(p-z)) (comap Complex.re atBot) (𝓝 0) := by
  have hi : Tendsto (fun p : ℂ => (p-z)⁻¹) (comap Complex.re atBot) (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [Function.comp_def,norm_inv] using tendsto_inv_atTop_zero.comp (tendsto_norm_sub_left z)
  simpa only [div_eq_mul_inv,mul_zero] using hi.const_mul C

/-- Head, prime heads and charges all vanish on far-left half-planes. -/
theorem tendsto_leftRemainder_left {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    Tendsto (leftRemainder F) (comap Complex.re atBot) (𝓝 0) := by
  have h1 := tendsto_charge_left (negativeHalfLineLaplace (cx F) (1/2)) (1/2)
  have h2 := tendsto_charge_left (negativeHalfLineLaplace (cx F) (-(1/2))) (-(1/2))
  change Tendsto (fun p => leftRemainder F p) _ _
  simpa only [leftRemainder,sub_neg_eq_add,add_zero] using
    (((tendsto_levyHeadTerm_left hF).add (tendsto_primeHead_left hF)).add h1).add h2

/-- The meromorphic continuation tends to zero as `Re w → -∞`, with no height restriction. -/
theorem tendsto_stateMeromorphic_left {W₀ : ℝ} {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) :
    Tendsto (stateMeromorphic W₀ F) (comap Complex.re atBot) (𝓝 0) := by
  have hre : Tendsto Complex.re (comap Complex.re atBot) atBot := tendsto_comap
  have ht : Tendsto (fun w : ℂ => w+8) (comap Complex.re atBot) (comap Complex.re atBot) := by
    apply tendsto_comap_iff.mpr
    refine tendsto_atBot.mpr fun R => ?_
    filter_upwards [hre.eventually (eventually_le_atBot (R-8))] with w hw
    change w.re + 8 ≤ R
    linarith
  have h : Tendsto (fun w : ℂ => -leftRemainder F (w+8) / criticalAliasCoefficient W₀)
      (comap Complex.re atBot) (𝓝 0) := by
    simpa only [Function.comp_def,neg_zero,zero_div] using
      ((tendsto_leftRemainder_left hF).comp ht).neg.div_const (criticalAliasCoefficient W₀ : ℂ)
  refine h.congr' ?_
  filter_upwards [hre.eventually (eventually_lt_atBot (-(17/2)))] with w hw
  exact (stateMeromorphic_eq_left hw).symm

/-- Every sufficiently far-left half-plane has arbitrarily small continuation,
with no restriction on imaginary part. -/
theorem exists_left_halfPlane_norm_stateMeromorphic_lt {W₀ : ℝ} {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℝ, ∀ w : ℂ, w.re ≤ A → ‖stateMeromorphic W₀ F w‖ < ε := by
  have he := Metric.tendsto_nhds.mp (tendsto_stateMeromorphic_left (W₀ := W₀) hF) ε hε
  obtain ⟨s,hs,hsub⟩ := mem_comap.mp he
  obtain ⟨A,hA⟩ := mem_atBot_sets.mp hs
  refine ⟨A,fun w hw => ?_⟩
  have hb : dist (stateMeromorphic W₀ F w) 0 < ε := hsub (hA w.re hw)
  simpa only [dist_zero_right] using hb

end GaloisForLFunctions.ExclusionOfTheCriticalState
