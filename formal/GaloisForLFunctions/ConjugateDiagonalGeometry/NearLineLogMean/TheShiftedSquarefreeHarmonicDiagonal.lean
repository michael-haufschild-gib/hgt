import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheConstantTermOfTheSquarefreeHarmonicDiagonal
import GaloisForLFunctions.RHTower.OscillatoryLogIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Small frequency shifts of the squarefree harmonic diagonal

Abel summation with El Kaouni's Mellin weight keeps the oscillatory
integral and the arithmetic finite part separate. This identifies the
entire scale u/log X of the critical Möbius diagonal, including
frequencies for which the leading integral is exactly zero.
-/
noncomputable section
open Finset Complex MeasureTheory Set Filter
open scoped Topology Interval
open RHTower.Sieve (squarefreeDensity)
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

private def coeff (n : ℕ) : ℝ := ((ArithmeticFunction.moebius n:ℤ):ℝ)^2/(n:ℝ)
private theorem coeff_zero : coeff 0=0 := by simp [coeff]
private theorem start_zero (N : ℕ) (g : ℕ → ℂ) (hg : g 0=0) :
    ∑ n∈Finset.Icc 0 N,g n=∑ n∈Finset.Icc 1 N,g n := by
  rw [←Nat.range_succ_eq_Icc_zero,Finset.sum_range_succ',hg,add_zero,
    RHTower.sum_Icc_eq_sum_range_shift]

/-- Harmonic squarefree mass observed through a complex scalar filter. -/
def weightedSquarefree (X : ℝ) (g : ℝ → ℂ) : ℂ :=
  ∑ n∈Finset.Icc 1 ⌊X⌋₊,g n*(coeff n:ℂ)

private def model (x : ℝ) : ℂ :=
  ((squarefreeDensity*Real.log x+squarefreeHarmonicConstant:ℝ):ℂ)
private def remainder (x : ℝ) := (harmonicMoebiusDiagonal x:ℂ)-model x
private theorem remainder_norm {x : ℝ} (hx : 1≤x) :
    ‖remainder x‖ ≤ 12*x^(-(1/2:ℝ)) := by
  simpa only [remainder,model,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
    sub_add_eq_sub_sub] using squarefree_harmonic_finite_part hx

private theorem remainder_measurable : Measurable remainder := by
  have hh : Measurable harmonicMoebiusDiagonal :=
    (measurable_of_countable (fun N : ℕ => ∑ n∈Finset.Icc 1 N,coeff n)).comp Nat.measurable_floor
  exact (Complex.continuous_ofReal.measurable.comp hh).sub (by unfold model;fun_prop)

private theorem derivative_model {x : ℝ} (hx : 0<x) :
    HasDerivAt model ((squarefreeDensity:ℂ)/(x:ℂ)) x := by
  have hlog : HasDerivAt (fun t : ℝ => (Real.log t:ℂ)) ((x⁻¹:ℝ):ℂ) x :=
    (Real.hasDerivAt_log hx.ne').ofReal_comp
  have he : model=fun t : ℝ => (squarefreeDensity:ℂ)*(Real.log t:ℂ)+(squarefreeHarmonicConstant:ℂ) := by
    funext t
    simp only [model,Complex.ofReal_add,Complex.ofReal_mul]
  rw [he,div_eq_mul_inv,←Complex.ofReal_inv]
  exact (hlog.const_mul _).add_const _

private theorem weighted_abel (g g' : ℝ → ℂ) {X : ℝ}
    (hg : ∀ x∈Set.Icc 1 X,HasDerivAt g (g' x) x)
    (hc : ContinuousOn g' (Set.Icc 1 X)) :
    weightedSquarefree X g = g X*(harmonicMoebiusDiagonal X:ℂ) -
      ∫ x in Set.Ioc 1 X,g' x*(harmonicMoebiusDiagonal x:ℂ) := by
  let c := fun n : ℕ => (coeff n:ℂ)
  have hder : IntegrableOn (deriv g) (Set.Icc 1 X) :=
    (hc.integrableOn_compact (μ:=volume) isCompact_Icc).congr_fun (fun x hx => (hg x hx).deriv.symm) measurableSet_Icc
  have h := sum_mul_eq_sub_integral_mul₀ c (by simp [c,coeff_zero]) X
    (fun t ht => (hg t ht).differentiableAt) hder
  have hsum (x : ℝ) : (∑ n∈Finset.Icc 0 ⌊x⌋₊,c n)=(harmonicMoebiusDiagonal x:ℂ) := by
    rw [start_zero _ c (by simp [c,coeff_zero])]
    simp only [harmonicMoebiusDiagonal,Complex.ofReal_sum,c,coeff,Complex.ofReal_div,Complex.ofReal_pow]
  simp only [hsum] at h
  rw [start_zero _ (fun n => g n*c n) (by simp [c,coeff_zero])] at h
  refine h.trans (congrArg (g X*(harmonicMoebiusDiagonal X:ℂ)-·) ?_)
  exact setIntegral_congr_fun measurableSet_Ioc fun x hx => by rw [(hg x ⟨hx.1.le,hx.2⟩).deriv]

private theorem error_envelope (g' : ℝ → ℂ) {D x : ℝ} (hx : 1≤x) (hD : x*‖g' x‖≤D) :
    ‖g' x*remainder x‖ ≤ 12*D*x^(-(3/2:ℝ)) := by
  have hp := zero_lt_one.trans_le hx
  have hg : ‖g' x‖≤D/x := (le_div_iff₀ hp).mpr ((mul_comm _ _).le.trans hD)
  rw [norm_mul]
  refine (mul_le_mul hg (remainder_norm hx) (norm_nonneg _) (div_nonneg
    ((mul_nonneg hp.le (norm_nonneg _)).trans hD) hp.le)).trans_eq ?_
  rw [div_eq_mul_inv,←Real.rpow_neg_one]
  calc _ = 12*D*(x^(-1:ℝ)*x^(-(1/2:ℝ))) := by ring
       _ = _ := by rw [←Real.rpow_add hp];norm_num

/-- A weight varying at logarithmic speed D preserves the endpoint
constant up to 24D. The boundary at the upper cutoff costs only
12 times its absolute value divided by the square root of the cutoff. -/
theorem squarefree_logarithmic_test {X D : ℝ} (hX : 1≤X) (g g' : ℝ → ℂ)
    (hg : ∀ x∈Set.Icc 1 X,HasDerivAt g (g' x) x)
    (hc : ContinuousOn g' (Set.Icc 1 X)) (hbound : ∀ x∈Set.Icc 1 X,x*‖g' x‖≤D) :
    ‖weightedSquarefree X g - (squarefreeDensity:ℂ)*(∫ x in Set.Ioc 1 X,g x/(x:ℂ)) -
      (squarefreeHarmonicConstant:ℂ)*g 1‖ ≤
      12*X^(-(1/2:ℝ))*‖g X‖+24*D := by
  let S := Set.Ioc 1 X
  have hD : 0≤D := (by simpa only [one_mul] using norm_nonneg (g' 1) : 0≤1*‖g' 1‖).trans
    (hbound 1 ⟨le_rfl,hX⟩)
  have hmodel : ContinuousOn model (Set.Icc 1 X) := fun x hx =>
    (derivative_model (zero_lt_one.trans_le hx.1)).continuousAt.continuousWithinAt
  have hgc : ContinuousOn g (Set.Icc 1 X) := fun x hx => (hg x hx).continuousAt.continuousWithinAt
  have hq : ContinuousOn (fun x : ℝ => g x/(x:ℂ)) (Set.Icc 1 X) :=
    hgc.div Complex.continuous_ofReal.continuousOn fun x hx => Complex.ofReal_ne_zero.mpr (zero_lt_one.trans_le hx.1).ne'
  have intU : IntegrableOn (fun x => g' x*model x) S := ((hc.mul hmodel).integrableOn_compact (μ:=volume) isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  have intQ : IntegrableOn (fun x : ℝ => g x/(x:ℂ)) S := (hq.integrableOn_compact (μ:=volume) isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  let b := fun x : ℝ => (12*D)*x^(-(3/2:ℝ))
  have hb : IntegrableOn b (Set.Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : -(3/2:ℝ)< -1) zero_lt_one).const_mul (12*D)
  have hle (x : ℝ) (hx : x∈S) := error_envelope g' hx.1.le (hbound x ⟨hx.1.le,hx.2⟩)
  have hI : IntegrableOn (fun x => g' x*remainder x) S := by
    refine (hb.mono_set Set.Ioc_subset_Ioi_self).mono' ?_ ?_
    · exact ((hc.mono Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc).mul
        remainder_measurable.aestronglyMeasurable.restrict
    · exact (ae_restrict_iff' measurableSet_Ioc).mpr (.of_forall hle)
  have hint : ‖∫ x in S,g' x*remainder x‖ ≤ 24*D := by
    apply (norm_integral_le_integral_norm _).trans
    apply (setIntegral_mono_on hI.norm (hb.mono_set Set.Ioc_subset_Ioi_self) measurableSet_Ioc hle).trans
    have hpos : 0 ≤ᵐ[volume.restrict (Set.Ioi (1:ℝ))] b := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact mul_nonneg (mul_nonneg (by norm_num) hD) (Real.rpow_nonneg (zero_lt_one.trans hx).le _)
    have hh := setIntegral_mono_set hb hpos
      (show S ⊆ Set.Ioi (1:ℝ) from Set.Ioc_subset_Ioi_self).eventuallyLE
    refine hh.trans_eq ?_
    dsimp only [b]
    rw [integral_const_mul,integral_Ioi_rpow_of_lt (by norm_num) zero_lt_one]
    norm_num
    ring
  let H := fun x => (squarefreeDensity:ℂ)*(g x/(x:ℂ)) + g' x*model x
  have hd (x : ℝ) (hx : x∈Set.Icc 1 X) : HasDerivAt (fun t => g t*model t) (H x) x := by
    refine ((hg x hx).mul (derivative_model (zero_lt_one.trans_le hx.1))).congr_deriv ?_
    dsimp only [H];ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=1) (b:=X)
    (fun x hx => hd x (Set.uIcc_of_le hX ▸ hx))
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hX).mpr ((intQ.const_mul (squarefreeDensity:ℂ)).add intU))
  rw [intervalIntegral.integral_of_le hX] at hFTC
  change (∫ x in S,(squarefreeDensity:ℂ)*(g x/(x:ℂ))+g' x*model x)=_ at hFTC
  rw [integral_add (intQ.const_mul (squarefreeDensity:ℂ)) intU,integral_const_mul] at hFTC
  have h1 : model 1=(squarefreeHarmonicConstant:ℂ) := by simp [model]
  rw [h1] at hFTC
  have hsplit : (∫ x in S,g' x*(harmonicMoebiusDiagonal x:ℂ)) =
      (∫ x in S,g' x*model x)+(∫ x in S,g' x*remainder x) := by
    rw [←integral_add intU hI]; apply setIntegral_congr_fun measurableSet_Ioc
    intro x _; unfold remainder;ring
  rw [weighted_abel g g' hg hc]
  change ‖g X*(harmonicMoebiusDiagonal X:ℂ)- (∫ x in S,_) - _ - _‖ ≤ _
  rw [hsplit]
  have he : g X*(harmonicMoebiusDiagonal X:ℂ)-((∫ x in S,g' x*model x)+(∫ x in S,g' x*remainder x))-
      (squarefreeDensity:ℂ)*(∫ x in S,g x/(x:ℂ))-(squarefreeHarmonicConstant:ℂ)*g 1 =
      g X*remainder X-(∫ x in S,g' x*remainder x) := by
    unfold remainder;linear_combination -hFTC
  rw [he]
  apply (norm_sub_le _ _).trans (add_le_add _ hint)
  rw [norm_mul,mul_comm]
  exact mul_le_mul_of_nonneg_right (remainder_norm hX) (norm_nonneg _)


open _root_.RHTower (logPhase norm_logPhase hasDerivAt_logPhase continuousAt_logPhase
  logPhaseAntideriv hasDerivAt_logPhaseAntideriv)

/-- Fourier transform of the uniform probability measure on the unit interval. -/
def unitLogWindow (v : ℝ) : ℂ := ∫ u in (0:ℝ)..1, Complex.exp (-(v:ℂ)*I*(u:ℂ))

private theorem phase_integral {X : ℝ} (hX : 1<X) (h : ℝ) :
    (∫ x in Set.Ioc 1 X,logPhase h x/(x:ℂ)) =
      (Real.log X:ℂ)*unitLogWindow (h*Real.log X) := by
  have hL := Real.log_pos hX
  by_cases hz : h=0
  · subst h
    have hlog : (∫ x in Set.Ioc 1 X,(x:ℂ)⁻¹)=(Real.log X:ℂ) := by
      simp_rw [←Complex.ofReal_inv]
      rw [integral_complex_ofReal,←intervalIntegral.integral_of_le hX.le,
        integral_inv_of_pos zero_lt_one (zero_lt_one.trans hX),div_one]
    simpa only [logPhase,Complex.ofReal_zero,neg_zero,zero_mul,Complex.exp_zero,
      one_div,unitLogWindow,intervalIntegral.integral_const,sub_zero,one_smul,mul_one] using hlog
  have hg : ContinuousOn (logPhase h) (Set.Icc 1 X) := fun x hx =>
    (continuousAt_logPhase h (zero_lt_one.trans_le hx.1).ne').continuousWithinAt
  have hi : IntervalIntegrable (fun x : ℝ => logPhase h x*((x⁻¹:ℝ):ℂ)) volume 1 X := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hX.le).mpr
    exact ((hg.mul (Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_id.inv₀ (fun x hx => (zero_lt_one.trans_le hx.1).ne')))).integrableOn_compact isCompact_Icc)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=1) (b:=X)
    (fun t ht => hasDerivAt_logPhaseAntideriv hz (zero_lt_one.trans_le ((Set.uIcc_of_le hX.le ▸ ht : t∈Set.Icc 1 X).1))) hi
  rw [intervalIntegral.integral_of_le hX.le] at hFTC
  simp only [div_eq_mul_inv,Complex.ofReal_inv] at hFTC ⊢
  rw [hFTC,unitLogWindow,integral_exp_mul_complex (mul_ne_zero
    (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (mul_ne_zero hz hL.ne'))) Complex.I_ne_zero)]
  simp only [logPhaseAntideriv,logPhase,Real.log_one,Complex.ofReal_zero,Complex.ofReal_one,
    Complex.ofReal_mul,mul_one,mul_zero,Complex.exp_zero]
  rw [show -((h:ℂ)*(Real.log X:ℂ))*I=-(h:ℂ)*I*(Real.log X:ℂ) by ring]
  have hlc := Complex.ofReal_ne_zero.mpr hL.ne'
  have hhc := Complex.ofReal_ne_zero.mpr hz
  field_simp [hlc,hhc,Complex.I_ne_zero]
  ring

/-- The complete microscopic shift profile of the sharp diagonal, with a
uniform error at every real frequency h and real cutoff X > 1. -/
theorem squarefree_shifted_diagonal {X : ℝ} (hX : 1<X) (h : ℝ) :
    ‖weightedSquarefree X (logPhase h) -
      (squarefreeDensity:ℂ)*(Real.log X:ℂ)*unitLogWindow (h*Real.log X) -
      (squarefreeHarmonicConstant:ℂ)‖ ≤ 12*X^(-(1/2:ℝ))+24*|h| := by
  let g' := fun t : ℝ => logPhase h t * (-(h:ℂ)*I*((t⁻¹:ℝ):ℂ))
  have hg : ContinuousOn (logPhase h) (Set.Icc 1 X) := fun x hx =>
    (continuousAt_logPhase h (zero_lt_one.trans_le hx.1).ne').continuousWithinAt
  have hc : ContinuousOn g' (Set.Icc 1 X) := hg.mul (continuousOn_const.mul
    (Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_id.inv₀ fun x hx => (zero_lt_one.trans_le hx.1).ne')))
  have hd (x : ℝ) (hx : x∈Set.Icc 1 X) : x*‖g' x‖ ≤ |h| := by
    have hp := zero_lt_one.trans_le hx.1
    simp only [g',norm_mul,norm_logPhase,norm_neg,Complex.norm_real,Real.norm_eq_abs,
      Complex.norm_I,mul_one,one_mul,abs_inv,abs_of_pos hp]
    exact (show x*((abs h)*x⁻¹)=abs h by field_simp).le
  have hb := squarefree_logarithmic_test hX.le _ g'
    (fun x hx => hasDerivAt_logPhase (zero_lt_one.trans_le hx.1)) hc hd
  rw [phase_integral hX h,←mul_assoc,norm_logPhase,
    show logPhase h 1=1 by simp [logPhase],mul_one,mul_one] at hb
  exact hb

/-- The same arithmetic constant survives every sequence of height
shifts tending to zero, after subtracting its exact Fourier main term. -/
theorem squarefree_vanishing_shift_limit {h : ℝ → ℝ} (hh : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun X : ℝ => weightedSquarefree X (logPhase (h X)) -
      (squarefreeDensity:ℂ)*(Real.log X:ℂ)*unitLogWindow (h X*Real.log X)) atTop
      (𝓝 (squarefreeHarmonicConstant:ℂ)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hr := (tendsto_rpow_neg_atTop (by norm_num : 0<(1/2:ℝ))).const_mul 12
  have ht := hr.add (hh.abs.const_mul 24)
  simp only [abs_zero,mul_zero,add_zero] at ht
  exact squeeze_zero' (.of_forall fun _ => norm_nonneg _) ((eventually_gt_atTop (1:ℝ)).mono
    fun X hX => squarefree_shifted_diagonal hX (h X)) ht

/-- Every nonzero integer Fourier harmonic cancels the entire logarithmic main term. -/
theorem unitLogWindow_nonzero_harmonic {k : ℤ} (hk : k≠0) :
    unitLogWindow ((k:ℝ)*(2*Real.pi))=0 := by
  have hc : (-(↑((k:ℝ)*(2*Real.pi)):ℂ)*I)≠0 := mul_ne_zero (neg_ne_zero.mpr
    (Complex.ofReal_ne_zero.mpr (mul_ne_zero (by exact_mod_cast hk) (mul_ne_zero (by norm_num) Real.pi_ne_zero)))) I_ne_zero
  rw [unitLogWindow,integral_exp_mul_complex hc]
  simp only [Complex.ofReal_zero,Complex.ofReal_one,mul_zero,mul_one,Complex.exp_zero,
    Complex.ofReal_mul,Complex.ofReal_ofNat,Complex.ofReal_intCast]
  rw [show -((k:ℂ)*(2*(Real.pi:ℂ)))*I = -(k*(2*(Real.pi:ℂ)*I)) by ring,
    Complex.exp_neg,Complex.exp_int_mul_two_pi_mul_I,inv_one,sub_self,zero_div]

/-- A moving nonzero lattice harmonic of order o(log X) isolates the
regular part of ζ(s)/ζ(2s) without subtracting a main term. -/
theorem squarefree_harmonic_null_reading (k : ℝ → ℤ) (hk : ∀ᶠ X in atTop,k X≠0)
    (hslow : Tendsto (fun X : ℝ => (k X:ℝ)/Real.log X) atTop (𝓝 0)) :
    Tendsto (fun X : ℝ => weightedSquarefree X (logPhase ((k X:ℝ)/Real.log X*(2*Real.pi))))
      atTop (𝓝 (squarefreeHarmonicConstant:ℂ)) := by
  have ht := squarefree_vanishing_shift_limit (by simpa only [zero_mul] using hslow.mul_const (2*Real.pi))
  apply ht.congr'
  filter_upwards [hk,eventually_gt_atTop (1:ℝ)] with X hX hX'
  rw [show (k X:ℝ)/Real.log X*(2*Real.pi)*Real.log X=(k X:ℝ)*(2*Real.pi) by
    field_simp [(Real.log_pos hX').ne'],unitLogWindow_nonzero_harmonic hX,mul_zero,sub_zero]

#print axioms squarefree_shifted_diagonal
#print axioms squarefree_vanishing_shift_limit
#print axioms squarefree_harmonic_null_reading

#print axioms squarefree_logarithmic_test
end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
