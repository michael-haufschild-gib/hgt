import GaloisForLFunctions.RHTower.SquarefreeDiscrepancyMellin
import GaloisForLFunctions.RHTower.MertensSecondTheorem
import GaloisForLFunctions.RHTower.ReflectionCocycleClass
import GaloisForLFunctions.RHTower.PrimeLogIncommensuratePhaseClock
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Squarefree Dirichlet sections with the density pole removed

The Abel summation step in El Kaouni, Proposition F.2, separates
a continuous density from its counting discrepancy. Substitution of the squarefree
count gives a uniform truncation inequality throughout Re s > 1/2,
including the removable point s=1.
-/
noncomputable section
open Finset Complex MeasureTheory Filter
open scoped Topology ComplexConjugate
open _root_.RHTower.SquarefreeDiscrepancy (count error moment)
open _root_.RHTower.Sieve (squarefreeDensity)
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

private def countingAtom (n : ℕ) : ℝ := ((ArithmeticFunction.moebius n:ℤ):ℝ)^2

/-- Ordinary real-cutoff squarefree Dirichlet polynomial. The atom at zero
vanishes, so the sum also agrees with the positive-index section. -/
def squarefreeSection (X : ℝ) (s : ℂ) :=
  ∑ n∈Icc 0 ⌊X⌋₊,(n:ℂ)^(-s)*(countingAtom n:ℂ)

theorem squarefreeSection_eq_positive (X : ℝ) (s : ℂ) :
    squarefreeSection X s=∑ n∈Icc 1 ⌊X⌋₊,(n:ℂ)^(-s)*((((ArithmeticFunction.moebius n:ℤ):ℝ)^2:ℝ):ℂ) := by
  rw [squarefreeSection,←Nat.range_succ_eq_Icc_zero,sum_range_succ',
    _root_.RHTower.sum_Icc_eq_sum_range_shift]
  simp [countingAtom]

/-- The density pole removed from a finite or infinite Mellin transform. -/
def squarefreeRegularPart (s : ℂ) : ℂ := (squarefreeDensity:ℂ)+s*moment s

/-- Holomorphic continuation of the regular part through one. -/
theorem differentiableAt_squarefreeRegularPart {s : ℂ} (hs : 1/2<s.re) :
    DifferentiableAt ℂ squarefreeRegularPart s :=
  (differentiableAt_const _).add (differentiableAt_id.mul (_root_.RHTower.SquarefreeDiscrepancy.differentiableAt_moment hs))

theorem squarefreeRegularPart_eq_quotient {s : ℂ} (hs : 1/2<s.re) (hne : s≠1) :
    squarefreeRegularPart s = riemannZeta s / riemannZeta (2*s) - (squarefreeDensity:ℂ)/(s-1) := by
  have hn : s≠0 := by rintro rfl; norm_num at hs
  have hz : riemannZeta (2*s)≠0 := riemannZeta_ne_zero_of_one_lt_re (by
    simp only [two_mul,Complex.add_re];linarith)
  rw [squarefreeRegularPart,_root_.RHTower.SquarefreeDiscrepancy.moment_eq_quotient hs hne]
  field_simp [hn,hz,sub_ne_zero.mpr hne]
  <;> ring

private theorem count_eq_prefix (x : ℝ) :
    (∑ n∈Icc 0 ⌊x⌋₊,(countingAtom n:ℂ))=(count x:ℂ) := by
  rw [count,Complex.ofReal_sum,←Nat.range_succ_eq_Icc_zero,sum_range_succ',
    _root_.RHTower.sum_Icc_eq_sum_range_shift]
  simp [countingAtom]

/-- Counting discrepancy against the differentiated power weight. -/
def weightedCountError (s : ℂ) (x : ℝ) := (error x:ℂ)*(x:ℂ)^(-(s+1))

private theorem abel_counting {X : ℝ} (hX : 1≤X) {s : ℂ} (hs : 1/2<s.re) :
    squarefreeSection X s = (X:ℂ)^(-s)*(count X:ℂ)+s*
      (∫ t in Set.Ioc 1 X,(count t:ℂ)*(t:ℂ)^(-(s+1))) := by
  have hs0 : s≠0 := by rintro rfl;norm_num at hs
  have hd (t : ℝ) (ht : t∈Set.Icc 1 X) : HasDerivAt (fun x : ℝ => (x:ℂ)^(-s))
      ((-s)*(t:ℂ)^(-s-1)) t :=
    hasDerivAt_ofReal_cpow_const (zero_lt_one.trans_le ht.1).ne' (neg_ne_zero.mpr hs0)
  have hc : ContinuousOn (fun t : ℝ => (t:ℂ)^(-s-1)) (Set.Icc 1 X) := fun x hx =>
    (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr (zero_lt_one.trans_le hx.1).ne')).continuousWithinAt
  have hi : IntegrableOn (deriv fun t : ℝ => (t:ℂ)^(-s)) (Set.Icc 1 X) :=
    (((continuousOn_const.mul hc).integrableOn_compact (μ:=volume) isCompact_Icc :
      IntegrableOn (fun t : ℝ => -s*(t:ℂ)^(-s-1)) (Set.Icc 1 X))).congr_fun
      (fun t ht => (hd t ht).deriv.symm) measurableSet_Icc
  have h := sum_mul_eq_sub_integral_mul₀ (fun n => (countingAtom n:ℂ)) (by simp [countingAtom])
    X (fun t ht => (hd t ht).differentiableAt) hi
  simp only [count_eq_prefix] at h
  change squarefreeSection X s = _ at h
  rw [h]
  have hc' : (∫ t in Set.Ioc 1 X,deriv (fun t : ℝ => (t:ℂ)^(-s)) t*(count t:ℂ)) =
      (-s)*(∫ t in Set.Ioc 1 X,(count t:ℂ)*(t:ℂ)^(-(s+1))) := by
    rw [←integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    rw [(hd t ⟨ht.1.le,ht.2⟩).deriv,show -s-1=-(s+1) by ring]
    ring
  rw [hc'];ring

private theorem continuous_cpow_positive (s : ℂ) {X : ℝ} :
    ContinuousOn (fun t : ℝ => (t:ℂ)^s) (Set.Icc 1 X) := fun t ht =>
  (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr (zero_lt_one.trans_le ht.1).ne')).continuousWithinAt

private theorem power_step (s : ℂ) {x : ℝ} (hx : 0<x) :
    (x:ℂ)*(x:ℂ)^s=(x:ℂ)^(1+s) := by
  rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne'),Complex.cpow_one]

theorem squarefree_density_primitive {X : ℝ} (hX : 1≤X) (s : ℂ) :
    (X:ℂ)^(1-s)-1=(1-s)*(∫ t in Set.Ioc 1 X,(t:ℂ)^(-s)) := by
  by_cases he : s=1
  · subst s;simp
  have hz : (0:ℝ)∉Set.uIcc 1 X := by rw [Set.uIcc_of_le hX];simp
  have h := integral_cpow (r:=-s) (a:=1) (b:=X) (Or.inr ⟨neg_injective.ne he,hz⟩)
  rw [intervalIntegral.integral_of_le hX] at h
  simp only [Complex.ofReal_one,Complex.one_cpow,show -s+1=1-s by ring] at h
  rw [h,mul_comm (1-s),div_mul_cancel₀ _ (sub_ne_zero.mpr (Ne.symm he))]

/-- Exact finite part, with an upper-endpoint jump and a discrepancy-tail
integral. This identity also holds at the pole and uses the literal count. -/
theorem squarefree_cutoff_remainder {X : ℝ} (hX : 1≤X) {s : ℂ} (hs : 1/2<s.re) :
    squarefreeSection X s-(squarefreeDensity:ℂ)*(∫ t in Set.Ioc 1 X,(t:ℂ)^(-s)) -
        squarefreeRegularPart s =
      (error X:ℂ)*(X:ℂ)^(-s)-s*∫ t in Set.Ioi X,weightedCountError s t := by
  let d := (squarefreeDensity:ℂ)
  have hx := zero_lt_one.trans_le hX
  have hc (t : ℝ) : (count t:ℂ)=(error t:ℂ)+d*(t:ℂ) := by
    simp only [d,error,Complex.ofReal_sub,Complex.ofReal_mul,sub_add_cancel]
  have herr : IntegrableOn (weightedCountError s) (Set.Ioi 1) :=
    _root_.RHTower.SquarefreeDiscrepancy.integrable_moment hs
  have hu : (∫ t in Set.Ioc 1 X,(count t:ℂ)*(t:ℂ)^(-(s+1))) =
      (∫ t in Set.Ioc 1 X,weightedCountError s t)+d*(∫ t in Set.Ioc 1 X,(t:ℂ)^(-s)) := by
    rw [←integral_const_mul,←integral_add (herr.mono_set Set.Ioc_subset_Ioi_self)
      (((continuous_cpow_positive (-s)).integrableOn_compact (μ:=volume) isCompact_Icc).mono_set
        Set.Ioc_subset_Icc_self |>.const_mul d)]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    beta_reduce
    rw [hc,add_mul,mul_assoc,power_step _ (zero_lt_one.trans ht.1),
      show (1:ℂ)+-(s+1) = -s by ring]
    rfl
  have heq := setIntegral_union (μ:=volume) (s:=Set.Ioc 1 X) (t:=Set.Ioi X)
    (Set.disjoint_left.mpr (fun _ h h' => h'.not_ge h.2)) measurableSet_Ioi
    (herr.mono_set Set.Ioc_subset_Ioi_self) (herr.mono_set (Set.Ioi_subset_Ioi hX))
  rw [Set.Ioc_union_Ioi_eq_Ioi hX] at heq
  replace heq : moment s = (∫ t in Set.Ioc 1 X,weightedCountError s t) + ∫ t in Set.Ioi X,weightedCountError s t :=
    (_root_.RHTower.SquarefreeDiscrepancy.moment_eq_integral s).trans heq
  rw [abel_counting hX hs,hu,hc,squarefreeRegularPart,heq]
  have hp := power_step (-s) hx
  rw [show (1:ℂ)+ -s = 1-s by ring] at hp
  change _ - d*_ -(d+s*_) = _
  linear_combination d*hp + d*squarefree_density_primitive hX s

private theorem point_envelope {s : ℂ} {x : ℝ} (hx : 1≤x) :
    ‖(error x:ℂ)*(x:ℂ)^(-s)‖ ≤ 4*x^(1/2-s.re) := by
  have hp := zero_lt_one.trans_le hx
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_cpow_eq_rpow_re_of_pos hp,Complex.neg_re]
  refine (mul_le_mul_of_nonneg_right (_root_.RHTower.SquarefreeDiscrepancy.abs_error_le hx)
    (Real.rpow_nonneg hp.le _)).trans_eq ?_
  rw [Real.sqrt_eq_rpow,mul_assoc,←Real.rpow_add hp,sub_eq_add_neg]

/-- The truncation error is uniform up to a linear height cost and an
explicit inverse distance to the convergence boundary Re s = 1/2. -/
theorem squarefree_section_regular_part_error {X : ℝ} (hX : 1≤X) {s : ℂ} (hs : 1/2<s.re) :
    ‖squarefreeSection X s-(squarefreeDensity:ℂ)*(∫ t in Set.Ioc 1 X,(t:ℂ)^(-s))-
      squarefreeRegularPart s‖ ≤ 4*(1+‖s‖/(s.re-1/2))*X^(1/2-s.re) := by
  have hp := zero_lt_one.trans_le hX
  have hlt : (1/2:ℝ)-(s.re+1)< -1 := by linarith
  have ht : ‖∫ t in Set.Ioi X,weightedCountError s t‖ ≤
      4*X^(1/2-s.re)/(s.re-1/2) := by
    apply (norm_integral_le_integral_norm _).trans
    have hi : IntegrableOn (weightedCountError s) (Set.Ioi X) :=
      (_root_.RHTower.SquarefreeDiscrepancy.integrable_moment hs).mono_set (Set.Ioi_subset_Ioi hX)
    apply (setIntegral_mono_on hi.norm ((integrableOn_Ioi_rpow_of_lt hlt hp).const_mul 4)
      measurableSet_Ioi (fun t ht => ?_)).trans_eq
    · rw [integral_const_mul,integral_Ioi_rpow_of_lt hlt hp,show 1/2-(s.re+1)+1=1/2-s.re by ring]
      field_simp [sub_ne_zero.mpr hs.ne',sub_ne_zero.mpr hs.ne]
      rw [show (2:ℝ)*s.re - 1 = -(1 - 2*s.re) by ring, one_div_neg_eq_neg_one_div]
    · simpa only [weightedCountError,Complex.add_re,Complex.one_re] using
        point_envelope (s:=s+1) (hX.trans (Set.mem_Ioi.mp ht).le)
  rw [squarefree_cutoff_remainder hX hs]
  apply (norm_sub_le _ _).trans
  rw [norm_mul s]
  apply (add_le_add (point_envelope hX) (mul_le_mul_of_nonneg_left ht (norm_nonneg _))).trans_eq
  ring


/-- Outside the removable point the finite main term is a single
power and the constant is the unregularized zeta quotient. -/
theorem squarefree_section_quotient_error {X : ℝ} (hX : 1≤X) {s : ℂ}
    (hs : 1/2<s.re) (hne : s≠1) :
    ‖squarefreeSection X s-(squarefreeDensity:ℂ)*(X:ℂ)^(1-s)/(1-s) -
      riemannZeta s/riemannZeta (2*s)‖ ≤ 4*(1+‖s‖/(s.re-1/2))*X^(1/2-s.re) := by
  have hd := squarefree_density_primitive hX s
  have hh := squarefree_section_regular_part_error hX hs
  rw [squarefreeRegularPart_eq_quotient hs hne] at hh
  have hrec : (∫ t in Set.Ioc 1 X,(t:ℂ)^(-s))=((X:ℂ)^(1-s)-1)/(1-s) := by
    rw [eq_div_iff (sub_ne_zero.mpr hne.symm),mul_comm];exact hd.symm
  rw [hrec] at hh
  convert hh using 2
  rw [show s-1=-(1-s) by ring,div_neg]
  ring

/-- The unnormalized dilation difference has a finite limit even when
its multiplier vanishes at a resonant height. -/
theorem squarefree_dilation_difference_limit {s : ℂ} (hs : 1/2<s.re) (hne : s≠1)
    {r : ℝ} (hr : 0<r) :
    Tendsto (fun X : ℝ => squarefreeSection (r*X) s-(r:ℂ)^(1-s)*squarefreeSection X s)
      atTop (𝓝 ((1-(r:ℂ)^(1-s))*(riemannZeta s/riemannZeta (2*s)))) := by
  let q := (r:ℂ)^(1-s)
  let Z := riemannZeta s/riemannZeta (2*s)
  let P := fun x : ℝ => (squarefreeDensity:ℂ)*(x:ℂ)^(1-s)/(1-s)
  have hu : Tendsto (fun x : ℝ => squarefreeSection x s-P x) atTop (𝓝 Z) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have ht := (tendsto_rpow_neg_atTop (sub_pos.mpr hs)).const_mul (4*(1+‖s‖/(s.re-1/2)))
    rw [mul_zero] at ht
    refine squeeze_zero' (.of_forall fun x => norm_nonneg _) ?_ ht
    filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
    simpa only [neg_sub] using squarefree_section_quotient_error hx hs hne
  have hc := (hu.comp (tendsto_id.const_mul_atTop hr)).sub (hu.const_mul q)
  rw [show Z-q*Z=(1-q)*Z by ring] at hc
  apply hc.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  have step : P (r*x)=q*P x := by
    dsimp only [P,q]
    rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg hr.le hx.le]
    ring
  change squarefreeSection _ s-P (r*x)-q*(squarefreeSection x s-P x) = _
  rw [step]
  dsimp only [q,id_eq]
  ring

/-- Two sharp cutoffs recover the zeta quotient wherever the dilation
multiplier differs from one. -/
theorem squarefree_two_cutoff_recovery {s : ℂ} (hs : 1/2<s.re) (hne : s≠1)
    {r : ℝ} (hr : 0<r) (hscale : (r:ℂ)^(1-s) ≠ 1) :
    Tendsto (fun X : ℝ =>
      (squarefreeSection (r*X) s-(r:ℂ)^(1-s)*squarefreeSection X s)/(1-(r:ℂ)^(1-s)))
      atTop (𝓝 (riemannZeta s/riemannZeta (2*s))) := by
  have h := (squarefree_dilation_difference_limit hs hne hr).div_const (1-(r:ℂ)^(1-s))
  simpa only [mul_div_cancel_left₀ _ (sub_ne_zero.mpr hscale.symm)] using h

/-- Unnormalized difference at the dyadic dilation. Its atom weights
depend only on squarefreeness, n and the spectral parameter. -/
def dyadicSquarefreeDifference (X : ℝ) (s : ℂ) :=
  squarefreeSection (2*X) s - (2:ℂ)^(1-s)*squarefreeSection X s

private theorem two_change_of_scale {s : ℂ} (hs : s.re<1) : (2:ℂ)^(1-s) ≠ 1 := by
  have hnorm : ‖(2:ℂ)^(1-s)‖=(2:ℝ)^(1-s.re) := by
    simpa only [Complex.ofReal_ofNat,Complex.sub_re,Complex.one_re] using
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:ℝ)<2) (1-s)
  intro hz
  rw [hz,norm_one] at hnorm
  exact (Real.one_lt_rpow (by norm_num : (1:ℝ)<2) (sub_pos.mpr hs)).ne hnorm

/-- The density-free dyadic difference converges along every cofinal
sequence, including cutoffs separated by arbitrarily large gaps. -/
theorem dyadic_squarefree_limit {s : ℂ} (hlo : 1/2<s.re) (hhi : s.re<1) :
    Tendsto (fun X : ℝ => dyadicSquarefreeDifference X s) atTop
      (𝓝 ((1-(2:ℂ)^(1-s))*(riemannZeta s/riemannZeta (2*s)))) := by
  have hs : s≠1 := by rintro rfl;norm_num at hhi
  simpa only [dyadicSquarefreeDifference,Complex.ofReal_ofNat] using
    squarefree_dilation_difference_limit hlo hs (by norm_num : (0:ℝ)<2)

/-- A single cofinal sequence of small dyadic readings detects exactly
the zeta zeros in the open right critical strip. -/
theorem dyadic_squarefree_subsequence_zero_iff {s : ℂ} (hlo : 1/2<s.re) (hhi : s.re<1) :
    (∃ X : ℕ → ℝ,Tendsto X atTop atTop ∧
      Tendsto (fun n => dyadicSquarefreeDifference (X n) s) atTop (𝓝 0)) ↔ riemannZeta s=0 := by
  have h := dyadic_squarefree_limit hlo hhi
  have hq := sub_ne_zero.mpr (two_change_of_scale hhi).symm
  have hz : riemannZeta (2*s)≠0 := riemannZeta_ne_zero_of_one_lt_re (by
    simp only [two_mul,Complex.add_re];linarith)
  constructor
  · rintro ⟨X,hX,hvan⟩
    have he := tendsto_nhds_unique (h.comp hX) hvan
    exact (div_eq_zero_iff.mp ((mul_eq_zero.mp he).resolve_left hq)).resolve_right hz
  · intro hs
    rw [hs,zero_div,mul_zero] at h
    exact ⟨fun n => (n:ℝ),tendsto_natCast_atTop_atTop,h.comp tendsto_natCast_atTop_atTop⟩

/-- RH as a nonvanishing test on ordinary finite squarefree sums:
every cofinal sequence works for each parameter in the open right strip. -/
theorem rh_iff_dyadic_squarefree_separation :
    RiemannHypothesis ↔ ∀ s : ℂ,1/2<s.re → s.re<1 →
      ¬∃ X : ℕ → ℝ,Tendsto X atTop atTop ∧
        Tendsto (fun n => dyadicSquarefreeDifference (X n) s) atTop (𝓝 0) := by
  rw [_root_.RHTower.riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip]
  exact forall_congr' fun s => forall_congr' fun h1 => forall_congr' fun h2 =>
    (not_congr (dyadic_squarefree_subsequence_zero_iff h1 h2)).symm



private theorem half_turn_of_dilation {h : ℝ} (hh : h≠0) :
    ((Real.exp (Real.pi/h):ℝ):ℂ)^(1-(1+(h:ℂ)*I))= -1 := by
  have hpos := Real.exp_pos (Real.pi/h)
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hpos.ne'),
    ←Complex.ofReal_log hpos.le,Real.log_exp,Complex.ofReal_div]
  rw [show (Real.pi:ℂ)/(h:ℂ)*(1-(1+(h:ℂ)*I)) = -((Real.pi:ℂ)*I) by
    field_simp [Complex.ofReal_ne_zero.mpr hh];ring,
    Complex.exp_neg,Complex.exp_pi_mul_I]
  norm_num

/-- On Re s=1 a half-period of the cutoff oscillation reverses its sign.
The unweighted average of two sharp squarefree sections then converges
to the actual zeta quotient at every nonzero height. -/
theorem squarefree_half_period_mean {h : ℝ} (hh : h≠0) :
    let s := 1+(h:ℂ)*I
    Tendsto (fun X : ℝ => (squarefreeSection (Real.exp (Real.pi/h)*X) s+squarefreeSection X s)/2)
      atTop (𝓝 (riemannZeta s/riemannZeta (2*s))) := by
  let s : ℂ := 1+(h:ℂ)*I
  have hne : s≠1 := by
    intro he
    have hi := congrArg Complex.im he
    exact hh (by simpa [s] using hi)
  have hs : 1/2<s.re := by norm_num [s]
  have hturn := half_turn_of_dilation hh
  have hz : ((Real.exp (Real.pi/h):ℝ):ℂ)^(1-s)≠1 := by rw [hturn];norm_num
  have ht := squarefree_two_cutoff_recovery hs hne (Real.exp_pos _) hz
  simp only [s,hturn,neg_one_mul,sub_neg_eq_add,one_add_one_eq_two] at ht
  exact ht


private theorem prime_scale_nonresonance {s : ℂ} (hs : s≠1) :
    (2:ℂ)^(1-s)≠1 ∨ (3:ℂ)^(1-s)≠1 := by
  by_contra hn
  push_neg at hn
  obtain ⟨h₂,h₃⟩ := hn
  have hm := congrArg norm h₂
  rw [norm_one] at hm
  have hpow := Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:ℝ)<2) (1-s)
  simp only [Complex.ofReal_ofNat,Complex.sub_re,Complex.one_re] at hpow
  have hr : s.re=1 := by
    rcases lt_trichotomy s.re 1 with h|h|h
    · exact ((Real.one_lt_rpow (by norm_num : (1:ℝ)<2) (sub_pos.mpr h)).ne (hm.symm.trans hpow)).elim
    · exact h
    · exact ((Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1:ℝ)<2) (sub_neg.mpr h)).ne (hpow.symm.trans hm)).elim
  have hform : 1-s=((-s.im:ℝ):ℂ)*I := by apply Complex.ext <;> simp [hr]
  have phase (p : ℕ) (hp : 0<p) :
      ((p:ℕ):ℂ)^(1-s)=_root_.HTGeometry.phaseClockValue (Real.log p) (-s.im) := by
    rw [hform,Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hp.ne')]
    change Complex.exp (Complex.log ((p:ℝ):ℂ)*_)=_
    rw [←Complex.ofReal_log (Nat.cast_nonneg p)]
    unfold _root_.HTGeometry.phaseClockValue
    push_cast
    congr 1
    ring
  have hclock : _root_.RHTower.primeLogPhaseClockPair 2 3 (-s.im)=_root_.RHTower.primeLogPhaseClockPair 2 3 0 := by
    simp only [_root_.RHTower.primeLogPhaseClockPair,_root_.HTGeometry.phaseClockPair,Prod.mk.injEq]
    constructor
    · rw [←phase 2 (by norm_num)];simpa [_root_.HTGeometry.phaseClockValue] using h₂
    · rw [←phase 3 (by norm_num)];simpa [_root_.HTGeometry.phaseClockValue] using h₃
  have hi := _root_.RHTower.primeLogPhaseClockPair_two_three_injective hclock
  exact hs (Complex.ext (by simpa using hr) (by simpa using neg_eq_zero.mp hi))

/-- Simultaneous measurements at three cutoffs recover the zeta quotient
even when one of the two dilations resonates. The denominator is the
sum of two squared moduli, positive throughout the punctured half-plane. -/
theorem squarefree_three_cutoff_recovery {s : ℂ} (hs : 1/2<s.re) (hne : s≠1) :
    let q := (2:ℂ)^(1-s)
    let r := (3:ℂ)^(1-s)
    let a := 1-q
    let b := 1-r
    Tendsto (fun X : ℝ => (conj a*(squarefreeSection (2*X) s-q*squarefreeSection X s)+
      conj b*(squarefreeSection (3*X) s-r*squarefreeSection X s))/
      ((‖a‖^2+‖b‖^2:ℝ):ℂ)) atTop (𝓝 (riemannZeta s/riemannZeta (2*s))) := by
  classical
  let q := (2:ℂ)^(1-s)
  let r := (3:ℂ)^(1-s)
  let a := 1-q
  let b := 1-r
  let Z := riemannZeta s/riemannZeta (2*s)
  have h₂ := squarefree_dilation_difference_limit hs hne (by norm_num : (0:ℝ)<2)
  have h₃ := squarefree_dilation_difference_limit hs hne (by norm_num : (0:ℝ)<3)
  simp only [Complex.ofReal_ofNat] at h₂ h₃
  have h := (((h₂.const_mul (conj a)).add (h₃.const_mul (conj b)))).div_const ((‖a‖^2+‖b‖^2:ℝ):ℂ)
  have hp : 0<‖a‖^2+‖b‖^2 := by
    rcases prime_scale_nonresonance hne with h|h
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr h.symm))) (sq_nonneg _)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr h.symm)))
  have he : (conj a*(a*Z)+conj b*(b*Z))/((‖a‖^2+‖b‖^2:ℝ):ℂ)=Z := by
    rw [div_eq_iff (Complex.ofReal_ne_zero.mpr hp.ne'),←mul_assoc,←mul_assoc,
      mul_comm (conj a),mul_comm (conj b),Complex.mul_conj,Complex.mul_conj,
      Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq,Complex.ofReal_add];ring
  rw [show (conj a*((1-(2:ℂ)^(1-s))*(riemannZeta s/riemannZeta (2*s)))+
      conj b*((1-(3:ℂ)^(1-s))*(riemannZeta s/riemannZeta (2*s))))/((‖a‖^2+‖b‖^2:ℝ):ℂ) = Z from he] at h
  exact h



end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
