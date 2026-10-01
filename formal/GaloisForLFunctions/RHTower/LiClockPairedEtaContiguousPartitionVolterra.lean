import GaloisForLFunctions.RHTower.LiClockPairedEtaContiguousMeasure
import GaloisForLFunctions.RHTower.LiClockPairedEtaContiguousComparison

open Complex Filter Set Metric Topology MeasureTheory ProbabilityTheory RiemannGaussian
open scoped BigOperators ComplexConjugate
namespace RHTower
noncomputable section

/-- Literal real restriction of the existing contiguous partition clock. -/
def liClockPairedEtaContiguousPartitionClockReal (L r t : ℝ) : ℝ :=
  (liClockPairedEtaContiguousPartitionClock L r (t : ℂ)).re

/-- Both raw odd factorials of the complete logarithmic-source clock term. -/
def liClockPairedEtaContiguousPartitionClockSeriesTerm
    (L : ℝ) (t : ℂ) (j : ℕ) : ℂ :=
  iteratedDeriv (2*j+1) (logDeriv (liClockPairedEtaContiguousPartition L)) (1/2 : ℂ) *
    t^(2*j+1) / ((2*j+1).factorial : ℂ)^2

private def referenceTrace (L : ℝ) (z : ℂ) : ℂ :=
  I*logDeriv (liClockPairedEtaContiguousPartition L) (1/2+z*I)

private lemma joint_weight_integrable (L : ℝ) :
    Integrable (fun p : ℝ×ℝ => Real.exp (-(p.1+p.2)/2))
      ((liClockPairedEtaContiguousLogMeasure L).prod (liClockPairedEtaContiguousLogMeasure L)) := by
  have h := (integrable_rexp_neg_mul_liClockPairedEtaContiguousLogMeasure L (1/2)).mul_prod
    (integrable_rexp_neg_mul_liClockPairedEtaContiguousLogMeasure L (1/2))
  convert h using 1
  funext p
  rw [← Real.exp_add]
  congr 1
  ring

private lemma sym_exp_integrable (L v : ℝ) :
    Integrable (fun p : ℝ×ℝ => Real.exp (v*(p.1-p.2)))
      (liClockPairedEtaContiguousSymmetrizedMeasure L) := by
  rw [liClockPairedEtaContiguousSymmetrizedMeasure, integrable_tilted_iff (joint_weight_integrable L)]
  have h := (integrable_rexp_neg_mul_liClockPairedEtaContiguousLogMeasure L (1/2-v)).mul_prod
    (integrable_rexp_neg_mul_liClockPairedEtaContiguousLogMeasure L (1/2+v))
  convert h using 1
  funext p
  simp only [smul_eq_mul]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

private lemma sym_interior (L : ℝ) (z : ℂ) :
    z.re ∈ interior (integrableExpSet (fun p : ℝ×ℝ => p.1-p.2)
      (liClockPairedEtaContiguousSymmetrizedMeasure L)) := by
  have hu : integrableExpSet (fun p : ℝ×ℝ => p.1-p.2)
      (liClockPairedEtaContiguousSymmetrizedMeasure L) = univ := by
    ext v
    simp only [mem_univ, iff_true]
    exact sym_exp_integrable L v
  rw [hu, interior_univ]
  trivial

private def symLaplace (L : ℝ) (z : ℂ) : ℂ :=
  liClockPairedEtaContiguousPartition L (1/2-z) *
  liClockPairedEtaContiguousPartition L (1/2+z) /
  (liClockPairedEtaContiguousPartitionNormalizer L : ℂ)^2
private def symSlope (L : ℝ) (z : ℂ) : ℂ :=
  logDeriv (liClockPairedEtaContiguousPartition L) (1/2+z) -
  logDeriv (liClockPairedEtaContiguousPartition L) (1/2-z)
private lemma analytic_sym (L : ℝ) (z : ℂ) : AnalyticAt ℂ (symLaplace L) z := by
  exact (((analyticAt_liClockPairedEtaContiguousPartition L (1/2-z)).comp
      (f := fun z : ℂ => 1/2-z) (analyticAt_const.sub analyticAt_id)).mul
    ((analyticAt_liClockPairedEtaContiguousPartition L (1/2+z)).comp
      (f := fun z : ℂ => 1/2+z) (analyticAt_const.add analyticAt_id))).div_const
private lemma sym_even (L : ℝ) (z : ℂ) : symLaplace L (-z) = symLaplace L z := by
  simp only [symLaplace, sub_neg_eq_add, ← sub_eq_add_neg]
  rw [mul_comm]
private lemma sym_odd_zero (L : ℝ) (j : ℕ) : iteratedDeriv (2*j+1) (symLaplace L) 0 = 0 := by
  have heq : (fun z : ℂ => symLaplace L (-z)) = symLaplace L := funext (sym_even L)
  have h := iteratedDeriv_comp_neg (2*j+1) (symLaplace L) (0:ℂ)
  rw [heq] at h
  simp only [neg_zero, smul_eq_mul, pow_add, pow_mul, neg_one_sq, one_pow, one_mul,
    pow_one] at h
  linear_combination (1/2:ℂ)*h
private lemma analytic_q {L : ℝ} (hL : 0 < L) :
    AnalyticAt ℂ (logDeriv (liClockPairedEtaContiguousPartition L)) (1/2:ℂ) := by
  have ha := analyticAt_liClockPairedEtaContiguousPartition L (1/2:ℂ)
  exact ha.deriv.div ha (liClockPairedEtaContiguousPartition_ne_zero hL (by norm_num))
private lemma slope_jet {L : ℝ} (hL : 0 < L) (n : ℕ) :
    iteratedDeriv n (symSlope L) 0 =
      (1 - (-1:ℂ)^n) * iteratedDeriv n (logDeriv (liClockPairedEtaContiguousPartition L)) (1/2) := by
  have hq := analytic_q hL
  have hplus : AnalyticAt ℂ (fun z : ℂ => logDeriv (liClockPairedEtaContiguousPartition L) (1/2+z)) 0 :=
    by
    have hq' : AnalyticAt ℂ (logDeriv (liClockPairedEtaContiguousPartition L)) ((fun z : ℂ => 1/2+z) 0) := by simpa only [add_zero] using hq
    exact hq'.comp (f := fun z : ℂ => 1/2+z) (analyticAt_const.add analyticAt_id)
  have hminus : AnalyticAt ℂ (fun z : ℂ => logDeriv (liClockPairedEtaContiguousPartition L) (1/2-z)) 0 :=
    by
    have hq' : AnalyticAt ℂ (logDeriv (liClockPairedEtaContiguousPartition L)) ((fun z : ℂ => 1/2-z) 0) := by simpa only [sub_zero] using hq
    exact hq'.comp (f := fun z : ℂ => 1/2-z) (analyticAt_const.sub analyticAt_id)
  change iteratedDeriv n ((fun z => logDeriv (liClockPairedEtaContiguousPartition L) (1/2+z)) -
    (fun z => logDeriv (liClockPairedEtaContiguousPartition L) (1/2-z))) 0 = _
  rw [iteratedDeriv_sub hplus.contDiffAt hminus.contDiffAt]
  rw [iteratedDeriv_comp_const_add, iteratedDeriv_comp_const_sub]
  simp only [add_zero, sub_zero, smul_eq_mul]
  ring
private lemma sym_deriv_eq {L : ℝ} (hL : 0 < L) :
    deriv (symLaplace L) =ᶠ[𝓝 (0:ℂ)] fun z => symSlope L z * symLaplace L z := by
  have h0 : liClockPairedEtaContiguousPartition L (1/2:ℂ) ≠ 0 :=
    liClockPairedEtaContiguousPartition_ne_zero hL (by norm_num)
  have hcA : Continuous (liClockPairedEtaContiguousPartition L) :=
    continuous_iff_continuousAt.mpr fun w => (analyticAt_liClockPairedEtaContiguousPartition L w).continuousAt
  have hcplus : ContinuousAt (fun z : ℂ => liClockPairedEtaContiguousPartition L (1/2+z)) 0 :=
    (hcA.comp (continuous_const.add continuous_id)).continuousAt
  have hcminus : ContinuousAt (fun z : ℂ => liClockPairedEtaContiguousPartition L (1/2-z)) 0 :=
    (hcA.comp (continuous_const.sub continuous_id)).continuousAt
  have hplus : ∀ᶠ z : ℂ in 𝓝 0, liClockPairedEtaContiguousPartition L (1/2+z) ≠ 0 :=
    hcplus.eventually_ne (by simpa only [add_zero] using h0)
  have hminus : ∀ᶠ z : ℂ in 𝓝 0, liClockPairedEtaContiguousPartition L (1/2-z) ≠ 0 :=
    hcminus.eventually_ne (by simpa only [sub_zero] using h0)
  filter_upwards [hplus, hminus] with z hp hm
  have hdminus := ((analyticAt_liClockPairedEtaContiguousPartition L (1/2-z)).differentiableAt.hasDerivAt).comp z
    ((hasDerivAt_const z (1/2:ℂ)).sub (hasDerivAt_id z))
  have hdplus := ((analyticAt_liClockPairedEtaContiguousPartition L (1/2+z)).differentiableAt.hasDerivAt).comp z
    ((hasDerivAt_const z (1/2:ℂ)).add (hasDerivAt_id z))
  have hd := (hdminus.mul hdplus).div_const ((liClockPairedEtaContiguousPartitionNormalizer L : ℂ)^2)
  change deriv (fun z : ℂ => liClockPairedEtaContiguousPartition L (1/2-z) *
    liClockPairedEtaContiguousPartition L (1/2+z) / (liClockPairedEtaContiguousPartitionNormalizer L : ℂ)^2) z = _
  have he : deriv (symLaplace L) z =
      (-deriv (liClockPairedEtaContiguousPartition L) (1/2-z)*liClockPairedEtaContiguousPartition L (1/2+z) +
        liClockPairedEtaContiguousPartition L (1/2-z)*deriv (liClockPairedEtaContiguousPartition L) (1/2+z)) /
        (liClockPairedEtaContiguousPartitionNormalizer L : ℂ)^2 := by
    change deriv (fun w : ℂ => liClockPairedEtaContiguousPartition L (1/2-w)*liClockPairedEtaContiguousPartition L (1/2+w) / (liClockPairedEtaContiguousPartitionNormalizer L : ℂ)^2) z = _
    simpa only [Function.comp_def, Pi.mul_apply, zero_sub, zero_add,
      mul_neg_one, mul_one] using hd.deriv
  change deriv (symLaplace L) z = _
  rw [he]
  have hhplus : deriv (liClockPairedEtaContiguousPartition L) (1/2+z) /
      liClockPairedEtaContiguousPartition L (1/2+z) *
      (liClockPairedEtaContiguousPartition L (1/2-z)*liClockPairedEtaContiguousPartition L (1/2+z)) =
      liClockPairedEtaContiguousPartition L (1/2-z)*deriv (liClockPairedEtaContiguousPartition L) (1/2+z) := by
    rw [div_eq_mul_inv]
    calc
      _ = liClockPairedEtaContiguousPartition L (1/2-z)*deriv (liClockPairedEtaContiguousPartition L) (1/2+z)*
          ((liClockPairedEtaContiguousPartition L (1/2+z))⁻¹*liClockPairedEtaContiguousPartition L (1/2+z)) := by ring
      _ = _ := by rw [inv_mul_cancel₀ hp,mul_one]
  have hhminus : deriv (liClockPairedEtaContiguousPartition L) (1/2-z) /
      liClockPairedEtaContiguousPartition L (1/2-z) *
      (liClockPairedEtaContiguousPartition L (1/2-z)*liClockPairedEtaContiguousPartition L (1/2+z)) =
      deriv (liClockPairedEtaContiguousPartition L) (1/2-z)*liClockPairedEtaContiguousPartition L (1/2+z) := by
    rw [div_eq_mul_inv]
    calc
      _ = deriv (liClockPairedEtaContiguousPartition L) (1/2-z)*liClockPairedEtaContiguousPartition L (1/2+z)*
          ((liClockPairedEtaContiguousPartition L (1/2-z))⁻¹*liClockPairedEtaContiguousPartition L (1/2-z)) := by ring
      _ = _ := by rw [inv_mul_cancel₀ hm,mul_one]
  simp only [symSlope, symLaplace, logDeriv, Pi.div_apply]
  rw [←mul_div_assoc,sub_mul,hhplus,hhminus]
  ring
private lemma slope_analytic {L : ℝ} (hL : 0 < L) : AnalyticAt ℂ (symSlope L) 0 := by
  have hq := analytic_q hL
  have hplus : AnalyticAt ℂ (fun z : ℂ => logDeriv (liClockPairedEtaContiguousPartition L) (1/2+z)) 0 := by
    have hq' : AnalyticAt ℂ (logDeriv (liClockPairedEtaContiguousPartition L)) ((fun z : ℂ => 1/2+z) 0) := by simpa only [add_zero] using hq
    exact hq'.comp (f := fun z : ℂ => 1/2+z) (analyticAt_const.add analyticAt_id)
  have hminus : AnalyticAt ℂ (fun z : ℂ => logDeriv (liClockPairedEtaContiguousPartition L) (1/2-z)) 0 := by
    have hq' : AnalyticAt ℂ (logDeriv (liClockPairedEtaContiguousPartition L)) ((fun z : ℂ => 1/2-z) 0) := by simpa only [sub_zero] using hq
    exact hq'.comp (f := fun z : ℂ => 1/2-z) (analyticAt_const.sub analyticAt_id)
  exact hplus.sub hminus
private lemma sum_range_two (f : ℕ → ℂ) (n : ℕ) :
    ∑ i ∈ Finset.range (2*n), f i = ∑ j ∈ Finset.range n, (f (2*j) + f (2*j+1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1)=2*n+1+1 by omega, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring
private lemma sym_recurrence {L : ℝ} (hL : 0 < L) (n : ℕ) :
    iteratedDeriv (2*n+2) (symLaplace L) 0 =
      ∑ j ∈ Finset.range (n+1),
        ((2*n+1).choose (2*j+1):ℂ) * 2 *
          iteratedDeriv (2*j+1) (logDeriv (liClockPairedEtaContiguousPartition L)) (1/2) *
          iteratedDeriv (2*(n-j)) (symLaplace L) 0 := by
  have h := (sym_deriv_eq hL).iteratedDeriv_eq (2*n+1)
  rw [← iteratedDeriv_succ'] at h
  rw [iteratedDeriv_fun_mul (slope_analytic hL).contDiffAt (analytic_sym L 0).contDiffAt,
    show 2*n+1+1=2*(n+1) by omega, sum_range_two] at h
  rw [show 2*n+2=2*(n+1) by omega, h]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j  ≤  n := by simpa using Finset.mem_range.mp hj
  rw [slope_jet hL, slope_jet hL]
  simp only [pow_mul, pow_add, neg_one_sq, one_pow, pow_one]
  rw [show 2*n+1-(2*j+1)=2*(n-j) by omega]
  ring

private def gTerm (c : ℕ → ℝ) (t : ℝ) (j : ℕ) := c j*t^(2*j)
private def gKernel (c : ℕ → ℝ) (t : ℝ) := ∑' j, gTerm c t j
private def gWeighted (c : ℕ → ℝ) (t : ℝ) := ∑' j : ℕ, (2*j:ℝ)*gTerm c t j
variable {c : ℕ → ℝ} {R : ℝ}
private lemma norm_gTerm_le (hc : ∀j, 0<c j) (hR : 0 ≤ R)
    (hbound : ∀j, c j  ≤  R^j/(j.factorial:ℝ)) {t T : ℝ} (ht : |t| ≤ T) (j : ℕ) :
    ‖gTerm c t j‖  ≤  (R*T^2)^j/(j.factorial:ℝ) := by
  rw [gTerm, norm_mul, Real.norm_eq_abs, abs_of_pos (hc j), norm_pow, Real.norm_eq_abs]
  calc
    c j*|t|^(2*j)  ≤  (R^j/(j.factorial:ℝ))*T^(2*j) :=
      mul_le_mul (hbound j) (pow_le_pow_left₀ (abs_nonneg t) ht _)
        (pow_nonneg (abs_nonneg t) _) (by positivity)
    _ = _ := by rw [mul_pow, ← pow_mul]; ring
private lemma summable_gTerm (hc : ∀j, 0<c j) (hR : 0 ≤ R)
    (hbound : ∀j, c j  ≤  R^j/(j.factorial:ℝ)) (t : ℝ) : Summable (gTerm c t) :=
  (Real.summable_pow_div_factorial (R*|t|^2)).of_norm_bounded
    (fun j => norm_gTerm_le hc hR hbound (le_refl |t|) j)
private lemma summable_degree_pow (r : ℝ) :
    Summable (fun j : ℕ => (2*j:ℝ)*r^j/(j.factorial:ℝ)) := by
  apply (summable_nat_add_iff 1).1
  have h := (Real.summable_pow_div_factorial r).mul_left (2*r)
  apply h.congr
  intro j
  rw [Nat.factorial_succ, pow_succ]
  push_cast
  have hf : (j.factorial:ℝ) ≠ 0 := by positivity
  have hj : (j+1:ℝ) ≠ 0 := by positivity
  field_simp
private lemma summable_gWeighted (hc : ∀j, 0<c j) (hR : 0 ≤ R)
    (hbound : ∀j, c j  ≤  R^j/(j.factorial:ℝ)) (t : ℝ) :
    Summable (fun j : ℕ => (2*j:ℝ)*gTerm c t j) := by
  apply (summable_degree_pow (R*|t|^2)).of_norm_bounded
  intro j
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2*j)]
  simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left
    (norm_gTerm_le hc hR hbound (le_refl |t|) j) (show (0:ℝ) ≤ 2*j by positivity)
private def gDerivTerm (c : ℕ → ℝ) (t : ℝ) (j : ℕ) := c j*(2*j:ℝ)*t^(2*j-1)
private lemma norm_gDerivTerm_le (hc : ∀j, 0<c j) (hR : 0 ≤ R)
    (hbound : ∀j, c j  ≤  R^j/(j.factorial:ℝ)) {t T : ℝ} (hT : 1 ≤ T) (ht : |t| ≤ T) (j : ℕ) :
    ‖gDerivTerm c t j‖  ≤  (2*j:ℝ)*(R*T^2)^j/(j.factorial:ℝ) := by
  have hpow : |t|^(2*j-1)  ≤  T^(2*j) :=
    (pow_le_pow_left₀ (abs_nonneg t) ht _).trans (pow_le_pow_right₀ hT (Nat.sub_le _ _))
  rw [gDerivTerm, norm_mul, norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (hc j), abs_of_nonneg (by positivity : (0:ℝ) ≤ 2*j), Real.norm_eq_abs]
  calc
    c j*(2*j:ℝ)*|t|^(2*j-1)  ≤  (R^j/(j.factorial:ℝ))*(2*j:ℝ)*T^(2*j) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right (hbound j) (by positivity)
      · exact hpow
      · positivity
      · positivity
    _ = _ := by rw [mul_pow, ← pow_mul]; ring
private lemma hasDerivAt_gKernel (hc : ∀j, 0<c j) (hR : 0 ≤ R)
    (hbound : ∀j, c j  ≤  R^j/(j.factorial:ℝ)) (t : ℝ) :
    HasDerivAt (gKernel c) (∑'j, gDerivTerm c t j) t := by
  let T : ℝ := |t|+1
  have hT : 1 ≤ T := by dsimp [T]; linarith [abs_nonneg t]
  have hg (j : ℕ) (y : ℝ) (_ : y∈Metric.ball 0 T) :
      HasDerivAt (fun z => gTerm c z j) (gDerivTerm c y j) y := by
    simpa only [gTerm, gDerivTerm, Pi.pow_apply, id_eq, mul_one, Nat.cast_mul,
      Nat.cast_ofNat, mul_assoc] using ((hasDerivAt_id y).pow (2*j)).const_mul (c j)
  exact hasDerivAt_tsum_of_isPreconnected (summable_degree_pow (R*T^2))
    Metric.isOpen_ball (convex_ball (0:ℝ) T).isPreconnected hg
    (fun j y hy => norm_gDerivTerm_le hc hR hbound hT
      (le_of_lt (by simpa [Metric.mem_ball, Real.dist_eq] using hy)) j)
    (by simp [Metric.mem_ball, T]; positivity)
    (summable_gTerm hc hR hbound 0) (by simp [Metric.mem_ball, T])
private lemma gKernel_mul_deriv (hc : ∀j, 0<c j) (hR : 0 ≤ R)
    (hbound : ∀j, c j  ≤  R^j/(j.factorial:ℝ)) (t : ℝ) :
    t*deriv (gKernel c) t = gWeighted c t := by
  rw [(hasDerivAt_gKernel hc hR hbound t).deriv, gWeighted, ← tsum_mul_left]
  apply tsum_congr
  intro j
  by_cases hj : j=0
  · simp [hj, gTerm, gDerivTerm]
  · have hdegree : 1 ≤ 2*j := by omega
    have hp : t*t^(2*j-1)=t^(2*j) := by rw [← pow_succ', Nat.sub_add_cancel hdegree]
    dsimp only [gDerivTerm, gTerm]
    calc
      t*(c j*(2*j:ℝ)*t^(2*j-1)) = (2*j:ℝ)*c j*(t*t^(2*j-1)) := by ring
      _ = _ := by rw [hp]; ring
private def dividedPower (n : ℕ) (t : ℝ) : ℝ := t^n/(n.factorial:ℝ)
@[fun_prop] private theorem continuous_dividedPower (n : ℕ) : Continuous (dividedPower n) := by
  unfold dividedPower
  fun_prop
private theorem dividedPower_deriv (n : ℕ) (t : ℝ) :
    HasDerivAt (dividedPower (n+1)) (dividedPower n t) t := by
  have h := ((hasDerivAt_id t).pow (n+1)).div_const ((n+1).factorial:ℝ)
  convert h using 1 <;> try rfl
  simp only [dividedPower, id_eq, Nat.add_sub_cancel, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_one]
  field_simp
private theorem integral_dividedPower_convolution (p q : ℕ) (t : ℝ) :
    ∫ s in 0..t, dividedPower p s * dividedPower q (t-s) =
      dividedPower (p+q+1) t := by
  induction q generalizing p with
  | zero =>
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a:=0) (b:=t) (fun x _ => dividedPower_deriv p x)
      (by exact (by fun_prop : Continuous (dividedPower p)).intervalIntegrable 0 t)
    simpa [dividedPower] using h
  | succ q ih =>
    have hu : ∀ x, HasDerivAt (fun s => dividedPower (q+1) (t-s))
        (-dividedPower q (t-x)) x := by
      intro x
      simpa only [Function.comp_def, zero_sub, mul_neg_one] using
        (dividedPower_deriv q (t-x)).comp x
          ((hasDerivAt_const x t).sub (hasDerivAt_id x))
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      (a:=0) (b:=t)
      (u:=fun s => dividedPower (q+1) (t-s)) (v:=dividedPower (p+1))
      (u':=fun s => -dividedPower q (t-s)) (v':=dividedPower p)
      (by fun_prop) (by fun_prop) (fun x _ => hu x)
      (fun x _ => dividedPower_deriv p x)
      ((by fun_prop : Continuous fun s => -dividedPower q (t-s)).intervalIntegrable 0 t)
      ((by fun_prop : Continuous (dividedPower p)).intervalIntegrable 0 t)
    simp only [dividedPower, sub_self, zero_pow (Nat.succ_ne_zero _), zero_div,
      zero_mul, mul_zero, sub_zero, zero_sub] at h
    have hn : (fun x : ℝ => -(dividedPower q (t-x)) * dividedPower (p+1) x) =
        (fun x => -(dividedPower q (t-x) * dividedPower (p+1) x)) := by
      funext x
      ring
    change (∫x in 0..t, dividedPower (q+1) (t-x)*dividedPower p x) =
      -(∫x in 0..t, -(dividedPower q (t-x))*dividedPower (p+1) x) at h
    rw [hn, intervalIntegral.integral_neg, neg_neg] at h
    calc
      (∫s in 0..t, dividedPower p s * dividedPower (q+1) (t-s)) =
          ∫s in 0..t, dividedPower (q+1) (t-s)*dividedPower p s := by
        congr 1
        funext s
        ring
      _ = ∫s in 0..t, dividedPower q (t-s)*dividedPower (p+1) s := h
      _ = ∫s in 0..t, dividedPower (p+1) s * dividedPower q (t-s) := by
        congr 1
        funext s
        ring
      _ = dividedPower (p+q+1+1) t := by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (p+1)

private def pTerm (p : ℕ→ℝ) (t : ℝ) (j : ℕ) : ℝ := p j*t^(2*j+1)
private def pResponse (p : ℕ→ℝ) (t : ℝ) : ℝ := ∑'j, pTerm p t j
private def pBlock (p c : ℕ→ℝ) (t s : ℝ) (n : ℕ) : ℝ :=
  ∑j∈Finset.range (n+1), pTerm p s j*gTerm c (t-s) (n-j)
private lemma pTerm_bound {p : ℕ→ℝ} {s T : ℝ} (hT : 0 ≤ T) (hs : |s| ≤ T) (j : ℕ) :
    ‖pTerm p s j‖  ≤  ‖pTerm p T j‖ := by
  simp only [pTerm, norm_mul, norm_pow, Real.norm_eq_abs, abs_of_nonneg hT]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg s) hs _) (abs_nonneg _)
private lemma pBlock_hasSum {p c : ℕ→ℝ} (hp : ∀t, Summable (fun j=>‖pTerm p t j‖))
    (hc : ∀j, 0<c j) {R : ℝ} (hR : 0 ≤ R) (hbound : ∀j, c j ≤ R^j/(j.factorial:ℝ)) (t s : ℝ) :
    HasSum (pBlock p c t s) (pResponse p s*gKernel c (t-s)) :=
  hasSum_sum_range_mul_of_summable_norm (hp s) (summable_gTerm hc hR hbound (t-s)).norm
private lemma integral_pTerm_mul_gTerm (p c : ℕ→ℝ) (j k : ℕ) (t : ℝ) :
    (∫s in (0:ℝ)..t, pTerm p s j*gTerm c (t-s) k) =
      p j*c k*((2*j+1).factorial:ℝ)*((2*k).factorial:ℝ)*dividedPower (2*j+2*k+2) t := by
  have heq : (fun s : ℝ=>pTerm p s j*gTerm c (t-s) k) =
      (fun s : ℝ=> (p j*c k*((2*j+1).factorial:ℝ)*((2*k).factorial:ℝ))*
        (dividedPower (2*j+1) s*dividedPower (2*k) (t-s))) := by
    funext s
    dsimp only [pTerm,gTerm,dividedPower]
    have hf : ((2*j+1).factorial:ℝ) ≠ 0 := by positivity
    have hg : ((2*k).factorial:ℝ) ≠ 0 := by positivity
    field_simp
  rw [heq, intervalIntegral.integral_const_mul, integral_dividedPower_convolution]
  congr 1
  congr 1
  omega
private lemma integral_pBlock {p c : ℕ→ℝ}
    (hrec : ∀n, 2*(∑j∈Finset.range (n+1), p j*c (n-j)*((2*j+1).factorial:ℝ)*((2*(n-j)).factorial:ℝ)) =
      (2*n+2:ℝ)*c (n+1)*((2*n+2).factorial:ℝ)) (n : ℕ) (t : ℝ) :
    2*(∫s in (0:ℝ)..t, pBlock p c t s n) = (2*(n+1):ℝ)*gTerm c t (n+1) := by
  unfold pBlock
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [integral_pTerm_mul_gTerm]
    have heq : ∑j∈Finset.range (n+1),
        p j*c (n-j)*((2*j+1).factorial:ℝ)*((2*(n-j)).factorial:ℝ)*dividedPower (2*j+2*(n-j)+2) t =
      (∑j∈Finset.range (n+1), p j*c (n-j)*((2*j+1).factorial:ℝ)*((2*(n-j)).factorial:ℝ))*dividedPower (2*n+2) t := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      rw [show 2*j+2*(n-j)+2=2*n+2 by have := Finset.mem_range.mp hj; omega]
    rw [heq, ← mul_assoc, hrec]
    dsimp only [dividedPower,gTerm]
    rw [show 2*(n+1)=2*n+2 by omega]
    have hf : ((2*n+2).factorial:ℝ) ≠ 0 := by positivity
    field_simp
  · intro j hj
    apply Continuous.intervalIntegrable
    unfold pTerm gTerm
    fun_prop
private lemma pResponse_volterra {p c : ℕ→ℝ} (hp : ∀t, Summable (fun j=>‖pTerm p t j‖))
    (hc : ∀j, 0<c j) {R : ℝ} (hR : 0 ≤ R) (hbound : ∀j, c j ≤ R^j/(j.factorial:ℝ))
    (hrec : ∀n, 2*(∑j∈Finset.range (n+1), p j*c (n-j)*((2*j+1).factorial:ℝ)*((2*(n-j)).factorial:ℝ)) =
      (2*n+2:ℝ)*c (n+1)*((2*n+2).factorial:ℝ)) {t : ℝ} (ht : 0 ≤ t) :
    2*(∫s in (0:ℝ)..t, pResponse p s*gKernel c (t-s))=gWeighted c t := by
  let Q (n : ℕ) : ℝ := ∑j∈Finset.range (n+1), ‖pTerm p t j‖*((R*t^2)^(n-j)/((n-j).factorial:ℝ))
  have hQ : Summable Q := (hasSum_sum_range_mul_of_summable_norm
    (hp t).norm (Real.summable_pow_div_factorial (R*t^2)).norm).summable
  have hboundBlock (n : ℕ) : ∀ᵐs:ℝ, s∈Set.uIoc (0:ℝ) t → ‖pBlock p c t s n‖ ≤ Q n := by
    filter_upwards [] with s hs
    have hs0 : 0 ≤ s := (Set.uIoc_of_le ht ▸ hs).1.le
    have hst : s ≤ t := (Set.uIoc_of_le ht ▸ hs).2
    have hsa : |s| ≤ t := by rw [abs_of_nonneg hs0]; exact hst
    have htsa : |t-s| ≤ t := by rw [abs_of_nonneg (by linarith)]; linarith
    dsimp only [pBlock,Q]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro j hj
    rw [norm_mul]
    exact mul_le_mul (pTerm_bound ht hsa j) (norm_gTerm_le hc hR hbound htsa (n-j))
      (norm_nonneg _) (norm_nonneg _)
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence
    (a:=0) (b:=t) (μ:=volume) (F:=fun n s=>pBlock p c t s n)
    (f:=fun s=>pResponse p s*gKernel c (t-s)) (fun n _=>Q n)
    (fun n=> (by unfold pBlock pTerm gTerm; fun_prop : Continuous (fun s=>pBlock p c t s n)).aestronglyMeasurable)
    hboundBlock (Eventually.of_forall (fun _ _=>hQ)) intervalIntegrable_const
    (Eventually.of_forall (fun s _=>pBlock_hasSum hp hc hR hbound t s))
  have hsum2 := hsum.mul_left 2
  have heq := hsum2.congr_fun (fun n=>(integral_pBlock hrec n t).symm)
  have hw := summable_gWeighted hc hR hbound t
  have hseries := hw.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, Nat.cast_zero, mul_zero, zero_mul, zero_add] at hseries
  change _ = ∑'j:ℕ, (2*j:ℝ)*gTerm c t j
  rw [← hseries]
  simpa only [Nat.cast_add,Nat.cast_one] using heq.tsum_eq.symm
private lemma sym_even_deriv (L : ℝ) (j : ℕ) :
    iteratedDeriv (2*j) (complexMGF (fun p : ℝ×ℝ=>p.1-p.2) (liClockPairedEtaContiguousSymmetrizedMeasure L)) 0 =
      (liClockPairedEtaContiguousSymmetrizedEvenMoment L j : ℂ) := by
  rw [iteratedDeriv_complexMGF (sym_interior L 0)]
  simp only [zero_mul, Complex.exp_zero, mul_one]
  rw [liClockPairedEtaContiguousSymmetrizedEvenMoment, ← integral_complex_ofReal (μ:=liClockPairedEtaContiguousSymmetrizedMeasure L) (f:=fun p : ℝ×ℝ=>(p.1-p.2)^(2*j))]
  apply integral_congr_ae
  filter_upwards [] with p
  push_cast
  rfl
private lemma sym_complexMGF_eq {L : ℝ} (hL : 0 < L) (z : ℂ) :
    complexMGF (fun p : ℝ×ℝ => p.1-p.2)
      (liClockPairedEtaContiguousSymmetrizedMeasure L) z = symLaplace L z :=
  liClockPairedEtaContiguousSymmetrizedMeasure_complexMGF_eq_source hL.le z

private lemma symLaplace_even_deriv {L : ℝ} (hL : 0 < L) (j : ℕ) :
    iteratedDeriv (2*j) (symLaplace L) 0 =
      (liClockPairedEtaContiguousSymmetrizedEvenMoment L j : ℂ) := by
  have hfun : complexMGF (fun p : ℝ×ℝ => p.1-p.2)
      (liClockPairedEtaContiguousSymmetrizedMeasure L) = symLaplace L :=
    funext (sym_complexMGF_eq hL)
  rw [← hfun]
  exact sym_even_deriv L j

/-- Raw even cumulant of order `2*j+2` selected from the reference partition logarithmic derivative. -/
private def referenceEvenCumulant (L : ℝ) (j : ℕ) : ℝ :=
  (iteratedDeriv (2*j+1) (logDeriv (liClockPairedEtaContiguousPartition L)) (1/2:ℂ)).re
private lemma moment_recurrence {L : ℝ} (hL : 0<L) (n : ℕ) :
    liClockPairedEtaContiguousSymmetrizedEvenMoment L (n+1) =
      ∑j∈Finset.range (n+1), ((2*n+1).choose (2*j+1):ℝ)*2*referenceEvenCumulant L j*
        liClockPairedEtaContiguousSymmetrizedEvenMoment L (n-j) := by
  have h := sym_recurrence hL n
  rw [show 2*n+2=2*(n+1) by omega, symLaplace_even_deriv hL] at h
  simp_rw [symLaplace_even_deriv hL] at h
  have hre := congrArg Complex.re h
  simpa [Complex.mul_re,referenceEvenCumulant] using hre
/-- Exact coefficient with both raw odd factorials in the literal partition clock. -/
private def referenceClockCoefficient (L : ℝ) (j : ℕ) : ℝ :=
  referenceEvenCumulant L j/((2*j+1).factorial:ℝ)^2
private lemma partitionCoefficient_recurrence {L : ℝ} (hL : 0<L) (n : ℕ) :
    2*(∑j∈Finset.range (n+1), referenceClockCoefficient L j*liClockPairedEtaContiguousBorelCoefficient L (n-j)*
      ((2*j+1).factorial:ℝ)*((2*(n-j)).factorial:ℝ)) =
      (2*n+2:ℝ)*liClockPairedEtaContiguousBorelCoefficient L (n+1)*((2*n+2).factorial:ℝ) := by
  have hfact : ((2*n+1).factorial:ℝ) ≠ 0 := by positivity
  have hs : 2*(∑j∈Finset.range (n+1), referenceClockCoefficient L j*liClockPairedEtaContiguousBorelCoefficient L (n-j)*
      ((2*j+1).factorial:ℝ)*((2*(n-j)).factorial:ℝ)) =
    (∑j∈Finset.range (n+1), ((2*n+1).choose (2*j+1):ℝ)*2*referenceEvenCumulant L j*
      liClockPairedEtaContiguousSymmetrizedEvenMoment L (n-j))/((2*n+1).factorial:ℝ) := by
    rw [Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j ≤ n := by simpa using Finset.mem_range.mp hj
    have hh := Nat.choose_mul_factorial_mul_factorial (show 2*j+1 ≤ 2*n+1 by omega)
    rw [show 2*n+1-(2*j+1)=2*(n-j) by omega] at hh
    have hc : ((2*n+1).choose (2*j+1):ℝ)*((2*j+1).factorial:ℝ)*((2*(n-j)).factorial:ℝ) =
        ((2*n+1).factorial:ℝ) := by exact_mod_cast hh
    have hchoose : ((2*n+1).choose (2*j+1):ℝ) ≠ 0 := by
      intro hz
      rw [hz,zero_mul,zero_mul] at hc
      exact hfact hc.symm
    rw [← hc]
    dsimp only [referenceClockCoefficient,liClockPairedEtaContiguousBorelCoefficient]
    have hf : ((2*j+1).factorial:ℝ) ≠ 0 := by positivity
    have hg : ((2*(n-j)).factorial:ℝ) ≠ 0 := by positivity
    field_simp
  rw [hs, ← moment_recurrence hL]
  have hfnext : ((2*n+2).factorial:ℝ)=(2*n+2:ℝ)*((2*n+1).factorial:ℝ) := by
    rw [show 2*n+2=(2*n+1)+1 by omega,Nat.factorial_succ]
    push_cast
    ring
  dsimp only [liClockPairedEtaContiguousBorelCoefficient]
  rw [show 2*(n+1)=2*n+2 by omega,hfnext]
  have hdegree : (2*n+2:ℝ) ≠ 0 := by positivity
  field_simp
private lemma partitionTrace_odd (L : ℝ) (j : ℕ) :
    iteratedDeriv (2*j+1) (referenceTrace L) 0 =
      (-1:ℂ)^(j+1)*iteratedDeriv (2*j+1) (logDeriv (liClockPairedEtaContiguousPartition L)) (1/2) := by
  unfold referenceTrace
  have hc : (fun z : ℂ=>logDeriv (liClockPairedEtaContiguousPartition L) (1/2+z*I)) =
      (fun z=>logDeriv (liClockPairedEtaContiguousPartition L) (I*z+1/2)) := by funext z; congr 1; ring
  rw [iteratedDeriv_const_mul_field,hc, GaloisForLFunctions.liClock_iteratedDeriv_comp_affine]
  simp only [mul_zero,zero_add]
  have hi : (I:ℂ)*(I:ℂ)^(2*j+1)=(-1:ℂ)^(j+1) := by
    rw [← pow_succ',show 2*j+1+1=2*(j+1) by omega,pow_mul,Complex.I_sq]
  rw [← mul_assoc,hi]
private lemma liClockPairedEtaContiguousPartitionClockSeriesTerm_eq_neg (L : ℝ) (t : ℂ) (j : ℕ) :
    liClockPairedEtaContiguousPartitionClockSeriesTerm L t j = -liClockCentralTraceSineContourTerm (referenceTrace L) t j := by
  unfold liClockPairedEtaContiguousPartitionClockSeriesTerm liClockCentralTraceSineContourTerm
  rw [partitionTrace_odd]
  have hs : (-1:ℂ)^j*(-1:ℂ)^(j+1)= -1 := by
    rw [← pow_add,show j+(j+1)=2*j+1 by omega,pow_add,pow_mul]
    norm_num
  rw [← mul_assoc,hs]
  ring
private lemma partition_real_term (L : ℝ) (t : ℝ) (j : ℕ) :
    (liClockPairedEtaContiguousPartitionClockSeriesTerm L (t:ℂ) j).re=pTerm (referenceClockCoefficient L) t j := by
  unfold liClockPairedEtaContiguousPartitionClockSeriesTerm pTerm referenceClockCoefficient referenceEvenCumulant
  have hd : (((((2*j+1).factorial:ℝ)^2):ℝ):ℂ)=((2*j+1).factorial:ℂ)^2 := by norm_cast
  rw [←hd,←Complex.ofReal_pow,Complex.div_ofReal_re]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  ring
private lemma partitionTrace_analytic {L : ℝ} {z : ℂ}
    (hn : liClockPairedEtaContiguousPartition L (1/2+z*I) ≠ 0) :
    AnalyticAt ℂ (referenceTrace L) z := by
  have ha := analyticAt_liClockPairedEtaContiguousPartition L (1/2+z*I)
  exact analyticAt_const.mul ((ha.deriv.div ha hn).comp (f:=fun z : ℂ=>1/2+z*I)
    (analyticAt_const.add (analyticAt_id.mul analyticAt_const)))
private lemma partitionTrace_diffCont {L : ℝ} {r : ℝ}
    (hclosed : ∀z∈closedBall (0:ℂ) r, liClockPairedEtaContiguousPartition L (1/2+z*I) ≠ 0) :
    DiffContOnCl ℂ (referenceTrace L) (ball (0:ℂ) r) := by
  have ha : AnalyticOnNhd ℂ (referenceTrace L) (closedBall (0:ℂ) r) :=
    fun z hz=>partitionTrace_analytic (hclosed z hz)
  exact ha.differentiableOn.diffContOnCl_ball (Subset.refl _)
private lemma liClockPairedEtaContiguousPartitionClockSeriesTerm_summable {L : ℝ} {r : ℝ} (hr : 0<r)
    (hclosed : ∀z∈closedBall (0:ℂ) r, liClockPairedEtaContiguousPartition L (1/2+z*I) ≠ 0) (t : ℂ) :
    Summable (fun j=>‖liClockPairedEtaContiguousPartitionClockSeriesTerm L t j‖) := by
  apply (summable_norm_liClockCentralTraceSineContourTerm hr (partitionTrace_diffCont hclosed) t).congr
  intro j
  rw [liClockPairedEtaContiguousPartitionClockSeriesTerm_eq_neg,norm_neg]
private lemma partitionPterm_summable {L : ℝ} {r : ℝ} (hr : 0<r)
    (hclosed : ∀z∈closedBall (0:ℂ) r, liClockPairedEtaContiguousPartition L (1/2+z*I) ≠ 0) (t : ℝ) :
    Summable (fun j=>‖pTerm (referenceClockCoefficient L) t j‖) := by
  apply (liClockPairedEtaContiguousPartitionClockSeriesTerm_summable hr hclosed (t:ℂ)).of_nonneg_of_le
  · intro j
    exact norm_nonneg _
  · intro j
    rw [← partition_real_term]
    exact Complex.abs_re_le_norm _
private lemma partitionClock_eq_series {L : ℝ} {r : ℝ} (hr : 0<r)
    (hclosed : ∀z∈closedBall (0:ℂ) r, liClockPairedEtaContiguousPartition L (1/2+z*I) ≠ 0) (t : ℝ) :
    (liClockPairedEtaContiguousPartitionClock L r (t:ℂ)).re=pResponse (referenceClockCoefficient L) t := by
  change (liClockCentralTraceSineContour (referenceTrace L) r (t : ℂ)).re = _
  rw [liClockCentralTraceSineContour_eq_neg_tsum hr (partitionTrace_diffCont hclosed)]
  have heq : -(∑'j, liClockCentralTraceSineContourTerm (referenceTrace L) (t:ℂ) j) =
      ∑'j,liClockPairedEtaContiguousPartitionClockSeriesTerm L (t:ℂ) j := by
    rw [← tsum_neg]
    exact tsum_congr (fun j=>(liClockPairedEtaContiguousPartitionClockSeriesTerm_eq_neg L (t:ℂ) j).symm)
  rw [heq,Complex.re_tsum (liClockPairedEtaContiguousPartitionClockSeriesTerm_summable hr hclosed (t:ℂ)).of_norm]
  exact tsum_congr (partition_real_term L t)
private lemma reference_closedDisk_nonzero {L r : ℝ} (hL : 0 < L)
    (hrhalf : r < 1/2) :
    ∀ z ∈ closedBall (0 : ℂ) r,
      liClockPairedEtaContiguousPartition L (1/2+z*I) ≠ 0 := by
  intro z hz
  have hzn : ‖z‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hz
  have hi := (abs_le.mp ((Complex.abs_im_le_norm z).trans hzn)).2
  apply liClockPairedEtaContiguousPartition_ne_zero hL
  have heq : (1/2+z*I).re = (1/2 : ℝ)-z.im := by
    norm_num [Complex.add_re, Complex.mul_re]
    ring
  rw [heq]
  linarith

/-- Exact full complex series of the literal reference partition contour. -/
theorem liClockPairedEtaContiguousPartitionClock_eq_tsum
    {L r : ℝ} (hL : 0 < L) (hr : 0 < r) (hrhalf : r < 1/2) (t : ℂ) :
    liClockPairedEtaContiguousPartitionClock L r t =
      ∑' j : ℕ, liClockPairedEtaContiguousPartitionClockSeriesTerm L t j := by
  change liClockCentralTraceSineContour (referenceTrace L) r t = _
  rw [liClockCentralTraceSineContour_eq_neg_tsum hr
      (partitionTrace_diffCont (reference_closedDisk_nonzero hL hrhalf)), ← tsum_neg]
  exact tsum_congr (fun j => (liClockPairedEtaContiguousPartitionClockSeriesTerm_eq_neg L t j).symm)

/-- Complete absolute summability at every complex clock. -/
theorem summable_norm_liClockPairedEtaContiguousPartitionClockSeriesTerm
    {L r : ℝ} (hL : 0 < L) (hr : 0 < r) (hrhalf : r < 1/2) (t : ℂ) :
    Summable (fun j : ℕ => ‖liClockPairedEtaContiguousPartitionClockSeriesTerm L t j‖) :=
  liClockPairedEtaContiguousPartitionClockSeriesTerm_summable hr
    (reference_closedDisk_nonzero hL hrhalf) t

/-- Real source series obtained from the whole complex series. -/
theorem liClockPairedEtaContiguousPartitionClockReal_eq_tsum
    {L r : ℝ} (hL : 0 < L) (hr : 0 < r) (hrhalf : r < 1/2) (t : ℝ) :
    liClockPairedEtaContiguousPartitionClockReal L r t =
      ∑' j : ℕ,
        (iteratedDeriv (2*j+1) (logDeriv (liClockPairedEtaContiguousPartition L))
          (1/2 : ℂ)).re * t^(2*j+1) / ((2*j+1).factorial : ℝ)^2 := by
  have h := partitionClock_eq_series hr (reference_closedDisk_nonzero hL hrhalf) t
  simpa only [liClockPairedEtaContiguousPartitionClockReal, pResponse, pTerm,
    referenceClockCoefficient, referenceEvenCumulant, div_mul_eq_mul_div] using h

/-- The literal reference clock is real at every real clock. -/
theorem liClockPairedEtaContiguousPartitionClock_im_ofReal_eq_zero
    {L r : ℝ} (hL : 0 < L) (hr : 0 < r) (hrhalf : r < 1/2) (t : ℝ) :
    (liClockPairedEtaContiguousPartitionClock L r (t : ℂ)).im = 0 := by
  rw [liClockPairedEtaContiguousPartitionClock_eq_two_sinh_sub_clock hL hr hrhalf,
    Complex.sub_im, liClockPairedEtaContiguousClock_im_ofReal_eq_zero hL t, sub_zero,
    Complex.mul_im]
  have hcast : 2*(t : ℂ) = ((2*t : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, ← Complex.ofReal_sinh]
  norm_num only [Complex.ofReal_re, Complex.ofReal_im, Complex.natCast_re,
    Complex.natCast_im, mul_zero, zero_mul, zero_add]
  change (0 : ℝ) * Real.sinh (2*t) = 0
  exact zero_mul _

/-- Genuine continuity of the original reference contour's real restriction. -/
theorem continuous_liClockPairedEtaContiguousPartitionClockReal
    {L r : ℝ} (hL : 0 < L) (hr : 0 < r) (hrhalf : r < 1/2) :
    Continuous (liClockPairedEtaContiguousPartitionClockReal L r) := by
  have hc := continuous_liClockCentralTraceSineContour hr
    ((partitionTrace_diffCont (reference_closedDisk_nonzero hL hrhalf)).continuousOn_ball.mono
      sphere_subset_closedBall)
  exact Complex.continuous_re.comp (hc.comp Complex.continuous_ofReal)

/-- Exact derivative of the complete reference Borel kernel, including zero clock. -/
theorem hasDerivAt_liClockPairedEtaContiguousBorelKernel
    {L : ℝ} (hL : 0 < L) (t : ℝ) :
    HasDerivAt (liClockPairedEtaContiguousBorelKernel L)
      (∑' j : ℕ, liClockPairedEtaContiguousBorelCoefficient L j *
        (2*j : ℝ) * t^(2*j-1)) t :=
  hasDerivAt_gKernel (liClockPairedEtaContiguousBorelCoefficient_pos hL) (sq_nonneg L)
    (liClockPairedEtaContiguousBorelCoefficient_le hL) t

private lemma reference_kernel_mul_deriv {L : ℝ} (hL : 0 < L) (t : ℝ) :
    t * deriv (liClockPairedEtaContiguousBorelKernel L) t =
      ∑' j : ℕ, (2*j : ℝ) * liClockPairedEtaContiguousBorelCoefficient L j * t^(2*j) := by
  change t * deriv (gKernel (liClockPairedEtaContiguousBorelCoefficient L)) t = _
  simpa only [gWeighted, gTerm, mul_assoc] using
    gKernel_mul_deriv (liClockPairedEtaContiguousBorelCoefficient_pos hL) (sq_nonneg L)
      (liClockPairedEtaContiguousBorelCoefficient_le hL) t

/-- Symmetrization factor two for the literal reference partition clock. -/
theorem liClockPairedEtaContiguousPartitionClock_volterra
    {L r : ℝ} (hL : 0 < L) (hr : 0 < r) (hrhalf : r < 1/2)
    {t : ℝ} (ht : 0 ≤ t) :
    2 * (∫ s in (0 : ℝ)..t,
      liClockPairedEtaContiguousPartitionClockReal L r s *
        liClockPairedEtaContiguousBorelKernel L (t-s)) =
      t * deriv (liClockPairedEtaContiguousBorelKernel L) t := by
  have h := pResponse_volterra
    (partitionPterm_summable hr (reference_closedDisk_nonzero hL hrhalf))
    (liClockPairedEtaContiguousBorelCoefficient_pos hL) (sq_nonneg L)
    (liClockPairedEtaContiguousBorelCoefficient_le hL) (partitionCoefficient_recurrence hL) ht
  have heq : liClockPairedEtaContiguousPartitionClockReal L r =
      pResponse (referenceClockCoefficient L) := by
    funext s
    exact partitionClock_eq_series hr (reference_closedDisk_nonzero hL hrhalf) s
  rw [heq, reference_kernel_mul_deriv hL]
  simpa only [gKernel, gWeighted, gTerm, liClockPairedEtaContiguousBorelKernel, mul_assoc] using h

/-- Every nonempty actual prefix and its contiguous reference share a full regular disk. -/
theorem liClockPairedEtaPartition_exists_common_regular_radius
    {N : ℕ} (hN : 0 < N) :
    ∃ r : ℝ, 0 < r ∧ r < 1/2 ∧
      (∀ z ∈ closedBall (0 : ℂ) r,
        pairedEtaFiniteLaplacePartition N (1/2+z*I) ≠ 0) ∧
      (∀ z ∈ closedBall (0 : ℂ) r,
        liClockPairedEtaContiguousPartition (Real.log (2*(N : ℝ))) (1/2+z*I) ≠ 0) := by
  obtain ⟨a, ha, hA⟩ := liClockPairedEtaPartition_exists_regular_radius hN
  have hL : 0 < Real.log (2*(N : ℝ)) := Real.log_pos (by exact_mod_cast (show 1 < 2*N by omega))
  refine ⟨min a (1/4), lt_min ha (by norm_num), (min_le_right _ _).trans_lt (by norm_num), ?_,
    reference_closedDisk_nonzero hL ((min_le_right _ _).trans_lt (by norm_num))⟩
  intro z hz
  exact hA z (closedBall_subset_closedBall (min_le_left _ _) hz)

end
end RHTower
