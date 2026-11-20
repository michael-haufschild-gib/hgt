import GaloisForLFunctions.MultiscaleMollifiedZetaField.RandomDirichletJets.TheCovarianceOfMixedZetaDerivatives
import GaloisForLFunctions.HTGeometry.HypoexponentialListLaw
import Mathlib.Analysis.SumIntegralComparisons

/-!
# Simultaneous critical and cutoff limits of Dirichlet jets

At distance ε/2 from the critical line, the fraction of the mixed
second moment visible up to N is an Erlang distribution function at
ε log N. The finite-cutoff error is uniform in N. The logarithmic
moment density is the difference of two decreasing Erlang survival
functions, each with a rectangle-rule error in the unit interval.
-/

noncomputable section
open Finset Filter Topology MeasureTheory
open GaloisForLFunctions.HTGeometry.PrimeShiftSource
open scoped Interval ComplexConjugate
namespace GaloisForLFunctions.MultiscaleMollifiedZetaField.RandomDirichletJets

private def rectangleError (g : ℝ → ℝ) (N : ℕ) :=
  (∑ n ∈ Icc (1:ℕ) N, g n) - ∫ x in (1:ℝ)..N, g x

private theorem rectangle_bounds {g : ℝ → ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hg : AntitoneOn g (Set.Ici 1)) (h₀ : 0 ≤ g N) (h₁ : g 1 ≤ 1) :
    0 ≤ rectangleError g N ∧ rectangleError g N ≤ 1 := by
  have h : AntitoneOn g (Set.Icc ((1:ℕ):ℝ) (N:ℝ)) := hg.mono fun x hx => by
    change (1:ℝ) ≤ x
    simpa only [Nat.cast_one] using hx.1
  have hlo := AntitoneOn.integral_le_sum_Ico (f:=g) hN h
  have hhi := AntitoneOn.sum_le_integral_Ico (f:=g) hN h
  have hs : (∑ i ∈ Ico 1 N, g (↑(i+1):ℝ)) = ∑ i ∈ Ioc 1 N, g (i:ℝ) := by
    have hi : Ico ((1:ℕ)+1) (N+1) = Ioc 1 N := by
      ext i
      simp only [mem_Ico,mem_Ioc]
      omega
    simpa only [hi] using sum_Ico_add' (fun i : ℕ => g i) 1 N 1
  rw [hs] at hhi
  simp only [Nat.cast_one] at hlo hhi
  constructor
  · rw [rectangleError,Icc_eq_cons_Ico hN,sum_cons]
    linarith only [hlo,h₀]
  · rw [rectangleError,Icc_eq_cons_Ioc hN,sum_cons,Nat.cast_one]
    linarith only [hhi,h₁]

private def survival (k : ℕ) (c x : ℝ) := 1-erlangCDF k c (Real.log x)

private theorem survival_bounds (k : ℕ) {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) :
    0 ≤ rectangleError (survival k c) N ∧ rectangleError (survival k c) N ≤ 1 := by
  let rates := List.replicate k c
  have hr : ∀ u ∈ rates, 0 < u := by
    intro u hu
    rw [List.eq_of_mem_replicate hu]
    exact hc
  have hfun (x : ℝ) : survival k c x = 1-hypoCDFList rates (Real.log x) := by
    rw [survival,hypoCDFList_replicate]
  apply rectangle_bounds hN
  · intro x hx y hy hxy
    rw [hfun,hfun]
    exact sub_le_sub_left (monotoneOn_hypoCDFList hr (Real.log_nonneg hx) (Real.log_nonneg hy)
      (Real.log_le_log (zero_lt_one.trans_le hx) hxy)) _
  · rw [hfun]
    exact sub_nonneg.mpr (hypoCDFList_le_one hr (Real.log_nonneg (Nat.one_le_cast.mpr hN)))
  · rw [hfun,Real.log_one]
    linarith only [hypoCDFList_nonneg hr (le_rfl : (0:ℝ) ≤ 0)]

private theorem erlang_step (k : ℕ) (c t : ℝ) :
    erlangCDF k c t-erlangCDF (k+1) c t =
      Real.exp (-(c*t))*(c*t)^k/(k.factorial:ℝ) := by
  simp only [erlangCDF,sum_range_succ]
  ring

private theorem erlang_deriv (k : ℕ) (c t : ℝ) :
    HasDerivAt (erlangCDF (k+1) c) (c*(Real.exp (-(c*t))*(c*t)^k/(k.factorial:ℝ))) t := by
  rw [←erlang_step]
  have H := (hasDerivAt_exp_mul_erlangCDF k c t).div (hasDerivAt_exp_mul c t) (Real.exp_ne_zero _)
  have he : ((fun s => Real.exp (c*s)*erlangCDF (k+1) c s)/(fun s => Real.exp (c*s))) =
      erlangCDF (k+1) c := by
    funext s
    rw [Pi.div_apply,div_eq_iff (Real.exp_ne_zero _)]; ring
  rw [he] at H
  apply H.congr_deriv
  field_simp

private def logDensity (k : ℕ) (c x : ℝ) := (Real.log x)^k*Real.exp (-(c*Real.log x))

private theorem log_density_formula (k : ℕ) {c : ℝ} (hc : 0 < c) (x : ℝ) :
    logDensity k c x = (k.factorial:ℝ)/c^k*(survival (k+1) c x-survival k c x) := by
  rw [survival,survival,sub_sub_sub_cancel_left,erlang_step,mul_pow,logDensity]
  have hk : (k.factorial:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  field_simp

private theorem density_quadrature (k : ℕ) {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) :
    |rectangleError (logDensity k c) N| ≤ (k.factorial:ℝ)/c^k := by
  let C := (k.factorial:ℝ)/c^k
  have hC : 0 ≤ C := div_nonneg (Nat.cast_nonneg _) (pow_nonneg hc.le _)
  have hi (j : ℕ) : IntervalIntegrable (survival j c) volume 1 N := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (Nat.one_le_cast.mpr hN)]
    intro x hx
    have hl := Real.continuousAt_log (zero_lt_one.trans_le hx.1).ne'
    have hc' : Continuous (fun y => 1-erlangCDF j c y) := by unfold erlangCDF; fun_prop
    exact (hc'.continuousAt.comp hl).continuousWithinAt
  have he : rectangleError (logDensity k c) N =
      C*(rectangleError (survival (k+1) c) N-rectangleError (survival k c) N) := by
    simp_rw [rectangleError,log_density_formula k hc]
    rw [←mul_sum,sum_sub_distrib,intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub (hi _) (hi _)]
    dsimp only [C]
    ring
  have ha := survival_bounds (k+1) hc hN
  have hb := survival_bounds k hc hN
  rw [he,abs_mul,abs_of_nonneg hC]
  exact (mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith only [ha.1,hb.2],
    by linarith only [ha.2,hb.1]⟩ : |rectangleError (survival (k+1) c) N-
      rectangleError (survival k c) N| ≤ 1) hC).trans_eq (mul_one C)

private theorem density_integral (k : ℕ) {ε : ℝ} (hε : 0 < ε) {N : ℕ} (hN : 1 ≤ N) :
    ε^(k+1)*(∫ x in (1:ℝ)..N, logDensity k (1+ε) x) =
      (k.factorial:ℝ)*erlangCDF (k+1) ε (Real.log N) := by
  let F (x : ℝ) := (k.factorial:ℝ)*erlangCDF (k+1) ε (Real.log x)
  let f (x : ℝ) := ε^(k+1)*logDensity k (1+ε) x
  have hpos {x : ℝ} (hx : x ∈ Set.uIcc (1:ℝ) N) : 0 < x := by
    rw [Set.uIcc_of_le (Nat.one_le_cast.mpr hN)] at hx
    exact zero_lt_one.trans_le hx.1
  have hd (x : ℝ) (hx : x ∈ Set.uIcc (1:ℝ) N) : HasDerivAt F (f x) x := by
    have hp := hpos hx
    have H := ((erlang_deriv k ε (Real.log x)).comp x (Real.hasDerivAt_log hp.ne')).const_mul (k.factorial:ℝ)
    apply H.congr_deriv
    have he : Real.exp (-((1+ε)*Real.log x)) = x⁻¹*Real.exp (-(ε*Real.log x)) := by
      rw [show -((1+ε)*Real.log x) = -Real.log x + -(ε*Real.log x) by ring,Real.exp_add,
        Real.exp_neg (Real.log x),Real.exp_log hp]
    dsimp only [f,logDensity]
    rw [he,mul_pow,pow_succ]
    have hk : (k.factorial:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
    field_simp
  have hi : IntervalIntegrable f volume 1 N := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    have hl := Real.continuousAt_log (hpos hx).ne'
    dsimp only [f,logDensity]
    fun_prop
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  have hzero : F 1=0 := by simp [F,erlangCDF,sum_range_succ']
  rw [hzero,sub_zero] at H
  simpa only [f,intervalIntegral.integral_const_mul,F] using H

/-- At every cutoff the rescaled logarithmic mode sum differs from its
Erlang profile by at most k! ε^(k+1)/(1+ε)^k. -/
theorem finite_log_moment_erlang_window (k : ℕ) {ε : ℝ} (hε : 0 < ε) {N : ℕ} (hN : 1 ≤ N) :
    |ε^(k+1)*(∑ n ∈ Icc (1:ℕ) N, (Real.log n)^k*Real.exp (-((1+ε)*Real.log n)))-
      (k.factorial:ℝ)*erlangCDF (k+1) ε (Real.log N)| ≤
      ε^(k+1)*((k.factorial:ℝ)/(1+ε)^k) := by
  rw [←density_integral k hε hN,←mul_sub,abs_mul,abs_of_nonneg (pow_nonneg hε.le _)]
  exact mul_le_mul_of_nonneg_left (density_quadrature k (by linarith only [hε]) hN) (pow_nonneg hε.le _)

private theorem finite_real_kernel (a b N : ℕ) (ε : ℝ) :
    mixedJetMoment N a b ((1+(ε:ℂ))/2) ((1+(ε:ℂ))/2) =
      ((-1:ℂ)^(a+b))*((∑ n ∈ Icc (1:ℕ) N, logDensity (a+b) (1+ε) n:ℝ):ℂ) := by
  rw [mixed_jet_finite_kernel,Complex.ofReal_sum,mul_sum]
  apply sum_congr rfl
  intro n _
  have he : (1+(ε:ℂ))/2+(starRingEnd ℂ) ((1+(ε:ℂ))/2) = 1+(ε:ℂ) := by
    simp only [map_div₀,map_add,map_one,map_ofNat,Complex.conj_ofReal]; ring
  rw [he,dirichletJetMode,logDensity,Complex.ofReal_mul,Complex.ofReal_exp,
    Complex.ofReal_neg,Complex.ofReal_mul,Complex.ofReal_add,Complex.ofReal_one,Complex.ofReal_pow]
  rw [show -(Real.log n:ℂ)*(1+(ε:ℂ)) = -((1+(ε:ℂ))*(Real.log n:ℂ)) by ring]
  rw [show -(Real.log n:ℂ)=(-1:ℂ)*(Real.log n:ℂ) by ring,mul_pow]
  ring

/-- The cutoff may grow together with the inverse distance to the line.
For finite ε log N the incomplete Erlang profile replaces the full factorial moment. -/
theorem joint_critical_jet_cutoff (a b : ℕ) (N : ℕ → ℕ) (ε : ℕ → ℝ) {t : ℝ}
    (hpos : ∀ᶠ j in atTop, 0 < ε j ∧ 1 ≤ N j) (hε : Tendsto ε atTop (𝓝 0))
    (ht : Tendsto (fun j => ε j*Real.log (N j)) atTop (𝓝 t)) :
    Tendsto (fun j => (ε j:ℂ)^(a+b+1)*mixedJetMoment (N j) a b
      ((1+(ε j:ℂ))/2) ((1+(ε j:ℂ))/2)) atTop
      (𝓝 ((-1:ℂ)^(a+b)*((a+b).factorial:ℂ)*(erlangCDF (a+b+1) 1 t:ℂ))) := by
  let k := a+b
  let S (j : ℕ) := (ε j)^(k+1)*∑ n ∈ Icc (1:ℕ) (N j), logDensity k (1+ε j) n
  let A (j : ℕ) := (k.factorial:ℝ)*erlangCDF (k+1) 1 (ε j*Real.log (N j))
  have hA : Tendsto A atTop (𝓝 ((k.factorial:ℝ)*erlangCDF (k+1) 1 t)) := by
    have H : Continuous (erlangCDF (k+1) 1) := by unfold erlangCDF; fun_prop
    exact (H.continuousAt.tendsto.comp ht).const_mul _
  have herr : Tendsto (fun j => S j-A j) atTop (𝓝 0) := by
    have hb : Tendsto (fun j => (ε j)^(k+1)*((k.factorial:ℝ)/(1+ε j)^k)) atTop (𝓝 0) := by
      simpa using (hε.pow (k+1)).mul (tendsto_const_nhds.div ((tendsto_const_nhds.add hε).pow k) (by simp))
    apply squeeze_zero_norm' _ hb
    filter_upwards [hpos] with j hj
    simpa only [S,A,Real.norm_eq_abs,logDensity,erlangCDF,one_mul] using
      finite_log_moment_erlang_window k hj.1 hj.2
  have hs : Tendsto S atTop (𝓝 ((k.factorial:ℝ)*erlangCDF (k+1) 1 t)) := by
    simpa only [Pi.add_apply,sub_add_cancel,zero_add] using herr.add hA
  have h := (Complex.continuous_ofReal.continuousAt.tendsto.comp hs).const_mul ((-1:ℂ)^k)
  simpa only [finite_real_kernel,S,k,Function.comp_apply,Complex.ofReal_mul,Complex.ofReal_pow,
    Complex.ofReal_natCast,mul_assoc,mul_left_comm] using h

/-- Fraction of the limiting factorial moment observed below the cutoff. -/
def criticalJetFraction (a b N : ℕ) (ε : ℝ) : ℝ :=
  ε^(a+b+1)*‖mixedJetMoment N a b ((1+(ε:ℂ))/2) ((1+(ε:ℂ))/2)‖/((a+b).factorial:ℝ)

private theorem fraction_error (a b : ℕ) {N : ℕ} {ε : ℝ} (hN : 1 ≤ N) (hε : 0 < ε) :
    |criticalJetFraction a b N ε-erlangCDF (a+b+1) 1 (ε*Real.log N)| ≤ ε^(a+b+1) := by
  let k := a+b
  have hs : 0 ≤ ∑ n ∈ Icc (1:ℕ) N, logDensity k (1+ε) n := by
    apply sum_nonneg
    intro n hn
    exact mul_nonneg (pow_nonneg (Real.log_nonneg (Nat.one_le_cast.mpr (mem_Icc.mp hn).1)) _)
      (Real.exp_pos _).le
  have he : erlangCDF (k+1) 1 (ε*Real.log N) = erlangCDF (k+1) ε (Real.log N) := by
    simp only [erlangCDF,one_mul]
  change |ε^(k+1)*‖mixedJetMoment N a b _ _‖/(k.factorial:ℝ)-_| ≤ _
  rw [finite_real_kernel,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hs,he]
  have hk : (0:ℝ)<k.factorial := Nat.cast_pos.mpr k.factorial_pos
  rw [div_sub' hk.ne',abs_div,abs_of_pos hk,div_le_iff₀ hk]
  have hd : (1:ℝ) ≤ (1+ε)^k := one_le_pow₀ (by linarith only [hε])
  have H := finite_log_moment_erlang_window k hε hN
  exact H.trans (mul_le_mul_of_nonneg_left (div_le_self hk.le hd) (pow_nonneg hε.le _))

/-- Full recovery of the mixed moment holds exactly when ε log N tends
to infinity. This also excludes oscillating cutoffs that repeatedly miss
a positive portion of the mass. -/
theorem full_critical_jet_fraction_iff (a b : ℕ) (N : ℕ → ℕ) (ε : ℕ → ℝ)
    (hpos : ∀ᶠ j in atTop, 0 < ε j ∧ 1 ≤ N j) (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun j => criticalJetFraction a b (N j) (ε j)) atTop (𝓝 1) ↔
    Tendsto (fun j => ε j*Real.log (N j)) atTop atTop := by
  let k := a+b+1
  let x (j : ℕ) := ε j*Real.log (N j)
  let F := erlangCDF k 1
  let S (j : ℕ) := criticalJetFraction a b (N j) (ε j)
  have hd : Tendsto (fun j => S j-F (x j)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (by simpa only [zero_pow (Nat.succ_ne_zero (a+b))] using hε.pow (a+b+1))
    filter_upwards [hpos] with j hj
    exact fraction_error a b hj.2 hj.1
  have rates : ∀ u ∈ List.replicate k (1:ℝ), 0 < u := by
    intro u hu
    rw [List.eq_of_mem_replicate hu]
    exact zero_lt_one
  have hF : hypoCDFList (List.replicate k 1) = F := funext (hypoCDFList_replicate k 1)
  have hm : MonotoneOn F (Set.Ici 0) := hF ▸ monotoneOn_hypoCDFList rates
  have hlim : Tendsto F atTop (𝓝 1) := hF ▸ tendsto_hypoCDFList_atTop rates
  constructor
  · intro h
    have hFj : Tendsto (fun j => F (x j)) atTop (𝓝 1) := by
      have H : Tendsto (fun j => S j-(S j-F (x j))) atTop (𝓝 (1-0)) := h.sub hd
      simpa only [sub_sub_cancel,sub_zero] using H
    apply tendsto_atTop.mpr
    intro B
    have hB : F (max 0 B) < 1 := erlangCDF_lt_one (Nat.succ_pos _) (by simp)
    filter_upwards [hFj.eventually (lt_mem_nhds hB),hpos] with j hj hposj
    have hx : 0 ≤ x j := mul_nonneg hposj.1.le (Real.log_nonneg (Nat.one_le_cast.mpr hposj.2))
    exact (le_max_right 0 B).trans (le_of_not_ge fun hle =>
      (not_le_of_gt hj) (hm hx (le_max_left (0:ℝ) B) hle))
  · intro hx
    have H : Tendsto (fun j => S j-F (x j)+F (x j)) atTop (𝓝 (0+1)) := hd.add (hlim.comp hx)
    simpa only [sub_add_cancel,zero_add] using H

#print axioms finite_log_moment_erlang_window
#print axioms joint_critical_jet_cutoff
#print axioms full_critical_jet_fraction_iff

end GaloisForLFunctions.MultiscaleMollifiedZetaField.RandomDirichletJets
