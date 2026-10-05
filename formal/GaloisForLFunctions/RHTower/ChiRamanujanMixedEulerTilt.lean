import GaloisForLFunctions.RHTower.ChiRamanujanOscillatoryLogWindow
import GaloisForLFunctions.RHTower.ChiRamanujanMovingCofactorLimit
/-!
# Stability of the actual off-pole Euler product under logarithmic tilts

For every nonzero real frequency and fixed complex displacement, the original
finite Euler product at `1 + i*tau - u/log N`, divided by its exact boundary
product at `1 + i*tau`, tends to one at the original prime cutoff.

The actual oscillatory prime-window theorem kills the full linear logarithmic
perturbation. A summable quadratic logarithm remainder controls all prime
factors simultaneously, including the fixed-prime head. Exponentiating the
exact finite identity gives the ratio without assuming boundary convergence.

Identification of the boundary product with inverse zeta, complete rational
label responses/collisions and uniform physical remainder/tails are separate
obligations. No complete mixed labelled source or signed axes saving is asserted.
-/

noncomputable section
open Filter MeasureTheory
open scoped Topology BigOperators
namespace RHTower.BAGTrace

private theorem complex_sum_zero {r : ℕ → ℕ → ℂ} {B : ℕ → ℝ}
    (hB : Summable B) (hB0 : ∀ n, 0 ≤ B n)
    (hbd : ∀ᶠ N in atTop, ∀ n, n ≤ N → ‖r N n‖ ≤ B n)
    (hr : ∀ n, Tendsto (fun N => r N n) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 0 N,r N n) atTop (𝓝 0) := by
  let f (N n : ℕ) : ℂ := if n ≤ N then r N n else 0
  have hs (N : ℕ) : (∑ n ∈ Finset.Icc 0 N,r N n) = ∑' n,f N n := by
    rw [tsum_eq_sum (s := Finset.Icc 0 N) (fun n hn => by
      simp only [Finset.mem_Icc,Nat.zero_le,true_and] at hn
      simp [f,hn])]
    exact Finset.sum_congr rfl fun n hn => by simp [f,(Finset.mem_Icc.mp hn).2]
  have hf (n : ℕ) : Tendsto (fun N => f N n) atTop (𝓝 0) := by
    apply (hr n).congr'
    filter_upwards [eventually_ge_atTop n] with N hN
    simp [f,hN]
  have hb : ∀ᶠ N in atTop, ∀ n, ‖f N n‖ ≤ B n := by
    filter_upwards [hbd] with N hN n
    by_cases hn : n ≤ N
    · simpa [f,hn] using hN n hn
    · simpa [f,hn] using hB0 n
  have h := tendsto_tsum_of_dominated_convergence
    (f := f) (g := fun _ : ℕ => (0 : ℂ)) hB hf hb
  simpa only [hs,tsum_zero] using h


private def mixedNome (tau : ℝ) (u : ℂ) (N n : ℕ) : ℂ :=
  Complex.exp ((u/(Real.log N : ℂ)-1-(tau : ℂ)*Complex.I)*(Real.log n : ℂ))

private theorem nome_eq (tau : ℝ) (u : ℂ) (N : ℕ) {n : ℕ} (hn : 0<n) :
    mixedNome tau u N n=(n : ℂ)^(-1-(tau : ℂ)*Complex.I+u/(Real.log N : ℂ)) := by
  rw [mixedNome,Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn.ne')]
  have hp : (0 : ℝ)<n := by exact_mod_cast hn
  rw [show (n : ℂ)=((n : ℝ) : ℂ) by simp,← Complex.ofReal_log hp.le]
  congr 1
  ring

private theorem nome_zero (tau : ℝ) (N : ℕ) {n : ℕ} (hn : 0<n) :
    mixedNome tau 0 N n=criticalPrimeBoundaryCoeff tau n := by
  rw [nome_eq tau 0 N hn]
  simp [criticalPrimeBoundaryCoeff]

private theorem nome_norm (tau : ℝ) (u : ℂ) (N : ℕ) {n : ℕ} (hn : 2≤n) :
    ‖mixedNome tau u N n‖=radialNome (u.re/(2*Real.log N)) n := by
  rw [mixedNome,Complex.norm_exp,radialNome_eq_exp hn]
  congr 1
  simp only [Complex.mul_re,Complex.sub_re,Complex.div_ofReal_re,Complex.I_re,Complex.I_im,
    Complex.one_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  ring

private theorem drift_zero (u : ℂ) :
    Tendsto (fun N : ℕ => u/(Real.log N : ℂ)) atTop (𝓝 0) := by
  have h := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp (tendsto_drift_zero 1)
  simpa only [Function.comp_def,Complex.ofReal_div,Complex.ofReal_one,
    Complex.ofReal_zero,mul_zero,mul_one_div] using h.const_mul u

private theorem nome_tendsto (tau : ℝ) (u : ℂ) {n : ℕ} (hn : 0<n) :
    Tendsto (fun N : ℕ => mixedNome tau u N n) atTop (𝓝 (criticalPrimeBoundaryCoeff tau n)) := by
  have h := (((drift_zero u).sub_const 1).sub_const ((tau : ℂ)*Complex.I)).mul_const (Real.log n : ℂ)
  have he := (Complex.continuous_exp.tendsto _).comp h
  have hval : Complex.exp ((0-1-(tau : ℂ)*Complex.I)*(Real.log n : ℂ))=
      criticalPrimeBoundaryCoeff tau n := by
    simpa [mixedNome] using nome_zero tau 1 hn
  simpa only [hval,Function.comp_def,mixedNome] using he

private theorem norm_log_error {q : ℂ} (hq : ‖q‖ ≤ 3/4) :
    ‖Complex.log (1-q)+q‖ ≤ 2*‖q‖^2 := by
  have hn : ‖-q‖ < 1 := by rw [norm_neg]; linarith
  have h := Complex.norm_log_one_add_sub_self_le hn
  have hden : 0 < 1-‖q‖ := by linarith
  have hi : (1-‖q‖)⁻¹ ≤ (4 : ℝ) := by
    have hm := mul_inv_cancel₀ hden.ne'
    nlinarith [mul_nonneg (show 0 ≤ 3/4-‖q‖ by linarith)
      (inv_nonneg.mpr hden.le)]
  have hb : ‖q‖^2*(1-‖q‖)⁻¹/2 ≤ 2*‖q‖^2 := by
    nlinarith [mul_le_mul_of_nonneg_left hi (sq_nonneg ‖q‖)]
  have h' : ‖Complex.log (1-q)+q‖ ≤ ‖q‖^2*(1-‖q‖)⁻¹/2 := by
    simpa only [norm_neg,sub_neg_eq_add,sub_eq_add_neg,neg_neg] using h
  exact h'.trans hb

private def mixedRemainder (tau : ℝ) (u : ℂ) (N n : ℕ) : ℂ :=
  if n.Prime then
    (Complex.log (1-mixedNome tau u N n)+mixedNome tau u N n)-
      (Complex.log (1-criticalPrimeBoundaryCoeff tau n)+criticalPrimeBoundaryCoeff tau n)
  else 0

private theorem remainder_bound (tau : ℝ) (u : ℂ) (N : ℕ)
    (hN : |u.re/(2*Real.log N)| ≤ 1/8) (n : ℕ) :
    ‖mixedRemainder tau u N n‖ ≤ 4*(n : ℝ)^(-(3/2) : ℝ) := by
  by_cases hn : n.Prime
  · have hn0 := hn.pos
    have hq : ‖mixedNome tau u N n‖ ≤ 3/4 := by
      rw [nome_norm tau u N hn.two_le]
      exact radialNome_le hn.two_le hN
    have hz : ‖criticalPrimeBoundaryCoeff tau n‖ ≤ 3/4 := by
      rw [← nome_zero tau N hn0,nome_norm tau 0 N hn.two_le]
      exact radialNome_le hn.two_le (by simp)
    have hs : ‖mixedNome tau u N n‖^2 ≤ (n : ℝ)^(-(3/2) : ℝ) := by
      rw [nome_norm tau u N hn.two_le]
      exact sq_radialNome_le hn.two_le hN
    have hsz : ‖criticalPrimeBoundaryCoeff tau n‖^2 ≤ (n : ℝ)^(-(3/2) : ℝ) := by
      rw [← nome_zero tau N hn0,nome_norm tau 0 N hn.two_le]
      exact sq_radialNome_le hn.two_le (by simp)
    rw [mixedRemainder,if_pos hn]
    refine (norm_sub_le _ _).trans ?_
    linarith [norm_log_error hq,norm_log_error hz]
  · simp only [mixedRemainder,if_neg hn,norm_zero]
    positivity

private theorem remainder_zero (tau : ℝ) (u : ℂ) (n : ℕ) :
    Tendsto (fun N : ℕ => mixedRemainder tau u N n) atTop (𝓝 0) := by
  by_cases hn : n.Prime
  · have hz : ‖-criticalPrimeBoundaryCoeff tau n‖ < 1 := by
      rw [norm_neg,← nome_zero tau 1 hn.pos,nome_norm tau 0 1 hn.two_le]
      simpa using (radialNome_le (c := 0) hn.two_le (by norm_num)).trans_lt
        (by norm_num : (3/4 : ℝ)<1)
    have h := nome_tendsto tau u hn.pos
    have hl := (tendsto_const_nhds.sub h).clog
      (by simpa only [sub_eq_add_neg] using Complex.mem_slitPlane_of_norm_lt_one hz)
    have he := (hl.add h).sub_const (Complex.log (1-criticalPrimeBoundaryCoeff tau n)+criticalPrimeBoundaryCoeff tau n)
    simpa only [mixedRemainder,if_pos hn,sub_self] using he
  · simp only [mixedRemainder,if_neg hn]
    exact tendsto_const_nhds

private theorem sum_remainder_zero (tau : ℝ) (u : ℂ) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 0 N,mixedRemainder tau u N n)
      atTop (𝓝 0) := by
  have hsum : Summable (fun n : ℕ => 4*(n : ℝ)^(-(3/2) : ℝ)) :=
    (Real.summable_nat_rpow.mpr (by norm_num : (-(3/2) : ℝ) < -1)).mul_left 4
  apply complex_sum_zero hsum (fun n => by positivity) _ (remainder_zero tau u)
  have he := eventually_abs_drift_le (u.re/2)
  filter_upwards [he] with N hN n _
  apply remainder_bound tau u N _ n
  convert hN using 1
  congr 1
  ring

private theorem nome_sub (tau : ℝ) (u : ℂ) (N : ℕ) {n : ℕ} (hn : 0<n) :
    mixedNome tau u N n-criticalPrimeBoundaryCoeff tau n =
      (Complex.exp (u*((Real.log n/Real.log N : ℝ) : ℂ))-1)*criticalPrimeBoundaryCoeff tau n := by
  have he : mixedNome tau u N n =
      Complex.exp (u*((Real.log n/Real.log N : ℝ) : ℂ))*mixedNome tau 0 N n := by
    rw [mixedNome,mixedNome,← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he,nome_zero tau N hn]
  ring

private theorem prime_linear_difference (tau : ℝˣ) (u : ℂ) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 0 N,
      if n.Prime then (Complex.exp (u*((Real.log n/Real.log N : ℝ) : ℂ))-1)*
        criticalPrimeBoundaryCoeff tau n else 0) atTop (𝓝 0) := by
  have h := criticalOscillatoryLogWindow_difference_tendsto tau u
  apply h.congr
  intro N
  rw [← Finset.sum_filter]
  congr 1
  ext n
  simp [Nat.mem_primesLE]

private def mixedLogRatio (tau : ℝ) (u : ℂ) (N n : ℕ) : ℂ :=
  if n.Prime then Complex.log (1-mixedNome tau u N n)-
    Complex.log (1-criticalPrimeBoundaryCoeff tau n) else 0

private theorem sum_log_ratio (tau : ℝˣ) (u : ℂ) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 0 N,mixedLogRatio tau u N n) atTop (𝓝 0) := by
  have h := (prime_linear_difference tau u).neg.add (sum_remainder_zero tau u)
  simp only [neg_zero,add_zero] at h
  refine h.congr fun N => ?_
  rw [← Finset.sum_neg_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : n.Prime
  · rw [if_pos hn,mixedRemainder,if_pos hn,mixedLogRatio,if_pos hn,← nome_sub tau u N hn.pos]
    ring
  · simp [hn,mixedRemainder,mixedLogRatio]

/-- The original growing Euler product divided by its exact off-pole boundary product. -/
def criticalMixedEulerTiltRatio (tau : ℝ) (u : ℂ) (N : ℕ) : ℂ :=
  ∏ p ∈ Nat.primesLE N,
    (1-(p : ℂ)^(-1-(tau : ℂ)*Complex.I+u/(Real.log N : ℂ)))/(1-criticalPrimeBoundaryCoeff tau p)

private theorem exp_sum_log_ratio (tau : ℝ) (u : ℂ) (N : ℕ)
    (hN : |u.re/(2*Real.log N)| ≤ 1/8) :
    Complex.exp (∑ n ∈ Finset.Icc 0 N,mixedLogRatio tau u N n)=criticalMixedEulerTiltRatio tau u N := by
  rw [Complex.exp_sum]
  have he (n : ℕ) : Complex.exp (mixedLogRatio tau u N n) =
      if n.Prime then
        (1-(n : ℂ)^(-1-(tau : ℂ)*Complex.I+u/(Real.log N : ℂ)))/(1-criticalPrimeBoundaryCoeff tau n)
        else 1 := by
    by_cases hn : n.Prime
    · have hq : ‖mixedNome tau u N n‖<1 := by
        rw [nome_norm tau u N hn.two_le]
        exact (radialNome_le hn.two_le hN).trans_lt (by norm_num)
      have hz : ‖criticalPrimeBoundaryCoeff tau n‖<1 := by
        rw [← nome_zero tau N hn.pos,nome_norm tau 0 N hn.two_le]
        exact (radialNome_le hn.two_le (show |(0 : ℂ).re/(2*Real.log N)| ≤ 1/8 by simp)).trans_lt
          (by norm_num : (3/4 : ℝ)<1)
      have hq0 : 1-mixedNome tau u N n≠0 := by
        intro hh
        have hh' := sub_eq_zero.mp hh
        rw [← hh',norm_one] at hq
        exact (lt_irrefl _ hq)
      have hz0 : 1-criticalPrimeBoundaryCoeff tau n≠0 := by
        intro hh
        have hh' := sub_eq_zero.mp hh
        rw [← hh',norm_one] at hz
        exact (lt_irrefl _ hz)
      rw [mixedLogRatio,if_pos hn,if_pos hn,Complex.exp_sub,
        Complex.exp_log hq0,Complex.exp_log hz0,nome_eq tau u N hn.pos]
    · simp [mixedLogRatio,hn]
  simp_rw [he]
  rw [← Finset.prod_filter,criticalMixedEulerTiltRatio]
  congr 1
  ext n
  simp [Finset.mem_filter,Finset.mem_Icc,Nat.mem_primesLE]

/-- Every fixed logarithmic complex tilt preserves the complete off-pole finite Euler product
asymptotically, at the original prime cutoff. No boundary-product limit is assumed. -/
theorem criticalMixedEulerTiltRatio_tendsto (tau : ℝˣ) (u : ℂ) :
    Tendsto (criticalMixedEulerTiltRatio tau u) atTop (𝓝 1) := by
  have h := (Complex.continuous_exp.tendsto _).comp (sum_log_ratio tau u)
  simp only [Complex.exp_zero] at h
  apply h.congr'
  have he := eventually_abs_drift_le (u.re/2)
  filter_upwards [he] with N hN
  apply exp_sum_log_ratio tau u N
  convert hN using 1
  congr 1
  ring

end RHTower.BAGTrace
