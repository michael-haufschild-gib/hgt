import GaloisForLFunctions.RHTower.MertensThirdTheorem
import GaloisForLFunctions.RHTower.ChiRamanujanCofactorPole
import GaloisForLFunctions.RHTower.Sieve.PrimeCosineSum
import GaloisForLFunctions.RHTower.SquarefreeCriticalNormalCone
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Growing coprime Mellin cofactors

The finite prime cutoff and the Mellin displacement move together.  The full
complex Euler ratio converges to the exponential of its prime-window integral.
Combining this with the zeta residue and Mertens' product theorem gives a finite
limit for the original coprime cofactor at every nonzero complex displacement.

The proof uses the corpus prime-window weak limit, a summable logarithmic
remainder, and the exact cofactor identity.  It does not give the complete
labelled two-variable source limit or the physical axes cancellation estimate.
-/

open scoped BigOperators Topology
open Filter MeasureTheory
noncomputable section
namespace RHTower.BAGTrace

private def complexPrimeWindow (g : ℝ → ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 0 N, g (Real.log n/Real.log N)*(mertensPrimeWeight n : ℂ)

private theorem window_split (g : ℝ → ℂ) (N : ℕ) :
    complexPrimeWindow g N =
      (mertensPrimeWindow (fun t => (g t).re) N : ℂ)+
      (mertensPrimeWindow (fun t => (g t).im) N : ℂ)*Complex.I := by
  apply Complex.ext <;> simp [complexPrimeWindow,mertensPrimeWindow]

private theorem complex_window_tendsto {g : ℝ → ℂ}
    (hg : ContinuousOn g (Set.Icc 0 1)) :
    Tendsto (fun N : ℕ => complexPrimeWindow g N/(Real.log N : ℂ)) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, g t)) := by
  have hre := tendsto_mertensPrimeWindow_div_log
    (Complex.continuous_re.comp_continuousOn hg)
  have him := tendsto_mertensPrimeWindow_div_log
    (Complex.continuous_im.comp_continuousOn hg)
  have h := ((Complex.continuous_ofReal.tendsto _).comp hre).add
    (((Complex.continuous_ofReal.tendsto _).comp him).mul_const Complex.I)
  have hrint : IntervalIntegrable (fun t => ((g t).re : ℂ)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num),Function.comp_def,Pi.mul_apply] using
      Complex.continuous_ofReal.comp_continuousOn
        (Complex.continuous_re.comp_continuousOn hg)
  have hiint : IntervalIntegrable (fun t => ((g t).im : ℂ)*Complex.I) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    have hci : ContinuousOn (fun t => ((g t).im : ℂ)) (Set.Icc 0 1) := by
      simpa only [Function.comp_def] using Complex.continuous_ofReal.comp_continuousOn
        (Complex.continuous_im.comp_continuousOn hg)
    intro t ht
    exact (hci t ht).mul continuousWithinAt_const
  have he : (∫ t in (0 : ℝ)..1, g t) =
      ((∫ t in (0 : ℝ)..1, (g t).re : ℝ) : ℂ)+
        ((∫ t in (0 : ℝ)..1, (g t).im : ℝ) : ℂ)*Complex.I := by
    calc (∫ t in (0 : ℝ)..1, g t) =
        ∫ t in (0 : ℝ)..1, ((g t).re : ℂ)+((g t).im : ℂ)*Complex.I := by
          congr 1
          funext t
          exact (Complex.re_add_im (g t)).symm
      _ = _ := by rw [intervalIntegral.integral_add hrint hiint,
        intervalIntegral.integral_mul_const,intervalIntegral.integral_ofReal,
        intervalIntegral.integral_ofReal]
  rw [he]
  simp only [Function.comp_def] at h
  refine h.congr fun N => ?_
  rw [window_split]
  push_cast
  ring

/-- Complex weak convergence of the original logarithmic prime window.
This explicit sum form also supports the moving distinguished-label responses. -/
theorem criticalComplexPrimeWindow_tendsto {g : ℝ → ℂ}
    (hg : ContinuousOn g (Set.Icc 0 1)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 0 N,
      g (Real.log n/Real.log N)*(mertensPrimeWeight n : ℂ))/(Real.log N : ℂ))
      atTop (𝓝 (∫ t in (0 : ℝ)..1,g t)) :=
  complex_window_tendsto hg

private theorem continuous_exp_dslope : Continuous (dslope Complex.exp 0) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hz : z=0
  · subst z
    exact continuousAt_dslope_same.mpr (Complex.differentiable_exp 0)
  · exact (continuousAt_dslope_of_ne hz).mpr Complex.continuous_exp.continuousAt

/-- The removable prime-window exponential quotient, with value u at zero. -/
def criticalEulerProfile (u : ℂ) (t : ℝ) : ℂ :=
  u*dslope Complex.exp 0 (u*(t : ℂ))

theorem criticalEulerProfile_continuous (u : ℂ) : Continuous (criticalEulerProfile u) :=
  continuous_const.mul (continuous_exp_dslope.comp
    (continuous_const.mul Complex.continuous_ofReal))

theorem criticalEulerProfile_mul (u : ℂ) (t : ℝ) :
    (t : ℂ)*criticalEulerProfile u t = Complex.exp (u*(t : ℂ))-1 := by
  have h := sub_smul_dslope Complex.exp 0 (u*(t : ℂ))
  simp only [sub_zero,smul_eq_mul,Complex.exp_zero] at h
  rw [criticalEulerProfile]
  convert h using 1
  ring

private theorem prime_exponential_window (u : ℂ) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 0 N,
      if n.Prime then (Complex.exp (u*((Real.log n/Real.log N : ℝ) : ℂ))-1)/(n : ℂ)
      else 0) atTop (𝓝 (∫ t in (0 : ℝ)..1,criticalEulerProfile u t)) := by
  have h := complex_window_tendsto (criticalEulerProfile_continuous u).continuousOn
  refine h.congr fun N => ?_
  rw [complexPrimeWindow,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : n.Prime
  · rw [if_pos hn,mertensPrimeWeight,if_pos hn,← criticalEulerProfile_mul u]
    push_cast
    ring
  · simp [hn,mertensPrimeWeight]

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

private def eulerNome (u : ℂ) (N n : ℕ) : ℂ :=
  Complex.exp ((u/(Real.log N : ℂ)-1)*(Real.log n : ℂ))

private theorem nome_eq_cpow (u : ℂ) (N : ℕ) {n : ℕ} (hn : 0 < n) :
    eulerNome u N n = (n : ℂ)^(-(1-u/(Real.log N : ℂ))) := by
  rw [eulerNome,Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn.ne')]
  have hp : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [show (n : ℂ) = ((n : ℝ) : ℂ) by simp,← Complex.ofReal_log hp.le]
  congr 1
  ring

private theorem nome_zero (N : ℕ) {n : ℕ} (hn : 0 < n) :
    eulerNome 0 N n = (n : ℂ)⁻¹ := by
  rw [nome_eq_cpow 0 N hn]
  simp [Complex.cpow_neg_one]

private theorem nome_norm (u : ℂ) (N : ℕ) {n : ℕ} (hn : 2 ≤ n) :
    ‖eulerNome u N n‖ = radialNome (u.re/(2*Real.log N)) n := by
  rw [eulerNome,Complex.norm_exp,radialNome_eq_exp hn]
  congr 1
  simp only [Complex.mul_re,Complex.sub_re,Complex.div_ofReal_re,
    Complex.one_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  ring

private theorem complex_drift_zero (u : ℂ) :
    Tendsto (fun N : ℕ => u/(Real.log N : ℂ)) atTop (𝓝 0) := by
  have h := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp (tendsto_drift_zero 1)
  simpa only [Function.comp_def,Complex.ofReal_div,Complex.ofReal_one,
    Complex.ofReal_zero,mul_zero,mul_one_div] using h.const_mul u

private theorem nome_tendsto (u : ℂ) {n : ℕ} (hn : 0 < n) :
    Tendsto (fun N : ℕ => eulerNome u N n) atTop (𝓝 ((n : ℂ)⁻¹)) := by
  have h := ((complex_drift_zero u).sub_const 1).mul_const (Real.log n : ℂ)
  have he := (Complex.continuous_exp.tendsto _).comp h
  have hval : Complex.exp ((0-1)*(Real.log n : ℂ)) = (n : ℂ)⁻¹ := by
    simpa [eulerNome] using nome_zero 1 hn
  simpa only [hval,Function.comp_def,eulerNome] using he

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

private def eulerLogRemainder (u : ℂ) (N n : ℕ) : ℂ :=
  if n.Prime then
    (Complex.log (1-eulerNome u N n)+eulerNome u N n)-
      (Complex.log (1-(n : ℂ)⁻¹)+(n : ℂ)⁻¹)
  else 0

private theorem remainder_bound (u : ℂ) (N : ℕ)
    (hN : |u.re/(2*Real.log N)| ≤ 1/8) (n : ℕ) :
    ‖eulerLogRemainder u N n‖ ≤ 4*(n : ℝ)^(-(3/2) : ℝ) := by
  by_cases hn : n.Prime
  · have hn0 := hn.pos
    have hq : ‖eulerNome u N n‖ ≤ 3/4 := by
      rw [nome_norm u N hn.two_le]
      exact radialNome_le hn.two_le hN
    have hz : ‖(n : ℂ)⁻¹‖ ≤ 3/4 := by
      rw [← nome_zero N hn0,nome_norm 0 N hn.two_le]
      exact radialNome_le hn.two_le (by simp)
    have hs : ‖eulerNome u N n‖^2 ≤ (n : ℝ)^(-(3/2) : ℝ) := by
      rw [nome_norm u N hn.two_le]
      exact sq_radialNome_le hn.two_le hN
    have hsz : ‖(n : ℂ)⁻¹‖^2 ≤ (n : ℝ)^(-(3/2) : ℝ) := by
      rw [← nome_zero N hn0,nome_norm 0 N hn.two_le]
      exact sq_radialNome_le hn.two_le (by simp)
    rw [eulerLogRemainder,if_pos hn]
    refine (norm_sub_le _ _).trans ?_
    linarith [norm_log_error hq,norm_log_error hz]
  · simp only [eulerLogRemainder,if_neg hn,norm_zero]
    positivity

private theorem remainder_zero (u : ℂ) (n : ℕ) :
    Tendsto (fun N : ℕ => eulerLogRemainder u N n) atTop (𝓝 0) := by
  by_cases hn : n.Prime
  · have hz : ‖-(n : ℂ)⁻¹‖ < 1 := by
      rw [norm_neg,← nome_zero 1 hn.pos,nome_norm 0 1 hn.two_le]
      simpa using (radialNome_le (c := 0) hn.two_le (by norm_num)).trans_lt
        (by norm_num : (3/4 : ℝ)<1)
    have h := nome_tendsto u hn.pos
    have hl := (tendsto_const_nhds.sub h).clog
      (by simpa only [sub_eq_add_neg] using Complex.mem_slitPlane_of_norm_lt_one hz)
    have he := (hl.add h).sub_const (Complex.log (1-(n : ℂ)⁻¹)+(n : ℂ)⁻¹)
    simpa only [eulerLogRemainder,if_pos hn,sub_self] using he
  · simp only [eulerLogRemainder,if_neg hn]
    exact tendsto_const_nhds

private theorem sum_remainder_zero (u : ℂ) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 0 N,eulerLogRemainder u N n)
      atTop (𝓝 0) := by
  have hsum : Summable (fun n : ℕ => 4*(n : ℝ)^(-(3/2) : ℝ)) :=
    (Real.summable_nat_rpow.mpr (by norm_num : (-(3/2) : ℝ) < -1)).mul_left 4
  apply complex_sum_zero hsum (fun n => by positivity) _ (remainder_zero u)
  have he := eventually_abs_drift_le (u.re/2)
  filter_upwards [he] with N hN n _
  apply remainder_bound u N _ n
  convert hN using 1
  congr 1
  ring

private theorem nome_sub (u : ℂ) (N : ℕ) {n : ℕ} (hn : 0 < n) :
    eulerNome u N n-(n : ℂ)⁻¹ =
      (Complex.exp (u*((Real.log n/Real.log N : ℝ) : ℂ))-1)/(n : ℂ) := by
  have hp : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [eulerNome,show (u/(Real.log N : ℂ)-1)*(Real.log n : ℂ) =
    u*((Real.log n/Real.log N : ℝ) : ℂ)-(Real.log n : ℂ) by push_cast; ring,
    Complex.exp_sub,← Complex.ofReal_exp,Real.exp_log hp]
  push_cast
  ring

private def eulerLogRatio (u : ℂ) (N n : ℕ) : ℂ :=
  if n.Prime then Complex.log (1-eulerNome u N n)-Complex.log (1-(n : ℂ)⁻¹) else 0

private theorem sum_log_ratio (u : ℂ) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 0 N,eulerLogRatio u N n) atTop
      (𝓝 (-(∫ t in (0 : ℝ)..1,criticalEulerProfile u t))) := by
  have h := (prime_exponential_window u).neg.add (sum_remainder_zero u)
  simp only [add_zero] at h
  refine h.congr fun N => ?_
  rw [← Finset.sum_neg_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : n.Prime
  · rw [if_pos hn,eulerLogRemainder,if_pos hn,eulerLogRatio,if_pos hn,
      ← nome_sub u N hn.pos]
    ring
  · simp [hn,eulerLogRemainder,eulerLogRatio]

/-- The original finite prime Euler factors at the jointly moving abscissa. -/
def criticalMovingEulerRatio (u : ℂ) (N : ℕ) : ℂ :=
  ∏ p ∈ Nat.primesLE N,
    (1-(p : ℂ)^(-(1-u/(Real.log N : ℂ))))/(1-(p : ℂ)⁻¹)

private theorem exp_sum_log_ratio (u : ℂ) (N : ℕ)
    (hN : |u.re/(2*Real.log N)| ≤ 1/8) :
    Complex.exp (∑ n ∈ Finset.Icc 0 N,eulerLogRatio u N n) =
      criticalMovingEulerRatio u N := by
  rw [Complex.exp_sum]
  have he (n : ℕ) : Complex.exp (eulerLogRatio u N n) =
      if n.Prime then
        (1-(n : ℂ)^(-(1-u/(Real.log N : ℂ))))/(1-(n : ℂ)⁻¹) else 1 := by
    by_cases hn : n.Prime
    · have hq : ‖eulerNome u N n‖ < 1 := by
        rw [nome_norm u N hn.two_le]
        exact (radialNome_le hn.two_le hN).trans_lt (by norm_num)
      have hz : ‖(n : ℂ)⁻¹‖ < 1 := by
        rw [← nome_zero N hn.pos,nome_norm 0 N hn.two_le]
        exact (radialNome_le hn.two_le (show |(0 : ℂ).re/(2*Real.log N)| ≤ 1/8 by simp)).trans_lt
          (by norm_num : (3/4 : ℝ)<1)
      have hq0 : 1-eulerNome u N n ≠ 0 := by
        intro hh
        have hh' := sub_eq_zero.mp hh
        rw [← hh',norm_one] at hq
        exact (lt_irrefl _ hq)
      have hz0 : 1-(n : ℂ)⁻¹ ≠ 0 := by
        intro hh
        have hh' := sub_eq_zero.mp hh
        rw [← hh',norm_one] at hz
        exact (lt_irrefl _ hz)
      rw [eulerLogRatio,if_pos hn,if_pos hn,Complex.exp_sub,
        Complex.exp_log hq0,Complex.exp_log hz0,nome_eq_cpow u N hn.pos]
    · simp [eulerLogRatio,hn]
  simp_rw [he]
  rw [← Finset.prod_filter]
  congr 1
  ext n
  simp [Finset.mem_filter,Finset.mem_Icc,Nat.mem_primesLE]

/-- The full growing-cutoff complex Euler ratio has its exponential-integral limit. -/
theorem criticalMovingEulerRatio_tendsto (u : ℂ) :
    Tendsto (criticalMovingEulerRatio u) atTop
      (𝓝 (Complex.exp (-(∫ t in (0 : ℝ)..1,criticalEulerProfile u t)))) := by
  have h := (Complex.continuous_exp.tendsto _).comp (sum_log_ratio u)
  apply h.congr'
  have he := eventually_abs_drift_le (u.re/2)
  filter_upwards [he] with N hN
  apply exp_sum_log_ratio u N
  convert hN using 1
  congr 1
  ring

/-- The removable value is u, including at nonzero complex parameters. -/
theorem criticalEulerProfile_zero (u : ℂ) : criticalEulerProfile u 0 = u := by
  rw [criticalEulerProfile,Complex.ofReal_zero,mul_zero,dslope_same,
    Complex.deriv_exp,Complex.exp_zero,mul_one]

private theorem prime_cutoff_prod (N : ℕ) (f : ℕ → ℂ) :
    (∏ p : Sieve.primeSubtypeLE N,f p.val.val) = ∏ n ∈ Nat.primesLE N,f n := by
  calc (∏ p : Sieve.primeSubtypeLE N,f p.val.val) =
      ∏ p ∈ Sieve.primeSubtypeLE N,f p.val :=
        Finset.prod_coe_sort (Sieve.primeSubtypeLE N) (fun p : Nat.Primes => f p.val)
    _ = _ := Finset.prod_subtype_of_mem f (fun n hn => Nat.prime_of_mem_primesLE hn)

private theorem product_ratio_eq (u : ℂ) (N : ℕ) :
    (∏ p : Sieve.primeSubtypeLE N, (1-cubicPrimeBase p (1-u/(Real.log N : ℂ))))/
      (criticalPrimeNormalization (Sieve.primeSubtypeLE N) : ℂ) =
        criticalMovingEulerRatio u N := by
  have hA : (criticalPrimeNormalization (Sieve.primeSubtypeLE N) : ℂ) =
      ∏ p : Sieve.primeSubtypeLE N, (1-((p : Nat.Primes) : ℂ)⁻¹) := by
    unfold criticalPrimeNormalization
    push_cast
    simp only [one_div]
  rw [hA]
  calc _ = (∏ n ∈ Nat.primesLE N,(1-(n : ℂ)^(-(1-u/(Real.log N : ℂ)))))/
      (∏ n ∈ Nat.primesLE N,(1-(n : ℂ)⁻¹)) := by
        apply congrArg₂ (fun a b : ℂ => a/b)
        · exact prime_cutoff_prod N (fun n => 1-(n : ℂ)^(-(1-u/(Real.log N : ℂ))))
        · exact prime_cutoff_prod N (fun n => 1-(n : ℂ)⁻¹)
    _ = _ := by rw [← Finset.prod_div_distrib]; rfl

private theorem moving_point_ne (u : ℂ) (hu : u ≠ 0) {N : ℕ} (hN : 2 ≤ N) :
    1-u/(Real.log N : ℂ) ≠ 1 := by
  have hlog : Real.log (N : ℝ) ≠ 0 := (Real.log_pos
    (by exact_mod_cast (show 1 < N by omega))).ne'
  intro hs
  have hz : u/(Real.log N : ℂ) = 0 := by linear_combination -hs
  exact (div_ne_zero hu (Complex.ofReal_ne_zero.mpr hlog)) hz

private theorem moving_zeta_residue (u : ℂ) (hu : u ≠ 0) :
    Tendsto (fun N : ℕ => (-u/(Real.log N : ℂ))*
      riemannZeta (1-u/(Real.log N : ℂ))) atTop (𝓝 1) := by
  have ht : Tendsto (fun N : ℕ => 1-u/(Real.log N : ℂ)) atTop (𝓝[≠] (1 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [sub_zero] using tendsto_const_nhds.sub (complex_drift_zero u)
    · filter_upwards [eventually_ge_atTop 2] with N hN
      exact moving_point_ne u hu hN
  have h := riemannZeta_residue_one.comp ht
  convert h using 1
  funext N
  congr 1
  ring

private theorem moving_cofactor_limit (u : ℂ) (hu : u ≠ 0) :
    Tendsto (fun N : ℕ => (-u/(Real.log N : ℂ))*
      criticalCofactor (Sieve.primeSubtypeLE N) (1-u/(Real.log N : ℂ))/
        (criticalPrimeNormalization (Sieve.primeSubtypeLE N) : ℂ)) atTop
      (𝓝 (Complex.exp (-(∫ t in (0 : ℝ)..1,criticalEulerProfile u t)))) := by
  have h := (moving_zeta_residue u hu).mul (criticalMovingEulerRatio_tendsto u)
  simp only [one_mul] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  rw [criticalCofactor_eq _ (moving_point_ne u hu hN),← product_ratio_eq]
  ring

/-- The original coprime numerator cofactor has its growing-cutoff,
logarithmically moving pole-removed limit at every nonzero complex parameter. -/
theorem criticalCofactor_logScale_limit (u : ℂˣ) :
    Tendsto (fun N : ℕ => (-(u : ℂ)/(Real.log N : ℂ))*
      criticalCofactor (Sieve.primeSubtypeLE N) (1-(u : ℂ)/(Real.log N : ℂ))/
        (criticalPrimeNormalization (Sieve.primeSubtypeLE N) : ℂ)) atTop
      (𝓝 (Complex.exp (-(∫ t in (0 : ℝ)..1,criticalEulerProfile u t)))) :=
  moving_cofactor_limit u u.ne_zero

private theorem normalization_mertens (N : ℕ) :
    criticalPrimeNormalization (Sieve.primeSubtypeLE N) = mertensPrimeProduct N := by
  calc criticalPrimeNormalization (Sieve.primeSubtypeLE N) =
      ∏ p : Sieve.primeSubtypeLE N, (1-(p.val.val : ℝ)⁻¹) := by
        simp only [criticalPrimeNormalization,one_div]
    _ = ∏ p ∈ Sieve.primeSubtypeLE N, (1-(p.val : ℝ)⁻¹) :=
      Finset.prod_coe_sort (Sieve.primeSubtypeLE N) (fun p : Nat.Primes => 1-(p.val : ℝ)⁻¹)
    _ = ∏ n ∈ Nat.primesLE N, (1-(n : ℝ)⁻¹) :=
      Finset.prod_subtype_of_mem (fun n : ℕ => 1-(n : ℝ)⁻¹)
        (fun n hn => Nat.prime_of_mem_primesLE hn)
    _ = mertensPrimeProduct N := by
      rw [mertensPrimeProduct,← Finset.prod_filter]
      congr 1
      ext n
      simp [Finset.mem_filter,Finset.mem_Icc,Nat.mem_primesLE]

/-- Mertens normalization on the original growing finite-prime set. -/
theorem criticalPrimeNormalization_logScale_tendsto :
    Tendsto (fun N : ℕ =>
      (criticalPrimeNormalization (Sieve.primeSubtypeLE N) : ℂ)*(Real.log N : ℂ))
      atTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant) : ℂ)) := by
  have h := (Complex.continuous_ofReal.tendsto _).comp tendsto_mertensPrimeProduct_mul_log
  simpa only [Function.comp_def,normalization_mertens,Complex.ofReal_mul] using h

/-- The actual growing coprime cofactor itself has an explicit finite
limit at each nonzero logarithmic Mellin displacement. -/
theorem criticalCofactor_moving_tendsto (u : ℂˣ) :
    Tendsto (fun N : ℕ => criticalCofactor (Sieve.primeSubtypeLE N)
      (1-(u : ℂ)/(Real.log N : ℂ))) atTop
      (𝓝 ((Complex.exp (-(∫ t in (0 : ℝ)..1,criticalEulerProfile u t))*
        (Real.exp (-Real.eulerMascheroniConstant) : ℂ))/(-(u : ℂ)))) := by
  have h := ((criticalCofactor_logScale_limit u).mul
    criticalPrimeNormalization_logScale_tendsto).div_const (-(u : ℂ))
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hlog : (Real.log N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
  have hA0 : (criticalPrimeNormalization (Sieve.primeSubtypeLE N) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (criticalPrimeNormalization_pos _).ne'
  have hu : (u : ℂ) ≠ 0 := u.ne_zero
  field_simp

end RHTower.BAGTrace
