import GaloisForLFunctions.RHTower.MobiusCriticalInitialPrimeResonance
import GaloisForLFunctions.RHTower.MobiusDivisorPhysicalCutoff
import GaloisForLFunctions.RHTower.MobiusCriticalPrimeBlockGammaBand
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.PrimeWindowCount
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Physical energy escapes every polynomial prime-scale cutoff

For the literal prime set `P_y = {p prime | y/3 < p ≤ y}`, the squared physical
head has total energy at least `c exp(sqrt(y)/(6 log(y)))/log(y)` eventually.
The proof transfers the existing prime-block gamma-band lower bound through the
exact Mellin pairing. The core-uniform source envelope bounds every physical
prefix by `(9/25) X`, so the energy beyond `y^A` exceeds every power of `y`.
Even weighting by the literal core density leaves a divergent tail.

The same escape holds for the natural exhaustive core containing every prime
at most `y`. The small-prime loss is absorbed by the terminal-window gain,
leaving the exponential lower bound with denominator `12 log(y)`.

This obstructs uniform approximation by limiting profiles over arbitrary cores.
It supplies no upper bound for the signed finite-cutoff cancellation required
by route MC for RH; the delayed energy is not an RH counterexample.
-/

noncomputable section
open Finset Set Filter Topology MeasureTheory GaloisForLFunctions.HTGeometry
namespace RHTower

private lemma cluster_unit_one_pos :
    0 < (mellin (fun x : ℝ => (divisorContinuousUnitHead x:ℂ)) (-1)).re := by
  have hempty : (fun x : ℝ => (mobiusDivisorContinuousHead ∅ x:ℂ)) =
      fun x : ℝ => (divisorContinuousUnitHead x:ℂ) := by
    funext x
    simp [mobiusDivisorContinuousHead]
  have hk (x : ℝ) : (x:ℂ)^((-1:ℂ)-1) • (divisorContinuousUnitHead x:ℂ) =
      ((divisorContinuousUnitHead x/x^2:ℝ):ℂ) := by
    rw [show (-1:ℂ)-1=-(2:ℂ) by norm_num,Complex.cpow_neg]
    norm_num only [Complex.cpow_ofNat,smul_eq_mul]
    push_cast
    ring
  have hi := mellinConvergent_mobiusDivisorContinuousHead ∅ (s := 1) (by norm_num)
  rw [hempty] at hi
  change IntegrableOn (fun x : ℝ => (x:ℂ)^((-1:ℂ)-1) • (divisorContinuousUnitHead x:ℂ)) (Ioi 0) at hi
  simp_rw [hk] at hi
  have hir : IntegrableOn (fun x : ℝ => divisorContinuousUnitHead x/x^2) (Ioi 0) := by
    simpa only [IntegrableOn,RCLike.re_to_complex,Complex.ofReal_re] using hi.re
  have hp : 0 < ∫ x in Ioi (0:ℝ), divisorContinuousUnitHead x/x^2 := by
    apply (integral_pos_iff_support_of_nonneg_ae _ hir).mpr
    · have hsub : Ioo (1:ℝ) 2 ⊆ Function.support (fun x => divisorContinuousUnitHead x/x^2) := by
        intro x hx
        exact ne_of_gt (div_pos (divisorContinuousUnitHead_pos_first hx) (sq_pos_of_pos (by linarith [hx.1])))
      apply lt_of_lt_of_le _ (measure_mono hsub)
      rw [Measure.restrict_apply measurableSet_Ioo]
      have he : Ioo (1:ℝ) 2 ∩ Ioi 0 = Ioo (1:ℝ) 2 :=
        inter_eq_left.mpr (fun x hx => by change 0 < x; linarith [hx.1])
      rw [he,Real.volume_Ioo]
      norm_num
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact div_nonneg (divisorContinuousUnitHead_nonneg x) (sq_nonneg _)
  rw [mellin]
  simp_rw [hk]
  rw [integral_complex_ofReal,Complex.ofReal_re]
  exact hp

private def clusterMellin (P : Finset ℕ) (t : ℝ) : ℂ :=
  mellin (fun x : ℝ => (mobiusDivisorContinuousHead P x:ℂ)) (-(1+(t:ℂ)*Complex.I))

private def clusterWeight (P : Finset ℕ) (t : ℝ) : ℝ := ‖clusterMellin P t‖^2

private lemma clusterMellin_continuous (P : Finset ℕ) : Continuous (clusterMellin P) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have h := (differentiableAt_mellin_mobiusDivisorContinuousHead P
    (s := 1+(t:ℂ)*Complex.I) (by simp; norm_num)).continuousAt
  exact h.comp (f := fun u : ℝ => 1+(u:ℂ)*Complex.I) (x := t) (by fun_prop)

private lemma clusterWeight_continuous (P : Finset ℕ) : Continuous (clusterWeight P) :=
  (clusterMellin_continuous P).norm.pow 2

private lemma clusterWeight_empty_pos : 0 < clusterWeight ∅ 0 := by
  have h := cluster_unit_one_pos
  have he : clusterMellin ∅ 0 = mellin (fun x : ℝ => (divisorContinuousUnitHead x:ℂ)) (-1) := by
    simp [clusterMellin, mobiusDivisorContinuousHead]
  apply sq_pos_of_pos
  apply norm_pos_iff.mpr
  intro hz
  change clusterMellin ∅ 0 = 0 at hz
  have hz' : mellin (fun x : ℝ => (divisorContinuousUnitHead x:ℂ)) (-1) = 0 := he.symm.trans hz
  rw [hz', Complex.zero_re] at h
  exact (lt_irrefl _ h)

private lemma clusterWeight_pair (P : Finset ℕ) (hP : P.Nonempty)
    (hPrime : ∀ p ∈ P,p.Prime) (t : ℝ) :
    divisorCoreMellinPair P (1+(t:ℂ)*Complex.I) = (clusterWeight P t:ℂ) := by
  have hfirst := mellin_mobiusDivisorContinuousHead_eq_core P hP hPrime
    (s := 1+(t:ℂ)*Complex.I) (by simp; norm_num)
  have hsecond := mellin_mobiusDivisorContinuousHead_eq_core P hP hPrime
    (s := 2-(1+(t:ℂ)*Complex.I)) (by simp; norm_num)
  have hconj := mellin_conj_of_conj_invariant
    (F := fun x : ℝ => (mobiusDivisorContinuousHead P x:ℂ))
    (by intro x; simp) (-(1+(t:ℂ)*Complex.I))
  have he : (starRingEnd ℂ) (-(1+(t:ℂ)*Complex.I)) = -(2-(1+(t:ℂ)*Complex.I)) := by
    simp
    ring
  rw [he,hsecond] at hconj
  rw [divisorCoreMellinPair,← hfirst,hconj,Complex.mul_conj]
  rw [Complex.normSq_eq_norm_sq]
  rfl

private lemma clusterWeight_integrable (P : Finset ℕ) (hP : P.Nonempty)
    (hPrime : ∀ p ∈ P,p.Prime) : Integrable (clusterWeight P) := by
  have hi := integrable_exp_mul_divisorCoreMellinPair_one P hP 0
  simp only [Complex.ofReal_zero,zero_mul,Complex.exp_zero,one_mul,
    clusterWeight_pair P hP hPrime] at hi
  simpa only [RCLike.re_to_complex,Complex.ofReal_re] using hi.re

private lemma cluster_dilation_spectrum (P : Finset ℕ) (hP : P.Nonempty)
    (hprime : ∀ p ∈ P,p.Prime) {r : ℝ} (hr : 0 < r) :
    mobiusDivisorDilationMean P r = r/(2*Real.pi)*∫ t,clusterWeight P t*Real.cos (Real.log r*t) := by
  let F : ℝ → ℂ := fun t => Complex.exp ((Real.log r:ℂ)*(1+(t:ℂ)*Complex.I))*
    divisorCoreMellinPair P (1+(t:ℂ)*Complex.I)
  have hi : Integrable F := integrable_exp_mul_divisorCoreMellinPair_one P hP (Real.log r)
  have hre (t : ℝ) : (F t).re = r*(clusterWeight P t*Real.cos (Real.log r*t)) := by
    dsimp [F]
    rw [clusterWeight_pair P hP hprime]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,
      sub_zero,Complex.exp_re,Complex.add_re,Complex.one_re,Complex.I_re,
      Complex.add_im,Complex.one_im,Complex.mul_im,Complex.I_im,mul_one,add_zero,zero_add,
      Real.exp_log hr]
    ring
  have h := congrArg Complex.re (mobiusDivisorDilationMean_eq_contour P hP hprime (Real.log r))
  rw [Real.exp_log hr,divisorCoreMellinContourMean] at h
  have hscalar : (1/(2*(Real.pi:ℂ))) = (((1/(2*Real.pi):ℝ)):ℂ) := by push_cast; rfl
  rw [hscalar] at h
  simp only [Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,zero_mul,sub_zero] at h
  have hRi : (∫ t,F t).re = ∫ t,(F t).re := (integral_re hi).symm
  change mobiusDivisorDilationMean P r = (1/(2*Real.pi))*(∫ t,F t).re at h
  rw [hRi] at h
  simp_rw [hre] at h
  rw [integral_const_mul] at h
  calc
    _ = (1/(2*Real.pi))*(r*∫ t,clusterWeight P t*Real.cos (Real.log r*t)) := h
    _ = _ := by ring

private lemma window_prime {y : ℝ} (hy : 0 ≤ y) {p : ℕ}
    (hp : p ∈ mobiusCriticalPrimeWindow y) : p.Prime :=
  ((mem_windowPrimes (by positivity) hy).mp hp).1

private lemma window_euler {y : ℝ} (hy : 0 ≤ y) (t : ℝ) :
    divisorCoreMellinEuler (mobiusCriticalPrimeWindow y) (1+(t:ℂ)*Complex.I) =
      mobiusCriticalPrimeBlock y t := by
  apply Finset.prod_congr rfl
  intro p hp
  have hpR : (0:ℝ) < p := by exact_mod_cast (window_prime hy hp).pos
  have hroot : (Real.sqrt p:ℂ) = Complex.exp ((Real.log p:ℂ)/2) := by
    rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos hpR,Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  unfold mobiusCriticalPrimeFactor mobiusCriticalPrimeRadius
  rw [Complex.ofReal_inv,hroot,← Complex.exp_neg,← Complex.exp_add]
  congr 2
  push_cast
  ring

private lemma window_weight {y : ℝ} (hy : 0 ≤ y) (t : ℝ) :
    clusterWeight (mobiusCriticalPrimeWindow y) t =
      clusterWeight ∅ t * ‖mobiusCriticalPrimeBlock y t‖^2 := by
  dsimp [clusterWeight,clusterMellin]
  rw [mellin_mobiusDivisorContinuousHead_euler _ (fun p hp => window_prime hy hp)
    (by simp; norm_num), window_euler hy]
  have hempty : (fun x : ℝ => (mobiusDivisorContinuousHead ∅ x:ℂ)) =
      fun x : ℝ => (divisorContinuousUnitHead x:ℂ) := by
    funext x
    simp [mobiusDivisorContinuousHead]
  rw [hempty,norm_mul,mul_pow,mul_comm]


private lemma window_card_lower :
    ∀ᶠ y : ℝ in atTop, y / (3 * Real.log y) ≤
      ((mobiusCriticalPrimeWindow y).card : ℝ) := by
  have hscale : Tendsto (fun y : ℝ => y/3) atTop atTop :=
    tendsto_id.atTop_div_const (by norm_num)
  have hh := hscale.eventually
    (GaloisForLFunctions.HTGeometry.eventually_primeCount_window_ge (K := 3) (by norm_num))
  filter_upwards [hh,eventually_gt_atTop (3:ℝ)] with y hh hy
  have hy0 : 0 < y := by linarith
  have hlog : 0 < Real.log (y/3) := Real.log_pos (by linarith)
  have hlo : Real.log (y/3) ≤ Real.log y :=
    Real.log_le_log (by positivity) (by linarith)
  have hc := GaloisForLFunctions.HTGeometry.card_primesInIoc
    (Nat.floor_le_floor (show y/3 ≤ y by linarith))
  have he : GaloisForLFunctions.HTGeometry.primesInIoc ⌊y/3⌋₊ ⌊y⌋₊ =
      mobiusCriticalPrimeWindow y := rfl
  rw [he] at hc
  norm_num only [show (3:ℝ)-1=2 by norm_num,div_self (by norm_num : (2:ℝ)≠0),one_mul,
    show (3:ℝ)*(y/3)=y by ring] at hh
  rw [← hc] at hh
  calc
    y/(3*Real.log y) = (y/3)/Real.log y := by ring
    _ ≤ (y/3)/Real.log (y/3) := div_le_div_of_nonneg_left (by positivity) hlog hlo
    _ ≤ _ := hh

private lemma primeBlock_nonempty : ∀ᶠ y : ℝ in atTop, (mobiusCriticalPrimeWindow y).Nonempty := by
  filter_upwards [window_card_lower,eventually_gt_atTop (3:ℝ)] with y hy hy3
  have hy0 : 0 < y := by linarith
  have hl : 0 < Real.log y := Real.log_pos (by linarith)
  apply Finset.card_pos.mp
  have h : (0:ℝ) < ((mobiusCriticalPrimeWindow y).card:ℝ) :=
    lt_of_lt_of_le (by positivity : 0 < y/(3*Real.log y)) hy
  exact_mod_cast h

private lemma physical_block_lower :
    ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧ ∀ y : ℝ, 27 ≤ y →
      (mobiusCriticalPrimeWindow y).Nonempty →
      4*Real.pi/(3*Real.log y) < δ →
      c/Real.log y * (1+1/Real.sqrt y)^(mobiusCriticalPrimeWindow y).card ≤
        mobiusDivisorDilationMean (mobiusCriticalPrimeWindow y) 1 := by
  have hw0 := clusterWeight_empty_pos
  obtain ⟨δ,hδ,hfloor⟩ := exists_local_half_floor_of_continuousAt_of_pos
    (clusterWeight_continuous ∅).continuousAt clusterWeight_empty_pos
  refine ⟨clusterWeight ∅ 0/12,δ,by positivity,hδ,?_⟩
  intro y hy hP hsmall
  have hy0 : 0 ≤ y := by linarith
  have hlog : 0 < Real.log y := Real.log_pos (by linarith)
  have hprime : ∀ p ∈ mobiusCriticalPrimeWindow y,p.Prime := fun _ hp => window_prime hy0 hp
  have hf : ∀ t ∈ Icc (Real.pi/Real.log y) (4*Real.pi/(3*Real.log y)),
      clusterWeight ∅ 0/2 ≤ clusterWeight ∅ t := by
    intro t ht
    apply hfloor t
    rw [abs_of_nonneg ((div_nonneg Real.pi_pos.le hlog.le).trans ht.1)]
    exact ht.2.trans_lt hsmall
  have hl := integral_weight_mul_mobiusCriticalPrimeBlock_norm_sq_lower_on_gammaBand
    (clusterWeight ∅) (clusterWeight_continuous ∅) (by positivity) hy hf
  have he : (fun t => clusterWeight ∅ t*‖mobiusCriticalPrimeBlock y t‖^2) =
      clusterWeight (mobiusCriticalPrimeWindow y) := by
    funext t
    exact (window_weight hy0 t).symm
  rw [he] at hl
  have hab : Real.pi/Real.log y ≤ 4*Real.pi/(3*Real.log y) := by
    apply (div_le_div_iff₀ hlog (by positivity : 0 < 3*Real.log y)).mpr
    nlinarith [Real.pi_pos]
  rw [intervalIntegral.integral_of_le hab] at hl
  have hi := clusterWeight_integrable (mobiusCriticalPrimeWindow y) hP hprime
  have hm := setIntegral_le_integral (s := Ioc (Real.pi/Real.log y)
    (4*Real.pi/(3*Real.log y))) hi
    (Filter.Eventually.of_forall (fun t => sq_nonneg ‖clusterMellin (mobiusCriticalPrimeWindow y) t‖))
  have hs := cluster_dilation_spectrum (mobiusCriticalPrimeWindow y) hP hprime
    (r := 1) (by norm_num)
  simp only [Real.log_one,zero_mul,Real.cos_zero,mul_one] at hs
  rw [hs]
  have hmul := mul_le_mul_of_nonneg_left (hl.trans hm)
    (by positivity : 0 ≤ 1/(2*Real.pi))
  calc
    _ = 1/(2*Real.pi) * (Real.pi/(3*Real.log y) *
        (clusterWeight ∅ 0/2 * (1+1/Real.sqrt y)^(mobiusCriticalPrimeWindow y).card)) := by
      field_simp [Real.pi_ne_zero]
      ring
    _ ≤ _ := hmul

private lemma window_power_exponential :
    ∀ᶠ y : ℝ in atTop, Real.exp (Real.sqrt y/(6*Real.log y)) ≤
      (1+1/Real.sqrt y)^(mobiusCriticalPrimeWindow y).card := by
  filter_upwards [window_card_lower,eventually_gt_atTop (3:ℝ)] with y hn hy
  have hy0 : 0 < y := by linarith
  have hlog : 0 < Real.log y := Real.log_pos (by linarith)
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy0
  have hs1 : 1 ≤ Real.sqrt y := Real.one_le_sqrt.mpr (by linarith)
  have hx0 : 0 ≤ 1/Real.sqrt y := by positivity
  have hx1 : 1/Real.sqrt y ≤ 1 := (div_le_one hs).mpr hs1
  have hl := Real.le_log_one_add_of_nonneg hx0
  have hhalf : (1/Real.sqrt y)/2 ≤ Real.log (1+1/Real.sqrt y) := by
    apply le_trans _ hl
    apply (le_div_iff₀ (by positivity : 0 < 1/Real.sqrt y+2)).mpr
    nlinarith
  have hcount := (div_le_iff₀ (by positivity : 0 < 3*Real.log y)).mp hn
  have hden : Real.sqrt y/(6*Real.log y) ≤
      ((mobiusCriticalPrimeWindow y).card:ℝ)*((1/Real.sqrt y)/2) := by
    apply (div_le_iff₀ (by positivity : 0 < 6*Real.log y)).mpr
    have hh := div_le_div_of_nonneg_right hcount hs.le
    have hys : y/Real.sqrt y = Real.sqrt y := by
      apply (div_eq_iff hs.ne').mpr
      nlinarith only [Real.sq_sqrt hy0.le]
    rw [hys] at hh
    convert hh using 1; ring
  have he : Real.sqrt y/(6*Real.log y) ≤
      ((mobiusCriticalPrimeWindow y).card:ℝ)*Real.log (1+1/Real.sqrt y) :=
    hden.trans (mul_le_mul_of_nonneg_left hhalf (Nat.cast_nonneg _))
  calc
    _ ≤ Real.exp (((mobiusCriticalPrimeWindow y).card:ℝ)*Real.log (1+1/Real.sqrt y)) :=
      Real.exp_le_exp.mpr he
    _ = _ := by rw [Real.exp_nat_mul,Real.exp_log (by positivity)]

/-- Literal prime-window cores have exponentially large limiting physical energy. -/
theorem eventually_mobiusDivisorPrimeBlock_energy_exponential :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ y : ℝ in atTop,
      c/Real.log y*Real.exp (Real.sqrt y/(6*Real.log y)) ≤
        mobiusDivisorDilationMean (mobiusCriticalPrimeWindow y) 1 := by
  obtain ⟨c,δ,hc,hδ,hbound⟩ := physical_block_lower
  have hsmall : Tendsto (fun y : ℝ => 4*Real.pi/(3*Real.log y)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.const_mul_atTop (by norm_num))
  refine ⟨c,hc,?_⟩
  filter_upwards [hsmall.eventually (eventually_lt_nhds hδ),primeBlock_nonempty,
    window_power_exponential,eventually_ge_atTop (27:ℝ)] with y hs hn hp hy
  have hl : 0 < Real.log y := Real.log_pos (by linarith)
  exact (mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ c/Real.log y)).trans
    (hbound y hy hn hs)

private lemma physical_energy_superpower (A C : ℝ) (hA : 0 < A) (hC : 0 < C) :
    ∀ᶠ y : ℝ in atTop, C*y^A ≤
      mobiusDivisorDilationMean (mobiusCriticalPrimeWindow y) 1 := by
  obtain ⟨c,hc,hbound⟩ := eventually_mobiusDivisorPrimeBlock_energy_exponential
  have hsmall : Tendsto (fun y : ℝ => (Real.log y)^2/Real.sqrt y) atTop (𝓝 0) := by
    simpa only [Real.rpow_two,← Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_rpow_atTop (2:ℝ) (by norm_num : (0:ℝ)<1/2)).tendsto_div_nhds_zero
  have hε : 0 < 1/(6*(A+2)) := by positivity
  filter_upwards [hbound,hsmall.eventually (eventually_lt_nhds hε),
    eventually_ge_atTop (C/c),eventually_gt_atTop (3:ℝ)] with y hb hh hcy hy
  have hy0 : 0 < y := by linarith
  have hl : 0 < Real.log y := Real.log_pos (by linarith)
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy0
  have hcross := (div_lt_div_iff₀ hs (by positivity : 0 < 6*(A+2))).mp hh
  have hexp : (A+2)*Real.log y ≤ Real.sqrt y/(6*Real.log y) := by
    apply (le_div_iff₀ (by positivity : 0 < 6*Real.log y)).mpr
    nlinarith only [hcross]
  have hp : y^(A+2) ≤ Real.exp (Real.sqrt y/(6*Real.log y)) := by
    rw [Real.rpow_def_of_pos hy0]
    exact Real.exp_le_exp.mpr (by simpa only [mul_comm] using hexp)
  have hcy' : C ≤ c*y := by
    have h := (div_le_iff₀ hc).mp hcy
    nlinarith only [h]
  have hcoef : C ≤ c/Real.log y*y^2 := by
    have hlogle : Real.log y ≤ y := (Real.log_le_sub_one_of_pos hy0).trans (by linarith)
    have hh1 := mul_le_mul_of_nonneg_left hlogle hC.le
    have hh2 := mul_le_mul_of_nonneg_right hcy' hy0.le
    have hdiv : C ≤ (c*y^2)/Real.log y :=
      (le_div_iff₀ hl).mpr (by nlinarith only [hh1,hh2])
    convert hdiv using 1; ring
  calc
    C*y^A ≤ (c/Real.log y*y^2)*y^A :=
      mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hy0.le A)
    _ = c/Real.log y*y^(A+2) := by rw [Real.rpow_add hy0,Real.rpow_two]; ring
    _ ≤ c/Real.log y*Real.exp (Real.sqrt y/(6*Real.log y)) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ ≤ _ := hb

private lemma physical_prefix_le (P : Finset ℕ) {X : ℝ} (hX : 1 ≤ X) :
    mobiusDivisorDilationMean P 1 ≤
      (∫ x in Ioi X, (mobiusDivisorContinuousHead P x)^2/x^3)+(9/25:ℝ)*X := by
  have hi : IntegrableOn (fun x => (mobiusDivisorContinuousHead P x)^2/x^3) (Ioi (1:ℝ)) := by
    simpa only [one_mul,pow_two] using
      integrable_mobiusDivisorDilationMean_kernel P (Y := 1) (by norm_num)
  have hp : IntervalIntegrable (fun x => (mobiusDivisorContinuousHead P x)^2/x^3)
      volume 1 X :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hX).mpr (hi.mono_set Ioc_subset_Ioi_self)
  have hpoint (x : ℝ) : (mobiusDivisorContinuousHead P x)^2/x^3 ≤ (9/25:ℝ) := by
    have h := abs_mobiusDivisorContinuousHead_mul_div_cube_le P P
      (a := 1) (b := 1) (by norm_num) (by norm_num) x
    norm_num only [one_mul,Real.sqrt_one,mul_one,← pow_two] at h
    exact (le_abs_self _).trans h
  have hm := intervalIntegral.integral_mono_on hX hp
    (intervalIntegrable_const (c := (9/25:ℝ))) (fun x _ => hpoint x)
  rw [intervalIntegral.integral_const,smul_eq_mul] at hm
  have he := intervalIntegral.integral_Ioi_sub_Ioi hi hX
  have hmean : mobiusDivisorDilationMean P 1 =
      ∫ x in Ioi (1:ℝ),(mobiusDivisorContinuousHead P x)^2/x^3 := by
    simp only [mobiusDivisorDilationMean,one_mul,pow_two]
  rw [← hmean] at he
  linarith

/-- Every polynomially rescaled tail beyond every polynomial prime-scale cutoff
still diverges for the literal prime-window head. -/
theorem tendsto_mobiusDivisorPrimeBlock_scaled_tail_energy (A : ℝ) (hA : 0 < A) (B : ℝ) :
    Tendsto (fun y : ℝ => (∫ x in Ioi (y^A),
      (mobiusDivisorContinuousHead (mobiusCriticalPrimeWindow y) x)^2/x^3)/y^B) atTop atTop := by
  apply tendsto_atTop.mpr
  intro L
  let C : ℝ := max L 0+1
  let D : ℝ := max A B+1
  have hC : 0<C := by dsimp [C]; have := le_max_right L 0; linarith
  have hD : 0<D := by dsimp [D]; have := le_max_left A B; linarith
  have hAD : A≤D := by dsimp [D]; have := le_max_left A B; linarith
  have hBD : B≤D := by dsimp [D]; have := le_max_right A B; linarith
  filter_upwards [physical_energy_superpower D (C+9/25) hD (by positivity),
    eventually_ge_atTop (1:ℝ)] with y hy hy1
  have hy0 : 0<y := by linarith
  have hpow : 1≤y^A := Real.one_le_rpow hy1 hA.le
  have hpa : y^A≤y^D := Real.rpow_le_rpow_of_exponent_le hy1 hAD
  have hpb : y^B≤y^D := Real.rpow_le_rpow_of_exponent_le hy1 hBD
  have hp := physical_prefix_le (mobiusCriticalPrimeWindow y) hpow
  have hmass : C*y^D ≤ ∫ x in Ioi (y^A),
      (mobiusDivisorContinuousHead (mobiusCriticalPrimeWindow y) x)^2/x^3 := by
    nlinarith only [hy,hp,hpa]
  have hscaled := (mul_le_mul_of_nonneg_left hpb hC.le).trans hmass
  have hLC : L≤C := by dsimp [C]; have := le_max_left L 0; linarith
  exact hLC.trans ((le_div_iff₀ (Real.rpow_pos_of_pos hy0 B)).mpr hscaled)

private lemma prod_integer_density (N : ℕ) :
    (∏ n ∈ Finset.Icc 1 N,(n:ℝ)/(n+1)) = 1/((N:ℝ)+1) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.prod_Icc_succ_top (by omega),ih]
      push_cast
      field_simp

private lemma window_density_lower {y : ℝ} (hy : 1 ≤ y) :
    1/(y+1) ≤ ∏ p ∈ mobiusCriticalPrimeWindow y,(p:ℝ)/(p+1) := by
  have hsub : mobiusCriticalPrimeWindow y ⊆ Finset.Icc 1 ⌊y⌋₊ := by
    intro p hp
    obtain ⟨hpp,_,hpy⟩ := (mem_windowPrimes (by positivity) (by linarith)).mp hp
    exact Finset.mem_Icc.mpr ⟨hpp.one_lt.le,Nat.le_floor hpy⟩
  have hh := Finset.prod_le_prod_of_subset_of_le_one hsub
    (fun p hp => show (0:ℝ) ≤ (p:ℝ)/(p+1) by positivity)
    (fun p hp _ => show (p:ℝ)/(p+1) ≤ 1 by
      apply (div_le_one (by positivity : (0:ℝ)<p+1)).mpr
      linarith)
  rw [prod_integer_density] at hh
  apply le_trans _ hh
  apply one_div_le_one_div_of_le (by positivity : (0:ℝ)<(⌊y⌋₊:ℝ)+1)
  linarith [Nat.floor_le (show 0 ≤ y by linarith)]

/-- Density weighting does not remove the literal energy escaping beyond every
polynomial physical cutoff. -/
theorem tendsto_mobiusDivisorPrimeBlock_density_tail_energy (A : ℝ) (hA : 0 < A) :
    Tendsto (fun y : ℝ => mobiusDivisorCoreDensity (mobiusCriticalPrimeWindow y) *
      ∫ x in Ioi (y^A), (mobiusDivisorContinuousHead (mobiusCriticalPrimeWindow y) x)^2/x^3)
      atTop atTop := by
  have hρ : 0 < Sieve.squarefreeDensity := by rw [Sieve.squarefreeDensity_eq]; positivity
  apply tendsto_atTop.mpr
  intro B
  let C : ℝ := max B 0+1
  have hC : 0<C := by dsimp [C]; have := le_max_right B 0; linarith
  have hpower := tendsto_mobiusDivisorPrimeBlock_scaled_tail_energy A hA 1
  have ht := hpower.eventually_ge_atTop (2*C/Sieve.squarefreeDensity)
  filter_upwards [ht,eventually_ge_atTop (1:ℝ)] with y ht hy
  let T := ∫ x in Ioi (y^A), (mobiusDivisorContinuousHead (mobiusCriticalPrimeWindow y) x)^2/x^3
  have hy0 : 0<y := by linarith
  have hT0 : 0≤T := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := (Real.rpow_pos_of_pos hy0 A).trans hx
    exact div_nonneg (sq_nonneg _) (by positivity)
  have ht' : 2*C/Sieve.squarefreeDensity*y ≤ T := by
    change 2*C/Sieve.squarefreeDensity ≤ T/y^1 at ht
    rw [Real.rpow_one] at ht
    exact (le_div_iff₀ hy0).mp ht
  have hden := window_density_lower hy
  have hfloor : Sieve.squarefreeDensity/(y+1) ≤
      mobiusDivisorCoreDensity (mobiusCriticalPrimeWindow y) := by
    simpa only [mobiusDivisorCoreDensity,mul_one_div] using
      mul_le_mul_of_nonneg_left hden hρ.le
  have hprod := mul_le_mul_of_nonneg_right hfloor hT0
  have hprod' := mul_le_mul_of_nonneg_left ht'
    (by positivity : 0≤Sieve.squarefreeDensity/(y+1))
  have hlower : C ≤ Sieve.squarefreeDensity/(y+1)*(2*C/Sieve.squarefreeDensity*y) := by
    have he : Sieve.squarefreeDensity/(y+1)*(2*C/Sieve.squarefreeDensity*y) = 2*C*y/(y+1) := by
      field_simp
    rw [he]
    apply (le_div_iff₀ (by positivity : 0<y+1)).mpr
    nlinarith only [mul_nonneg hC.le (sub_nonneg.mpr hy)]
  have hBC : B≤C := by dsimp [C]; have := le_max_left B 0; linarith
  exact hBC.trans (hlower.trans (hprod'.trans hprod))

private lemma initial_prime {y : ℝ} (hy : 0≤y) {p : ℕ}
    (hp : p∈windowPrimes 0 y) : p.Prime :=
  ((mem_windowPrimes (by norm_num) hy).mp hp).1

private lemma initial_weight {y : ℝ} (hy : 0≤y) (t : ℝ) :
    clusterWeight (windowPrimes 0 y) t = clusterWeight ∅ t *
      ‖∏p∈windowPrimes 0 y,mobiusCriticalPrimeFactor p t‖^2 := by
  have he : divisorCoreMellinEuler (windowPrimes 0 y) (1+(t:ℂ)*Complex.I) =
      ∏p∈windowPrimes 0 y,mobiusCriticalPrimeFactor p t := by
    apply Finset.prod_congr rfl
    intro p hp
    have hpR : (0:ℝ)<p := by exact_mod_cast (initial_prime hy hp).pos
    have hroot : (Real.sqrt p:ℂ) = Complex.exp ((Real.log p:ℂ)/2) := by
      rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos hpR,Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    unfold mobiusCriticalPrimeFactor mobiusCriticalPrimeRadius
    rw [Complex.ofReal_inv,hroot,← Complex.exp_neg,← Complex.exp_add]
    congr 2
    push_cast
    ring
  dsimp [clusterWeight,clusterMellin]
  rw [mellin_mobiusDivisorContinuousHead_euler _ (fun p hp => initial_prime hy hp)
    (by simp; norm_num),he]
  have hempty : (fun x : ℝ => (mobiusDivisorContinuousHead ∅ x:ℂ)) =
      fun x : ℝ => (divisorContinuousUnitHead x:ℂ) := by
    funext x
    simp [mobiusDivisorContinuousHead]
  rw [hempty,norm_mul,mul_pow,mul_comm]

private lemma physical_initial_lower :
    ∃ c δ : ℝ, 0<c ∧ 0<δ ∧ ∀ y : ℝ, 27≤y →
      4*Real.pi/(3*Real.log y)<δ →
      c/Real.log y * (Real.exp (-16*Real.sqrt (Real.sqrt y)) *
        (1+1/Real.sqrt y)^(mobiusCriticalPrimeWindow y).card) ≤
        mobiusDivisorDilationMean (windowPrimes 0 y) 1 := by
  have hw0 := clusterWeight_empty_pos
  obtain ⟨δ,hδ,hfloor⟩ := exists_local_half_floor_of_continuousAt_of_pos
    (clusterWeight_continuous ∅).continuousAt hw0
  refine ⟨clusterWeight ∅ 0/12,δ,by positivity,hδ,?_⟩
  intro y hy hsmall
  have hy0 : 0≤y := by linarith
  have hl : 0<Real.log y := Real.log_pos (by linarith)
  have hp : (windowPrimes 0 y).Nonempty := by
    refine ⟨2,(mem_windowPrimes (by norm_num) hy0).mpr ?_⟩
    exact ⟨Nat.prime_two,by norm_num,by norm_num; linarith⟩
  have hprime : ∀p∈windowPrimes 0 y,p.Prime := fun _ h => initial_prime hy0 h
  let L := Real.exp (-16*Real.sqrt (Real.sqrt y)) *
        (1+1/Real.sqrt y)^(mobiusCriticalPrimeWindow y).card
  have hL : 0≤L := by dsimp [L]; positivity
  have hpoint (t : ℝ) (ht : t∈Icc (Real.pi/Real.log y) (4*Real.pi/(3*Real.log y))) :
      clusterWeight ∅ 0/2*L ≤ clusterWeight (windowPrimes 0 y) t := by
    have hwt : clusterWeight ∅ 0/2≤clusterWeight ∅ t := by
      apply hfloor
      rw [abs_of_nonneg ((div_nonneg Real.pi_pos.le hl.le).trans ht.1)]
      exact ht.2.trans_lt hsmall
    rw [initial_weight hy0]
    exact mul_le_mul hwt (mobiusCriticalInitialPrime_norm_sq_lower_on_gammaBand hy ht)
      hL (by dsimp [clusterWeight]; positivity)
  have hab : Real.pi/Real.log y ≤ 4*Real.pi/(3*Real.log y) := by
    apply (div_le_div_iff₀ hl (by positivity : 0<3*Real.log y)).mpr
    nlinarith [Real.pi_pos]
  have hm := intervalIntegral.integral_mono_on (μ := volume) hab
    (intervalIntegrable_const (c := clusterWeight ∅ 0/2*L))
    ((clusterWeight_continuous (windowPrimes 0 y)).intervalIntegrable _ _) hpoint
  rw [intervalIntegral.integral_const,smul_eq_mul,mobiusCriticalPrimeGammaBand_width (by linarith)] at hm
  rw [intervalIntegral.integral_of_le hab] at hm
  have hi := clusterWeight_integrable (windowPrimes 0 y) hp hprime
  have hwhole := setIntegral_le_integral (s := Ioc (Real.pi/Real.log y)
    (4*Real.pi/(3*Real.log y))) hi
    (Filter.Eventually.of_forall (fun t => sq_nonneg ‖clusterMellin (windowPrimes 0 y) t‖))
  have hs := cluster_dilation_spectrum (windowPrimes 0 y) hp hprime (r := 1) (by norm_num)
  simp only [Real.log_one,zero_mul,Real.cos_zero,mul_one] at hs
  rw [hs]
  have hmul := mul_le_mul_of_nonneg_left (hm.trans hwhole)
    (by positivity : 0≤1/(2*Real.pi))
  change clusterWeight ∅ 0/12/Real.log y*L ≤ _
  calc
    _ = 1/(2*Real.pi) * (Real.pi/(3*Real.log y) * (clusterWeight ∅ 0/2*L)) := by
      field_simp [Real.pi_ne_zero]
      ring
    _ ≤ _ := hmul

private lemma small_prime_loss_absorbed : ∀ᶠ y : ℝ in atTop,
    16*Real.sqrt (Real.sqrt y) ≤ Real.sqrt y/(12*Real.log y) := by
  have he {y : ℝ} (hy : 0≤y) : Real.sqrt (Real.sqrt y) = y^(1/4:ℝ) := by
    rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,← Real.rpow_mul hy]
    norm_num
  have ht : Tendsto (fun y : ℝ => Real.log y/Real.sqrt (Real.sqrt y)) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/4)).tendsto_div_nhds_zero
    apply h.congr'
    filter_upwards [eventually_ge_atTop (0:ℝ)] with y hy
    rw [he hy]
  filter_upwards [ht.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1/192)),
    eventually_gt_atTop (1:ℝ)] with y hy hy1
  have hy0 : 0<y := by linarith
  have hs : 0<Real.sqrt (Real.sqrt y) := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hy0)
  have hl : 0<Real.log y := Real.log_pos hy1
  have hcross := (div_lt_iff₀ hs).mp hy
  have hmul := mul_le_mul_of_nonneg_right hcross.le hs.le
  have hsq := Real.sq_sqrt (Real.sqrt_nonneg y)
  apply (le_div_iff₀ (by positivity : 0<12*Real.log y)).mpr
  nlinarith only [hmul,hsq]

/-- The natural exhaustive initial-prime core also has exponentially growing
limiting physical energy. -/
theorem eventually_mobiusDivisorInitialPrime_energy_exponential :
    ∃ c : ℝ,0<c ∧ ∀ᶠ y : ℝ in atTop,
      c/Real.log y*Real.exp (Real.sqrt y/(12*Real.log y)) ≤
        mobiusDivisorDilationMean (windowPrimes 0 y) 1 := by
  obtain ⟨c,δ,hc,hδ,hbound⟩ := physical_initial_lower
  have hsmall : Tendsto (fun y : ℝ => 4*Real.pi/(3*Real.log y)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.const_mul_atTop (by norm_num))
  refine ⟨c,hc,?_⟩
  filter_upwards [hsmall.eventually (eventually_lt_nhds hδ),small_prime_loss_absorbed,
    window_power_exponential,eventually_ge_atTop (27:ℝ)] with y hsmall hloss hpow hy
  have hl : 0<Real.log y := Real.log_pos (by linarith)
  have he : Real.exp (Real.sqrt y/(12*Real.log y)) ≤
      Real.exp (-16*Real.sqrt (Real.sqrt y))*Real.exp (Real.sqrt y/(6*Real.log y)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hr : Real.sqrt y/(6*Real.log y) = 2*(Real.sqrt y/(12*Real.log y)) := by ring
    rw [hr]
    linarith
  have hh := he.trans (mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le)
  exact (mul_le_mul_of_nonneg_left hh (by positivity : 0≤c/Real.log y)).trans
    (hbound y hy hsmall)

private lemma initial_energy_superpower (A C : ℝ) (hA : 0 < A) (hC : 0 < C) :
    ∀ᶠ y : ℝ in atTop, C*y^A ≤
      mobiusDivisorDilationMean (windowPrimes 0 y) 1 := by
  obtain ⟨c,hc,hbound⟩ := eventually_mobiusDivisorInitialPrime_energy_exponential
  have hsmall : Tendsto (fun y : ℝ => (Real.log y)^2/Real.sqrt y) atTop (𝓝 0) := by
    simpa only [Real.rpow_two,← Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_rpow_atTop (2:ℝ) (by norm_num : (0:ℝ)<1/2)).tendsto_div_nhds_zero
  have hε : 0 < 1/(12*(A+2)) := by positivity
  filter_upwards [hbound,hsmall.eventually (eventually_lt_nhds hε),
    eventually_ge_atTop (C/c),eventually_gt_atTop (3:ℝ)] with y hb hh hcy hy
  have hy0 : 0 < y := by linarith
  have hl : 0 < Real.log y := Real.log_pos (by linarith)
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy0
  have hcross := (div_lt_div_iff₀ hs (by positivity : 0 < 12*(A+2))).mp hh
  have hexp : (A+2)*Real.log y ≤ Real.sqrt y/(12*Real.log y) := by
    apply (le_div_iff₀ (by positivity : 0 < 12*Real.log y)).mpr
    nlinarith only [hcross]
  have hp : y^(A+2) ≤ Real.exp (Real.sqrt y/(12*Real.log y)) := by
    rw [Real.rpow_def_of_pos hy0]
    exact Real.exp_le_exp.mpr (by simpa only [mul_comm] using hexp)
  have hcy' : C ≤ c*y := by
    have h := (div_le_iff₀ hc).mp hcy
    nlinarith only [h]
  have hcoef : C ≤ c/Real.log y*y^2 := by
    have hlogle : Real.log y ≤ y := (Real.log_le_sub_one_of_pos hy0).trans (by linarith)
    have hh1 := mul_le_mul_of_nonneg_left hlogle hC.le
    have hh2 := mul_le_mul_of_nonneg_right hcy' hy0.le
    have hdiv : C ≤ (c*y^2)/Real.log y :=
      (le_div_iff₀ hl).mpr (by nlinarith only [hh1,hh2])
    convert hdiv using 1; ring
  calc
    C*y^A ≤ (c/Real.log y*y^2)*y^A :=
      mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hy0.le A)
    _ = c/Real.log y*y^(A+2) := by rw [Real.rpow_add hy0,Real.rpow_two]; ring
    _ ≤ c/Real.log y*Real.exp (Real.sqrt y/(12*Real.log y)) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ ≤ _ := hb

/-- Every polynomially rescaled tail beyond every polynomial prime-scale cutoff
still diverges for the literal initial-prime head. -/
theorem tendsto_mobiusDivisorInitialPrime_scaled_tail_energy (A : ℝ) (hA : 0 < A) (B : ℝ) :
    Tendsto (fun y : ℝ => (∫ x in Ioi (y^A),
      (mobiusDivisorContinuousHead (windowPrimes 0 y) x)^2/x^3)/y^B) atTop atTop := by
  apply tendsto_atTop.mpr
  intro L
  let C : ℝ := max L 0+1
  let D : ℝ := max A B+1
  have hC : 0<C := by dsimp [C]; have := le_max_right L 0; linarith
  have hD : 0<D := by dsimp [D]; have := le_max_left A B; linarith
  have hAD : A≤D := by dsimp [D]; have := le_max_left A B; linarith
  have hBD : B≤D := by dsimp [D]; have := le_max_right A B; linarith
  filter_upwards [initial_energy_superpower D (C+9/25) hD (by positivity),
    eventually_ge_atTop (1:ℝ)] with y hy hy1
  have hy0 : 0<y := by linarith
  have hpow : 1≤y^A := Real.one_le_rpow hy1 hA.le
  have hpa : y^A≤y^D := Real.rpow_le_rpow_of_exponent_le hy1 hAD
  have hpb : y^B≤y^D := Real.rpow_le_rpow_of_exponent_le hy1 hBD
  have hp := physical_prefix_le (windowPrimes 0 y) hpow
  have hmass : C*y^D ≤ ∫ x in Ioi (y^A),
      (mobiusDivisorContinuousHead (windowPrimes 0 y) x)^2/x^3 := by
    nlinarith only [hy,hp,hpa]
  have hscaled := (mul_le_mul_of_nonneg_left hpb hC.le).trans hmass
  have hLC : L≤C := by dsimp [C]; have := le_max_left L 0; linarith
  exact hLC.trans ((le_div_iff₀ (Real.rpow_pos_of_pos hy0 B)).mpr hscaled)

private lemma initial_density_lower {y : ℝ} (hy : 1 ≤ y) :
    1/(y+1) ≤ ∏ p ∈ windowPrimes 0 y,(p:ℝ)/(p+1) := by
  have hsub : windowPrimes 0 y ⊆ Finset.Icc 1 ⌊y⌋₊ := by
    intro p hp
    obtain ⟨hpp,_,hpy⟩ := (mem_windowPrimes (by positivity) (by linarith)).mp hp
    exact Finset.mem_Icc.mpr ⟨hpp.one_lt.le,Nat.le_floor hpy⟩
  have hh := Finset.prod_le_prod_of_subset_of_le_one hsub
    (fun p hp => show (0:ℝ) ≤ (p:ℝ)/(p+1) by positivity)
    (fun p hp _ => show (p:ℝ)/(p+1) ≤ 1 by
      apply (div_le_one (by positivity : (0:ℝ)<p+1)).mpr
      linarith)
  rw [prod_integer_density] at hh
  apply le_trans _ hh
  apply one_div_le_one_div_of_le (by positivity : (0:ℝ)<(⌊y⌋₊:ℝ)+1)
  linarith [Nat.floor_le (show 0 ≤ y by linarith)]

/-- Density weighting does not remove the literal energy escaping beyond every
polynomial physical cutoff. -/
theorem tendsto_mobiusDivisorInitialPrime_density_tail_energy (A : ℝ) (hA : 0 < A) :
    Tendsto (fun y : ℝ => mobiusDivisorCoreDensity (windowPrimes 0 y) *
      ∫ x in Ioi (y^A), (mobiusDivisorContinuousHead (windowPrimes 0 y) x)^2/x^3)
      atTop atTop := by
  have hρ : 0 < Sieve.squarefreeDensity := by rw [Sieve.squarefreeDensity_eq]; positivity
  apply tendsto_atTop.mpr
  intro B
  let C : ℝ := max B 0+1
  have hC : 0<C := by dsimp [C]; have := le_max_right B 0; linarith
  have hpower := tendsto_mobiusDivisorInitialPrime_scaled_tail_energy A hA 1
  have ht := hpower.eventually_ge_atTop (2*C/Sieve.squarefreeDensity)
  filter_upwards [ht,eventually_ge_atTop (1:ℝ)] with y ht hy
  let T := ∫ x in Ioi (y^A), (mobiusDivisorContinuousHead (windowPrimes 0 y) x)^2/x^3
  have hy0 : 0<y := by linarith
  have hT0 : 0≤T := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := (Real.rpow_pos_of_pos hy0 A).trans hx
    exact div_nonneg (sq_nonneg _) (by positivity)
  have ht' : 2*C/Sieve.squarefreeDensity*y ≤ T := by
    change 2*C/Sieve.squarefreeDensity ≤ T/y^1 at ht
    rw [Real.rpow_one] at ht
    exact (le_div_iff₀ hy0).mp ht
  have hden := initial_density_lower hy
  have hfloor : Sieve.squarefreeDensity/(y+1) ≤
      mobiusDivisorCoreDensity (windowPrimes 0 y) := by
    simpa only [mobiusDivisorCoreDensity,mul_one_div] using
      mul_le_mul_of_nonneg_left hden hρ.le
  have hprod := mul_le_mul_of_nonneg_right hfloor hT0
  have hprod' := mul_le_mul_of_nonneg_left ht'
    (by positivity : 0≤Sieve.squarefreeDensity/(y+1))
  have hlower : C ≤ Sieve.squarefreeDensity/(y+1)*(2*C/Sieve.squarefreeDensity*y) := by
    have he : Sieve.squarefreeDensity/(y+1)*(2*C/Sieve.squarefreeDensity*y) = 2*C*y/(y+1) := by
      field_simp
    rw [he]
    apply (le_div_iff₀ (by positivity : 0<y+1)).mpr
    nlinarith only [mul_nonneg hC.le (sub_nonneg.mpr hy)]
  have hBC : B≤C := by dsimp [C]; have := le_max_left B 0; linarith
  exact hBC.trans (hlower.trans (hprod'.trans hprod))

end RHTower
