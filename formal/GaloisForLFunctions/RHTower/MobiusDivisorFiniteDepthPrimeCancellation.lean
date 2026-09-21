import GaloisForLFunctions.RHTower.DivisorContinuousHeadMellin
import GaloisForLFunctions.PNTPlus.Consequences
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Uniform actual-prime cancellation in arbitrary finite child fields

Two processed primes force the physical Mellin transform to tend to zero at
one half. Every nonzero finite combination of delayed source components must
therefore take both signs: a nonnegative profile would have a strictly positive
Mellin moment, bounded below uniformly as the exponent approaches one half.
The first nonzero delay supplies a nonzero interval without any boundary
absolute-convergence assumption.

Compactness of the coefficient unit sphere makes the inward margin uniform
before the receiving coefficients are chosen. Prime windows then produce an
actual fresh prime at every sufficiently large original integer cutoff. That
prime preserves the signed margin throughout a common multiplicative cutoff
collar. The field may be any finite set of positive integer delays.

The constants and threshold depend on the processed core and child field.
No bound for their dependence on growing depth, complete energy payment,
exhaustive insertion schedule, or critical-action completion is asserted.
-/

noncomputable section
open Complex Filter Set Topology MeasureTheory Finset
namespace RHTower

/-- Two finite-prime factors leave a zero after the unit half-pole is filled. -/
theorem divisorCoreMellin_half_eq_zero (P : Finset ℕ) (hP : 1 < P.card) :
    divisorCoreMellin P (1/2) = 0 := by
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp hP
  have he : divisorCoreMellinEuler P = fun s =>
      (1-Complex.exp ((1/2-s)*(Real.log p : ℂ))) *
        divisorCoreMellinEuler (P.erase p) s := by
    funext s
    exact (Finset.mul_prod_erase P _ hp).symm
  have hd : deriv (divisorCoreMellinEuler P) (1/2) = 0 := by
    rw [he]
    have hf : DifferentiableAt ℂ (fun s : ℂ =>
        1-Complex.exp ((1/2-s)*(Real.log p : ℂ))) (1/2) := by fun_prop
    have hg := (differentiable_divisorCoreMellinEuler (P.erase p)) (1/2)
    rw [deriv_fun_mul hf hg,
      divisorCoreMellinEuler_half (P.erase p) ⟨q, mem_erase.mpr ⟨hpq.symm, hq⟩⟩]
    simp
  rw [divisorCoreMellin, divisorCoreMellinNumerator, dslope_same, hd]
  simp

/-- A finite linear functional of actual delayed processed-head components. -/
def mobiusDivisorDelayedProfile (P I : Finset ℕ) (a : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ r ∈ I, a r * mobiusDivisorContinuousHead P (x/r)

private lemma delayed_convergent (P I : Finset ℕ) (a : ℕ → ℝ)
    (hI : ∀ r ∈ I, 0 < r) {s : ℂ} (hs : 1/2 < s.re) :
    MellinConvergent (fun x => (mobiusDivisorDelayedProfile P I a x : ℂ)) (-s) := by
  have hc (r : ℕ) (hr : r ∈ I) :
      MellinConvergent (fun x => (a r : ℂ) • (mobiusDivisorContinuousHead P (x/r) : ℂ)) (-s) := by
    have hrR : (0:ℝ) < r := by exact_mod_cast hI r hr
    have h := (MellinConvergent.comp_mul_left (a := (r:ℝ)⁻¹) (inv_pos.mpr hrR)).mpr
      (mellinConvergent_mobiusDivisorContinuousHead P hs)
    have h' : MellinConvergent (fun x => (mobiusDivisorContinuousHead P (x/r) : ℂ)) (-s) := by
      simpa only [div_eq_mul_inv, mul_comm] using h
    exact h'.const_smul (a r : ℂ)
  unfold MellinConvergent mobiusDivisorDelayedProfile
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.smul_sum]
  exact integrable_finsetSum I (fun r hr => by simpa only [MellinConvergent, IntegrableOn, smul_eq_mul] using hc r hr)

private lemma delayed_mellin (P I : Finset ℕ) (a : ℕ → ℝ)
    (hP : P.Nonempty) (hprime : ∀ p ∈ P, p.Prime)
    (hI : ∀ r ∈ I, 0 < r) {s : ℂ} (hs : 1/2 < s.re) :
    mellin (fun x => (mobiusDivisorDelayedProfile P I a x : ℂ)) (-s) =
      (∑ r ∈ I, (a r : ℂ) * Complex.exp (-s*(Real.log r : ℂ))) * divisorCoreMellin P s := by
  have hc (r : ℕ) (hr : r ∈ I) :=
    delayed_convergent P {r} a (by simpa using hI r hr) hs
  unfold mellin mobiusDivisorDelayedProfile
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.smul_sum]
  rw [integral_finsetSum I (fun r hr => by
    simpa only [MellinConvergent, IntegrableOn, mobiusDivisorDelayedProfile, Finset.sum_singleton, Complex.ofReal_mul]
      using hc r hr), Finset.sum_mul]
  apply sum_congr rfl
  intro r hr
  change mellin (fun x => (a r : ℂ) • (mobiusDivisorContinuousHead P (x/r) : ℂ)) (-s) = _
  rw [mellin_const_smul, smul_eq_mul]
  have hrR : (0:ℝ) < r := by exact_mod_cast hI r hr
  have h := mellin_comp_mul_left (fun x => (mobiusDivisorContinuousHead P x : ℂ)) (-s)
    (inv_pos.mpr hrR)
  have harg : (r:ℂ).arg ≠ Real.pi := by
    rw [Complex.natCast_arg]
    exact ne_of_lt Real.pi_pos
  have h' : mellin (fun x => (mobiusDivisorContinuousHead P (x/r) : ℂ)) (-s) =
      (r:ℂ)^(-s)*mellin (fun x => (mobiusDivisorContinuousHead P x : ℂ)) (-s) := by
    simpa only [div_eq_mul_inv, mul_comm, neg_neg, Complex.ofReal_inv, Complex.ofReal_natCast,
      Complex.inv_cpow _ _ harg, ← Complex.cpow_neg, smul_eq_mul] using h
  rw [h', mellin_mobiusDivisorContinuousHead_eq_core P hP hprime hs,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast (hI r hr).ne'), ← Complex.natCast_log]
  rw [mul_comm (Real.log r : ℂ) (-s)]
  ring

private lemma delayed_mellin_boundary (P I : Finset ℕ) (a : ℕ → ℝ)
    (hP : 1 < P.card) (hprime : ∀ p ∈ P, p.Prime) (hI : ∀ r ∈ I, 0 < r) :
    Tendsto (fun σ : ℝ => mellin (fun x => (mobiusDivisorDelayedProfile P I a x : ℂ))
      (-(σ : ℂ))) (𝓝[>] (1/2)) (𝓝 0) := by
  have hn : P.Nonempty := Finset.card_pos.mp (by omega)
  have he : Continuous (fun s : ℂ => ∑ r ∈ I, (a r : ℂ) * Complex.exp (-s*(Real.log r : ℂ))) := by
    fun_prop
  have hc : ContinuousAt (divisorCoreMellin P) (1/2) :=
    ((differentiable_divisorCoreMellinNumerator P).continuous.continuousAt).div
      continuousAt_id (by norm_num)
  have hc' : ContinuousAt (divisorCoreMellin P) ((1/2:ℝ):ℂ) := by simpa using hc
  have ht := ((he.continuousAt.mul hc').comp (x := (1/2:ℝ))
    Complex.continuous_ofReal.continuousAt).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (1/2:ℝ)))
  simp only [Function.comp_apply, Pi.mul_apply, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
    divisorCoreMellin_half_eq_zero P hP, mul_zero] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  exact (delayed_mellin P I a hn hprime hI (by simpa using hσ)).symm

private lemma delayed_zero (P I : Finset ℕ) (a : ℕ → ℝ)
    (hI : ∀ r ∈ I, 0 < r) {x : ℝ} (hx : x ≤ 1) :
    mobiusDivisorDelayedProfile P I a x = 0 := by
  apply Finset.sum_eq_zero
  intro r hr
  have hrR : (1:ℝ) ≤ r := by exact_mod_cast hI r hr
  rw [mobiusDivisorContinuousHead_eq_zero P ((div_le_one (by linarith)).mpr (hx.trans hrR)), mul_zero]

private lemma real_mellin_integrand (f : ℝ → ℝ) (σ : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    (((x : ℂ)^(-(σ:ℂ)-1)) • (f x : ℂ)).re = x^(-σ-1)*f x := by
  rw [show -(σ:ℂ)-1 = ((-σ-1:ℝ):ℂ) by push_cast; rfl, ← Complex.ofReal_cpow hx]
  simp only [smul_eq_mul, ← Complex.ofReal_mul, Complex.ofReal_re]

private lemma delayed_real_integrable (P I : Finset ℕ) (a : ℕ → ℝ)
    (hI : ∀ r ∈ I, 0 < r) {σ : ℝ} (hσ : 1/2 < σ) :
    IntegrableOn (fun x => x^(-σ-1)*mobiusDivisorDelayedProfile P I a x) (Ioi 0) := by
  have h := (delayed_convergent P I a hI (s := (σ:ℂ)) (by simpa using hσ)).re
  apply h.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact real_mellin_integrand _ _ hx.le

private lemma delayed_real_mellin (P I : Finset ℕ) (a : ℕ → ℝ)
    (hI : ∀ r ∈ I, 0 < r) {σ : ℝ} (hσ : 1/2 < σ) :
    (∫ x in Ioi (0:ℝ), x^(-σ-1)*mobiusDivisorDelayedProfile P I a x) =
      (mellin (fun x => (mobiusDivisorDelayedProfile P I a x : ℂ)) (-(σ:ℂ))).re := by
  calc
    _ = ∫ x in Ioi (0:ℝ), (((x : ℂ)^(-(σ:ℂ)-1)) •
        (mobiusDivisorDelayedProfile P I a x : ℂ)).re := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact (real_mellin_integrand _ _ hx.le).symm
    _ = _ := integral_re (delayed_convergent P I a hI (s := (σ:ℂ)) (by simpa using hσ))

private lemma nonnegative_delayed_moment_zero (P I : Finset ℕ) (a : ℕ → ℝ)
    (hP : 1 < P.card) (hprime : ∀ p ∈ P, p.Prime) (hI : ∀ r ∈ I, 0 < r)
    (hpos : ∀ x, 0 ≤ mobiusDivisorDelayedProfile P I a x) :
    (∫ x in Ioi (0:ℝ), x^(-2:ℝ)*mobiusDivisorDelayedProfile P I a x) = 0 := by
  have hi := delayed_real_integrable P I a hI (σ := 1) (by norm_num)
  norm_num only at hi
  apply le_antisymm
  · have hb := Complex.continuous_re.continuousAt.tendsto.comp
      (delayed_mellin_boundary P I a hP hprime hI)
    have hb' : Tendsto (fun σ : ℝ => ∫ x in Ioi (0:ℝ),
        x^(-σ-1)*mobiusDivisorDelayedProfile P I a x) (𝓝[>] (1/2)) (𝓝 0) := by
      apply hb.congr'
      filter_upwards [self_mem_nhdsWithin] with σ hσ
      exact (delayed_real_mellin P I a hI hσ).symm
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hb'
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (1/2:ℝ)<1)).filter_mono nhdsWithin_le_nhds] with σ hσ hσ1
    apply integral_mono_ae hi (delayed_real_integrable P I a hI hσ)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    by_cases hx1 : x ≤ 1
    · rw [delayed_zero P I a hI hx1]
      simp
    · exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hx1) (by linarith)) (hpos x)
  · apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (Real.rpow_nonneg hx.le _) (hpos x)

private lemma head_first_block (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    {x : ℝ} (hx : x ∈ Set.Ioo (1:ℝ) 2) :
    mobiusDivisorContinuousHead P x = divisorContinuousUnitHead x := by
  unfold mobiusDivisorContinuousHead
  rw [Finset.sum_eq_single 1]
  · simp
  · intro d hd hd1
    have hd0 := Nat.pos_of_mem_divisors hd
    have hd2 : (2:ℝ) ≤ d := by exact_mod_cast (show 2 ≤ d by omega)
    rw [divisorContinuousUnitHead_eq_zero ((div_le_one (by linarith)).mpr (by linarith [hx.2]))]
    ring
  · intro h1
    exact (h1 (Nat.one_mem_divisors.mpr (Finset.prod_ne_zero_iff.mpr
      (fun p hp => (hprime p hp).ne_zero)))).elim

private lemma delayed_first_block (P I : Finset ℕ) (a : ℕ → ℝ)
    (hprime : ∀ p ∈ P, p.Prime) (hI : ∀ r ∈ I, 0 < r)
    (ha : ∃ r ∈ I, a r ≠ 0) :
    ∃ r : ℕ, 0 < r ∧ ∀ x ∈ Set.Ioo (r:ℝ) (r+1),
      mobiusDivisorDelayedProfile P I a x ≠ 0 := by
  let J := I.filter (fun r => a r ≠ 0)
  have hJ : J.Nonempty := by
    obtain ⟨r,hr,ha⟩ := ha
    exact ⟨r, mem_filter.mpr ⟨hr,ha⟩⟩
  let r := J.min' hJ
  have hrJ : r ∈ J := J.min'_mem hJ
  have hrI : r ∈ I := (mem_filter.mp hrJ).1
  have har : a r ≠ 0 := (mem_filter.mp hrJ).2
  have hr0 : 0 < r := hI r hrI
  have hrR : (1:ℝ) ≤ r := by exact_mod_cast hr0
  refine ⟨r,hr0,?_⟩
  intro x hx
  have hxr : x/r ∈ Set.Ioo (1:ℝ) 2 := by
    constructor
    · exact (one_lt_div (by linarith)).mpr hx.1
    · apply (div_lt_iff₀ (by linarith)).mpr
      linarith [hx.2]
  have he : mobiusDivisorDelayedProfile P I a x =
      a r * divisorContinuousUnitHead (x/r) := by
    unfold mobiusDivisorDelayedProfile
    rw [Finset.sum_eq_single r, head_first_block P hprime hxr]
    · intro k hk hkr
      by_cases hak : a k = 0
      · simp [hak]
      · have hrk : r ≤ k := J.min'_le _ (mem_filter.mpr ⟨hk,hak⟩)
        have hrk' : r+1 ≤ k := by omega
        have hkR : (0:ℝ)<k := by exact_mod_cast hI k hk
        rw [mobiusDivisorContinuousHead_eq_zero P ((div_le_one hkR).mpr (by
          have : (r:ℝ)+1 ≤ k := by exact_mod_cast hrk'
          linarith [hx.2])), mul_zero]
    · exact fun h => (h hrI).elim
  rw [he]
  exact mul_ne_zero har (divisorContinuousUnitHead_pos_first hxr).ne'

private lemma delayed_not_nonnegative (P I : Finset ℕ) (a : ℕ → ℝ)
    (hP : 1 < P.card) (hprime : ∀ p ∈ P, p.Prime) (hI : ∀ r ∈ I, 0 < r)
    (ha : ∃ r ∈ I, a r ≠ 0) :
    ¬ ∀ x, 0 ≤ mobiusDivisorDelayedProfile P I a x := by
  intro hpos
  have hz := nonnegative_delayed_moment_zero P I a hP hprime hI hpos
  have hi := delayed_real_integrable P I a hI (σ := 1) (by norm_num)
  norm_num only at hi
  have hp : 0 < ∫ x in Ioi (0:ℝ), x^(-2:ℝ)*mobiusDivisorDelayedProfile P I a x := by
    apply (integral_pos_iff_support_of_nonneg_ae _ hi).mpr
    · obtain ⟨r,hr,hf⟩ := delayed_first_block P I a hprime hI ha
      have hrR : (0:ℝ)<r := by exact_mod_cast hr
      have hsub : Set.Ioo (r:ℝ) (r+1) ⊆ Function.support
          (fun x => x^(-2:ℝ)*mobiusDivisorDelayedProfile P I a x) := by
        intro x hx
        exact mul_ne_zero (Real.rpow_pos_of_pos (hrR.trans hx.1) _).ne' (hf x hx)
      apply lt_of_lt_of_le _ (measure_mono hsub)
      rw [Measure.restrict_apply measurableSet_Ioo, inter_eq_left.mpr
        (show Set.Ioo (r:ℝ) (r+1) ⊆ Set.Ioi 0 from fun x hx => hrR.trans hx.1), Real.volume_Ioo]
      simp
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact mul_nonneg (Real.rpow_nonneg hx.le _) (hpos x)
  linarith

/-- Every nonzero finite combination of delayed components of a processed
source with at least two primes takes both signs. The delays have no fixed
upper bound, and no correlation sign is assumed. -/
theorem mobiusDivisorDelayedProfile_both_signs (P I : Finset ℕ) (a : ℕ → ℝ)
    (hP : 1 < P.card) (hprime : ∀ p ∈ P, p.Prime) (hI : ∀ r ∈ I, 0 < r)
    (ha : ∃ r ∈ I, a r ≠ 0) :
    (∃ x : ℝ, 1 < x ∧ mobiusDivisorDelayedProfile P I a x < 0) ∧
      (∃ x : ℝ, 1 < x ∧ 0 < mobiusDivisorDelayedProfile P I a x) := by
  have hn := delayed_not_nonnegative P I a hP hprime hI ha
  push Not at hn
  have ha' : ∃ r ∈ I, -a r ≠ 0 := by
    obtain ⟨r,hr,ha⟩ := ha
    exact ⟨r,hr,neg_ne_zero.mpr ha⟩
  have hp := delayed_not_nonnegative P I (fun r => -a r) hP hprime hI ha'
  push Not at hp
  have he (x : ℝ) : mobiusDivisorDelayedProfile P I (fun r => -a r) x =
      -mobiusDivisorDelayedProfile P I a x := by
    simp [mobiusDivisorDelayedProfile, Finset.sum_neg_distrib]
  obtain ⟨x,hx⟩ := hn
  obtain ⟨y,hy⟩ := hp
  rw [he] at hy
  have hx1 : 1<x := by
    by_contra h
    rw [delayed_zero P I a hI (le_of_not_gt h)] at hx
    exact lt_irrefl _ hx
  have hy1 : 1<y := by
    by_contra h
    rw [delayed_zero P I a hI (le_of_not_gt h)] at hy
    linarith
  exact ⟨⟨x,hx1,hx⟩,⟨y,hy1,by linarith⟩⟩

private lemma continuous_unit_head : Continuous divisorContinuousUnitHead := by
  let b : ℕ → ℂ := fun n => (primeFreeDivisorIncrement n : ℂ)
  let k : ℝ → ℂ := fun t => (1/(2*Real.sqrt t) : ℝ)
  let g : ℝ → ℂ := fun t => k t * ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, b n
  have hk {t : ℝ} (ht : 0<t) : (t:ℂ)^(1/2:ℂ)/(2*t)=k t := by
    have hs : (t:ℂ)^(1/2:ℂ)=(Real.sqrt t:ℂ) := by
      rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow ht.le]
      norm_num
    have htC : (t:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
    have hsC : (Real.sqrt t:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr ht).ne'
    have hsq : (Real.sqrt t:ℂ)^2=(t:ℂ) := by exact_mod_cast Real.sq_sqrt ht.le
    rw [hs]
    dsimp [k]
    push_cast
    apply (div_eq_div_iff (mul_ne_zero (by norm_num) htC)
      (mul_ne_zero (by norm_num) hsC)).mpr
    linear_combination 2*hsq
  have he (x : ℝ) : divisorContinuousUnitHead x =
      (∫ t in Set.Ioc (1:ℝ) (max 1 x), g t).re := by
    by_cases hx : x ≤ 1
    · simp [max_eq_left hx, divisorContinuousUnitHead_eq_zero hx]
    · rw [max_eq_right (le_of_not_ge hx), integral_Ioc_eq_integral_Ioo,
        divisorContinuousUnitHead, squareRootSummatoryPrimitive_eq_integral]
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioo
      intro t ht
      change ((t:ℂ)^(1/2:ℂ)/(2*t)) * _ = _
      rw [hk (by linarith [ht.1])]
  have hi (B : ℝ) : IntegrableOn g (Set.Icc 1 B) := by
    apply integrableOn_mul_sum_Icc b (by norm_num)
    apply ContinuousOn.integrableOn_Icc
    apply Complex.continuous_ofReal.comp_continuousOn
    apply continuousOn_const.div (continuousOn_const.mul Real.continuous_sqrt.continuousOn)
    intro t ht
    exact mul_ne_zero (by norm_num) (Real.sqrt_pos.mpr (by linarith [ht.1])).ne'
  rw [continuous_iff_continuousAt]
  intro x
  let B := max 1 x + 1
  have hB : 1 < B := by dsimp [B]; linarith [le_max_left (1:ℝ) x]
  have hxB : x < B := by dsimp [B]; linarith [le_max_right (1:ℝ) x]
  have hc : ContinuousOn (fun y => (∫ t in Set.Ioc (1:ℝ) (max 1 y), g t).re) (Set.Iio B) := by
    apply Complex.continuous_re.comp_continuousOn
    apply (intervalIntegral.continuousOn_primitive (hi B)).comp
      (continuous_const.max continuous_id).continuousOn
    intro y hy
    exact ⟨le_max_left _ _, max_le hB.le hy.le⟩
  have hc' : ContinuousAt (fun y => (∫ t in Set.Ioc (1:ℝ) (max 1 y), g t).re) x :=
    (hc x hxB).continuousAt (Iio_mem_nhds hxB)
  exact hc'.congr (Filter.Eventually.of_forall fun y => (he y).symm)

/-- Finite prime processing and arbitrary finite integer delays preserve
continuity of the physical source profile. -/
theorem continuous_mobiusDivisorDelayedProfile (P I : Finset ℕ) (a : ℕ → ℝ) :
    Continuous (mobiusDivisorDelayedProfile P I a) := by
  unfold mobiusDivisorDelayedProfile mobiusDivisorContinuousHead
  apply continuous_finsetSum
  intro r hr
  apply continuous_const.mul
  apply continuous_finsetSum
  intro d hd
  exact continuous_const.mul (continuous_unit_head.comp ((continuous_id.div_const _).div_const _))

private lemma actual_prime_in_child_band {l u : ℝ} (hl : 1<l) (hlu : l<u) (B : ℕ) :
    ∀ᶠ M : ℕ in atTop, ∃ p : ℕ, p.Prime ∧ B < p ∧
      (M:ℝ)/(p:ℝ) ∈ Set.Ioo l u := by
  have hu : 0<u := by linarith
  have hl0 : 0<l := by linarith
  have he : 0<u/l-1 := by rw [sub_pos, one_lt_div hl0]; exact hlu
  have hlim : Tendsto (fun M : ℕ => (M:ℝ)/u) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_div_const hu
  have hp := hlim.eventually (prime_between he)
  filter_upwards [hp, hlim.eventually_gt_atTop (B:ℝ)] with M hp hB
  obtain ⟨p,hp,hlo,hhi⟩ := hp
  have hpR : (0:ℝ)<p := by exact_mod_cast hp.pos
  have hfrac : (1+(u/l-1))*((M:ℝ)/u)=(M:ℝ)/l := by field_simp; ring
  rw [hfrac] at hhi
  refine ⟨p,hp,by exact_mod_cast hB.trans hlo,?_⟩
  constructor
  · apply (lt_div_iff₀ hpR).mpr
    have := (lt_div_iff₀ hl0).mp hhi
    nlinarith
  · apply (div_lt_iff₀ hpR).mpr
    have := (div_lt_iff₀ hu).mp hlo
    nlinarith

private lemma source_negative_rectangle (P I : Finset ℕ)
    (hP : 1 < P.card) (hprime : ∀ p ∈ P, p.Prime) (hI : ∀ r ∈ I, 0 < r)
    (z : I → ℝ) (hz : z ≠ 0) :
    ∃ (U : Set (I → ℝ)) (l u c : ℝ), U ∈ 𝓝 z ∧ 1<l ∧ l<u ∧ 0<c ∧
      ∀ w ∈ U, ∀ x ∈ Set.Ioo l u,
        (∑ r : I, w r * mobiusDivisorContinuousHead P (x/(r:ℕ))) ≤ -c := by
  classical
  let a : ℕ → ℝ := fun r => if hr : r∈I then z ⟨r,hr⟩ else 0
  have ha : ∃ r ∈ I, a r ≠ 0 := by
    by_contra h
    push Not at h
    apply hz
    funext r
    simpa [a] using h r r.property
  have he (x : ℝ) : mobiusDivisorDelayedProfile P I a x =
      ∑ r : I, z r * mobiusDivisorContinuousHead P (x/(r:ℕ)) := by
    rw [mobiusDivisorDelayedProfile, ← Finset.sum_coe_sort I]
    simp only [a, dif_pos (Subtype.property _)]
  obtain ⟨x,hx,hf⟩ := (mobiusDivisorDelayedProfile_both_signs P I a hP hprime hI ha).1
  rw [he] at hf
  let c := -(∑ r : I, z r * mobiusDivisorContinuousHead P (x/(r:ℕ)))/2
  have hc : 0<c := by
    change 0 < -(∑ r : I, z r * mobiusDivisorContinuousHead P (x/(r:ℕ)))/2
    linarith only [hf]
  have hhead : Continuous (mobiusDivisorContinuousHead P) := by
    have heh : mobiusDivisorDelayedProfile P {1} (fun _ => 1) = mobiusDivisorContinuousHead P := by
      funext y
      simp [mobiusDivisorDelayedProfile]
    rw [← heh]
    exact continuous_mobiusDivisorDelayedProfile P {1} (fun _ => 1)
  have hcont : Continuous (fun v : (I → ℝ) × ℝ =>
      ∑ r : I, v.1 r * mobiusDivisorContinuousHead P (v.2/(r:ℕ))) := by
    apply continuous_finsetSum
    intro r hr
    exact ((continuous_apply r).comp continuous_fst).mul
      (hhead.comp (continuous_snd.div_const _))
  have hn : {v : (I → ℝ) × ℝ | (∑ r : I, v.1 r *
      mobiusDivisorContinuousHead P (v.2/(r:ℕ))) < -c} ∈ 𝓝 (z,x) :=
    hcont.continuousAt.eventually (eventually_lt_nhds (by
      change (∑ r : I, z r * mobiusDivisorContinuousHead P (x/(r:ℕ))) <
        -(-(∑ r : I, z r * mobiusDivisorContinuousHead P (x/(r:ℕ)))/2)
      linarith only [hf]))
  rw [nhds_prod_eq] at hn
  obtain ⟨U,hU,V,hV,hUV⟩ := Filter.mem_prod_iff.mp hn
  obtain ⟨l,u,hxlu,hlu⟩ := mem_nhds_iff_exists_Ioo_subset.mp hV
  let l' := (max 1 l+x)/2
  have hl' : 1<l' := by dsimp [l']; linarith [le_max_left (1:ℝ) l]
  have hlx : l'<x := by dsimp [l']; have := max_lt hx hxlu.1; linarith
  have hll' : l ≤ l' := by dsimp [l']; linarith [le_max_right (1:ℝ) l, hxlu.1]
  refine ⟨U,l',u,c,hU,hl',hlx.trans hxlu.2,hc,?_⟩
  intro w hw y hy
  exact (hUV (show (w,y) ∈ U ×ˢ V from ⟨hw,hlu ⟨hll'.trans_lt hy.1,hy.2⟩⟩)).le

private lemma positive_finite_lower {α : Type*} (T : Finset α) (f : α → ℝ)
    (hf : ∀ t ∈ T, 0 < f t) : ∃ c : ℝ, 0<c ∧ ∀ t ∈ T, c ≤ f t := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨1,one_pos,by simp⟩
  | @insert t T ht ih =>
    obtain ⟨c,hc,hbound⟩ := ih (fun s hs => hf s (mem_insert_of_mem hs))
    refine ⟨min c (f t), lt_min hc (hf t (mem_insert_self _ _)), ?_⟩
    intro s hs
    rcases mem_insert.mp hs with rfl | hs
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hbound s hs)

private lemma prime_child_collar {l u : ℝ} (hl : 1<l) (hlu : l<u) :
    ∃ η : ℝ, 0<η ∧ ∀ B : ℕ, ∀ᶠ M : ℕ in atTop,
      ∃ p : ℕ, p.Prime ∧ B<p ∧ ∀ L : ℕ, M≤L → (L:ℝ)≤(1+η)*M →
        (L:ℝ)/p ∈ Set.Ioo l u := by
  let v := (l+u)/2
  have hlv : l<v := by dsimp [v]; linarith
  have hvu : v<u := by dsimp [v]; linarith
  have hv : 0<v := by linarith
  let η := (u/v-1)/2
  have hη : 0<η := by dsimp [η]; have := (one_lt_div hv).mpr hvu; linarith
  have huv : (1+η)*v < u := by dsimp [η]; field_simp; nlinarith
  refine ⟨η,hη,?_⟩
  intro B
  filter_upwards [actual_prime_in_child_band hl hlv B] with M hM
  obtain ⟨p,hp,hpB,hpv⟩ := hM
  have hp0 : (0:ℝ)<p := by exact_mod_cast hp.pos
  refine ⟨p,hp,hpB,?_⟩
  intro L hML hL
  constructor
  · exact hpv.1.trans_le (div_le_div_of_nonneg_right (by exact_mod_cast hML) hp0.le)
  · calc
      (L:ℝ)/p ≤ ((1+η)*M)/p := (div_le_div_iff_of_pos_right hp0).mpr hL
      _ = (1+η)*((M:ℝ)/p) := by ring
      _ < (1+η)*v := mul_lt_mul_of_pos_left hpv.2 (by linarith)
      _ < u := huv

/-- For every finite child field there is a uniform inward source margin.
The margin, cutoff collar and prime-supply threshold are chosen before the
receiving coefficients. Coefficients may be selected at the current clock
and are held fixed on the collar. Fixed product and logarithmic weights may
be included in those coefficients. -/
theorem eventually_exists_mobiusDivisorFiniteDepth_uniform_prime_collar
    (P I : Finset ℕ) (hP : 1 < P.card) (hprime : ∀ p ∈ P, p.Prime)
    (hI : ∀ r ∈ I, 0 < r) :
    ∃ c η : ℝ, 0<c ∧ 0<η ∧ ∀ B : ℕ, ∀ᶠ M : ℕ in atTop,
      ∀ a : I → ℝ, a ≠ 0 → ∃ p : ℕ, p.Prime ∧ B<p ∧ p ∉ P ∧
        ∀ L : ℕ, M≤L → (L:ℝ)≤(1+η)*M →
          (∑ r : I, a r * mobiusDivisorInterpolatedFibre L (p*(r:ℕ)) P ∅) ≤ -c*‖a‖ := by
  classical
  let E := I → ℝ
  let S : Set E := Metric.sphere 0 1
  have hrect (z : S) := source_negative_rectangle P I hP hprime hI (z:E) (by
    intro hz
    have hn : ‖(z:E)‖=1 := by simpa only [S,Metric.mem_sphere,dist_zero_right] using z.property
    simp [hz] at hn)
  choose U l u c hU hl hlu hc hrect using hrect
  obtain ⟨T,hcover⟩ := (isCompact_sphere (0:E) 1).elim_nhds_subcover'
    (fun z hz => U ⟨z,hz⟩) (fun z hz => hU ⟨z,hz⟩)
  obtain ⟨d,hd,hdc⟩ := positive_finite_lower T c (fun t _ => hc t)
  choose η hη hp using fun t : S => prime_child_collar (hl t) (hlu t)
  obtain ⟨ε,hε,hεη⟩ := positive_finite_lower T η (fun t _ => hη t)
  refine ⟨d,ε,hd,hε,?_⟩
  intro B
  have hall : ∀ᶠ M : ℕ in atTop, ∀ t ∈ T,
      ∃ p : ℕ, p.Prime ∧ max B (P.sup id)<p ∧ ∀ L : ℕ,
        M≤L → (L:ℝ)≤(1+η t)*M → (L:ℝ)/p ∈ Set.Ioo (l t) (u t) :=
    (eventually_all_finset T).mpr (fun t _ => hp t (max B (P.sup id)))
  filter_upwards [hall] with M hM
  intro a ha
  have hn : 0<‖a‖ := norm_pos_iff.mpr ha
  let z : E := ‖a‖⁻¹ • a
  have hz : z ∈ S := by simp [z,S,Metric.mem_sphere,norm_smul,hn.ne']
  obtain ⟨t,ht,hzt⟩ := Set.mem_iUnion₂.mp (hcover hz)
  obtain ⟨p,hp,hpB,hpL⟩ := hM t ht
  refine ⟨p,hp,(le_max_left _ _).trans_lt hpB,?_,?_⟩
  · intro hpP
    have hle : p ≤ P.sup id := Finset.le_sup (f := id) hpP
    exact (not_le_of_gt hpB) (hle.trans (le_max_right _ _))
  · intro L hML hL
    have hL' : (L:ℝ) ≤ (1+η t)*M := hL.trans (by
      have := mul_le_mul_of_nonneg_right (hεη t ht) (Nat.cast_nonneg M)
      nlinarith)
    have hneg := (hrect t z hzt ((L:ℝ)/p) (hpL L hML hL')).trans (neg_le_neg (hdc t ht))
    have he : (∑ r : I, z r * mobiusDivisorInterpolatedFibre L (p*(r:ℕ)) P ∅) =
        ∑ r : I, z r * mobiusDivisorContinuousHead P (((L:ℝ)/p)/(r:ℕ)) := by
      apply sum_congr rfl
      intro r hr
      rw [← mobiusDivisorContinuousHead_div P hprime L (p*(r:ℕ))
        (Nat.mul_pos hp.pos (hI r r.property))]
      push_cast
      rw [div_div]
    rw [← he] at hneg
    have hs : (∑ r : I, z r * mobiusDivisorInterpolatedFibre L (p*(r:ℕ)) P ∅) =
        ‖a‖⁻¹ * (∑ r : I, a r * mobiusDivisorInterpolatedFibre L (p*(r:ℕ)) P ∅) := by
      simp only [z,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,mul_assoc]
    rw [hs] at hneg
    have hh := mul_le_mul_of_nonneg_left hneg hn.le
    have he' (x : ℝ) : ‖a‖*(‖a‖⁻¹*x)=x := by field_simp
    rw [he'] at hh
    exact hh.trans_eq (mul_comm _ _)

end RHTower
