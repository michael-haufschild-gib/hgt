import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.ArithmeticPhaseMixtureEuler
import Mathlib.Analysis.Meromorphic.Order

/-!
# Exact moving zero and pole of the arithmetic mixture

The two principal shifts carry a fourth-order zero and a second-order
pole. Their remaining factor is holomorphic and nonvanishing on a fixed
disc. Clearing the moving pole and applying the identity theorem rules
out a joint holomorphic endpoint germ, even with only real Euler agreement.
-/

open Complex Filter Topology Metric Set
open GaloisForLFunctions.ArithmeticGaugeTheory
open GaloisForLFunctions.ArithmeticCorrelationGeometry
open GaloisForLFunctions.PrimeTorusTheory
open _root_.RHTower
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations

private theorem analyticAt_mixtureFiniteCorrection (t : ℝ) (s : ℂ) :
    AnalyticAt ℂ (mixtureFiniteCorrection t) s := by
  have hp : AnalyticAt ℂ (fun w : ℂ => (2 : ℂ) ^ (-w)) s := by
    have he : AnalyticAt ℂ (fun w : ℂ => Complex.exp (Complex.log 2 * (-w))) s :=
      (analyticAt_const.mul analyticAt_id.neg).cexp
    simpa only [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)] using he
  exact analyticAt_const.mul hp

/-- A fixed spectral disc contains both moving divisor points, with a
holomorphic nonvanishing unit for every sufficiently small nonnegative parameter. -/
theorem exists_mixtureDivisorUnit_germ :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 8 ∧ ∀ t : ℝ, 0 ≤ t → t < r / 8 →
      AnalyticOnNhd ℂ (mixtureDivisorUnit t) (ball 1 r) ∧
      (∀ s ∈ ball (1 : ℂ) r, mixtureDivisorUnit t s ≠ 0) := by
  obtain ⟨R, hR, hE, _⟩ := exists_primeLogRegularPart_germ
  have hZ : ∀ᶠ s : ℂ in 𝓝 1, zetaResidueFactor s ≠ 0 :=
    differentiable_zetaResidueFactor.continuous.continuousAt.eventually_ne
      (by rw [zetaResidueFactor_one]; exact one_ne_zero)
  obtain ⟨S, hS, hSZ⟩ := Metric.mem_nhds_iff.mp hZ
  let r := min (mixtureCharacterWidth / 2) (min (R / 4) (min S (1 / 8)))
  have hr : 0 < r := lt_min (div_pos mixtureCharacterWidth_pos (by norm_num))
    (lt_min (div_pos hR (by norm_num)) (lt_min hS (by norm_num)))
  have hrE : r ≤ R / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hrS : r ≤ S := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hr8 : r ≤ 1 / 8 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hre : r ≤ mixtureCharacterWidth := (min_le_left _ _).trans
    (by linarith only [mixtureCharacterWidth_pos])
  obtain ⟨C, hC, hF, hb, _⟩ := mixtureCharacterLog_properties
  refine ⟨r, hr, hr8, ?_⟩
  intro t ht htR
  have hhalf (s : ℂ) (hs : s ∈ ball (1 : ℂ) r) : 1 / 2 < s.re := by
    have hh := (mixture_ball_in_tube le_rfl hs).1
    linarith only [hh, hr8]
  have hA : AnalyticOnNhd ℂ (mixtureDivisorUnit t) (ball 1 r) := by
    intro s hs
    have hs2 := mixture_small_shift_mem hr hrE ht htR hs 2 (by norm_num)
    have hs4 := mixture_small_shift_mem hr hrE ht htR hs 4 (by norm_num)
    simp only [Nat.cast_ofNat] at hs2 hs4
    have h2 := hE _ hs2
    have h4 := hE _ hs4
    have h2c := h2.comp (f := fun s : ℂ => s + 2 * (t : ℂ))
      (analyticAt_id.add analyticAt_const)
    have h4c := h4.comp (f := fun s : ℂ => s + 4 * (t : ℂ))
      (analyticAt_id.add analyticAt_const)
    have hχ := analyticOnNhd_characterShiftSeries hF hb summable_norm_mixtureSkewCoefficient ht
      s (mixture_ball_in_tube hre hs)
    have hH := analyticOnNhd_mixtureHigherPrimeLog ht s (hhalf s hs)
    have h0 := analyticOnNhd_hullRem (norm_twist_prime 0) s (hhalf s hs)
    have hExp : AnalyticAt ℂ (mixtureRegularExponent t) s :=
      (((((analyticAt_const.mul h2c).add (analyticAt_const.mul h4c)).add (analyticAt_const.mul hχ)).add
        (analyticAt_mixtureFiniteCorrection t s)).add hH).sub h0
    exact (differentiable_zetaResidueFactor.analyticAt s).mul hExp.cexp
  refine ⟨hA, ?_⟩
  intro s hs
  exact mul_ne_zero (hSZ (ball_subset_ball hrS hs)) (Complex.exp_ne_zero _)

private theorem mixture_moving_point_mem {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t)
    (htR : t < r / 8) (n : ℕ) (hn : n ≤ 4) :
    1 - (n : ℂ) * (t : ℂ) ∈ ball (1 : ℂ) r := by
  rw [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_mul,
    Complex.norm_natCast, norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
  have hnt : (n : ℝ) * t ≤ 4 * t := mul_le_mul_of_nonneg_right (by exact_mod_cast hn) ht
  linarith only [hr, htR, hnt]

/-- The arithmetic mixture has an exact zero of order four followed by an
exact pole of order two. Both statements concern the actual Euler continuation. -/
theorem mixture_exact_moving_divisor :
    ∃ T : ℝ, 0 < T ∧ ∀ t : ℝ, 0 < t → t < T →
      AnalyticAt ℂ (mixtureContinuation t) (1 - 2 * (t : ℂ)) ∧
      analyticOrderAt (mixtureContinuation t) (1 - 2 * (t : ℂ)) = 4 ∧
      MeromorphicAt (mixtureContinuation t) (1 - 4 * (t : ℂ)) ∧
      meromorphicOrderAt (mixtureContinuation t) (1 - 4 * (t : ℂ)) = (-2 : WithTop ℤ) := by
  obtain ⟨r, hr, hr8, hg⟩ := exists_mixtureDivisorUnit_germ
  refine ⟨r / 8, by positivity, ?_⟩
  intro t ht htR
  obtain ⟨ha, hne⟩ := hg t ht.le htR
  let z : ℂ := 1 - 2 * (t : ℂ)
  let p : ℂ := 1 - 4 * (t : ℂ)
  have hz : z ∈ ball (1 : ℂ) r := by
    simpa only [Nat.cast_ofNat] using mixture_moving_point_mem hr ht.le htR 2 (by norm_num)
  have hp : p ∈ ball (1 : ℂ) r := by
    simpa only [Nat.cast_ofNat] using mixture_moving_point_mem hr ht.le htR 4 (by norm_num)
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hzp : z - p ≠ 0 := by
    rw [show z - p = 2 * (t : ℂ) by dsimp only [z, p]; ring]
    exact mul_ne_zero (by norm_num) ht0
  have hpz : p - z ≠ 0 := by simpa only [sub_ne_zero] using (sub_ne_zero.mp hzp).symm
  have hdenz : (z - p) ^ 2 ≠ 0 := pow_ne_zero _ hzp
  have hAz := ha z hz
  have hAp := ha p hp
  have hW : AnalyticAt ℂ (mixtureContinuation t) z :=
    (hAz.mul ((analyticAt_id.sub analyticAt_const).pow 4)).div
      ((analyticAt_id.sub analyticAt_const).pow 2) hdenz
  have horder : analyticOrderAt (mixtureContinuation t) z = 4 := by
    refine hW.analyticOrderAt_eq_natCast.mpr
      ⟨fun s : ℂ => mixtureDivisorUnit t s / (s - p) ^ 2,
        hAz.div ((analyticAt_id.sub analyticAt_const).pow 2) hdenz,
        div_ne_zero (hne z hz) hdenz, ?_⟩
    filter_upwards with s
    dsimp only [mixtureContinuation, z, p]
    ring
  have hNum : AnalyticAt ℂ (fun s : ℂ => mixtureDivisorUnit t s * (s - z) ^ 4) p :=
    hAp.mul ((analyticAt_id.sub analyticAt_const).pow 4)
  have hDen : AnalyticAt ℂ (fun s : ℂ => (s - p) ^ 2) p :=
    (analyticAt_id.sub analyticAt_const).pow 2
  have hNum0 : mixtureDivisorUnit t p * (p - z) ^ 4 ≠ 0 :=
    mul_ne_zero (hne p hp) (pow_ne_zero _ hpz)
  have hDenOrder : analyticOrderAt (fun s : ℂ => (s - p) ^ 2) p = 2 := by
    refine hDen.analyticOrderAt_eq_natCast.mpr ⟨fun _ : ℂ => 1, analyticAt_const, one_ne_zero, ?_⟩
    filter_upwards with s
    simp only [mul_one]
  refine ⟨hW, horder, hNum.meromorphicAt.div hDen.meromorphicAt, ?_⟩
  change meromorphicOrderAt ((fun s : ℂ => mixtureDivisorUnit t s * (s - z) ^ 4) /
    (fun s : ℂ => (s - p) ^ 2)) p = _
  rw [meromorphicOrderAt_div hNum.meromorphicAt hDen.meromorphicAt,
    hNum.meromorphicOrderAt_eq, hNum.analyticOrderAt_eq_zero.mpr hNum0,
    hDen.meromorphicOrderAt_eq, hDenOrder]
  norm_num

/-- A genuine joint holomorphic endpoint germ cannot agree even with the
nearby real Euler products: its spectral restriction would remove the moving pole. -/
theorem mixture_no_joint_endpoint_regularization :
    ¬ ∃ U : ℂ × ℂ → ℂ, AnalyticAt ℂ U (0, 1) ∧
      ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ᶠ σ : ℝ in 𝓝[>] 1,
        U ((t : ℂ), (σ : ℂ)) = ((σ : ℂ) - 1) * gaugeFibre (mixturePhaseGauge t) (σ : ℂ) := by
  rintro ⟨U, hU, hagree⟩
  obtain ⟨R, hR, hUa⟩ := hU.exists_ball_analyticOnNhd
  obtain ⟨r, hr, hr8, hA⟩ := exists_mixtureDivisorUnit_germ
  obtain ⟨E, hE, he⟩ := mixtureEuler_factorization
  let a := min r (min (E / 4) R)
  have ha : 0 < a := lt_min hr (lt_min (div_pos hE (by norm_num)) hR)
  have har : a ≤ r := min_le_left _ _
  have haE : a ≤ E / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have haR : a ≤ R := (min_le_right _ _).trans (min_le_right _ _)
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t < a / 8 :=
    nhdsWithin_le_nhds (gt_mem_nhds (by positivity : 0 < a / 8))
  obtain ⟨t, ht, htAgree, htSmall⟩ := (hpos.and (hagree.and hsmall)).exists
  have htR : t < R := by linarith only [htSmall, ha, haR]
  have htr : t < r / 8 := by linarith only [htSmall, har]
  obtain ⟨hAa, hAne⟩ := hA t ht.le htr
  let p : ℂ := 1 - 4 * (t : ℂ)
  let z : ℂ := 1 - 2 * (t : ℂ)
  let F : ℂ → ℂ := fun s => U ((t : ℂ), s) * (s - p) ^ 2
  let G : ℂ → ℂ := fun s => mixtureDivisorUnit t s * (s - z) ^ 4
  have hFa : AnalyticOnNhd ℂ F (ball 1 a) := by
    intro s hs
    have hq : ((t : ℂ), s) ∈ ball ((0 : ℂ), (1 : ℂ)) R := by
      rw [mem_ball, Prod.dist_eq, max_lt_iff]
      refine ⟨?_, ball_subset_ball haR hs⟩
      simpa only [dist_zero_right, norm_real, Real.norm_eq_abs, abs_of_pos ht] using htR
    exact ((hUa _ hq).comp (g := U) (f := fun w : ℂ => ((t : ℂ), w))
      (analyticAt_const.prod analyticAt_id)).mul ((analyticAt_id.sub analyticAt_const).pow 2)
  have hGa : AnalyticOnNhd ℂ G (ball 1 a) := fun s hs =>
    (hAa s (ball_subset_ball har hs)).mul ((analyticAt_id.sub analyticAt_const).pow 4)
  have hmap : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] 1) (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa only [Complex.ofReal_one] using
        (Complex.continuous_ofReal.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      exact fun h => (ne_of_gt hσ) (Complex.ofReal_eq_one.mp h)
  have hball : ∀ᶠ σ : ℝ in 𝓝[>] 1, (σ : ℂ) ∈ ball (1 : ℂ) a :=
    (hmap.mono_right nhdsWithin_le_nhds).eventually (isOpen_ball.mem_nhds (mem_ball_self ha))
  have hreal : ∀ᶠ σ : ℝ in 𝓝[>] 1, F (σ : ℂ) = G (σ : ℂ) := by
    filter_upwards [htAgree, self_mem_nhdsWithin, hball] with σ hσ hσ1 hσa
    change 1 < σ at hσ1
    have hs : 1 < (σ : ℂ).re := hσ1
    have hEuler := he t ht.le (σ : ℂ)
      (by simpa only [Nat.cast_ofNat] using mixture_small_shift_mem ha haE ht.le htSmall hσa 2 (by norm_num))
      (by simpa only [Nat.cast_ofNat] using mixture_small_shift_mem ha haE ht.le htSmall hσa 4 (by norm_num)) hs
    have hp0 : (σ : ℂ) - p ≠ 0 := by
      have hh : 0 < ((σ : ℂ) - p).re := by
        dsimp only [p]
        norm_num
        linarith only [hσ1, ht]
      exact fun h => (ne_of_gt hh) (by rw [h]; rfl)
    dsimp only [F, G]
    rw [hσ, hEuler, mixtureContinuation, div_mul_cancel₀ _ (pow_ne_zero 2 hp0)]
  have hid := hFa.eqOn_of_preconnected_of_frequently_eq hGa (convex_ball (1 : ℂ) a).isPreconnected
    (mem_ball_self ha) (hmap.frequently hreal.frequently)
  have hp : p ∈ ball (1 : ℂ) a := by
    simpa only [Nat.cast_ofNat] using mixture_moving_point_mem ha ht.le htSmall 4 (by norm_num)
  have heq := hid hp
  change U ((t : ℂ), p) * (p - p) ^ 2 = mixtureDivisorUnit t p * (p - z) ^ 4 at heq
  rw [sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] at heq
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hpz : p - z ≠ 0 := by
    rw [show p - z = -2 * (t : ℂ) by dsimp only [p, z]; ring]
    exact mul_ne_zero (by norm_num) ht0
  exact (mul_ne_zero (hAne p (ball_subset_ball har hp)) (pow_ne_zero 4 hpz)) heq.symm

#print axioms mixture_exact_moving_divisor
#print axioms mixture_no_joint_endpoint_regularization
end GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations
