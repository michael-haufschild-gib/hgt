import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheDenjoyCarlemanProfiles
import GaloisForLFunctions.HTGeometry.UniformCauchyLimit
import GaloisForLFunctions.HTGeometry.UniformIteratedDerivLimit

/-!
# Super-Gevrey Critical Overlap Growth via Steklov Denjoy–Carleman Profiles

Every Gevrey profile `dcProfile r` (`r` odd, Gevrey class `1 + 1/r`) yields an RH-equivalent
atomic overlap window `(log log N)^α` for `α > 1 + 1/r`, requiring the profile parameter `r` to
depend on `α` and leaving every fixed profile strictly above some power `(log log N)^{1+ε}`.

This module constructs **one single explicit smooth compactly supported profile**
`steklovDCProfile : ℝ → ℝ` via an infinite sequence of Steklov moving averages with summable radii
`a_m = 1 / (4 (m + 3) (log(m + 3))²)` (`∑ a_m < 1/2`), starting from `dilate 2 (dcProfile 1)`, and
proves:

1. **Smoothness, compact support, and unit mass** (`contDiff_steklovDCProfile`,
   `steklovDCProfile_vanishesOff`, `integral_steklovDCProfile`):
   `steklovDCProfile ∈ C_c^∞([-1, 1])` and `∫ x, steklovDCProfile x = 1`.
2. **Logarithmic Denjoy–Carleman `L¹` derivative bound**
   (`integral_abs_iteratedDeriv_steklovDCProfile_le`):
   `∫ t, |iteratedDeriv q steklovDCProfile t| ≤ A * 12^q * q! * (log(q + 3))^{2q}` for all `q`,
   strictly below every Gevrey class `(q!)^{1+ε}` (`ε > 0`) while remaining non-quasianalytic
   (`∑ 1 / ((m + 3) (log(m + 3))²) < ∞`).
3. **Euler–Maclaurin synthesis in the logarithmic Denjoy–Carleman class**
   (`riemannHypothesis_iff_atomicFamilies_nonneg_of_superGevrey`,
   `riemannHypothesis_iff_steklovDCProfile_nonneg_superGevrey`):
   for **every** `β > 2`, eventual nonnegativity of `weilQuad` on the atomic families of the single
   fixed profile `steklovDCProfile` at overlap ratio
   `c_N = (log log N) (log log log N)^β` (width `c_N / N`) is **equivalent to `RiemannHypothesis`**,
   and `c_N = o((log log N)^{1+ε})` for every `ε > 0` (`superGevreyRatio_isLittleO_loglog_rpow`).
-/

noncomputable section

open MeasureTheory Filter Topology RHTower RHTower.DQPT
open scoped Real ContDiff Convolution

namespace GaloisForLFunctions.TransMetzlerWeilPositivity

open ArithmeticElectrostatics
open SpacingScaleHarmonicAnalysis

/-! ### 1. Steklov moving-average operator on `ℝ` -/

/-- Symmetric Steklov moving average `(S_a f)(x) = (2a)⁻¹ ∫_{-a}^a f(x + t) dt`. -/
def steklovAvg (a : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (2 * a)⁻¹ * ∫ t in (-a)..a, f (x + t)

private theorem steklovAvg_eq_primitive_sub {f : ℝ → ℝ} (hf : Continuous f) (a x : ℝ) :
    steklovAvg a f x = (2 * a)⁻¹ * ((∫ u in (0 : ℝ)..(x + a), f u) - ∫ u in (0 : ℝ)..(x - a), f u) := by
  unfold steklovAvg
  congr 1
  have hcomp : (∫ t in (-a)..a, f (x + t)) = ∫ u in (x - a)..(x + a), f u := by
    have h := intervalIntegral.integral_comp_add_left f x (a := -a) (b := a)
    rwa [show x + -a = x - a by ring] at h
  rw [hcomp]
  have hadj := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hf.intervalIntegrable 0 (x - a)) (hf.intervalIntegrable (x - a) (x + a))
  linarith

theorem hasDerivAt_steklovAvg {f : ℝ → ℝ} (hf : Continuous f) {a : ℝ} (ha : 0 < a) (x : ℝ) :
    HasDerivAt (steklovAvg a f) ((2 * a)⁻¹ * (f (x + a) - f (x - a))) x := by
  set F : ℝ → ℝ := fun y => ∫ u in (0 : ℝ)..y, f u
  have hFd : ∀ y : ℝ, HasDerivAt F (f y) y := fun y =>
    intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 y)
      (hf.stronglyMeasurableAtFilter volume (𝓝 y)) hf.continuousAt
  have heq : steklovAvg a f = fun z => (2 * a)⁻¹ * (F (z + a) - F (z - a)) :=
    funext fun z => steklovAvg_eq_primitive_sub hf a z
  rw [heq]
  have hd1 : HasDerivAt (fun z => F (z + a)) (f (x + a)) x := by
    simpa only [Function.comp_def, id_eq, mul_one] using
      (hFd (x + a)).comp x ((hasDerivAt_id x).add_const a)
  have hd2 : HasDerivAt (fun z => F (z - a)) (f (x - a)) x := by
    simpa only [Function.comp_def, id_eq, mul_one] using
      (hFd (x - a)).comp x ((hasDerivAt_id x).sub_const a)
  exact (hd1.sub hd2).const_mul (2 * a)⁻¹

theorem deriv_steklovAvg_eq_sub {f : ℝ → ℝ} (hf : Continuous f) {a : ℝ} (ha : 0 < a) (x : ℝ) :
    deriv (steklovAvg a f) x = (2 * a)⁻¹ * (f (x + a) - f (x - a)) :=
  (hasDerivAt_steklovAvg hf ha x).deriv

theorem contDiff_steklovAvg {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {a : ℝ} (ha : 0 < a) :
    ContDiff ℝ ∞ (steklovAvg a f) := by
  have hcont : Continuous (steklovAvg a f) :=
    continuous_iff_continuousAt.mpr fun x => (hasDerivAt_steklovAvg hf.continuous ha x).continuousAt
  have hsub : ContDiff ℝ ∞ (fun x => (2 * a)⁻¹ * (f (x + a) - f (x - a))) :=
    contDiff_const.mul ((hf.comp (contDiff_id.add contDiff_const)).sub
      (hf.comp (contDiff_id.sub contDiff_const)))
  rw [contDiff_infty]
  intro k
  rcases k with _ | k
  · exact contDiff_zero.mpr hcont
  · have hcast : ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 := by push_cast; ring
    rw [hcast, contDiff_succ_iff_deriv]
    refine ⟨fun x => (hasDerivAt_steklovAvg hf.continuous ha x).differentiableAt,
      fun h => absurd h (by simp), ?_⟩
    rw [show deriv (steklovAvg a f) = fun x => (2 * a)⁻¹ * (f (x + a) - f (x - a)) from
      funext (deriv_steklovAvg_eq_sub hf.continuous ha)]
    exact hsub.of_le (natCast_le_infty k)

theorem deriv_steklovAvg {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {a : ℝ} (ha : 0 < a) :
    deriv (steklovAvg a f) = steklovAvg a (deriv f) := by
  funext x
  rw [deriv_steklovAvg_eq_sub hf.continuous ha]
  unfold steklovAvg
  congr 1
  have hdf : Differentiable ℝ f := hf.differentiable (by simp)
  have hdc : Continuous (deriv f) := hf.continuous_deriv (natCast_le_infty 1)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t => f (x + t)) (f' := fun t => deriv f (x + t)) (a := -a) (b := a)
    (fun t _ => by
      simpa only [Function.comp_def, id_eq, mul_one] using
        ((hdf (x + t)).hasDerivAt.comp t ((hasDerivAt_id t).const_add x)))
    ((hdc.comp (continuous_const.add continuous_id)).intervalIntegrable (-a) a)
  rw [hftc, show x + -a = x - a by ring]

theorem iteratedDeriv_steklovAvg {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {a : ℝ} (ha : 0 < a) (q : ℕ) :
    iteratedDeriv q (steklovAvg a f) = steklovAvg a (iteratedDeriv q f) := by
  induction q with
  | zero => simp only [iteratedDeriv_zero]
  | succ q ih =>
    have hfq : ContDiff ℝ ∞ (iteratedDeriv q f) := by
      rw [iteratedDeriv_eq_iterate]
      exact hf.iterate_deriv q
    rw [iteratedDeriv_succ, ih, deriv_steklovAvg hfq ha, ← iteratedDeriv_succ]

theorem abs_steklovAvg_le {f : ℝ → ℝ} {B a : ℝ} (ha : 0 < a)
    (hB : ∀ x, |f x| ≤ B) (x : ℝ) :
    |steklovAvg a f x| ≤ B := by
  unfold steklovAvg
  rw [abs_mul, abs_of_pos (inv_pos.mpr (by positivity : 0 < 2 * a)), ← Real.norm_eq_abs]
  have hint : ‖∫ t in (-a)..a, f (x + t)‖ ≤ B * |a - (-a)| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun t _ => by
      rw [Real.norm_eq_abs]; exact hB (x + t)
  rw [show a - (-a) = 2 * a by ring, abs_of_pos (by positivity : 0 < 2 * a)] at hint
  calc (2 * a)⁻¹ * ‖∫ t in (-a)..a, f (x + t)‖
      ≤ (2 * a)⁻¹ * (B * (2 * a)) := mul_le_mul_of_nonneg_left hint (by positivity)
    _ = B := by field_simp [ha.ne']

theorem abs_deriv_steklovAvg_le {f : ℝ → ℝ} (hf : Continuous f) {B a : ℝ} (ha : 0 < a)
    (hB : ∀ x, |f x| ≤ B) (x : ℝ) :
    |deriv (steklovAvg a f) x| ≤ a⁻¹ * B := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  rw [deriv_steklovAvg_eq_sub hf ha, abs_mul, abs_of_pos (inv_pos.mpr (by positivity : 0 < 2 * a))]
  have hdiff : |f (x + a) - f (x - a)| ≤ 2 * B :=
    (abs_sub _ _).trans (by linarith [hB (x + a), hB (x - a)])
  calc (2 * a)⁻¹ * |f (x + a) - f (x - a)|
      ≤ (2 * a)⁻¹ * (2 * B) := mul_le_mul_of_nonneg_left hdiff (by positivity)
    _ = a⁻¹ * B := by field_simp [ha.ne']

theorem abs_steklovAvg_sub_self_le {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {M a : ℝ} (ha : 0 < a)
    (hM : ∀ y, |deriv f y| ≤ M) (x : ℝ) :
    |steklovAvg a f x - f x| ≤ M * a := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hconst : (2 * a)⁻¹ * (∫ _t in (-a)..a, f x) = f x := by
    rw [intervalIntegral.integral_const, smul_eq_mul, show a - (-a) = 2 * a by ring]
    field_simp [ha.ne']
  have heq : steklovAvg a f x - f x = (2 * a)⁻¹ * ∫ t in (-a)..a, (f (x + t) - f x) := by
    rw [intervalIntegral.integral_sub (f := fun t : ℝ => f (x + t))
      (g := fun _ : ℝ => f x) (μ := volume)
      ((hf.continuous.comp (continuous_const.add continuous_id)).intervalIntegrable (-a) a)
      intervalIntegrable_const, mul_sub, hconst]
    rfl
  rw [heq, abs_mul, abs_of_pos (inv_pos.mpr (by positivity : 0 < 2 * a)), ← Real.norm_eq_abs]
  have hdf : Differentiable ℝ f := hf.differentiable (by simp)
  have hmv : ∀ t ∈ Set.uIoc (-a) a, ‖f (x + t) - f x‖ ≤ M * a := by
    intro t ht
    rw [Set.uIoc_of_le (by linarith : -a ≤ a)] at ht
    have ht_abs : |t| ≤ a := abs_le.mpr ⟨ht.1.le, ht.2⟩
    have hnorm := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (s := Set.univ)
      (fun y _ => hdf y) (fun y _ => by rw [Real.norm_eq_abs]; exact hM y)
      convex_univ (Set.mem_univ x) (Set.mem_univ (x + t))
    rw [show x + t - x = t by ring, Real.norm_eq_abs] at hnorm
    exact hnorm.trans (mul_le_mul_of_nonneg_left ht_abs hM0)
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hmv
  rw [show a - (-a) = 2 * a by ring, abs_of_pos (by positivity : 0 < 2 * a)] at hint
  calc (2 * a)⁻¹ * ‖∫ t in (-a)..a, (f (x + t) - f x)‖
      ≤ (2 * a)⁻¹ * (M * a * (2 * a)) := mul_le_mul_of_nonneg_left hint (by positivity)
    _ = M * a := by field_simp [ha.ne']

theorem supportedIn_steklovAvg {f : ℝ → ℝ} {R a : ℝ} (ha : 0 < a) (hsupp : SupportedIn R f) :
    SupportedIn (R + a) (steklovAvg a f) := by
  intro x hx
  unfold steklovAvg
  have hzero : ∀ t ∈ Set.uIcc (-a) a, f (x + t) = 0 := by
    intro t ht
    rw [Set.uIcc_of_le (by linarith : -a ≤ a)] at ht
    have ht_abs : |t| ≤ a := abs_le.mpr ht
    have hxt : R < |x + t| := by
      have htri := abs_sub_abs_le_abs_sub x (-t)
      rw [sub_neg_eq_add, abs_neg] at htri
      linarith
    exact hsupp (x + t) hxt
  rw [intervalIntegral.integral_congr hzero, intervalIntegral.integral_zero, mul_zero]

private theorem integral_eq_intervalIntegral_of_supportedIn {g : ℝ → ℝ} {R L : ℝ}
    (hsupp : SupportedIn R g) (hR : 0 ≤ R) (hRL : R < L) :
    (∫ x, g x) = ∫ x in (-L)..L, g x := by
  have hL0 : 0 < L := lt_of_le_of_lt hR hRL
  rw [intervalIntegral.integral_of_le (by linarith : -L ≤ L),
    ← setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro x hx
  simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hx
  refine hsupp x ?_
  rcases hx with hx | hx
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

theorem integral_steklovAvg {f : ℝ → ℝ} {R a : ℝ} (hf : Continuous f) (hsupp : SupportedIn R f)
    (hR : 0 ≤ R) (ha : 0 < a) :
    (∫ x, steklovAvg a f x) = ∫ x, f x := by
  set L := R + a + 1
  have hcont_avg : Continuous (steklovAvg a f) :=
    continuous_iff_continuousAt.mpr fun x => (hasDerivAt_steklovAvg hf ha x).continuousAt
  have hsupp_avg : SupportedIn (R + a) (steklovAvg a f) := supportedIn_steklovAvg ha hsupp
  rw [integral_eq_intervalIntegral_of_supportedIn (L := L) hsupp_avg
      (by linarith) (by dsimp only [L]; linarith),
    integral_eq_intervalIntegral_of_supportedIn hsupp hR (show R < R + 1 by linarith)]
  set F : ℝ → ℝ := fun y => ∫ u in (0 : ℝ)..y, f u
  have hFc : Continuous F :=
    continuous_iff_continuousAt.mpr fun y =>
      (intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 y)
        (hf.stronglyMeasurableAtFilter volume (𝓝 y)) hf.continuousAt).continuousAt
  have heq : ∀ x : ℝ, steklovAvg a f x = (2 * a)⁻¹ * (F (x + a) - F (x - a)) :=
    fun x => steklovAvg_eq_primitive_sub hf a x
  simp_rw [heq]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub (f := fun x : ℝ => F (x + a))
      (g := fun x : ℝ => F (x - a)) (μ := volume)
      ((hFc.comp (continuous_id.add continuous_const)).intervalIntegrable (-L) L)
      ((hFc.comp (continuous_id.sub continuous_const)).intervalIntegrable (-L) L),
    intervalIntegral.integral_comp_add_right F a,
    intervalIntegral.integral_comp_sub_right F a]
  -- Split both `F` integrals via `-L - a`, `-L + a`, `L - a`, `L + a`
  have hsplit1 : (∫ y in (-L + a)..(L + a), F y) =
      (∫ y in (-L + a)..(L - a), F y) + ∫ y in (L - a)..(L + a), F y :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hFc.intervalIntegrable (-L + a) (L - a))
      (hFc.intervalIntegrable (L - a) (L + a))).symm
  have hsplit2 : (∫ y in (-L - a)..(L - a), F y) =
      (∫ y in (-L - a)..(-L + a), F y) + ∫ y in (-L + a)..(L - a), F y :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hFc.intervalIntegrable (-L - a) (-L + a))
      (hFc.intervalIntegrable (-L + a) (L - a))).symm
  rw [hsplit1, hsplit2]
  have hF_right : ∀ y ∈ Set.uIcc (L - a) (L + a), F y = F (R + 1) := by
    intro y hy
    rw [Set.uIcc_of_le (by linarith : L - a ≤ L + a)] at hy
    have hyR : R + 1 ≤ y := by dsimp [L] at hy; linarith [hy.1]
    have hadj := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hf.intervalIntegrable 0 (R + 1)) (hf.intervalIntegrable (R + 1) y)
    have htail : (∫ u in (R + 1)..y, f u) = 0 := by
      have hz : ∀ u ∈ Set.uIcc (R + 1) y, f u = 0 := by
        intro u hu
        rw [Set.uIcc_of_le hyR] at hu
        exact hsupp u (by
          rw [abs_of_pos (by linarith only [hu.1, hR])]
          linarith only [hu.1])
      rw [intervalIntegral.integral_congr hz, intervalIntegral.integral_zero]
    dsimp only [F]
    linarith only [hadj, htail]
  have hF_left : ∀ y ∈ Set.uIcc (-L - a) (-L + a), F y = F (-(R + 1)) := by
    intro y hy
    rw [Set.uIcc_of_le (by linarith : -L - a ≤ -L + a)] at hy
    have hyR : y ≤ -(R + 1) := by dsimp [L] at hy; linarith [hy.2]
    have hadj := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hf.intervalIntegrable 0 (-(R + 1))) (hf.intervalIntegrable (-(R + 1)) y)
    have htail : (∫ u in (-(R + 1))..y, f u) = 0 := by
      have hz : ∀ u ∈ Set.uIcc (-(R + 1)) y, f u = 0 := by
        intro u hu
        rw [Set.uIcc_of_ge hyR] at hu
        exact hsupp u (by
          rw [abs_of_neg (by linarith only [hu.2, hR])]
          linarith only [hu.2])
      rw [intervalIntegral.integral_congr hz, intervalIntegral.integral_zero]
    dsimp only [F]
    linarith only [hadj, htail]
  rw [intervalIntegral.integral_congr hF_right, intervalIntegral.integral_const, smul_eq_mul,
    intervalIntegral.integral_congr hF_left, intervalIntegral.integral_const, smul_eq_mul]
  have hF_diff : F (R + 1) - F (-(R + 1)) = ∫ x in (-(R + 1))..(R + 1), f x := by
    dsimp only [F]
    have hadj := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hf.intervalIntegrable (-(R + 1)) 0) (hf.intervalIntegrable 0 (R + 1))
    rw [intervalIntegral.integral_symm 0 (-(R + 1))] at hadj
    linarith only [hadj]
  rw [show L + a - (L - a) = 2 * a by ring, show -L + a - (-L - a) = 2 * a by ring]
  have halg : (2 * a)⁻¹ * ((∫ y in (-L + a)..(L - a), F y) + 2 * a * F (R + 1) -
      (2 * a * F (-(R + 1)) + ∫ y in (-L + a)..(L - a), F y)) = F (R + 1) - F (-(R + 1)) := by
    field_simp [ha.ne']
    ring
  rw [halg, hF_diff]

/-! ### 2. Summable radii `a_m = 1 / (4 (m + 3) (log(m + 3))²)` and logarithmic weight -/

/-- Steklov radius at stage `m`: `1 / (4 (m + 3) (log(m + 3))²)`. -/
def steklovRadius (m : ℕ) : ℝ :=
  1 / (4 * ((m : ℝ) + 3) * Real.log ((m : ℝ) + 3) ^ 2)

/-- Telescoping majorant `1 / (4 log(m + 2))`. -/
private def steklovTel (m : ℕ) : ℝ :=
  1 / (4 * Real.log ((m : ℝ) + 2))

theorem steklovRadius_pos (m : ℕ) : 0 < steklovRadius m := by
  unfold steklovRadius
  have hm3 : (1 : ℝ) < (m : ℝ) + 3 := by linarith only [Nat.cast_nonneg (α := ℝ) m]
  have hlog : 0 < Real.log ((m : ℝ) + 3) := Real.log_pos hm3
  positivity

private theorem steklovRadius_le_tel_sub (m : ℕ) :
    steklovRadius m ≤ steklovTel m - steklovTel (m + 1) := by
  have hm2 : (0 : ℝ) < (m : ℝ) + 2 := by positivity
  have hm3 : (0 : ℝ) < (m : ℝ) + 3 := by positivity
  have hl2 : 0 < Real.log ((m : ℝ) + 2) := Real.log_pos (by linarith)
  have hl3 : 0 < Real.log ((m : ℝ) + 3) := Real.log_pos (by linarith)
  have hl23 : Real.log ((m : ℝ) + 2) ≤ Real.log ((m : ℝ) + 3) :=
    Real.log_le_log hm2 (by linarith)
  have hlog_lb : 1 / ((m : ℝ) + 3) ≤ Real.log ((m : ℝ) + 3) - Real.log ((m : ℝ) + 2) := by
    have h := Real.one_sub_inv_le_log_of_pos (div_pos hm3 hm2)
    rw [inv_div, Real.log_div hm3.ne' hm2.ne'] at h
    have h1 : 1 - ((m : ℝ) + 2) / ((m : ℝ) + 3) = 1 / ((m : ℝ) + 3) := by
      field_simp [hm3.ne']; ring
    rwa [h1] at h
  have htel : steklovTel m - steklovTel (m + 1) =
      (Real.log ((m : ℝ) + 3) - Real.log ((m : ℝ) + 2)) /
        (4 * Real.log ((m : ℝ) + 2) * Real.log ((m : ℝ) + 3)) := by
    unfold steklovTel
    push_cast
    rw [show (m : ℝ) + 1 + 2 = (m : ℝ) + 3 by ring]
    field_simp [hl2.ne', hl3.ne']
  rw [htel, steklovRadius]
  have hnum : (1 : ℝ) = (1 / ((m : ℝ) + 3)) * ((m : ℝ) + 3) := by field_simp [hm3.ne']
  calc 1 / (4 * ((m : ℝ) + 3) * Real.log ((m : ℝ) + 3) ^ 2)
      = (1 / ((m : ℝ) + 3)) / (4 * Real.log ((m : ℝ) + 3) ^ 2) := by
          field_simp [hm3.ne', hl3.ne']
    _ ≤ (Real.log ((m : ℝ) + 3) - Real.log ((m : ℝ) + 2)) /
          (4 * Real.log ((m : ℝ) + 3) ^ 2) :=
        div_le_div_of_nonneg_right hlog_lb (by positivity)
    _ ≤ (Real.log ((m : ℝ) + 3) - Real.log ((m : ℝ) + 2)) /
          (4 * Real.log ((m : ℝ) + 2) * Real.log ((m : ℝ) + 3)) := by
        refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
        rw [sq, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hl23 (by norm_num)) hl3.le

theorem sum_Ico_steklovRadius_le {K M : ℕ} (hKM : K ≤ M) :
    ∑ m ∈ Finset.Ico K M, steklovRadius m ≤ 1 / (4 * Real.log ((K : ℝ) + 2)) := by
  calc ∑ m ∈ Finset.Ico K M, steklovRadius m
      ≤ ∑ m ∈ Finset.Ico K M, (steklovTel m - steklovTel (m + 1)) :=
        Finset.sum_le_sum fun m _ => steklovRadius_le_tel_sub m
    _ = steklovTel K - steklovTel M := by
        calc ∑ m ∈ Finset.Ico K M, (steklovTel m - steklovTel (m + 1)) =
            ∑ m ∈ Finset.Ico K M, ((-steklovTel (m + 1)) - (-steklovTel m)) := by
              refine Finset.sum_congr rfl fun m _ => ?_
              ring
          _ = -steklovTel M - (-steklovTel K) :=
            Finset.sum_Ico_sub (fun m => -steklovTel m) hKM
          _ = steklovTel K - steklovTel M := by ring
    _ ≤ steklovTel K := by
        have hpos : 0 ≤ steklovTel M := by
          unfold steklovTel
          have : 0 < Real.log ((M : ℝ) + 2) :=
            Real.log_pos (by linarith only [Nat.cast_nonneg (α := ℝ) M])
          positivity
        linarith
    _ = 1 / (4 * Real.log ((K : ℝ) + 2)) := rfl

theorem sum_range_steklovRadius_le_half (M : ℕ) :
    ∑ m ∈ Finset.range M, steklovRadius m ≤ 1 / 2 := by
  rw [← Nat.Ico_zero_eq_range]
  refine (sum_Ico_steklovRadius_le (Nat.zero_le M)).trans ?_
  simp only [Nat.cast_zero, zero_add]
  have hl2 : (1 / 2 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- Logarithmic Denjoy–Carleman weight `W_q = q! (log(q + 3))^{2q}`. -/
def dcLogWeight (q : ℕ) : ℝ :=
  (q.factorial : ℝ) * Real.log ((q : ℝ) + 3) ^ (2 * q)

theorem dcLogWeight_zero : dcLogWeight 0 = 1 := by
  simp [dcLogWeight]

theorem dcLogWeight_pos (q : ℕ) : 0 < dcLogWeight q := by
  unfold dcLogWeight
  have hfac : (0 : ℝ) < q.factorial := by exact_mod_cast Nat.factorial_pos q
  have hlog : 0 < Real.log ((q : ℝ) + 3) :=
    Real.log_pos (by linarith only [Nat.cast_nonneg (α := ℝ) q])
  positivity

private theorem one_le_log_add_three (q : ℕ) : 1 ≤ Real.log ((q : ℝ) + 3) := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  have he := Real.exp_one_lt_d9
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  linarith

theorem dcLogWeight_mono {a b : ℕ} (hab : a ≤ b) : dcLogWeight a ≤ dcLogWeight b := by
  unfold dcLogWeight
  have hfac : (a.factorial : ℝ) ≤ b.factorial := by exact_mod_cast Nat.factorial_le hab
  have hlog_le : Real.log ((a : ℝ) + 3) ≤ Real.log ((b : ℝ) + 3) :=
    Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right hab 3)
  have hl1 := one_le_log_add_three a
  have hpow1 : Real.log ((a : ℝ) + 3) ^ (2 * a) ≤ Real.log ((b : ℝ) + 3) ^ (2 * a) :=
    pow_le_pow_left₀ (by linarith) hlog_le (2 * a)
  have hpow2 : Real.log ((b : ℝ) + 3) ^ (2 * a) ≤ Real.log ((b : ℝ) + 3) ^ (2 * b) :=
    pow_le_pow_right₀ (hl1.trans hlog_le) (by omega)
  exact mul_le_mul hfac (hpow1.trans hpow2) (by positivity) (by positivity)

theorem dcLogWeight_mul_le {i l : ℕ} (hl : l ≤ i) :
    dcLogWeight l * dcLogWeight (i - l) ≤ dcLogWeight i := by
  unfold dcLogWeight
  have hfac : (l.factorial : ℝ) * ((i - l).factorial : ℝ) ≤ i.factorial := by
    exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos i) (Nat.factorial_mul_factorial_dvd_factorial hl)
  have hl_log : Real.log ((l : ℝ) + 3) ≤ Real.log ((i : ℝ) + 3) :=
    Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right hl 3)
  have hil_log : Real.log (((i - l : ℕ) : ℝ) + 3) ≤ Real.log ((i : ℝ) + 3) :=
    Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right (Nat.sub_le i l) 3)
  have hp1 : Real.log ((l : ℝ) + 3) ^ (2 * l) ≤ Real.log ((i : ℝ) + 3) ^ (2 * l) :=
    pow_le_pow_left₀ (le_trans zero_le_one (one_le_log_add_three l)) hl_log _
  have hp2 : Real.log (((i - l : ℕ) : ℝ) + 3) ^ (2 * (i - l)) ≤
      Real.log ((i : ℝ) + 3) ^ (2 * (i - l)) :=
    pow_le_pow_left₀ (le_trans zero_le_one (one_le_log_add_three (i - l))) hil_log _
  have hp_mul : Real.log ((l : ℝ) + 3) ^ (2 * l) *
      Real.log (((i - l : ℕ) : ℝ) + 3) ^ (2 * (i - l)) ≤ Real.log ((i : ℝ) + 3) ^ (2 * i) := by
    calc Real.log ((l : ℝ) + 3) ^ (2 * l) * Real.log (((i - l : ℕ) : ℝ) + 3) ^ (2 * (i - l))
        ≤ Real.log ((i : ℝ) + 3) ^ (2 * l) * Real.log ((i : ℝ) + 3) ^ (2 * (i - l)) :=
          mul_le_mul hp1 hp2 (pow_nonneg (le_trans zero_le_one (one_le_log_add_three _)) _)
            (pow_nonneg (le_trans zero_le_one (one_le_log_add_three i)) _)
      _ = Real.log ((i : ℝ) + 3) ^ (2 * i) := by
          rw [← pow_add, show 2 * l + 2 * (i - l) = 2 * i by omega]
  calc ((l.factorial : ℝ) * Real.log ((l : ℝ) + 3) ^ (2 * l)) *
        (((i - l).factorial : ℝ) * Real.log (((i - l : ℕ) : ℝ) + 3) ^ (2 * (i - l)))
      = ((l.factorial : ℝ) * ((i - l).factorial : ℝ)) *
          (Real.log ((l : ℝ) + 3) ^ (2 * l) *
            Real.log (((i - l : ℕ) : ℝ) + 3) ^ (2 * (i - l))) := by ring
    _ ≤ (i.factorial : ℝ) * Real.log ((i : ℝ) + 3) ^ (2 * i) :=
        mul_le_mul hfac hp_mul
          (mul_nonneg (pow_nonneg (le_trans zero_le_one (one_le_log_add_three l)) _)
            (pow_nonneg (le_trans zero_le_one (one_le_log_add_three (i - l))) _))
          (Nat.cast_nonneg _)

theorem dcLogWeight_le_pow (p : ℕ) :
    dcLogWeight p ≤ ((p : ℝ) * Real.log ((p : ℝ) + 3) ^ 2) ^ p := by
  unfold dcLogWeight
  have hfac : (p.factorial : ℝ) ≤ (p : ℝ) ^ p := by exact_mod_cast Nat.factorial_le_pow p
  have hlog : Real.log ((p : ℝ) + 3) ^ (2 * p) = (Real.log ((p : ℝ) + 3) ^ 2) ^ p := pow_mul _ 2 p
  rw [mul_pow, hlog]
  exact mul_le_mul_of_nonneg_right hfac (by positivity)

theorem prod_inv_steklovRadius_le (q : ℕ) :
    ∏ j ∈ Finset.range q, (steklovRadius j)⁻¹ ≤ 12 ^ q * dcLogWeight q := by
  have hprod_fac : ∏ j ∈ Finset.range q, ((j : ℝ) + 1) = (q.factorial : ℝ) := by
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Finset.prod_range_succ, ih, Nat.factorial_succ, Nat.cast_mul]
      push_cast; ring
  calc ∏ j ∈ Finset.range q, (steklovRadius j)⁻¹
      = ∏ j ∈ Finset.range q, (4 * ((j : ℝ) + 3) * Real.log ((j : ℝ) + 3) ^ 2) := by
          refine Finset.prod_congr rfl fun j _ => ?_
          unfold steklovRadius
          rw [one_div, inv_inv]
    _ ≤ ∏ j ∈ Finset.range q, (12 * ((j : ℝ) + 1) * Real.log ((q : ℝ) + 3) ^ 2) := by
          refine Finset.prod_le_prod (fun j _ => by
            have := one_le_log_add_three j; positivity) fun j hj => ?_
          have hjq : j ≤ q := Nat.le_of_lt (Finset.mem_range.mp hj)
          have hlin : 4 * ((j : ℝ) + 3) ≤ 12 * ((j : ℝ) + 1) := by
            have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
            linarith
          have hlog : Real.log ((j : ℝ) + 3) ^ 2 ≤ Real.log ((q : ℝ) + 3) ^ 2 :=
            pow_le_pow_left₀ (le_trans zero_le_one (one_le_log_add_three j))
              (Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right hjq 3)) 2
          exact mul_le_mul hlin hlog (by positivity) (by positivity)
    _ = 12 ^ q * (∏ j ∈ Finset.range q, ((j : ℝ) + 1)) * Real.log ((q : ℝ) + 3) ^ (2 * q) := by
          rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
            Finset.prod_const, Finset.card_range, ← pow_mul]
    _ = 12 ^ q * dcLogWeight q := by
          rw [hprod_fac]; unfold dcLogWeight; ring

/-! ### 3. Construction and `L¹` derivative bounds of `steklovDCProfile` -/

/-- Smooth base bump `dilate 2 (dcProfile 1)`, supported in `[-1/2, 1/2]` with unit integral. -/
def steklovBase : ℝ → ℝ :=
  dilate 2 (dcProfile 1)

/-- Explicit supremum bound on `steklovBase`. -/
def steklovBaseSup : ℝ :=
  2 * (∫ y, dcBump 1 y)⁻¹

theorem steklovBaseSup_pos : 0 < steklovBaseSup := by
  unfold steklovBaseSup
  exact mul_pos two_pos (inv_pos.mpr (integral_dcBump_pos odd_one))

theorem contDiff_steklovBase : ContDiff ℝ ∞ steklovBase :=
  contDiff_dilate_smooth (contDiff_dcProfile 1) 2

theorem supportedIn_steklovBase : SupportedIn (1 / 2) steklovBase :=
  fun x hx => dilate_vanishes (dcProfile_vanishesOff odd_one) two_pos hx

theorem integral_steklovBase : ∫ x, steklovBase x = 1 := by
  unfold steklovBase dilate
  rw [MeasureTheory.integral_const_mul, Measure.integral_comp_mul_left (dcProfile 1) 2,
    smul_eq_mul, abs_inv, abs_of_pos two_pos, integral_dcProfile odd_one]
  norm_num

theorem abs_steklovBase_le (x : ℝ) : |steklovBase x| ≤ steklovBaseSup := by
  unfold steklovBase steklovBaseSup dilate dcProfile
  have hc0 : 0 ≤ (∫ y, dcBump 1 y)⁻¹ := inv_nonneg.mpr (integral_dcBump_pos odd_one).le
  have hb := abs_iteratedDeriv_dcBump_le odd_one 0 (2 * x)
  simp only [iteratedDeriv_zero, pow_zero, Nat.factorial_zero, Nat.cast_one,
    Real.one_rpow, mul_one] at hb
  rw [abs_mul, abs_mul, abs_of_pos two_pos, abs_of_nonneg hc0]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb hc0) (by norm_num : (0 : ℝ) ≤ 2)

/-- Iterated Steklov approximation sequence: `steklovSeq 0 = steklovBase`,
`steklovSeq (m + 1) = steklovAvg (steklovRadius m) (steklovSeq m)`. -/
def steklovSeq : ℕ → ℝ → ℝ
  | 0 => steklovBase
  | m + 1 => steklovAvg (steklovRadius m) (steklovSeq m)

theorem contDiff_steklovSeq (m : ℕ) : ContDiff ℝ ∞ (steklovSeq m) := by
  induction m with
  | zero => exact contDiff_steklovBase
  | succ m ih => exact contDiff_steklovAvg ih (steklovRadius_pos m)

theorem supportedIn_steklovSeq_sum (m : ℕ) :
    SupportedIn (1 / 2 + ∑ j ∈ Finset.range m, steklovRadius j) (steklovSeq m) := by
  induction m with
  | zero => simpa only [Finset.range_zero, Finset.sum_empty, add_zero, steklovSeq] using
      supportedIn_steklovBase
  | succ m ih =>
    rw [Finset.sum_range_succ, ← add_assoc]
    exact supportedIn_steklovAvg (steklovRadius_pos m) ih

theorem supportedIn_one_steklovSeq (m : ℕ) : SupportedIn 1 (steklovSeq m) := by
  intro x hx
  have hsum := sum_range_steklovRadius_le_half m
  exact supportedIn_steklovSeq_sum m x (by linarith)

theorem integral_steklovSeq (m : ℕ) : ∫ x, steklovSeq m x = 1 := by
  induction m with
  | zero => exact integral_steklovBase
  | succ m ih =>
    have hR : 0 ≤ 1 / 2 + ∑ j ∈ Finset.range m, steklovRadius j :=
      add_nonneg (by norm_num) (Finset.sum_nonneg fun j _ => (steklovRadius_pos j).le)
    rw [steklovSeq, integral_steklovAvg (contDiff_steklovSeq m).continuous
      (supportedIn_steklovSeq_sum m) hR (steklovRadius_pos m), ih]

theorem abs_iteratedDeriv_steklovSeq_le :
    ∀ (m q : ℕ), q ≤ m → ∀ x : ℝ,
      |iteratedDeriv q (steklovSeq m) x| ≤
        steklovBaseSup * ∏ j ∈ Finset.range q, (steklovRadius j)⁻¹
  | 0, q, hq, x => by
      have hq0 : q = 0 := Nat.le_zero.mp hq
      subst hq0
      simpa [steklovSeq] using abs_steklovBase_le x
  | m + 1, q, hq, x => by
      rcases Nat.of_le_succ hq with hle | rfl
      · rw [steklovSeq, iteratedDeriv_steklovAvg (contDiff_steklovSeq m) (steklovRadius_pos m) q]
        exact abs_steklovAvg_le (steklovRadius_pos m)
          (abs_iteratedDeriv_steklovSeq_le m q hle) x
      · rw [steklovSeq, iteratedDeriv_succ,
          iteratedDeriv_steklovAvg (contDiff_steklovSeq m) (steklovRadius_pos m) m]
        have hcont : Continuous (iteratedDeriv m (steklovSeq m)) :=
          (contDiff_steklovSeq m).continuous_iteratedDeriv m (natCast_le_infty m)
        have hd := abs_deriv_steklovAvg_le hcont (steklovRadius_pos m)
          (abs_iteratedDeriv_steklovSeq_le m m le_rfl) x
        rw [Finset.prod_range_succ]
        linarith

private theorem abs_iteratedDeriv_steklovSeq_step_le {q m : ℕ} (hqm : q + 1 ≤ m) (x : ℝ) :
    |iteratedDeriv q (steklovSeq (m + 1)) x - iteratedDeriv q (steklovSeq m) x| ≤
      (steklovBaseSup * ∏ j ∈ Finset.range (q + 1), (steklovRadius j)⁻¹) * steklovRadius m := by
  rw [steklovSeq, iteratedDeriv_steklovAvg (contDiff_steklovSeq m) (steklovRadius_pos m) q]
  have hsmooth : ContDiff ℝ ∞ (iteratedDeriv q (steklovSeq m)) := by
    rw [iteratedDeriv_eq_iterate]
    exact (contDiff_steklovSeq m).iterate_deriv q
  refine abs_steklovAvg_sub_self_le hsmooth (steklovRadius_pos m) (fun y => ?_) x
  rw [← iteratedDeriv_succ]
  exact abs_iteratedDeriv_steklovSeq_le m (q + 1) hqm y

private theorem abs_iteratedDeriv_steklovSeq_sub_le {q K M : ℕ} (hqK : q + 1 ≤ K) (hKM : K ≤ M)
    (x : ℝ) :
    |iteratedDeriv q (steklovSeq M) x - iteratedDeriv q (steklovSeq K) x| ≤
      (steklovBaseSup * ∏ j ∈ Finset.range (q + 1), (steklovRadius j)⁻¹) /
        (4 * Real.log ((K : ℝ) + 2)) := by
  set C := steklovBaseSup * ∏ j ∈ Finset.range (q + 1), (steklovRadius j)⁻¹
  have hC0 : 0 ≤ C := mul_nonneg steklovBaseSup_pos.le
    (Finset.prod_nonneg fun j _ => inv_nonneg.mpr (steklovRadius_pos j).le)
  have htel : iteratedDeriv q (steklovSeq M) x - iteratedDeriv q (steklovSeq K) x =
      ∑ m ∈ Finset.Ico K M,
        (iteratedDeriv q (steklovSeq (m + 1)) x - iteratedDeriv q (steklovSeq m) x) :=
    (Finset.sum_Ico_sub (fun m => iteratedDeriv q (steklovSeq m) x) hKM).symm
  calc |iteratedDeriv q (steklovSeq M) x - iteratedDeriv q (steklovSeq K) x|
      ≤ ∑ m ∈ Finset.Ico K M,
          |iteratedDeriv q (steklovSeq (m + 1)) x - iteratedDeriv q (steklovSeq m) x| := by
        rw [htel]; exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ Finset.Ico K M, C * steklovRadius m :=
        Finset.sum_le_sum fun m hm =>
          abs_iteratedDeriv_steklovSeq_step_le (hqK.trans (Finset.mem_Ico.mp hm).1) x
    _ = C * ∑ m ∈ Finset.Ico K M, steklovRadius m := (Finset.mul_sum _ _ _).symm
    _ ≤ C * (1 / (4 * Real.log ((K : ℝ) + 2))) :=
        mul_le_mul_of_nonneg_left (sum_Ico_steklovRadius_le hKM) hC0
    _ = C / (4 * Real.log ((K : ℝ) + 2)) := by ring

theorem uniformCauchySeqOn_iteratedDeriv_steklovSeq (q : ℕ) :
    UniformCauchySeqOn (fun m => iteratedDeriv q (steklovSeq m)) atTop Set.univ := by
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  set C := steklovBaseSup * ∏ j ∈ Finset.range (q + 1), (steklovRadius j)⁻¹
  have hC0 : 0 ≤ C := mul_nonneg steklovBaseSup_pos.le
    (Finset.prod_nonneg fun j _ => inv_nonneg.mpr (steklovRadius_pos j).le)
  have htend : Tendsto (fun K : ℕ => C / (4 * Real.log ((K : ℝ) + 2))) atTop (𝓝 0) := by
    have hlog : Tendsto (fun K : ℕ => 4 * Real.log ((K : ℝ) + 2)) atTop atTop :=
      (Real.tendsto_log_atTop.comp
        (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)).const_mul_atTop (by norm_num)
    exact tendsto_const_nhds.div_atTop hlog
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp (htend.eventually (gt_mem_nhds (half_pos hε)))
  refine ⟨max N₀ (q + 1), fun n hn m hm x _ => ?_⟩
  set K := max N₀ (q + 1)
  have hqK : q + 1 ≤ K := le_max_right _ _
  have hKlt : C / (4 * Real.log ((K : ℝ) + 2)) < ε / 2 := hN₀ K (le_max_left _ _)
  have hn' := abs_iteratedDeriv_steklovSeq_sub_le hqK hn x
  have hm' := abs_iteratedDeriv_steklovSeq_sub_le hqK hm x
  rw [Real.dist_eq]
  have htri : |iteratedDeriv q (steklovSeq n) x - iteratedDeriv q (steklovSeq m) x| ≤
      |iteratedDeriv q (steklovSeq n) x - iteratedDeriv q (steklovSeq K) x| +
        |iteratedDeriv q (steklovSeq m) x - iteratedDeriv q (steklovSeq K) x| := by
    have h := abs_sub (iteratedDeriv q (steklovSeq n) x - iteratedDeriv q (steklovSeq K) x)
      (iteratedDeriv q (steklovSeq m) x - iteratedDeriv q (steklovSeq K) x)
    rwa [sub_sub_sub_cancel_right] at h
  linarith

/-- Uniform limit family `(G_q)_{q ≥ 0}` of `(iteratedDeriv q (steklovSeq m))_{m ≥ 0}`. -/
private def steklovDerivLimit (q : ℕ) : ℝ → ℝ :=
  Classical.choose (HTGeometry.exists_tendstoUniformly_of_uniformCauchySeq
    (uniformCauchySeqOn_iteratedDeriv_steklovSeq q))

private theorem tendstoUniformly_steklovDerivLimit (q : ℕ) :
    TendstoUniformly (fun m => iteratedDeriv q (steklovSeq m)) (steklovDerivLimit q) atTop :=
  Classical.choose_spec (HTGeometry.exists_tendstoUniformly_of_uniformCauchySeq
    (uniformCauchySeqOn_iteratedDeriv_steklovSeq q))

/-- **The Steklov Denjoy–Carleman profile**: uniform limit of `steklovSeq m` on `ℝ`. -/
def steklovDCProfile : ℝ → ℝ :=
  steklovDerivLimit 0

theorem contDiff_steklovDCProfile : ContDiff ℝ ∞ steklovDCProfile :=
  HTGeometry.contDiff_infty_of_tendstoUniformly_iteratedDeriv
    contDiff_steklovSeq tendstoUniformly_steklovDerivLimit

theorem iteratedDeriv_steklovDCProfile_eq (q : ℕ) :
    iteratedDeriv q steklovDCProfile = steklovDerivLimit q :=
  HTGeometry.iteratedDeriv_eq_of_tendstoUniformly_iteratedDeriv
    contDiff_steklovSeq tendstoUniformly_steklovDerivLimit q

theorem steklovDCProfile_vanishesOff : VanishesOff steklovDCProfile := by
  intro x hx
  have hpt : ∀ y, Tendsto (fun m => steklovSeq m y) atTop (𝓝 (steklovDCProfile y)) := by
    intro y
    simpa only [iteratedDeriv_zero, steklovDCProfile] using
      (tendstoUniformly_steklovDerivLimit 0).tendsto_at y
  exact HTGeometry.eq_zero_of_tendsto_of_forall_eq_zero (J := Set.Icc (-1 : ℝ) 1) hpt
    (fun m y hy => supportedIn_one_steklovSeq m y (by
      simp only [Set.mem_Icc, not_and_or, not_le] at hy
      rcases hy with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith))
    (by
      intro hmem
      have := abs_le.mpr hmem
      linarith)

theorem integral_steklovDCProfile : ∫ x, steklovDCProfile x = 1 := by
  have hvan : SupportedIn 1 steklovDCProfile := steklovDCProfile_vanishesOff
  rw [integral_eq_intervalIntegral_of_supportedIn
    hvan zero_le_one (by norm_num : (1 : ℝ) < 2)]
  have hseq_int : ∀ m : ℕ, (∫ x in (-2 : ℝ)..2, steklovSeq m x) = 1 := by
    intro m
    rw [← integral_eq_intervalIntegral_of_supportedIn
      (supportedIn_one_steklovSeq m) zero_le_one (by norm_num : (1 : ℝ) < 2),
      integral_steklovSeq m]
  have htend : Tendsto (fun m : ℕ => ∫ x in (-2 : ℝ)..2, steklovSeq m x) atTop
      (𝓝 (∫ x in (-2 : ℝ)..2, steklovDCProfile x)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hunif := Metric.tendstoUniformly_iff.mp (tendstoUniformly_steklovDerivLimit 0) (ε / 8)
      (by positivity)
    filter_upwards [hunif] with m hm
    rw [Real.dist_eq, ← intervalIntegral.integral_sub
      ((contDiff_steklovSeq m).continuous.intervalIntegrable (-2) 2)
      (contDiff_steklovDCProfile.continuous.intervalIntegrable (-2) 2),
      ← Real.norm_eq_abs]
    have hle := intervalIntegral.norm_integral_le_of_norm_le_const (C := ε / 8)
      (f := fun x => steklovSeq m x - steklovDCProfile x) (a := -2) (b := 2) fun x _ => by
        have hx := hm x
        simp only [iteratedDeriv_zero, Real.dist_eq] at hx
        rw [Real.norm_eq_abs, abs_sub_comm]
        exact hx.le
    rw [show (2 : ℝ) - (-2) = 4 by norm_num, abs_of_pos (by norm_num : (0 : ℝ) < 4)] at hle
    linarith
  exact tendsto_nhds_unique htend
    (Filter.Tendsto.congr (fun m => (hseq_int m).symm) tendsto_const_nhds)

theorem abs_iteratedDeriv_steklovDCProfile_le (q : ℕ) (x : ℝ) :
    |iteratedDeriv q steklovDCProfile x| ≤ steklovBaseSup * 12 ^ q * dcLogWeight q := by
  have hpt : Tendsto (fun m => |iteratedDeriv q (steklovSeq m) x|) atTop
      (𝓝 |iteratedDeriv q steklovDCProfile x|) := by
    rw [iteratedDeriv_steklovDCProfile_eq q]
    exact ((tendstoUniformly_steklovDerivLimit q).tendsto_at x).abs
  refine le_of_tendsto hpt ?_
  filter_upwards [eventually_ge_atTop q] with m hqm
  calc |iteratedDeriv q (steklovSeq m) x|
      ≤ steklovBaseSup * ∏ j ∈ Finset.range q, (steklovRadius j)⁻¹ :=
        abs_iteratedDeriv_steklovSeq_le m q hqm x
    _ ≤ steklovBaseSup * (12 ^ q * dcLogWeight q) :=
        mul_le_mul_of_nonneg_left (prod_inv_steklovRadius_le q) steklovBaseSup_pos.le
    _ = steklovBaseSup * 12 ^ q * dcLogWeight q := by ring

/-- **`L¹` derivative bound in the logarithmic Denjoy–Carleman class**:
`∫ |iteratedDeriv q steklovDCProfile| ≤ (2 * steklovBaseSup) * 12^q * q! * (log(q + 3))^{2q}`. -/
theorem integral_abs_iteratedDeriv_steklovDCProfile_le (q : ℕ) :
    ∫ t, |iteratedDeriv q steklovDCProfile t| ≤
      (2 * steklovBaseSup) * 12 ^ q * dcLogWeight q := by
  have hd : Continuous (iteratedDeriv q steklovDCProfile) :=
    contDiff_steklovDCProfile.continuous_iteratedDeriv q (natCast_le_infty q)
  have hvan : ∀ t, t ∉ Set.Icc (-1 : ℝ) 1 → steklovDCProfile t = 0 := fun t ht =>
    steklovDCProfile_vanishesOff t (by
      simp only [Set.mem_Icc, not_and_or, not_le] at ht
      rcases ht with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith)
  have hdR : SupportedIn 1 (iteratedDeriv q steklovDCProfile) := fun t ht =>
    iteratedDeriv_eq_zero_of_vanish hvan q fun h => by
      have := abs_le.mpr ⟨h.1, h.2⟩; linarith
  have hbound := integral_abs_le_of_bound hd (hasCompactSupport_of_vanishes hdR)
    (abs_iteratedDeriv_steklovDCProfile_le q) hdR zero_le_one
  linarith

/-! ### 4. Euler–Maclaurin synthesis and transfer in the logarithmic Denjoy–Carleman class -/

theorem integral_abs_iteratedDeriv_logTower_le_dcLogWeight {H : ℝ → ℝ} (hH : ContDiff ℝ ∞ H)
    {α β : ℝ} (hHs : ∀ t, t ∉ Set.Icc α β → H t = 0) {C X : ℝ} (hC : 0 ≤ C) (hX : 0 ≤ X)
    (hHb : ∀ j, ∫ t, |iteratedDeriv j H t| ≤ C * dcLogWeight j * X ^ j) (p : ℕ) :
    ∀ j : ℕ, ∫ t, |iteratedDeriv j (logTower H p) t| ≤
      C * dcLogWeight (j + p) * X ^ j * ∏ i ∈ Finset.range p, (X + ((i : ℝ) + 1)) := by
  induction p with
  | zero => intro j; simpa [logTower] using hHb j
  | succ p ih =>
    intro j
    have h1 := ih (j + 1)
    have h2 := ih j
    set P := ∏ i ∈ Finset.range p, (X + ((i : ℝ) + 1))
    have hP : 0 ≤ P := Finset.prod_nonneg fun i _ => by positivity
    have hmono : dcLogWeight (j + p) ≤ dcLogWeight (j + (p + 1)) :=
      dcLogWeight_mono (by omega)
    rw [show j + 1 + p = j + (p + 1) by omega] at h1
    rw [Finset.prod_range_succ]
    calc ∫ t, |iteratedDeriv j (logTower H (p + 1)) t|
        ≤ (∫ t, |iteratedDeriv (j + 1) (logTower H p) t|) +
            ((p : ℝ) + 1) * ∫ t, |iteratedDeriv j (logTower H p) t| :=
          integral_abs_iteratedDeriv_logTower_succ_le hH hHs p j
      _ ≤ C * dcLogWeight (j + (p + 1)) * X ^ (j + 1) * P +
            ((p : ℝ) + 1) * (C * dcLogWeight (j + (p + 1)) * X ^ j * P) := by
          refine add_le_add h1 (mul_le_mul_of_nonneg_left (h2.trans ?_) (by positivity))
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmono hC)
              (pow_nonneg hX j)) hP
      _ = C * dcLogWeight (j + (p + 1)) * X ^ j * (P * (X + ((p : ℝ) + 1))) := by ring

theorem integral_abs_iteratedDeriv_mul_le_dcLogWeight {F G : ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    (hG : ContDiff ℝ ∞ G) (hGc : HasCompactSupport G) {M b A B' : ℝ} (hM0 : 0 ≤ M)
    (hb : 0 ≤ b) (hB' : 0 ≤ B')
    (hM : ∀ l t, |iteratedDeriv l F t| ≤ M * b ^ l * dcLogWeight l)
    (hA : ∀ q, ∫ t, |iteratedDeriv q G t| ≤ A * B' ^ q * dcLogWeight q) (c a : ℝ) (i : ℕ) :
    ∫ t, |iteratedDeriv i (fun t => F (t - c) * G (a - t)) t| ≤
      M * A * dcLogWeight i * (b + B') ^ i := by
  refine (integral_abs_iteratedDeriv_mul_le hF hG hGc hM c a i).trans ?_
  unfold leibnizBound
  rw [add_pow, Finset.mul_sum]
  have hA0 : 0 ≤ A := by
    have := (integral_nonneg fun t => abs_nonneg (iteratedDeriv 0 G t)).trans (hA 0)
    simpa [dcLogWeight_zero] using this
  refine Finset.sum_le_sum fun l hl => ?_
  have hli : l ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
  have hw := dcLogWeight_mul_le hli
  have hwl : 0 ≤ dcLogWeight l := (dcLogWeight_pos l).le
  have h1 : (i.choose l : ℝ) * (M * b ^ l * dcLogWeight l) *
      (∫ s', |iteratedDeriv (i - l) G s'|) ≤
      (i.choose l : ℝ) * (M * b ^ l * dcLogWeight l) *
        (A * B' ^ (i - l) * dcLogWeight (i - l)) :=
    mul_le_mul_of_nonneg_left (hA (i - l)) (by positivity)
  refine h1.trans ?_
  calc (i.choose l : ℝ) * (M * b ^ l * dcLogWeight l) *
        (A * B' ^ (i - l) * dcLogWeight (i - l))
      = M * A * ((i.choose l : ℝ) * b ^ l * B' ^ (i - l)) *
          (dcLogWeight l * dcLogWeight (i - l)) := by ring
    _ ≤ M * A * ((i.choose l : ℝ) * b ^ l * B' ^ (i - l)) * dcLogWeight i :=
        mul_le_mul_of_nonneg_left hw (by positivity)
    _ = M * A * dcLogWeight i * (b ^ l * B' ^ (i - l) * (i.choose l : ℝ)) := by ring

theorem abs_dcLogSynth_sub_le {φ F : ℝ → ℝ} {R M b A B : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hF : ContDiff ℝ ∞ F) (hFs : ∀ t, t ∉ Set.Icc (-R) R → F t = 0)
    (hM0 : 0 ≤ M) (hb : 0 ≤ b) (hB : 0 ≤ B)
    (hM : ∀ l t, |iteratedDeriv l F t| ≤ M * b ^ l * dcLogWeight l)
    (hA : ∀ q, ∫ t, |iteratedDeriv q φ t| ≤ A * B ^ q * dcLogWeight q)
    {n₀ N : ℕ} (hn₀ : 2 ≤ n₀) (hN : Real.log n₀ + 2 * R < Real.log (1 + N))
    {k : ℝ} (hk : 1 ≤ k) (m : ℕ) (r : ℝ) :
    |atomicTest (N + 1) (emWeights F (Real.log n₀ + R)) (dilate k φ) (r + (Real.log n₀ + R)) -
        ∫ v, F v * dilate k φ (r - v)| ≤
      M * A * (((2 * m + 2 : ℕ) : ℝ) * Real.log (((2 * m + 2 : ℕ) : ℝ) + 3) ^ 2 *
        (b + B * k + (2 * m + 2 : ℕ)) / n₀) ^ (2 * m + 2) := by
  have hk0 : 0 < k := by linarith
  have hn0 : (1 : ℝ) < n₀ := by exact_mod_cast hn₀
  set c := Real.log n₀ + R
  set p := 2 * m + 2
  set X := b + B * k
  have hX : 0 ≤ X := by positivity
  have hψ : ContDiff ℝ ∞ (dilate k φ) :=
    contDiff_const.mul (hφ.comp (contDiff_const.mul contDiff_id))
  have hψc : HasCompactSupport (dilate k φ) := by
    have : dilate k φ = fun s => k * φ (k * s) := rfl
    rw [this]; exact (hφc.comp_smul hk0.ne').mul_left
  have hA0 : 0 ≤ A := by
    have := (integral_nonneg fun t => abs_nonneg (iteratedDeriv 0 φ t)).trans (hA 0)
    simpa [dcLogWeight_zero] using this
  have hψA : ∀ q, ∫ t, |iteratedDeriv q (dilate k φ) t| ≤ A * (B * k) ^ q * dcLogWeight q :=
    fun q => by
      rw [integral_abs_iteratedDeriv_dilate hφ hk0, mul_pow]
      have := mul_le_mul_of_nonneg_left (hA q) (pow_nonneg hk0.le q)
      linarith
  set H : ℝ → ℝ := fun t => F (t - c) * dilate k φ (r + c - t)
  have hH : ContDiff ℝ ∞ H :=
    (hF.comp (contDiff_id.sub contDiff_const)).mul (hψ.comp (contDiff_const.sub contDiff_id))
  have hHs : ∀ t, t ∉ Set.Icc (c - R) (c + R) → H t = 0 := fun t ht => by
    have : t - c ∉ Set.Icc (-R) R := fun h => ht ⟨by linarith [h.1], by linarith [h.2]⟩
    simp only [H, hFs _ this, zero_mul]
  have hc : 0 < c - R := by simp only [c, add_sub_cancel_right]; exact Real.log_pos hn0
  have hEM := abs_sum_logTowerS_sub_integral_le hH hc hHs (N := N) (by simp only [c]; linarith) m
  have hsum : atomicTest (N + 1) (emWeights F c) (dilate k φ) (r + c) =
      ∑ n ∈ Finset.range (N + 1), logTowerS H 0 (1 + n) := by
    rw [atomicTest_emWeights]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [logTowerS, logTower, zero_add, pow_one, H]; ring
  have hint : ∫ t, H t = ∫ v, F v * dilate k φ (r - v) := by
    rw [← integral_add_right_eq_self H c]
    exact integral_congr_ae (Eventually.of_forall fun v => by simp only [H]; ring_nf)
  have hHb : ∀ j, ∫ t, |iteratedDeriv j H t| ≤ M * A * dcLogWeight j * X ^ j := fun j =>
    integral_abs_iteratedDeriv_mul_le_dcLogWeight hF hψ hψc hM0 hb (by positivity) hM hψA c (r + c) j
  have htower := integral_abs_iteratedDeriv_logTower_le_dcLogWeight hH hHs (by positivity) hX hHb p 0
  simp only [iteratedDeriv_zero, zero_add, pow_zero, mul_one] at htower
  rw [hsum, ← hint]
  refine hEM.trans ?_
  have hB1 := abs_bernoulli_div_factorial_le m
  have hexp : Real.exp (-(c - R)) = (n₀ : ℝ)⁻¹ := by
    simp only [c, add_sub_cancel_right, Real.exp_neg, Real.exp_log (by linarith : (0 : ℝ) < n₀)]
  rw [hexp]
  have hprod : ∏ i ∈ Finset.range p, (X + ((i : ℝ) + 1)) ≤ (X + p) ^ p := by
    calc ∏ i ∈ Finset.range p, (X + ((i : ℝ) + 1)) ≤ ∏ _i ∈ Finset.range p, (X + p) :=
          Finset.prod_le_prod (fun i _ => by positivity) fun i hi => by
            have : (i : ℝ) + 1 ≤ p := by exact_mod_cast Finset.mem_range.mp hi
            linarith
      _ = (X + p) ^ p := by rw [Finset.prod_const, Finset.card_range]
  have hw_pow := dcLogWeight_le_pow p
  have hlogp0 : 0 ≤ Real.log ((p : ℝ) + 3) ^ 2 := sq_nonneg _
  have hT : ∫ t, |logTower H p t| ≤
      M * A * ((p : ℝ) * Real.log ((p : ℝ) + 3) ^ 2) ^ p * (X + p) ^ p := by
    refine htower.trans ?_
    exact mul_le_mul (mul_le_mul_of_nonneg_left hw_pow (by positivity)) hprod
      (Finset.prod_nonneg fun i _ => by positivity) (by positivity)
  have hT0 : 0 ≤ ∫ t, |logTower H p t| := integral_nonneg fun t => abs_nonneg _
  have hnp : (0 : ℝ) ≤ (n₀ : ℝ)⁻¹ ^ p := by positivity
  calc |((bernoulli (2 * m + 2) : ℚ) : ℝ)| / ((2 * m + 2).factorial : ℝ) *
        ((n₀ : ℝ)⁻¹ ^ p * ∫ t, |logTower H p t|)
      ≤ 1 * ((n₀ : ℝ)⁻¹ ^ p *
          (M * A * ((p : ℝ) * Real.log ((p : ℝ) + 3) ^ 2) ^ p * (X + p) ^ p)) :=
        mul_le_mul hB1 (mul_le_mul_of_nonneg_left hT hnp) (mul_nonneg hnp hT0) zero_le_one
    _ = M * A * (((p : ℕ) : ℝ) * Real.log (((p : ℕ) : ℝ) + 3) ^ 2 *
          (X + (p : ℕ)) / n₀) ^ p := by
        simp only [mul_pow, div_eq_mul_inv, inv_pow]
        ring

/-- Supremum error of the logarithmic Denjoy–Carleman synthesis of order `2m + 2`. -/
def dcSynthErr (M b A B k A0 : ℝ) (m n₀ : ℕ) : ℝ :=
  M * A * (((2 * m + 2 : ℕ) : ℝ) * Real.log (((2 * m + 2 : ℕ) : ℝ) + 3) ^ 2 *
    (b + B * k + (2 * m + 2 : ℕ)) / n₀) ^ (2 * m + 2) +
      M * b * dcLogWeight 1 * (1 / k) * A0

/-- Quadrature ratio for the logarithmic Denjoy–Carleman synthesis at `m = gevOrder k`. -/
def dcSynthRatio (b Bφ k : ℝ) (n₀ : ℕ) : ℝ :=
  ((2 * gevOrder k + 2 : ℕ) : ℝ) * Real.log (((2 * gevOrder k + 2 : ℕ) : ℝ) + 3) ^ 2 *
    (b + Bφ * k + (2 * gevOrder k + 2 : ℕ)) / n₀

theorem exists_dcLogSynthesis {φ F : ℝ → ℝ} {R M b A B : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφ1 : VanishesOff φ) (hφint : ∫ s, φ s = 1)
    (hF : ContDiff ℝ ∞ F) (hFR : SupportedIn R F)
    (hM0 : 0 ≤ M) (hb : 0 ≤ b) (hB : 0 ≤ B)
    (hM : ∀ l t, |iteratedDeriv l F t| ≤ M * b ^ l * dcLogWeight l)
    (hA : ∀ q, ∫ t, |iteratedDeriv q φ t| ≤ A * B ^ q * dcLogWeight q)
    {n₀ : ℕ} (hn₀ : 2 ≤ n₀) {k : ℝ} (hk : 1 ≤ k) (m : ℕ) :
    ∃ (x : ℕ → ℝ) (D : ℝ → ℝ),
      atomicTest (n₀ * blockSize R) x (dilate k φ) =
        (fun u => F (u - (Real.log n₀ + R)) + D (u - (Real.log n₀ + R))) ∧
      ContDiff ℝ 2 D ∧ SupportedIn (R + 1) D ∧
      (∀ u, |D u| ≤ dcSynthErr M b A B k (∫ s, |φ s|) m n₀) ∧
      ∀ u v, |D u - D v| ≤ emLip (fun l => M * b ^ l * dcLogWeight l)
        (fun q => ∫ s, |iteratedDeriv q φ s|) k n₀ * |u - v| := by
  have hn₀1 : 1 ≤ n₀ := by omega
  have hB1 : 1 ≤ n₀ * blockSize R := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by omega) (by have := one_le_blockSize R; omega))
  obtain ⟨N, hNB⟩ : ∃ N : ℕ, n₀ * blockSize R = N + 1 := ⟨n₀ * blockSize R - 1, by omega⟩
  have hN : Real.log n₀ + 2 * R < Real.log (1 + N) := by
    have := log_lt_log_block hn₀1 R
    rw [hNB] at this; push_cast at this; rwa [add_comm (N : ℝ) 1] at this
  have hFs : ∀ t, t ∉ Set.Icc (-R) R → F t = 0 := fun t ht => hFR t (by
    simp only [Set.mem_Icc, not_and_or, not_le] at ht
    rcases ht with ht | ht
    · exact lt_of_lt_of_le (by linarith) (neg_le_abs t)
    · exact lt_of_lt_of_le ht (le_abs_self t))
  obtain ⟨x, D, hx, hD2, hDR, hsup, hlip⟩ := exists_emSynthesis_of hφ hφ1 hφint hF hFR hM
    (fun l => mul_nonneg (mul_nonneg hM0 (pow_nonneg hb l)) (dcLogWeight_pos l).le)
    hn₀ hk fun r => by
      rw [hNB]
      exact abs_dcLogSynth_sub_le hφ (hasCompactSupport_of_vanishes hφ1) hF hFs
        hM0 hb hB hM hA hn₀ hN hk m r
  refine ⟨x, D, hx, hD2, hDR, fun u => (hsup u).trans (le_of_eq ?_), hlip⟩
  unfold dcSynthErr; simp

/-- **Super-Gevrey overlap growth**: dilations `κ_N → ∞` whose overlap ratio `N / κ_N` beats
`(log log κ_N) (log log log κ_N)²`. -/
def OverlapGrowthSuperGevrey (κ : ℕ → ℝ) : Prop :=
  Tendsto κ atTop atTop ∧
    Tendsto (fun N : ℕ =>
      ((N : ℝ) / κ N) /
        (Real.log (Real.log (κ N)) * Real.log (Real.log (Real.log (κ N))) ^ 2))
      atTop atTop

private theorem dcSynthRatio_nonneg {b Bφ k : ℝ} (hb : 0 ≤ b) (hBφ : 0 ≤ Bφ) (hk : 0 ≤ k)
    (n : ℕ) : 0 ≤ dcSynthRatio b Bφ k n := by
  unfold dcSynthRatio
  have hlog0 : 0 ≤ Real.log (((2 * gevOrder k + 2 : ℕ) : ℝ) + 3) ^ 2 := sq_nonneg _
  positivity

private theorem dcSynthRatio_le {b Bφ : ℝ} (hb : 0 ≤ b) (hBφ : 0 ≤ Bφ) {k : ℝ} {n B : ℕ}
    (hk1 : 1 ≤ k) (hn : 1 ≤ n) (hℓ9 : 9 ≤ Real.log (Real.log k))
    (hll1 : 1 ≤ Real.log (Real.log (Real.log k)))
    (hK1 : 1 ≤ ((n * B : ℕ) : ℝ) / k /
      (Real.log (Real.log k) * Real.log (Real.log (Real.log k)) ^ 2)) :
    dcSynthRatio b Bφ k n ≤
      24 * b * (Real.log ((n * B : ℕ) : ℝ) ^ (3 : ℝ) / n) +
      144 * (Real.log ((n * B : ℕ) : ℝ) ^ (4 : ℝ) / n) +
      24 * Bφ * B * (((n * B : ℕ) : ℝ) / k /
        (Real.log (Real.log k) * Real.log (Real.log (Real.log k)) ^ 2))⁻¹ := by
  set ℓ := Real.log (Real.log k)
  set ℓ₂ := Real.log ℓ
  set W := ℓ * ℓ₂ ^ 2
  have hk0 : 0 < k := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hW1 : 1 ≤ W := by
    have : 1 ≤ ℓ₂ ^ 2 := by nlinarith only [hll1]
    nlinarith only [hℓ9, this]
  have hW0 : 0 < W := by linarith
  have hK'1 : 1 ≤ ((n * B : ℕ) : ℝ) / k := by
    have heq : ((n * B : ℕ) : ℝ) / k = (((n * B : ℕ) : ℝ) / k / W) * W := by field_simp [hW0.ne']
    nlinarith only [hK1, hW1, heq]
  have hkN : k ≤ ((n * B : ℕ) : ℝ) := by
    have := (le_div_iff₀ hk0).mp hK'1; linarith
  have hlogk : 1 < Real.log k := by
    by_contra h; push Not at h
    have : ℓ ≤ 0 := Real.log_nonpos (Real.log_nonneg hk1) h
    linarith
  set L := Real.log ((n * B : ℕ) : ℝ)
  have hℓL : ℓ ≤ L := by
    have h1 : ℓ ≤ Real.log k := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
    exact h1.trans (Real.log_le_log hk0 hkN)
  have hL0 : 0 < L := by linarith
  set p : ℝ := ((2 * gevOrder k + 2 : ℕ) : ℝ)
  have hp0 : 0 ≤ p := by positivity
  have hp6 : p ≤ 6 * ℓ := by
    have hceil := Nat.ceil_lt_add_one (show 0 ≤ ℓ by linarith)
    simp only [p, gevOrder]; push_cast; linarith
  have hp3_sq : p + 3 ≤ ℓ ^ 2 := by nlinarith only [hp6, hℓ9]
  have hlogp : Real.log (p + 3) ≤ 2 * ℓ₂ := by
    calc Real.log (p + 3) ≤ Real.log (ℓ ^ 2) := Real.log_le_log (by positivity) hp3_sq
      _ = 2 * ℓ₂ := by rw [Real.log_pow]; push_cast; rfl
  have hlogp0 : 0 ≤ Real.log (p + 3) := (Real.log_pos (by linarith [hp0])).le
  have hlogp_sq : Real.log (p + 3) ^ 2 ≤ 4 * ℓ₂ ^ 2 := by
    calc Real.log (p + 3) ^ 2 ≤ (2 * ℓ₂) ^ 2 := pow_le_pow_left₀ hlogp0 hlogp 2
      _ = 4 * ℓ₂ ^ 2 := by ring
  have hpW : p * Real.log (p + 3) ^ 2 ≤ 24 * W := by
    calc p * Real.log (p + 3) ^ 2 ≤ (6 * ℓ) * (4 * ℓ₂ ^ 2) :=
          mul_le_mul hp6 hlogp_sq (sq_nonneg _) (by linarith)
      _ = 24 * W := by dsimp [W]; ring
  have hℓ₂L : ℓ₂ ≤ L := by
    have : ℓ₂ ≤ ℓ := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
    exact this.trans hℓL
  have hWL3 : W ≤ L ^ (3 : ℝ) := by
    have h3 : L ^ (3 : ℝ) = L * L ^ 2 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
    rw [h3]
    have hsq : ℓ₂ ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (by linarith) hℓ₂L 2
    exact mul_le_mul hℓL hsq (sq_nonneg _) hL0.le
  have hL4 : L ^ (4 : ℝ) = L ^ (3 : ℝ) * L := by
    rw [show (4 : ℝ) = 3 + 1 by norm_num, Real.rpow_add_one hL0.ne']
  set Kq := ((n * B : ℕ) : ℝ) / k / W
  have hB0 : (0 : ℝ) < B := by
    rcases Nat.eq_zero_or_pos B with hBzero | hBpos
    · have hknonpos : k ≤ 0 := by
        simpa only [hBzero, Nat.mul_zero, Nat.cast_zero] using hkN
      exact False.elim ((not_le_of_gt hk0) hknonpos)
    · exact_mod_cast hBpos
  have hkn : k / n = B * Kq⁻¹ * W⁻¹ := by
    dsimp only [Kq]; push_cast; field_simp [hk0.ne', hn0.ne', hW0.ne', hB0.ne']
  have hρe : dcSynthRatio b Bφ k n =
      (p * Real.log (p + 3) ^ 2) * b / n + Bφ * ((p * Real.log (p + 3) ^ 2) * (k / n)) +
        (p * Real.log (p + 3) ^ 2) * p / n := by
    simp only [dcSynthRatio, p]; ring
  rw [hρe, hL4]
  have hpL3 : p * Real.log (p + 3) ^ 2 ≤ 24 * L ^ (3 : ℝ) :=
    hpW.trans (mul_le_mul_of_nonneg_left hWL3 (by norm_num))
  have t1 : (p * Real.log (p + 3) ^ 2) * b / n ≤ 24 * b * (L ^ (3 : ℝ) / n) := by
    rw [div_le_iff₀ hn0, mul_div_assoc', div_mul_cancel₀ _ hn0.ne']
    nlinarith [mul_le_mul_of_nonneg_right hpL3 hb]
  have t2 : Bφ * ((p * Real.log (p + 3) ^ 2) * (k / n)) ≤ 24 * Bφ * B * Kq⁻¹ := by
    rw [hkn]
    have hKi : 0 ≤ Kq⁻¹ := inv_nonneg.mpr (by linarith)
    have h1 : (p * Real.log (p + 3) ^ 2) * (B * Kq⁻¹ * W⁻¹) ≤
        (24 * W) * (B * Kq⁻¹ * W⁻¹) :=
      mul_le_mul_of_nonneg_right hpW (by positivity)
    have h2 : (24 * W) * (B * Kq⁻¹ * W⁻¹) = 24 * B * Kq⁻¹ := by field_simp [hW0.ne']
    calc Bφ * ((p * Real.log (p + 3) ^ 2) * (B * Kq⁻¹ * W⁻¹))
        ≤ Bφ * ((24 * W) * (B * Kq⁻¹ * W⁻¹)) := mul_le_mul_of_nonneg_left h1 hBφ
      _ = 24 * Bφ * B * Kq⁻¹ := by rw [h2]; ring
  have t3 : (p * Real.log (p + 3) ^ 2) * p / n ≤ 144 * (L ^ (3 : ℝ) * L / n) := by
    rw [div_le_iff₀ hn0, mul_div_assoc', div_mul_cancel₀ _ hn0.ne']
    have hpL : p ≤ 6 * L := hp6.trans (by linarith)
    have hpW0 : 0 ≤ p * Real.log (p + 3) ^ 2 := mul_nonneg hp0 (sq_nonneg _)
    nlinarith [mul_le_mul hpL3 hpL hp0 (by positivity)]
  linarith

private theorem tendsto_dcLogSynthesis {κ : ℕ → ℝ} (hκ : OverlapGrowthSuperGevrey κ) {B : ℕ}
    (hB : 1 ≤ B) {M b A Bφ A0 : ℝ} (hMA : 0 ≤ M * A) (hb : 0 ≤ b) (hBφ : 0 ≤ Bφ)
    (M' A' : ℕ → ℝ) (R' : ℝ) :
    Tendsto (fun n : ℕ => dcSynthErr M b A Bφ (κ (n * B)) A0 (gevOrder (κ (n * B))) n) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => synthLevy R'
      (dcSynthErr M b A Bφ (κ (n * B)) A0 (gevOrder (κ (n * B))) n)
      (emLip M' A' (κ (n * B)) n) (κ (n * B))) atTop (𝓝 0) := by
  obtain ⟨hk, hkl⟩ := hκ
  have hNB : Tendsto (fun n : ℕ => n * B) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_right n hB) tendsto_id
  have hK : Tendsto (fun n => κ (n * B)) atTop atTop := hk.comp hNB
  have hlogK : Tendsto (fun n => Real.log (κ (n * B))) atTop atTop :=
    Real.tendsto_log_atTop.comp hK
  have hℓ : Tendsto (fun n => Real.log (Real.log (κ (n * B)))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlogK
  have hℓ₂ : Tendsto (fun n => Real.log (Real.log (Real.log (κ (n * B))))) atTop atTop :=
    Real.tendsto_log_atTop.comp hℓ
  have hKW : Tendsto (fun n : ℕ => ((n * B : ℕ) : ℝ) / κ (n * B) /
      (Real.log (Real.log (κ (n * B))) * Real.log (Real.log (Real.log (κ (n * B)))) ^ 2))
      atTop atTop := hkl.comp hNB
  have hev := (hK.eventually_ge_atTop 1).and ((eventually_ge_atTop 1).and
    ((hℓ.eventually_ge_atTop 9).and ((hℓ₂.eventually_ge_atTop 1).and
      (hKW.eventually_ge_atTop 1))))
  have hup : Tendsto (fun n : ℕ =>
      24 * b * (Real.log ((n * B : ℕ) : ℝ) ^ (3 : ℝ) / n) +
      144 * (Real.log ((n * B : ℕ) : ℝ) ^ (4 : ℝ) / n) +
      24 * Bφ * B * (((n * B : ℕ) : ℝ) / κ (n * B) /
        (Real.log (Real.log (κ (n * B))) *
          Real.log (Real.log (Real.log (κ (n * B)))) ^ 2))⁻¹) atTop (𝓝 0) := by
    have := (((tendsto_log_rpow_div (r := 3) hB).const_mul (24 * b)).add
      ((tendsto_log_rpow_div (r := 4) hB).const_mul 144)).add
      (hKW.inv_tendsto_atTop.const_mul (24 * Bφ * B))
    simp only [mul_zero, add_zero] at this
    exact this
  have hρ : Tendsto (fun n => dcSynthRatio b Bφ (κ (n * B)) n) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
      (hev.mono fun n h => dcSynthRatio_nonneg hb hBφ (by linarith [h.1]) n)
      (hev.mono fun n ⟨hk1, hn, hℓ9, hll1, hK1⟩ => dcSynthRatio_le hb hBφ hk1 hn hℓ9 hll1 hK1)
  have hρ1 := hρ.eventually (Iic_mem_nhds (Real.exp_pos (-1)))
  have he₁ : ∀ᶠ n : ℕ in atTop,
      0 ≤ M * A * dcSynthRatio b Bφ (κ (n * B)) n ^ (2 * gevOrder (κ (n * B)) + 2) ∧
      M * A * dcSynthRatio b Bφ (κ (n * B)) n ^ (2 * gevOrder (κ (n * B)) + 2) ≤
        M * A * (1 / Real.log (κ (n * B)) ^ 2) := by
    filter_upwards [hev, hρ1] with n ⟨hk1, _, hℓ9, _, _⟩ hρn
    have hρ0 := dcSynthRatio_nonneg (k := κ (n * B)) hb hBφ
      (by linarith only [hk1]) n
    refine ⟨mul_nonneg hMA (pow_nonneg hρ0 _), mul_le_mul_of_nonneg_left ?_ hMA⟩
    have hlogk : 1 < Real.log (κ (n * B)) := by
      by_contra h; push Not at h
      have : Real.log (Real.log (κ (n * B))) ≤ 0 := Real.log_nonpos (Real.log_nonneg hk1) h
      linarith
    have h2p : 2 * Real.log (Real.log (κ (n * B))) ≤ ((2 * gevOrder (κ (n * B)) + 2 : ℕ) : ℝ) := by
      have := Nat.le_ceil (Real.log (Real.log (κ (n * B))))
      simp only [gevOrder]; push_cast; linarith
    have h1 := pow_le_pow_left₀ hρ0 hρn (2 * gevOrder (κ (n * B)) + 2)
    have h2 : Real.exp (-1) ^ (2 * gevOrder (κ (n * B)) + 2) =
        Real.exp (-((2 * gevOrder (κ (n * B)) + 2 : ℕ) : ℝ)) := by
      rw [← Real.exp_nat_mul]; ring_nf
    have h3 : Real.exp (-((2 * gevOrder (κ (n * B)) + 2 : ℕ) : ℝ)) ≤
        Real.exp (-(2 * Real.log (Real.log (κ (n * B))))) :=
      Real.exp_le_exp.mpr (by linarith)
    have h4 : Real.exp (-(2 * Real.log (Real.log (κ (n * B))))) =
        1 / Real.log (κ (n * B)) ^ 2 := by
      rw [Real.exp_neg,
        show (2 : ℝ) * Real.log (Real.log (κ (n * B))) =
          ((2 : ℕ) : ℝ) * Real.log (Real.log (κ (n * B))) by norm_num,
        Real.exp_nat_mul, Real.exp_log (by linarith), one_div]
    linarith
  have hinvlog2 : Tendsto (fun n => 1 / Real.log (κ (n * B)) ^ 2) atTop (𝓝 0) := by
    simp only [one_div]
    exact ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hlogK).inv_tendsto_atTop
  have hinv : Tendsto (fun n => 1 / κ (n * B)) atTop (𝓝 0) := by
    simp only [one_div]; exact hK.inv_tendsto_atTop
  have he₁t : Tendsto (fun n => M * A * dcSynthRatio b Bφ (κ (n * B)) n ^
      (2 * gevOrder (κ (n * B)) + 2)) atTop (𝓝 0) := by
    have hup' := hinvlog2.const_mul (M * A)
    rw [mul_zero] at hup'
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup'
      (he₁.mono fun n h => h.1) (he₁.mono fun n h => h.2)
  have herr_eq : ∀ n, dcSynthErr M b A Bφ (κ (n * B)) A0 (gevOrder (κ (n * B))) n =
      M * A * dcSynthRatio b Bφ (κ (n * B)) n ^ (2 * gevOrder (κ (n * B)) + 2) +
        M * b * dcLogWeight 1 * (1 / κ (n * B)) * A0 := fun _ => rfl
  have he : Tendsto (fun n : ℕ => dcSynthErr M b A Bφ (κ (n * B)) A0 (gevOrder (κ (n * B))) n)
      atTop (𝓝 0) := by
    simp_rw [herr_eq]
    simpa using he₁t.add ((hinv.const_mul (M * b * dcLogWeight 1)).mul_const A0)
  refine ⟨he, ?_⟩
  have hLE : Tendsto (fun n => Real.log (κ (n * B)) *
      dcSynthErr M b A Bφ (κ (n * B)) A0 (gevOrder (κ (n * B))) n ^ 2) atTop (𝓝 0) := by
    simp_rw [herr_eq]
    exact log_mul_sq_tendsto (k := fun n => κ (n * B)) hK he₁
  -- Note `OverlapGrowthSuperGevrey κ` implies `OverlapGrowthGevrey 1 κ` on the subsequence,
  -- giving `emLip / κ → M' 0 * A' 1`.
  have hK'ℓ1 : Tendsto (fun n : ℕ => ((n * B : ℕ) : ℝ) / κ (n * B) /
      Real.log (Real.log (κ (n * B))) ^ (1 : ℝ)) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ hKW
    filter_upwards [hev] with n ⟨hk1, _, hℓ9, hll1, _⟩
    rw [Real.rpow_one]
    have hℓ_pos : 0 < Real.log (Real.log (κ (n * B))) := by linarith
    have hsq1 : 1 ≤ Real.log (Real.log (Real.log (κ (n * B)))) ^ 2 := by nlinarith only [hll1]
    have hnum0 : 0 ≤ ((n * B : ℕ) : ℝ) / κ (n * B) :=
      div_nonneg (Nat.cast_nonneg _) (by linarith only [hk1])
    exact div_le_div_of_nonneg_left hnum0 hℓ_pos (le_mul_of_one_le_right hℓ_pos.le hsq1)
  have hev1 : ∀ᶠ n : ℕ in atTop, 1 ≤ κ (n * B) ∧ 1 ≤ n ∧
      1 ≤ Real.log (Real.log (κ (n * B))) ∧
      1 ≤ ((n * B : ℕ) : ℝ) / κ (n * B) / Real.log (Real.log (κ (n * B))) ^ (1 : ℝ) := by
    filter_upwards [hev, hK'ℓ1.eventually_ge_atTop 1] with n ⟨hk1, hn, hℓ9, _, _⟩ h1
    exact ⟨hk1, hn, by linarith, h1⟩
  exact tendsto_synthLevy_of he hLE (gevrey_lip_tendsto zero_le_one hK hK'ℓ1 hev1 M' A')

private theorem abs_iteratedDeriv_mollify_le_dcLogWeight {φ g : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφ1 : VanishesOff φ) (hg : Continuous g)
    {Mg : ℝ} (hgM : ∀ t, |g t| ≤ Mg) {m : ℝ} (hm : 0 < m) {A Bφ : ℝ}
    (hA : ∀ q, ∫ t, |iteratedDeriv q φ t| ≤ A * Bφ ^ q * dcLogWeight q)
    (l : ℕ) (x : ℝ) :
    |iteratedDeriv l (mollify g φ m) x| ≤ Mg * A * (Bφ * m) ^ l * dcLogWeight l := by
  have hMg : 0 ≤ Mg := (abs_nonneg _).trans (hgM 0)
  have hψ : ContDiff ℝ ∞ (iteratedDeriv l (dilate m φ)) := by
    rw [iteratedDeriv_eq_iterate]; exact (contDiff_dilate_smooth hφ m).iterate_deriv l
  have hψc := hasCompactSupport_iteratedDeriv (hasCompactSupport_dilate_of hφ1 hm) l
  rw [iteratedDeriv_mollify hφ hφ1 hg hm l]
  refine (abs_integral_mul_le_sup_mul hgM
    (hψ.continuous.integrable_of_hasCompactSupport hψc) x).trans ?_
  rw [integral_abs_iteratedDeriv_dilate hφ hm l]
  have := mul_le_mul_of_nonneg_left (hA l) (mul_nonneg hMg (pow_nonneg hm.le l))
  calc Mg * (m ^ l * ∫ t, |iteratedDeriv l φ t|) = Mg * m ^ l * ∫ t, |iteratedDeriv l φ t| := by
        ring
    _ ≤ Mg * m ^ l * (A * Bφ ^ l * dcLogWeight l) := this
    _ = _ := by rw [mul_pow]; ring

theorem nonneg_iff_atomicFamilies_nonneg_of_stable_superGevrey {Φ : (ℝ → ℝ) → ℝ}
    (hΦ : StableForm Φ) {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφ1 : VanishesOff φ)
    (hφint : ∫ s, φ s = 1) {A Bφ : ℝ} (hBφ : 0 ≤ Bφ)
    (hA : ∀ q, ∫ t, |iteratedDeriv q φ t| ≤ A * Bφ ^ q * dcLogWeight q)
    {κ : ℕ → ℝ} (hκ : OverlapGrowthSuperGevrey κ) :
    (∀ g : ℝ → ℝ, ContDiff ℝ 2 g → HasCompactSupport g → 0 ≤ Φ g) ↔
      ∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ, 0 ≤ Φ (atomicTest N x (dilate (κ N) φ)) := by
  constructor
  · intro hpos
    filter_upwards [hκ.1.eventually_gt_atTop 0] with N hk x
    obtain ⟨h2, hc⟩ := atomicTest_dilate_mem (hφ.of_le (natCast_le_infty 2)) hφ1 hk N x
    exact hpos _ h2 hc
  · intro H
    by_contra hneg0
    push Not at hneg0
    obtain ⟨g, hg, hgc, hneg⟩ := hneg0
    -- 1. Mollify `g` by `φ` to obtain a negative `dcLogWeight` test `G`
    obtain ⟨Rg, Mg, Lg, hRg, hgR, hgM, hgL⟩ := exists_test_bounds hg hgc
    obtain ⟨Err0, hErr0, hle0⟩ := hΦ.2 g hg hgc (Rg + 1) (by linarith)
      (fun u hu => hgR u (by linarith))
    obtain ⟨he0, hV0, -, -⟩ := tendsto_mollifyErr Lg (∫ s, |φ s|) Mg (∫ s, |deriv φ s|) (Rg + 1)
    obtain ⟨m0, hm0_err, hm0_1⟩ := (((hErr0 _ _ he0 hV0).eventually (gt_mem_nhds
      (show (0 : ℝ) < -Φ g by linarith))).and (eventually_ge_atTop 1)).exists
    have hm0_r : (1 : ℝ) ≤ m0 := by exact_mod_cast hm0_1
    have hMg : 0 ≤ Mg := (abs_nonneg _).trans (hgM 0)
    have hA0 : 0 ≤ A := by
      have := (integral_nonneg fun t => abs_nonneg (iteratedDeriv 0 φ t)).trans (hA 0)
      simpa [dcLogWeight_zero] using this
    set G := mollify g φ m0
    have hG : ContDiff ℝ ∞ G := contDiff_mollify hφ hφ1 hg.continuous (by linarith)
    have hGc : HasCompactSupport G :=
      hasCompactSupport_of_vanishes (mollify_supportedIn hφ1 hgR hm0_r)
    have hGneg : Φ G < 0 := by
      obtain ⟨hD2, hDR, hsup, hlip⟩ := mollify_perturbation hφ hφ1 hφint hg hgR hgM hgL hm0_r
      have h := hle0 _ _ _ _ hD2 hDR hsup hlip hm0_r
      have he' : (fun u => g u + (mollify g φ m0 u - g u)) = G := by funext u; dsimp [G]; ring
      rw [he'] at h; linarith
    have hGM : ∀ l t, |iteratedDeriv l G t| ≤ (Mg * A) * (Bφ * m0) ^ l * dcLogWeight l :=
      fun l t => abs_iteratedDeriv_mollify_le_dcLogWeight hφ hφ1 hg.continuous hgM
        (by linarith) hA l t
    -- 2. Synthesize `G` at super-Gevrey overlap growth
    have hG2 : ContDiff ℝ 2 G := hG.of_le (natCast_le_infty 2)
    obtain ⟨R, -, -, _, hGR, -, -⟩ := exists_test_bounds hG2 hGc
    obtain ⟨Err, hErr, hle⟩ := hΦ.2 G hG2 hGc (R + 1) (by linarith)
      (fun u hu => hGR u (by linarith))
    set B := blockSize R
    have hB : 1 ≤ B := one_le_blockSize R
    obtain ⟨he, hV⟩ := tendsto_dcLogSynthesis hκ hB (M := Mg * A) (b := Bφ * m0) (A := A)
      (Bφ := Bφ) (A0 := ∫ s, |φ s|) (by positivity) (by positivity) hBφ
      (fun l => (Mg * A) * (Bφ * m0) ^ l * dcLogWeight l)
      (fun q => ∫ s, |iteratedDeriv q φ s|) (R + 1)
    have h1 := (hErr _ _ he hV).eventually (gt_mem_nhds (show (0 : ℝ) < -Φ G by linarith))
    have hNB : Tendsto (fun n : ℕ => n * B) atTop atTop :=
      tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_right n hB) tendsto_id
    have h3 := hNB.eventually (hκ.1.eventually_ge_atTop 1)
    have hfr : ∃ᶠ N : ℕ in atTop, ∃ x : ℕ → ℝ, Φ (atomicTest N x (dilate (κ N) φ)) < 0 := by
      rw [Filter.frequently_atTop]
      intro a
      obtain ⟨n, hn1, hk, hn3, hna⟩ :=
        (h1.and (h3.and ((eventually_ge_atTop 2).and (eventually_ge_atTop a)))).exists
      refine ⟨n * B, hna.trans (Nat.le_mul_of_pos_right n hB), ?_⟩
      obtain ⟨x, D, hx, hD2, hDR, hsup, hlip⟩ := exists_dcLogSynthesis hφ hφ1 hφint hG hGR
        (by positivity) (by positivity) hBφ hGM hA hn3 hk (gevOrder (κ (n * B)))
      refine ⟨x, ?_⟩
      rw [hx, hΦ.1 _ (hG2.add hD2) (hGc.add (hasCompactSupport_of_vanishes hDR))]
      have := hle D _ _ _ hD2 hDR hsup hlip hk
      linarith
    obtain ⟨N, ⟨x, hx⟩, hN⟩ := (hfr.and_eventually H).exists
    exact absurd (hN x) (not_le.mpr hx)

theorem riemannHypothesis_iff_atomicFamilies_nonneg_of_superGevrey {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφ1 : VanishesOff φ) (hφint : ∫ s, φ s = 1)
    {A Bφ : ℝ} (hBφ : 0 ≤ Bφ)
    (hA : ∀ q, ∫ t, |iteratedDeriv q φ t| ≤ A * Bφ ^ q * dcLogWeight q)
    {κ : ℕ → ℝ} (hκ : OverlapGrowthSuperGevrey κ) :
    RiemannHypothesis ↔ ∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ,
      0 ≤ weilQuad (atomicTest N x (dilate (κ N) φ)) :=
  RHTower.WeilSpectral.riemannHypothesis_iff_real_weilPositive.trans
    (nonneg_iff_atomicFamilies_nonneg_of_stable_superGevrey stableForm_weilQuad
      hφ hφ1 hφint hBφ hA hκ)

/-! ### 5. The super-Gevrey schedule `c_N = (log log N) (log log log N)^β` (`β > 2`) -/

/-- Super-Gevrey overlap ratio `(log log N) (log log log N)^β`. -/
def superGevreyRatio (β : ℝ) (N : ℕ) : ℝ :=
  Real.log (Real.log N) * Real.log (Real.log (Real.log N)) ^ β

/-- For every `β` and every `ε > 0`, `(log log N) (log log log N)^β = o((log log N)^{1+ε})`,
placing `superGevreyRatio β` strictly below all Gevrey power schedules. -/
theorem superGevreyRatio_isLittleO_loglog_rpow (β : ℝ) {ε : ℝ} (hε : 0 < ε) :
    superGevreyRatio β =o[atTop] fun N : ℕ => Real.log (Real.log N) ^ (1 + ε) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hll : Tendsto (fun N : ℕ => Real.log (Real.log N)) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  have hdiv : Tendsto (fun N : ℕ => superGevreyRatio β N /
      Real.log (Real.log N) ^ (1 + ε)) atTop (𝓝 0) := by
    refine ((isLittleO_log_rpow_rpow_atTop β hε).tendsto_div_nhds_zero.comp hll).congr' ?_
    filter_upwards [hll.eventually_gt_atTop 0] with N hpos
    simp only [Function.comp, superGevreyRatio]
    rw [Real.rpow_add hpos, Real.rpow_one]
    field_simp [hpos.ne']
  exact Asymptotics.isLittleO_of_tendsto'
    (by
      filter_upwards [hll.eventually_gt_atTop 0] with N hpos h0
      exact absurd h0 (Real.rpow_pos_of_pos hpos (1 + ε)).ne')
    hdiv

/-- For every `β > 2`, the dilation sequence `N / ((log log N) (log log log N)^β)` satisfies
`OverlapGrowthSuperGevrey`. -/
theorem overlapGrowthSuperGevrey_of_two_lt {β : ℝ} (hβ : 2 < β) :
    OverlapGrowthSuperGevrey fun N : ℕ => (N : ℝ) / superGevreyRatio β N := by
  have hβ0 : 0 < β := by linarith
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hll : Tendsto (fun N : ℕ => Real.log (Real.log N)) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  have hlll : Tendsto (fun N : ℕ => Real.log (Real.log (Real.log N))) atTop atTop :=
    Real.tendsto_log_atTop.comp hll
  have hratio_le_sq : ∀ᶠ N : ℕ in atTop, superGevreyRatio β N ≤ Real.log N ^ (2 : ℝ) := by
    have hlit := (superGevreyRatio_isLittleO_loglog_rpow β one_pos).bound one_pos
    filter_upwards [hlit, hll.eventually_gt_atTop 1, hlog.eventually_gt_atTop 1] with N hN hll1 hl1
    rw [one_mul, Real.norm_of_nonneg (by
        unfold superGevreyRatio
        have h1 : 0 < Real.log (Real.log (Real.log N)) := Real.log_pos hll1
        exact mul_nonneg (by linarith) (Real.rpow_pos_of_pos h1 β).le),
      Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _),
      show (1 : ℝ) + 1 = 2 by norm_num] at hN
    have hll_le_l : Real.log (Real.log N) ≤ Real.log N :=
      (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
    exact hN.trans (Real.rpow_le_rpow (by linarith) hll_le_l (by norm_num))
  have hκ_log2 : Tendsto (fun N : ℕ => (N : ℝ) / Real.log N ^ (2 : ℝ)) atTop atTop := by
    have ho := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) one_pos).tendsto_div_nhds_zero
    have hpos : ∀ᶠ y : ℝ in atTop, 0 < Real.log y ^ (2 : ℝ) / y ^ (1 : ℝ) := by
      filter_upwards [eventually_gt_atTop 1] with y hy
      exact div_pos (Real.rpow_pos_of_pos (Real.log_pos hy) 2)
        (Real.rpow_pos_of_pos (by linarith only [hy]) 1)
    have hinv := (tendsto_nhdsWithin_iff.mpr ⟨ho, hpos⟩).inv_tendsto_nhdsGT_zero
    refine (hinv.comp tendsto_natCast_atTop_atTop).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N _
    simp only [Function.comp, Real.rpow_one, Pi.inv_apply, inv_div]
  have hκ : Tendsto (fun N : ℕ => (N : ℝ) / superGevreyRatio β N) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ hκ_log2
    filter_upwards [hratio_le_sq, hll.eventually_gt_atTop 1, hlll.eventually_gt_atTop 1,
      eventually_ge_atTop 1] with N hle hll1 hlll1 _
    have hrpos : 0 < superGevreyRatio β N :=
      mul_pos (by linarith) (Real.rpow_pos_of_pos (by linarith) β)
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg N) hrpos hle
  refine ⟨hκ, ?_⟩
  have hup : Tendsto (fun N : ℕ => Real.log (Real.log (Real.log N)) ^ (β - 2)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp hlll
  refine tendsto_atTop_mono' atTop ?_ hup
  have hκ_lll := Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp
    (Real.tendsto_log_atTop.comp hκ))
  filter_upwards [hll.eventually_ge_atTop 2, hlll.eventually_ge_atTop 2,
    eventually_ge_atTop 1, hκ.eventually_ge_atTop 2,
    (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hκ)).eventually_ge_atTop 2,
    hκ_lll.eventually_ge_atTop 1] with N hll2 hlll2 hN1 hκ2 hκll2 hκlll1
  dsimp only [Function.comp_def] at hκll2 hκlll1
  set cN := superGevreyRatio β N
  have hcN1 : 1 ≤ cN := by
    dsimp only [cN, superGevreyRatio]
    have : 1 ≤ Real.log (Real.log (Real.log N)) ^ β :=
      Real.one_le_rpow (by linarith) hβ0.le
    nlinarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hκ_le_N : (N : ℝ) / cN ≤ N := div_le_self hN0.le hcN1
  have hl_le : Real.log ((N : ℝ) / cN) ≤ Real.log N :=
    Real.log_le_log (by linarith) hκ_le_N
  have hll_le : Real.log (Real.log ((N : ℝ) / cN)) ≤ Real.log (Real.log N) :=
    Real.log_le_log (Real.log_pos (by linarith only [hκ2])) hl_le
  have hlll_le : Real.log (Real.log (Real.log ((N : ℝ) / cN))) ≤
      Real.log (Real.log (Real.log N)) :=
    Real.log_le_log (by linarith) hll_le
  have hquot : (N : ℝ) / ((N : ℝ) / cN) = cN := div_div_cancel₀ hN0.ne'
  rw [hquot]
  have hden_le : Real.log (Real.log ((N : ℝ) / cN)) *
      Real.log (Real.log (Real.log ((N : ℝ) / cN))) ^ 2 ≤
      Real.log (Real.log N) * Real.log (Real.log (Real.log N)) ^ 2 :=
    mul_le_mul hll_le (pow_le_pow_left₀ (by linarith) hlll_le 2) (sq_nonneg _) (by linarith)
  have hden_pos : 0 < Real.log (Real.log ((N : ℝ) / cN)) *
      Real.log (Real.log (Real.log ((N : ℝ) / cN))) ^ 2 :=
    mul_pos (by linarith only [hκll2]) (sq_pos_of_pos (by linarith only [hκlll1]))
  calc Real.log (Real.log (Real.log N)) ^ (β - 2)
      = cN / (Real.log (Real.log N) * Real.log (Real.log (Real.log N)) ^ 2) := by
          dsimp only [cN, superGevreyRatio]
          have hpos : 0 < Real.log (Real.log (Real.log N)) := by linarith
          have hrp : Real.log (Real.log (Real.log N)) ^ β =
              Real.log (Real.log (Real.log N)) ^ (β - 2) *
                Real.log (Real.log (Real.log N)) ^ 2 := by
            rw [← Real.rpow_natCast, ← Real.rpow_add hpos]
            congr 1; push_cast; ring
          rw [hrp]
          field_simp [(by linarith : Real.log (Real.log N) ≠ 0), hpos.ne']
    _ ≤ cN / (Real.log (Real.log ((N : ℝ) / cN)) *
          Real.log (Real.log (Real.log ((N : ℝ) / cN))) ^ 2) :=
        div_le_div_of_nonneg_left (by linarith) hden_pos hden_le

/-- **Super-Gevrey RH equivalence for the single fixed profile `steklovDCProfile`**:
for every `β > 2`, `RiemannHypothesis` holds if and only if `weilQuad` is eventually nonnegative on
the atomic families of `steklovDCProfile` at overlap ratio `(log log N) (log log log N)^β`. -/
theorem riemannHypothesis_iff_steklovDCProfile_nonneg_superGevrey {β : ℝ} (hβ : 2 < β) :
    RiemannHypothesis ↔ ∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ,
      0 ≤ weilQuad (atomicTest N x
        (dilate ((N : ℝ) / superGevreyRatio β N) steklovDCProfile)) :=
  riemannHypothesis_iff_atomicFamilies_nonneg_of_superGevrey
    contDiff_steklovDCProfile steklovDCProfile_vanishesOff integral_steklovDCProfile
    (by norm_num) integral_abs_iteratedDeriv_steklovDCProfile_le
    (overlapGrowthSuperGevrey_of_two_lt hβ)

end GaloisForLFunctions.TransMetzlerWeilPositivity

#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.contDiff_steklovDCProfile
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.steklovDCProfile_vanishesOff
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.integral_steklovDCProfile
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.integral_abs_iteratedDeriv_steklovDCProfile_le
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.superGevreyRatio_isLittleO_loglog_rpow
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.riemannHypothesis_iff_steklovDCProfile_nonneg_superGevrey
