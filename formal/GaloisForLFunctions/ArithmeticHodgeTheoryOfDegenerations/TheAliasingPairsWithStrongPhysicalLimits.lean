import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheAliasingMeanIsStableUnderL1Convergence
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.AtomicSynthesisRecoversLipschitzTests
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheCanonicalCriticalClockEntersFromTheNegativeSide
import GaloisForLFunctions.HTGeometry.ReflectionIntegral
import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStateKernelBounds

/-!
# Aliasing pairs with strong physical limits

The exponential change of variables preserves L¹ distance and transports the
spline's aliasing mean to the logarithmic coordinate. On a fixed terminal
window, the scaled alias multiplier has Lipschitz constant `O(c⁹)`. The adjoint
synthesis estimate therefore transfers its integral limit to arbitrary bounded
coefficient vectors whose physical sources converge strongly in L¹.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Set Finset

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open ArithmeticDegenerationTheory SpacingScaleHarmonicAnalysis ArithmeticElectrostatics

private def expDensity (F : ℝ → ℝ) (x : ℝ) : ℝ :=
  if 0 < x then F (Real.log x) / x else 0

private theorem exp_mul_expDensity (F : ℝ → ℝ) (y : ℝ) :
    Real.exp y * expDensity F (Real.exp y) = F y := by
  rw [expDensity, if_pos (Real.exp_pos y), Real.log_exp]
  field_simp

private theorem expDensity_zero {F : ℝ → ℝ} {x : ℝ} (hx : x ≤ 0) :
    expDensity F x = 0 := by simp only [expDensity, if_neg (not_lt.mpr hx)]

private theorem integral_expDensity (F : ℝ → ℝ) :
    (∫ x, expDensity F x) = ∫ y, F y := by
  have h := HTGeometry.integral_Ioi_comp_exp (expDensity F)
  have he : (∫ x in Ioi (0 : ℝ), expDensity F x) = ∫ x, expDensity F x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    exact expDensity_zero (not_lt.mp hx)
  rw [he] at h
  simpa only [exp_mul_expDensity] using h

private theorem integrable_expDensity {F : ℝ → ℝ} (hF : Integrable F) :
    Integrable (expDensity F) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul
    (f := Real.exp) (f' := Real.exp) (s := (Set.univ : Set ℝ))
    MeasurableSet.univ
    (fun y _ => (Real.hasDerivAt_exp y).hasDerivWithinAt)
    Real.exp_injective.injOn (expDensity F)
  rw [Set.image_univ, Real.range_exp] at h
  have hi : IntegrableOn (expDensity F) (Ioi 0) := h.mpr (by
    simpa only [abs_of_pos (Real.exp_pos _), smul_eq_mul, exp_mul_expDensity,
      integrableOn_univ] using hF)
  have he : (Ioi (0 : ℝ)).indicator (expDensity F) = expDensity F := by
    funext x
    by_cases hx : x ∈ Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, expDensity_zero (not_lt.mp hx)]
  simpa only [he] using hi.integrable_indicator measurableSet_Ioi

private theorem expDensity_sub (F G : ℝ → ℝ) (x : ℝ) :
    expDensity F x - expDensity G x = expDensity (fun y => F y - G y) x := by
  unfold expDensity
  split_ifs <;> ring

private theorem integral_abs_expDensity_sub (F G : ℝ → ℝ) :
    (∫ x, |expDensity F x - expDensity G x|) = ∫ y, |F y - G y| := by
  simp_rw [expDensity_sub]
  have he : (fun x => |expDensity (fun y => F y - G y) x|) =
      expDensity (fun y => |F y - G y|) := by
    funext x
    unfold expDensity
    split_ifs with hx
    · rw [abs_div, abs_of_pos hx]
    · exact abs_zero
  rw [he, integral_expDensity]

private theorem expDensity_supported {F : ℝ → ℝ} {a : ℝ}
    (hs : ∀ y, y < a → F y = 0) :
    ∀ x, x < Real.exp a → expDensity F x = 0 := by
  intro x hx
  unfold expDensity
  split_ifs with hx0
  · rw [hs (Real.log x) ((Real.log_lt_iff_lt_exp hx0).mpr hx), zero_div]
  · rfl

private theorem integral_expDensity_mul (F b : ℝ → ℝ) :
    (∫ x, expDensity F x * b x) = ∫ y, F y * b (Real.exp y) := by
  have he : (fun x => expDensity F x * b x) =
      expDensity (fun y => F y * b (Real.exp y)) := by
    funext x
    unfold expDensity
    split_ifs with hx
    · dsimp only
      rw [Real.exp_log hx]; ring
    · exact zero_mul _
  rw [he, integral_expDensity]

/-- The tilted-spline aliasing mean in the logarithmic coordinate. -/
theorem tendsto_integrable_logarithmic_tilted_aliasDensity {F : ℝ → ℝ} {a : ℝ}
    (hF : Integrable F) (hs : ∀ y, y < a → F y = 0) :
    Tendsto (fun c : ℝ => ∫ y, F y *
      (c ^ 8 * aliasDensity tiltedUnitSpline (c * Real.exp y))) atTop
      (𝓝 ((7 / 2 : ℝ) * (∫ u, tiltedUnitSpline u ^ 2) * tiltedJordanOne *
        ∫ y, F y * Real.exp (-(8 * y)))) := by
  have h := tendsto_integrable_tilted_aliasDensity (integrable_expDensity hF)
    (Real.exp_pos a) (expDensity_supported hs)
  simp_rw [integral_expDensity_mul] at h
  have he (y : ℝ) : (Real.exp y ^ 8)⁻¹ = Real.exp (-(8 * y)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_neg]
    norm_num
  simp_rw [he] at h
  exact h

/-- Strong L¹ convergence also preserves the aliasing mean in logarithmic coordinates. -/
theorem tendsto_logarithmic_tilted_aliasDensity_of_L1_convergence {ι : Type*} {l : Filter ι} {F : ℝ → ℝ}
    {Fₙ : ι → ℝ → ℝ} {a : ℝ} (hF : Integrable F) (hFₙ : ∀ n, Integrable (Fₙ n))
    (hs : ∀ y, y < a → F y = 0) (hsₙ : ∀ n y, y < a → Fₙ n y = 0)
    (hL1 : Tendsto (fun n => ∫ y, ‖Fₙ n y - F y‖) l (𝓝 0))
    {c : ι → ℝ} (hc : Tendsto c l atTop) :
    Tendsto (fun n => ∫ y, Fₙ n y *
      (c n ^ 8 * aliasDensity tiltedUnitSpline (c n * Real.exp y))) l
      (𝓝 ((7 / 2 : ℝ) * (∫ u, tiltedUnitSpline u ^ 2) * tiltedJordanOne *
        ∫ y, F y * Real.exp (-(8 * y)))) := by
  have hd : Tendsto (fun n => ∫ x, ‖expDensity (Fₙ n) x - expDensity F x‖)
      l (𝓝 0) := by
    simpa only [Real.norm_eq_abs, integral_abs_expDensity_sub] using hL1
  have h := tendsto_tilted_aliasDensity_of_L1_convergence (integrable_expDensity hF)
    (fun n => integrable_expDensity (hFₙ n)) (Real.exp_pos a) (expDensity_supported hs)
    (fun n => expDensity_supported (hsₙ n)) hd hc
  simp_rw [integral_expDensity_mul] at h
  have he (y : ℝ) : (Real.exp y ^ 8)⁻¹ = Real.exp (-(8 * y)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_neg]
    norm_num
  simp_rw [he] at h
  exact h

private def terminalClamp (A y : ℝ) : ℝ := max (-A) (min 0 y)

private theorem terminalClamp_mem {A : ℝ} (hA : 0 ≤ A) (y : ℝ) :
    terminalClamp A y ∈ Icc (-A) 0 :=
  ⟨le_max_left _ _, max_le (neg_nonpos.mpr hA) (min_le_left _ _)⟩

private theorem terminalClamp_eq {A y : ℝ} (hy : y ∈ Icc (-A) 0) :
    terminalClamp A y = y := by
  rw [terminalClamp, min_eq_right hy.2, max_eq_right hy.1]

private theorem exists_lipschitz_exp_terminalClamp {A : ℝ} (hA : 0 ≤ A) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ y z,
      |Real.exp (terminalClamp A y) - Real.exp (terminalClamp A z)| ≤ L * |y - z| := by
  obtain ⟨L, hL0, hL⟩ := ArithmeticCriticalityTheory.exists_lipschitz_bound_on_Icc
    (f := Real.exp) Real.contDiff_exp (-A) 0
  have hclip : LipschitzWith 1 (terminalClamp A) :=
    (LipschitzWith.id.const_min 0).const_max (-A)
  refine ⟨L, hL0, fun y z => ?_⟩
  have h := hL _ (terminalClamp_mem hA z) _ (terminalClamp_mem hA y)
  have hc := hclip.dist_le_mul y z
  simp only [Real.dist_eq, NNReal.coe_one, one_mul] at hc
  exact h.trans (mul_le_mul_of_nonneg_left hc hL0)

private theorem exists_tilted_aliasDensity_bounds {δ : ℝ} (hδ : 0 < δ) :
    ∃ B L : ℝ, 0 ≤ B ∧ 0 ≤ L ∧
      (∀ s, δ ≤ s → |aliasDensity tiltedUnitSpline s| ≤ B) ∧
      (∀ s t, δ ≤ s → δ ≤ t →
        |aliasDensity tiltedUnitSpline s - aliasDensity tiltedUnitSpline t| ≤ L * |s - t|) := by
  have hC : 0 ≤ tiltedDecayConst := by unfold tiltedDecayConst; positivity
  let B := tiltedDecayConst * (2 * Real.pi * δ) ^ (-(8 : ℝ)) *
    ∑' k : ℕ, ((k : ℝ) + 1) ^ (-(8 : ℝ))
  let L := 4 * Real.pi * Real.sqrt tiltedDecayConst * (∫ u, |tiltedUnitSpline u|) *
    (2 * Real.pi * δ) ^ (-(8 : ℝ) / 2) *
      ∑' k : ℕ, ((k : ℝ) + 1) ^ (1 - (8 : ℝ) / 2)
  refine ⟨|B|, |L|, abs_nonneg _, abs_nonneg _, ?_, ?_⟩
  · intro s hs
    rw [abs_of_nonneg (aliasDensity_nonneg _)]
    exact (aliasDensity_le contDiff_tiltedUnitSpline tiltedUnitSpline_support
      (by norm_num : (1 : ℝ) < 8) tiltedUnitSpline_decay hC hδ hs).trans (le_abs_self B)
  · intro s t hs ht
    have h := abs_aliasDensity_sub_le contDiff_tiltedUnitSpline tiltedUnitSpline_support
      (by norm_num : (4 : ℝ) < 8) hC tiltedUnitSpline_decay hδ hs ht
    exact h.trans (mul_le_mul_of_nonneg_right (le_abs_self L) (abs_nonneg _))

/-- On a fixed terminal window the scaled aliasing multiplier has polynomial
Lipschitz growth, uniformly over the overlap. -/
theorem exists_scaled_tilted_aliasMultiplier_lipschitz {g : ℝ → ℝ} {A : ℝ}
    (hA : 0 ≤ A) (hs : ∀ y, y ∉ Icc (-A) 0 → g y = 0)
    {Lg : NNReal} (hg : LipschitzWith Lg g) {B : ℝ} (hB : ∀ y, |g y| ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, 1 ≤ c →
      LipschitzWith (Real.toNNReal (C * c ^ 9))
        (fun y => g y * (c ^ 8 * aliasDensity tiltedUnitSpline (c * Real.exp y))) := by
  obtain ⟨Ba, La, hBa0, hLa0, hBa, hLa⟩ :=
    exists_tilted_aliasDensity_bounds (Real.exp_pos (-A))
  obtain ⟨Le, hLe0, hLe⟩ := exists_lipschitz_exp_terminalClamp hA
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  let C := (Lg : ℝ) * Ba + B * La * Le
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, fun c hc => ?_⟩
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have harg (y : ℝ) : Real.exp (-A) ≤ c * Real.exp (terminalClamp A y) :=
    (Real.exp_le_exp.mpr (terminalClamp_mem hA y).1).trans
      (le_mul_of_one_le_left (Real.exp_pos _).le hc)
  have he (y : ℝ) : g y * (c ^ 8 * aliasDensity tiltedUnitSpline (c * Real.exp y)) =
      g y * (c ^ 8 * aliasDensity tiltedUnitSpline (c * Real.exp (terminalClamp A y))) := by
    by_cases hy : y ∈ Icc (-A) 0
    · rw [terminalClamp_eq hy]
    · rw [hs y hy, zero_mul, zero_mul]
  refine LipschitzWith.of_dist_le_mul fun y z => ?_
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (mul_nonneg hC (pow_nonneg hc0.le 9)),
    he y, he z]
  have hgd := hg.dist_le_mul y z
  rw [Real.dist_eq, Real.dist_eq] at hgd
  have had : |aliasDensity tiltedUnitSpline (c * Real.exp (terminalClamp A y)) -
      aliasDensity tiltedUnitSpline (c * Real.exp (terminalClamp A z))| ≤
        La * (c * (Le * |y - z|)) := by
    refine (hLa _ _ (harg y) (harg z)).trans ?_
    rw [← mul_sub, _root_.abs_mul, abs_of_pos hc0]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hLe y z) hc0.le) hLa0
  have hp : c ^ 8 ≤ c ^ 9 := pow_le_pow_right₀ hc (by norm_num)
  have hdiff : g y * (c ^ 8 * aliasDensity tiltedUnitSpline (c * Real.exp (terminalClamp A y))) -
      g z * (c ^ 8 * aliasDensity tiltedUnitSpline (c * Real.exp (terminalClamp A z))) =
      (g y - g z) * c ^ 8 * aliasDensity tiltedUnitSpline (c * Real.exp (terminalClamp A y)) +
        g z * c ^ 8 * (aliasDensity tiltedUnitSpline (c * Real.exp (terminalClamp A y)) -
          aliasDensity tiltedUnitSpline (c * Real.exp (terminalClamp A z))) := by ring
  rw [hdiff]
  calc
    _ ≤ (|g y - g z| * c ^ 8) * |aliasDensity tiltedUnitSpline (c * Real.exp (terminalClamp A y))| +
        (|g z| * c ^ 8) * |aliasDensity tiltedUnitSpline (c * Real.exp (terminalClamp A y)) -
          aliasDensity tiltedUnitSpline (c * Real.exp (terminalClamp A z))| := by
      refine (abs_add_le _ _).trans ?_
      apply add_le_add <;>
        rw [_root_.abs_mul, _root_.abs_mul, abs_of_nonneg (pow_nonneg hc0.le 8)]
    _ ≤ (((Lg : ℝ) * |y - z|) * c ^ 8) * Ba +
        (B * c ^ 8) * (La * (c * (Le * |y - z|))) := by
      apply add_le_add
      · exact mul_le_mul (mul_le_mul_of_nonneg_right hgd (pow_nonneg hc0.le 8))
          (hBa _ (harg y)) (abs_nonneg _) (by positivity)
      · exact mul_le_mul (mul_le_mul_of_nonneg_right (hB z) (pow_nonneg hc0.le 8))
          had (abs_nonneg _) (by positivity)
    _ ≤ C * c ^ 9 * |y - z| := by
      have h := mul_le_mul_of_nonneg_left hp
        (mul_nonneg (mul_nonneg Lg.coe_nonneg hBa0) (abs_nonneg (y - z)))
      dsimp only [C]
      nlinarith only [h]

private theorem integrable_mul_bounded {F g : ℝ → ℝ} (hF : Integrable F)
    (hg : Continuous g) {B : ℝ} (hB : ∀ y, |g y| ≤ B) :
    Integrable (fun y => F y * g y) := by
  refine (hF.norm.mul_const B).mono' (hF.aestronglyMeasurable.mul hg.aestronglyMeasurable) ?_
  filter_upwards with y
  rw [norm_mul, Real.norm_eq_abs (g y)]
  exact mul_le_mul_of_nonneg_left (hB y) (norm_nonneg _)

private theorem tendsto_L1_mul_bounded {ι : Type*} {l : Filter ι} {F : ℝ → ℝ} {Fₙ : ι → ℝ → ℝ}
    (hF : Integrable F) (hFₙ : ∀ n, Integrable (Fₙ n))
    (hL1 : Tendsto (fun n => ∫ y, ‖Fₙ n y - F y‖) l (𝓝 0))
    {g : ℝ → ℝ} (hg : Continuous g) {B : ℝ} (hB : ∀ y, |g y| ≤ B) :
    Tendsto (fun n => ∫ y, ‖Fₙ n y * g y - F y * g y‖) l (𝓝 0) := by
  have hi := integrable_mul_bounded hF hg hB
  have hin (n : ι) := integrable_mul_bounded (hFₙ n) hg hB
  refine squeeze_zero (fun n => integral_nonneg fun y => norm_nonneg _) (fun n => ?_)
    (by simpa only [mul_zero] using hL1.const_mul B)
  rw [← integral_const_mul]
  apply integral_mono ((hin n).sub hi).norm (((hFₙ n).sub hF).norm.const_mul B)
  intro y
  change ‖Fₙ n y * g y - F y * g y‖ ≤ B * ‖Fₙ n y - F y‖
  rw [← sub_mul, norm_mul, Real.norm_eq_abs (g y), mul_comm B]
  exact mul_le_mul_of_nonneg_left (hB y) (norm_nonneg _)

private theorem integrable_normalized_tilted_atomicTest {c : ℝ} (hc : 0 < c)
    (N : ℕ) (x : ℕ → ℝ) :
    Integrable (normalizedCentredAtomicTest tiltedUnitSpline x c N) := by
  by_cases hN : N = 0
  · subst N
    have he : normalizedCentredAtomicTest tiltedUnitSpline x c 0 = fun _ => 0 := by
      funext y
      simp only [normalizedCentredAtomicTest, Nat.cast_zero, Real.sqrt_zero, zero_div, zero_mul]
    rw [he]
    exact integrable_zero ℝ ℝ volume
  have hw : 0 < c / N := div_pos hc (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN))
  have hcs : HasCompactSupport (centredAtomicTest tiltedUnitSpline x c N) := by
    exact (hasCompactSupport_atomicTest (tiltedUnitSpline_atom_support hw) N x).comp_homeomorph
      (Homeomorph.addRight (Real.log N))
  exact Continuous.integrable_of_hasCompactSupport
    ((contDiff_centredAtomicTest contDiff_tiltedUnitSpline x c N).continuous.const_mul
      (Real.sqrt N / c)) hcs.mul_left

/-- The discrete tilted-spline aliasing pairs with a strong physical limit.
The synthesis error permits oscillatory multipliers on every critical schedule. -/
theorem tendsto_discrete_tilted_aliasing_pair_of_synthesis_rate_along_filter
    {l : Filter ℕ} (hl : l ≤ atTop)
    {x : ℕ → ℕ → ℝ} {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N)
    (hc : Tendsto c l atTop)
    (hrate : Tendsto (fun N : ℕ => c N ^ 10 / N *
      Real.sqrt (∑ n ∈ Icc 1 N, x N n ^ 2)) l (𝓝 0))
    {F g : ℝ → ℝ} (hF : Integrable F)
    (hL1 : Tendsto (fun N => ∫ y,
      ‖normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N y - F y‖) l (𝓝 0))
    {A : ℝ} (hA : 0 ≤ A) (hs : ∀ y, y ∉ Icc (-A) 0 → g y = 0)
    {Lg : NNReal} (hg : LipschitzWith Lg g) {Bg : ℝ} (hBg : ∀ y, |g y| ≤ Bg) :
    Tendsto (fun N : ℕ => (∫ u, tiltedUnitSpline u) / Real.sqrt N *
      ∑ n ∈ Icc 1 N, x N n * g (Real.log n - Real.log N) *
        (c N ^ 8 * aliasDensity tiltedUnitSpline (c N * n / N))) l
      (𝓝 ((7 / 2 : ℝ) * (∫ u, tiltedUnitSpline u ^ 2) * tiltedJordanOne *
        ∫ y, (F y * g y) * Real.exp (-(8 * y)))) := by
  let Fₙ := fun N => normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N
  have hFn (N : ℕ) : Integrable (Fₙ N) :=
    integrable_normalized_tilted_atomicTest (zero_lt_one.trans_le (hc1 N)) N (x N)
  have hFg := integrable_mul_bounded hF hg.continuous hBg
  have hFng (N : ℕ) := integrable_mul_bounded (hFn N) hg.continuous hBg
  have hg0 (y : ℝ) (hy : y < -A) : g y = 0 := hs y (fun hm => (not_le.mpr hy) hm.1)
  have hprod := tendsto_L1_mul_bounded hF hFn hL1 hg.continuous hBg
  have hmain := tendsto_logarithmic_tilted_aliasDensity_of_L1_convergence hFg hFng
    (fun y hy => by rw [hg0 y hy, mul_zero])
    (fun N y hy => by rw [hg0 y hy, mul_zero]) hprod hc
  obtain ⟨C, hC, hLip⟩ := exists_scaled_tilted_aliasMultiplier_lipschitz hA hs hg hBg
  let S := fun N : ℕ => (∫ u, tiltedUnitSpline u) / Real.sqrt N *
    ∑ n ∈ Icc 1 N, x N n * g (Real.log n - Real.log N) *
      (c N ^ 8 * aliasDensity tiltedUnitSpline (c N * n / N))
  have herror : Tendsto (fun N =>
      (∫ y, (Fₙ N y * g y) * (c N ^ 8 * aliasDensity tiltedUnitSpline (c N * Real.exp y))) -
        S N) l (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (by
      simpa only [mul_zero] using hrate.const_mul ((∫ u, |tiltedUnitSpline u|) * C))
    filter_upwards [(eventually_ge_atTop 1).filter_mono hl] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hcn : 0 < c N := zero_lt_one.trans_le (hc1 N)
    have h := abs_integral_normalizedCentredAtomicTest_mul_sub_le
      contDiff_tiltedUnitSpline.continuous tiltedUnitSpline_support (hLip (c N) (hc1 N)) hcn hN (x N)
    rw [Real.coe_toNNReal _ (mul_nonneg hC (pow_nonneg hcn.le 9))] at h
    have hsum : (∑ n ∈ Icc 1 N, x N n *
        (g (Real.log n - Real.log N) *
          (c N ^ 8 * aliasDensity tiltedUnitSpline (c N * Real.exp (Real.log n - Real.log N))))) =
        ∑ n ∈ Icc 1 N, x N n * g (Real.log n - Real.log N) *
          (c N ^ 8 * aliasDensity tiltedUnitSpline (c N * n / N)) := by
      apply sum_congr rfl
      intro n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      rw [Real.exp_sub, Real.exp_log hn0, Real.exp_log hN0,
        show c N * ((n : ℝ) / N) = c N * n / N by ring]
      ring
    rw [hsum] at h
    have he : (∫ y, Fₙ N y *
        (g y * (c N ^ 8 * aliasDensity tiltedUnitSpline (c N * Real.exp y)))) =
        ∫ y, (Fₙ N y * g y) * (c N ^ 8 * aliasDensity tiltedUnitSpline (c N * Real.exp y)) := by
      apply integral_congr_ae
      filter_upwards with y
      ring
    change |(∫ y, Fₙ N y *
      (g y * (c N ^ 8 * aliasDensity tiltedUnitSpline (c N * Real.exp y)))) - S N| ≤ _ at h
    rw [he] at h
    rw [Real.norm_eq_abs]
    refine h.trans (le_of_eq ?_)
    ring
  simpa only [sub_sub_cancel, sub_zero] using hmain.sub herror

/-- The synthesis-rate pairing along the full sequence of horizons. -/
theorem tendsto_discrete_tilted_aliasing_pair_of_synthesis_rate
    {x : ℕ → ℕ → ℝ} {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N)
    (hc : Tendsto c atTop atTop)
    (hrate : Tendsto (fun N : ℕ => c N ^ 10 / N *
      Real.sqrt (∑ n ∈ Icc 1 N, x N n ^ 2)) atTop (𝓝 0))
    {F g : ℝ → ℝ} (hF : Integrable F)
    (hL1 : Tendsto (fun N => ∫ y,
      ‖normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N y - F y‖) atTop (𝓝 0))
    {A : ℝ} (hA : 0 ≤ A) (hs : ∀ y, y ∉ Icc (-A) 0 → g y = 0)
    {Lg : NNReal} (hg : LipschitzWith Lg g) {Bg : ℝ} (hBg : ∀ y, |g y| ≤ Bg) :
    Tendsto (fun N : ℕ => (∫ u, tiltedUnitSpline u) / Real.sqrt N *
      ∑ n ∈ Icc 1 N, x N n * g (Real.log n - Real.log N) *
        (c N ^ 8 * aliasDensity tiltedUnitSpline (c N * n / N))) atTop
      (𝓝 ((7 / 2 : ℝ) * (∫ u, tiltedUnitSpline u ^ 2) * tiltedJordanOne *
        ∫ y, (F y * g y) * Real.exp (-(8 * y)))) := by
  exact tendsto_discrete_tilted_aliasing_pair_of_synthesis_rate_along_filter le_rfl
    hc1 hc hrate hF hL1 hA hs hg hBg

/-- The discrete pairing limit for coefficient vectors with bounded Euclidean norm. -/
theorem tendsto_discrete_tilted_aliasing_pair_of_L1_convergence
    {x : ℕ → ℕ → ℝ} {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N)
    (hc : Tendsto c atTop atTop)
    (hrate : Tendsto (fun N : ℕ => c N ^ 10 / N) atTop (𝓝 0))
    {B : ℝ} (hB : ∀ N, Real.sqrt (∑ n ∈ Icc 1 N, x N n ^ 2) ≤ B)
    {F g : ℝ → ℝ} (hF : Integrable F)
    (hL1 : Tendsto (fun N => ∫ y,
      ‖normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N y - F y‖) atTop (𝓝 0))
    {A : ℝ} (hA : 0 ≤ A) (hs : ∀ y, y ∉ Icc (-A) 0 → g y = 0)
    {Lg : NNReal} (hg : LipschitzWith Lg g) {Bg : ℝ} (hBg : ∀ y, |g y| ≤ Bg) :
    Tendsto (fun N : ℕ => (∫ u, tiltedUnitSpline u) / Real.sqrt N *
      ∑ n ∈ Icc 1 N, x N n * g (Real.log n - Real.log N) *
        (c N ^ 8 * aliasDensity tiltedUnitSpline (c N * n / N))) atTop
      (𝓝 ((7 / 2 : ℝ) * (∫ u, tiltedUnitSpline u ^ 2) * tiltedJordanOne *
        ∫ y, (F y * g y) * Real.exp (-(8 * y)))) := by
  have hweighted : Tendsto (fun N : ℕ => c N ^ 10 / N *
      Real.sqrt (∑ n ∈ Icc 1 N, x N n ^ 2)) atTop (𝓝 0) := by
    refine squeeze_zero (fun N => by have := hc1 N; positivity) (fun N => ?_)
      (by simpa only [mul_zero] using hrate.const_mul B)
    have hn := hc1 N
    exact (mul_le_mul_of_nonneg_left (hB N) (by positivity : 0 ≤ c N ^ 10 / N)).trans_eq
      (mul_comm _ _)
  exact tendsto_discrete_tilted_aliasing_pair_of_synthesis_rate hc1 hc hweighted hF hL1 hA hs hg hBg

/-- Every critical overlap schedule has the discrete aliasing limit along
strong L¹ limits of the physical sources. -/
theorem tendsto_criticalCurve_discrete_aliasing_pair_of_L1_convergence
    {x : ℕ → ℕ → ℝ} {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N)
    {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    {B : ℝ} (hB : ∀ N, Real.sqrt (∑ n ∈ Icc 1 N, x N n ^ 2) ≤ B)
    {F g : ℝ → ℝ} (hF : Integrable F)
    (hL1 : Tendsto (fun N => ∫ y,
      ‖normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N y - F y‖) atTop (𝓝 0))
    {A : ℝ} (hA : 0 ≤ A) (hs : ∀ y, y ∉ Icc (-A) 0 → g y = 0)
    {Lg : NNReal} (hg : LipschitzWith Lg g) {Bg : ℝ} (hBg : ∀ y, |g y| ≤ Bg) :
    Tendsto (fun N : ℕ => (∫ u, tiltedUnitSpline u) / Real.sqrt N *
      ∑ n ∈ Icc 1 N, x N n * g (Real.log n - Real.log N) *
        (c N ^ 8 * aliasDensity tiltedUnitSpline (c N * n / N))) atTop
      (𝓝 ((7 / 2 : ℝ) * (∫ u, tiltedUnitSpline u ^ 2) * tiltedJordanOne *
        ∫ y, (F y * g y) * Real.exp (-(8 * y)))) := by
  have hrate : Tendsto (fun N : ℕ => c N ^ 10 / N) atTop (𝓝 0) := by
    simpa only [pow_zero, mul_one] using criticalCurve_pow_log_div_natCast hc1 hR hcrit 10 0
  exact tendsto_discrete_tilted_aliasing_pair_of_L1_convergence hc1
    (criticalCurve_facts hc1 hR hcrit).1 hrate hB hF hL1 hA hs hg hBg

/-- Polynomial growth of the coefficient norm is absorbed by the critical clock. -/
theorem tendsto_criticalCurve_aliasing_pair_of_polynomial_norm_bound_along_filter
    {l : Filter ℕ} (hl : l ≤ atTop)
    {x : ℕ → ℕ → ℝ} {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N)
    {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    {B : ℝ} {m : ℕ}
    (hB : ∀ N, Real.sqrt (∑ n ∈ Icc 1 N, x N n ^ 2) ≤ B * c N ^ m)
    {F g : ℝ → ℝ} (hF : Integrable F)
    (hL1 : Tendsto (fun N => ∫ y,
      ‖normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N y - F y‖) l (𝓝 0))
    {A : ℝ} (hA : 0 ≤ A) (hs : ∀ y, y ∉ Icc (-A) 0 → g y = 0)
    {Lg : NNReal} (hg : LipschitzWith Lg g) {Bg : ℝ} (hBg : ∀ y, |g y| ≤ Bg) :
    Tendsto (fun N : ℕ => (∫ u, tiltedUnitSpline u) / Real.sqrt N *
      ∑ n ∈ Icc 1 N, x N n * g (Real.log n - Real.log N) *
        (c N ^ 8 * aliasDensity tiltedUnitSpline (c N * n / N))) l
      (𝓝 ((7 / 2 : ℝ) * (∫ u, tiltedUnitSpline u ^ 2) * tiltedJordanOne *
        ∫ y, (F y * g y) * Real.exp (-(8 * y)))) := by
  have hrate : Tendsto (fun N : ℕ => c N ^ (10 + m) / N) atTop (𝓝 0) := by
    simpa only [pow_zero, mul_one] using criticalCurve_pow_log_div_natCast hc1 hR hcrit (10 + m) 0
  have hweighted : Tendsto (fun N : ℕ => c N ^ 10 / N *
      Real.sqrt (∑ n ∈ Icc 1 N, x N n ^ 2)) atTop (𝓝 0) := by
    refine squeeze_zero (fun N => by have := hc1 N; positivity) (fun N => ?_)
      (by simpa only [mul_zero] using hrate.const_mul B)
    have hn := hc1 N
    calc
      _ ≤ c N ^ 10 / N * (B * c N ^ m) :=
        mul_le_mul_of_nonneg_left (hB N) (by positivity)
      _ = B * (c N ^ (10 + m) / N) := by rw [pow_add]; ring
  exact tendsto_discrete_tilted_aliasing_pair_of_synthesis_rate_along_filter hl hc1
    ((criticalCurve_facts hc1 hR hcrit).1.mono_left hl) (hweighted.mono_left hl) hF hL1 hA hs hg hBg

/-- Polynomial coefficient growth preserves the aliasing limit along all horizons. -/
theorem tendsto_criticalCurve_aliasing_pair_of_polynomial_norm_bound
    {x : ℕ → ℕ → ℝ} {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N)
    {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    {B : ℝ} {m : ℕ}
    (hB : ∀ N, Real.sqrt (∑ n ∈ Icc 1 N, x N n ^ 2) ≤ B * c N ^ m)
    {F g : ℝ → ℝ} (hF : Integrable F)
    (hL1 : Tendsto (fun N => ∫ y,
      ‖normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N y - F y‖) atTop (𝓝 0))
    {A : ℝ} (hA : 0 ≤ A) (hs : ∀ y, y ∉ Icc (-A) 0 → g y = 0)
    {Lg : NNReal} (hg : LipschitzWith Lg g) {Bg : ℝ} (hBg : ∀ y, |g y| ≤ Bg) :
    Tendsto (fun N : ℕ => (∫ u, tiltedUnitSpline u) / Real.sqrt N *
      ∑ n ∈ Icc 1 N, x N n * g (Real.log n - Real.log N) *
        (c N ^ 8 * aliasDensity tiltedUnitSpline (c N * n / N))) atTop
      (𝓝 ((7 / 2 : ℝ) * (∫ u, tiltedUnitSpline u ^ 2) * tiltedJordanOne *
        ∫ y, (F y * g y) * Real.exp (-(8 * y)))) := by
  exact tendsto_criticalCurve_aliasing_pair_of_polynomial_norm_bound_along_filter le_rfl
    hc1 hR hcrit hB hF hL1 hA hs hg hBg

#print axioms tendsto_criticalCurve_aliasing_pair_of_polynomial_norm_bound

#print axioms tendsto_logarithmic_tilted_aliasDensity_of_L1_convergence
#print axioms tendsto_criticalCurve_discrete_aliasing_pair_of_L1_convergence

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
