import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheSplineHasUniformFourthDerivativeRegularizations
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.LogarithmicOverlapOfTheCompleteWeilMatrixIsTheRiemannHypothesis

/-!
# Fourth-order synthesis for the tilted spline

The recentred tilted spline is a fixed scalar multiple of `splineProbe (4x)`.
Its smooth regularizations have uniform derivative bounds through order four,
so the smooth Euler–Maclaurin estimates can pass to this `C²` profile.
-/

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace GaloisForLFunctions.SpacingScaleHarmonicAnalysis

open BiScaleUncertainty.ChebyshevGauge RenormalizedArithmeticPotentialTheory
  ArithmeticElectrostatics

private theorem integral_abs_iteratedDeriv_scale_four {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (c : ℝ) (q : ℕ) :
    (∫ x, |iteratedDeriv q (fun x => c * f (4 * x)) x|) =
      |c| * ((4 : ℝ) ^ q / 4) * ∫ x, |iteratedDeriv q f x| := by
  have hq : (q : ℕ∞ω) ≤ ∞ := by exact_mod_cast (le_top : (q : ℕ∞) ≤ ⊤)
  have hs : ContDiff ℝ ∞ (fun x => f (4 * x)) :=
    hf.comp (contDiff_const.mul contDiff_id)
  have hd : iteratedDeriv q (fun x => c * f (4 * x)) =
      fun x => (c * (4 : ℝ) ^ q) * iteratedDeriv q f (4 * x) := by
    funext x
    rw [iteratedDeriv_const_mul c ((hs.of_le hq).contDiffAt),
      iteratedDeriv_comp_const_mul (hf.of_le hq)]
    ring
  simp_rw [hd, abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  rw [integral_const_mul, Measure.integral_comp_mul_left (fun x => |iteratedDeriv q f x|) 4]
  norm_num only [smul_eq_mul, show |(4 : ℝ)⁻¹| = 1 / 4 by norm_num]
  ring

/-- Recentering the unit spline cancels its translation. -/
theorem recentred_tiltedUnitSpline_eq (s : ℝ) :
    recentredProfile tiltedUnitSpline s =
      (2 * ∫ u, tiltedUnitSpline u)⁻¹ * splineProbe (4 * s) := by
  unfold recentredProfile tiltedUnitSpline atomDilate
  rw [show ((s + 1) / 2 - 1 / 2) / (1 / 8 : ℝ) = 4 * s by ring]
  rw [div_eq_mul_inv, mul_comm]

private theorem scaled_regularization_bounds {f : ℝ → ℝ} (C : ℝ)
    (hsource : ∃ A : ℕ → ℝ, (∀ q, 0 ≤ A q) ∧ ∀ ε : ℝ, 0 < ε →
      ∃ G : ℝ → ℝ, ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧
        (∀ x, |G x - f x| ≤ ε) ∧
        ∀ q : ℕ, q ≤ 4 → (∫ x, |iteratedDeriv q G x|) ≤ A q) :
    ∃ A : ℕ → ℝ, (∀ q, 0 ≤ A q) ∧ (∫ x, |C * f (4 * x)|) ≤ A 0 ∧
      ∀ ε : ℝ, 0 < ε → ∃ G : ℝ → ℝ, ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧
        (∀ x, |G x - C * f (4 * x)| ≤ ε) ∧
        ∀ q : ℕ, q ≤ 4 → (∫ x, |iteratedDeriv q G x|) ≤ A q := by
  obtain ⟨A, hA0, hA⟩ := hsource
  let J := ∫ x, |C * f (4 * x)|
  have hJ : 0 ≤ J := integral_nonneg fun x => abs_nonneg _
  have hcoeff : ∀ q : ℕ, 0 ≤ |C| * ((4 : ℝ) ^ q / 4) := fun q =>
    mul_nonneg (abs_nonneg C) (div_nonneg (pow_nonneg (by norm_num) q) (by norm_num))
  have hbase : ∀ q, 0 ≤ |C| * ((4 : ℝ) ^ q / 4) * A q :=
    fun q => mul_nonneg (hcoeff q) (hA0 q)
  refine ⟨fun q => |C| * ((4 : ℝ) ^ q / 4) * A q + J,
    fun q => add_nonneg (hbase q) hJ, le_add_of_nonneg_left (hbase 0), ?_⟩
  intro ε hε
  let δ := ε / (|C| + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨G, hG, hGc, hclose, hGd⟩ := hA δ hδ
  have hscale : ContDiff ℝ ∞ (fun x => G (4 * x)) :=
    hG.comp (contDiff_const.mul contDiff_id)
  have hcscale : HasCompactSupport (fun x => G (4 * x)) :=
    hGc.comp_smul (by norm_num : (4 : ℝ) ≠ 0)
  refine ⟨fun x => C * G (4 * x), contDiff_const.mul hscale, hcscale.mul_left, ?_, ?_⟩
  · intro x
    have hεδ : |C| * δ ≤ ε := by
      calc
        |C| * δ ≤ (|C| + 1) * δ :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hδ.le
        _ = ε := by
          rw [mul_comm]
          exact div_mul_cancel₀ ε (by positivity)
    calc
      |C * G (4 * x) - C * f (4 * x)| =
          |C| * |G (4 * x) - f (4 * x)| := by
        rw [← mul_sub, abs_mul]
      _ ≤ |C| * δ := mul_le_mul_of_nonneg_left (hclose _) (abs_nonneg C)
      _ ≤ ε := hεδ
  · intro q hq
    rw [integral_abs_iteratedDeriv_scale_four hG C q]
    exact (mul_le_mul_of_nonneg_left (hGd q hq) (hcoeff q)).trans
      (le_add_of_nonneg_right hJ)

/-- The normalized spline inherits uniform derivative bounds through order four
from its box regularizations. -/
theorem exists_recentred_tiltedUnitSpline_regularization_bounds :
    ∃ A : ℕ → ℝ, (∀ q, 0 ≤ A q) ∧
      (∫ x, |recentredProfile tiltedUnitSpline x|) ≤ A 0 ∧ ∀ ε : ℝ, 0 < ε →
      ∃ G : ℝ → ℝ, ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧
        (∀ x, |G x - recentredProfile tiltedUnitSpline x| ≤ ε) ∧
        ∀ q : ℕ, q ≤ 4 → (∫ x, |iteratedDeriv q G x|) ≤ A q := by
  have h := scaled_regularization_bounds (2 * ∫ u, tiltedUnitSpline u)⁻¹
    exists_splineProbe_regularization_bounds
  simpa only [← recentred_tiltedUnitSpline_eq] using h

private theorem leibnizBound_mono_up_to {M A B : ℕ → ℝ} (hM : ∀ q, 0 ≤ M q)
    {p i : ℕ} (hAB : ∀ q, q ≤ p → A q ≤ B q) (hi : i ≤ p) :
    leibnizBound M A i ≤ leibnizBound M B i := by
  unfold leibnizBound
  refine Finset.sum_le_sum fun j _ => ?_
  exact mul_le_mul_of_nonneg_left (hAB (i - j) ((Nat.sub_le i j).trans hi))
    (mul_nonneg (Nat.cast_nonneg _) (hM j))

private theorem emConst_mono_up_to {M A B : ℕ → ℝ} (hM : ∀ q, 0 ≤ M q) (m : ℕ)
    (hAB : ∀ q, q ≤ 2 * m + 2 → A q ≤ B q) : emConst M A m ≤ emConst M B m := by
  unfold emConst
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Finset.sum_le_sum fun i hi => leibnizBound_mono_up_to hM hAB
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))

/-- Uniform approximation with bounded first four derivative norms transfers
both the fourth-order quadrature error and the synthesis Lipschitz estimate.
The limiting profile need only be continuous. -/
theorem fourthOrderSynthesis_of_uniform_regularizations {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) {A : ℕ → ℝ}
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ G : ℝ → ℝ,
      ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧ (∀ x, |G x - φ x| ≤ ε) ∧
      ∀ q : ℕ, q ≤ 4 → (∫ x, |iteratedDeriv q G x|) ≤ A q)
    {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) {R : ℝ}
    (hFs : ∀ t, t ∉ Icc (-R) R → F t = 0) {M : ℕ → ℝ}
    (hM : ∀ q t, |iteratedDeriv q F t| ≤ M q) (hM0 : ∀ q, 0 ≤ M q)
    {n₀ N : ℕ} (hn₀ : 2 ≤ n₀) (hN : Real.log n₀ + 2 * R < Real.log (1 + N))
    {k : ℝ} (hk : 1 ≤ k) :
    (∀ r, |atomicTest (N + 1) (emWeights F (Real.log n₀ + R)) (dilate k φ)
      (r + (Real.log n₀ + R)) - ∫ v, F v * dilate k φ (r - v)| ≤
        emConst M A 1 * (k / n₀) ^ 4) ∧
    ∀ u v, |atomicTest (N + 1) (emWeights F (Real.log n₀ + R)) (dilate k φ)
      (u + (Real.log n₀ + R)) -
        atomicTest (N + 1) (emWeights F (Real.log n₀ + R)) (dilate k φ)
          (v + (Real.log n₀ + R))| ≤
      k * (M 0 * A 1 + emConst M (fun q => A (q + 1)) 0 * (k / n₀) ^ 2) * |u - v| := by
  have hk0 : 0 < k := by linarith
  choose ψ hψ hψc hclose hderiv using
    fun j : ℕ => happrox (1 / ((j : ℝ) + 1)) (by positivity)
  have he : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : ∀ x, Tendsto (fun j => ψ j x) atTop (𝓝 (φ x)) := by
    intro x
    have hlo := (tendsto_const_nhds (x := φ x)).sub he
    have hhi := (tendsto_const_nhds (x := φ x)).add he
    simp only [sub_zero, add_zero] at hlo hhi
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi (fun j => ?_) (fun j => ?_)
    · linarith only [(abs_le.mp (hclose j x)).1]
    · linarith only [(abs_le.mp (hclose j x)).2]
  have hsum : ∀ r, Tendsto
      (fun j => atomicTest (N + 1) (emWeights F (Real.log n₀ + R)) (dilate k (ψ j)) r)
      atTop (𝓝 (atomicTest (N + 1) (emWeights F (Real.log n₀ + R)) (dilate k φ) r)) := by
    intro r
    unfold atomicTest dilate
    exact tendsto_finsetSum _ fun n _ =>
      ((hlim (k * (r - Real.log n))).const_mul k).const_mul _
  -- Uniform approximation bounds every convolution integrand by one fixed integrable function.
  obtain ⟨C, hC⟩ := hφc.exists_bound_of_continuous hφ
  have hψbound : ∀ j x, |ψ j x| ≤ C + 1 := by
    intro j x
    have he1 : 1 / ((j : ℝ) + 1) ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      linarith [j.cast_nonneg (α := ℝ)]
    have hCx : |φ x| ≤ C := by simpa only [Real.norm_eq_abs] using hC x
    calc
      |ψ j x| ≤ |ψ j x - φ x| + |φ x| := by
        simpa only [sub_add_cancel] using abs_add_le (ψ j x - φ x) (φ x)
      _ ≤ C + 1 := by linarith only [hclose j x, he1, hCx]
  have hFi : Integrable F :=
    hF.continuous.integrable_of_hasCompactSupport (HasCompactSupport.intro isCompact_Icc hFs)
  have hint : ∀ r, Tendsto (fun j => ∫ v, F v * dilate k (ψ j) (r - v))
      atTop (𝓝 (∫ v, F v * dilate k φ (r - v))) := by
    intro r
    apply tendsto_integral_filter_of_dominated_convergence
      (fun v => (k * (C + 1)) * |F v|)
    · exact Eventually.of_forall fun j =>
        (hF.continuous.mul ((contDiff_dilate_smooth (hψ j) k).continuous.comp
          (continuous_const.sub continuous_id))).aestronglyMeasurable
    · exact Eventually.of_forall fun j => Eventually.of_forall fun v => by
        simp only [Real.norm_eq_abs, dilate, abs_mul, abs_of_pos hk0]
        calc
          |F v| * (k * |ψ j (k * (r - v))|) ≤ |F v| * (k * (C + 1)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (hψbound j _) hk0.le) (abs_nonneg _)
          _ = (k * (C + 1)) * |F v| := mul_comm _ _
    · exact hFi.abs.const_mul _
    · exact Eventually.of_forall fun v =>
        ((hlim (k * (r - v))).const_mul k).const_mul (F v)
  constructor
  · intro r
    refine le_of_tendsto ((hsum (r + (Real.log n₀ + R))).sub (hint r)).abs
      (Eventually.of_forall fun j => ?_)
    have h := abs_emSynth_dilate_sub_le (hψ j) (hψc j) hF hFs hM hM0 hn₀ hN hk 1 r
    have hc := emConst_mono_up_to hM0 1 (fun q hq => hderiv j q (by omega))
    exact h.trans (mul_le_mul_of_nonneg_right hc (by positivity))
  · intro u v
    refine le_of_tendsto ((hsum (u + (Real.log n₀ + R))).sub
      (hsum (v + (Real.log n₀ + R)))).abs (Eventually.of_forall fun j => ?_)
    apply abs_sub_le_of_hasDerivAt
      (fun r => hasDerivAt_atomicTest
        ((contDiff_dilate_smooth (hψ j) k).differentiable (by simp))
        (N + 1) (emWeights F (Real.log n₀ + R)) (Real.log n₀ + R) r)
    intro r
    refine (abs_emSynth_deriv_le (hψ j) (hψc j) hF hFs hM hM0 hn₀ hN hk r).trans ?_
    have hfirst : (∫ s, |deriv (ψ j) s|) ≤ A 1 := by
      simpa only [iteratedDeriv_one] using hderiv j 1 (by omega)
    have hc := emConst_mono_up_to hM0 0
      (fun q hq => hderiv j (q + 1) (by omega))
    exact mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_left hfirst (hM0 0))
        (mul_le_mul_of_nonneg_right hc (sq_nonneg _))) hk0.le

/-- Fourth-order synthesis gives a compactly supported `C²` perturbation.
Uniform regularization controls quadrature; the unit integral controls the
approximate identity error. -/
theorem exists_fourthOrderSynthesis {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφ1 : VanishesOff φ) (hφint : ∫ s, φ s = 1) {A : ℕ → ℝ}
    (hAint : (∫ s, |φ s|) ≤ A 0)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ G : ℝ → ℝ,
      ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧ (∀ x, |G x - φ x| ≤ ε) ∧
      ∀ q : ℕ, q ≤ 4 → (∫ x, |iteratedDeriv q G x|) ≤ A q)
    {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) {R : ℝ} (hFR : SupportedIn R F)
    {M : ℕ → ℝ} (hM : ∀ l t, |iteratedDeriv l F t| ≤ M l) (hM0 : ∀ l, 0 ≤ M l)
    {n₀ : ℕ} (hn₀ : 2 ≤ n₀) {k : ℝ} (hk : 1 ≤ k) :
    ∃ (x : ℕ → ℝ) (D : ℝ → ℝ),
      atomicTest (n₀ * blockSize R) x (dilate k φ) =
        (fun u => F (u - (Real.log n₀ + R)) + D (u - (Real.log n₀ + R))) ∧
      ContDiff ℝ 2 D ∧ SupportedIn (R + 1) D ∧
      (∀ u, |D u| ≤ emErr M A 1 k n₀) ∧
      ∀ u v, |D u - D v| ≤ emLip M A k n₀ * |u - v| := by
  have hk0 : 0 < k := by linarith
  have hn₀1 : 1 ≤ n₀ := by omega
  have hB : 1 ≤ n₀ * blockSize R := by
    have : 1 ≤ blockSize R := by
      have h := Nat.le_ceil (1 + Real.exp (2 * R))
      have : (1 : ℝ) ≤ blockSize R := by
        have := Real.exp_pos (2 * R)
        simp only [blockSize] at h ⊢
        linarith
      exact_mod_cast this
    nlinarith
  obtain ⟨N, hNB⟩ : ∃ N : ℕ, n₀ * blockSize R = N + 1 :=
    ⟨n₀ * blockSize R - 1, by omega⟩
  have hN : Real.log n₀ + 2 * R < Real.log (1 + N) := by
    have := log_lt_log_block hn₀1 R
    rw [hNB] at this
    push_cast at this
    rwa [add_comm (N : ℝ) 1] at this
  have hψ : ContDiff ℝ 2 (dilate k φ) :=
    contDiff_const.mul (hφ.comp (contDiff_const.mul contDiff_id))
  have hFs : ∀ t, t ∉ Icc (-R) R → F t = 0 := fun t ht => hFR t (by
    simp only [mem_Icc, not_and_or, not_le] at ht
    rcases ht with ht | ht
    · exact lt_of_lt_of_le (by linarith) (neg_le_abs t)
    · exact lt_of_lt_of_le ht (le_abs_self t))
  have hFL : ∀ u v, |F u - F v| ≤ M 1 * |u - v| :=
    abs_sub_le_of_hasDerivAt
      (fun t => (hF.differentiable (by simp) t).hasDerivAt)
      (fun t => by simpa only [iteratedDeriv_one] using hM 1 t)
  obtain ⟨hquad, hS⟩ := fourthOrderSynthesis_of_uniform_regularizations hφ.continuous
    (hasCompactSupport_of_vanishes hφ1) happrox hF hFs hM hM0 hn₀ hN hk
  have hconv : ∀ r, |(∫ v, F v * dilate k φ (r - v)) - F r| ≤ M 1 * (1 / k) * A 0 := by
    intro r
    have h := abs_integral_mul_sub_le hF.continuous hψ.continuous
      (hasCompactSupport_of_vanishes fun s hs => dilate_vanishes hφ1 hk0 hs)
      (by rw [integral_dilate hk0, hφint])
      (fun s hs => dilate_vanishes hφ1 hk0 hs) hFL r
    rw [integral_abs_dilate hk0] at h
    exact h.trans (mul_le_mul_of_nonneg_left hAint
      (mul_nonneg (hM0 1) (one_div_pos.mpr hk0).le))
  let S : ℝ → ℝ := fun r =>
    atomicTest (N + 1) (emWeights F (Real.log n₀ + R)) (dilate k φ)
      (r + (Real.log n₀ + R))
  let D : ℝ → ℝ := fun r => S r - F r
  have hsup : ∀ r, |D r| ≤ emErr M A 1 k n₀ := by
    intro r
    calc
      |D r| = |(S r - ∫ v, F v * dilate k φ (r - v)) +
          ((∫ v, F v * dilate k φ (r - v)) - F r)| := by
        simp only [D]
        ring_nf
      _ ≤ emConst M A 1 * (k / n₀) ^ 4 + M 1 * (1 / k) * A 0 :=
        (abs_add_le _ _).trans (add_le_add (hquad r) (hconv r))
      _ = emErr M A 1 k n₀ := by norm_num only [emErr]
  have hlip : ∀ u v, |D u - D v| ≤ emLip M A k n₀ * |u - v| := by
    intro u v
    have e : D u - D v = (S u - S v) - (F u - F v) := by simp only [D]; ring
    rw [e]
    refine (abs_sub _ _).trans ?_
    have h := add_le_add (hS u v) (hFL u v)
    dsimp only [S] at h ⊢
    simpa only [emLip, add_mul] using h
  have hDsupp : SupportedIn (R + 1) D := by
    intro r hr
    have hS0 : S r = 0 := by
      simp only [S, atomicTest]
      refine Finset.sum_eq_zero fun n _ => ?_
      by_cases hn : |Real.log n - (Real.log n₀ + R)| ≤ R
      · have hk1 : 1 / k ≤ 1 := by rw [div_le_one hk0]; exact hk
        rw [dilate_vanishes hφ1 hk0 (by
          have := abs_sub_abs_le_abs_sub r (Real.log n - (Real.log n₀ + R))
          rw [show r + (Real.log n₀ + R) - Real.log n =
            r - (Real.log n - (Real.log n₀ + R)) by ring]
          linarith), mul_zero]
      · push Not at hn
        rw [emWeights, hFR _ hn, mul_zero, zero_mul]
    simp only [D, hS0, hFR r (by linarith), sub_zero]
  have hD2 : ContDiff ℝ 2 D :=
    ((contDiff_atomicTest hψ (N + 1) (emWeights F (Real.log n₀ + R))).comp
      (contDiff_id.add contDiff_const)).sub (hF.of_le (natCast_le_infty 2))
  refine ⟨emWeights F (Real.log n₀ + R), D, ?_, hD2, hDsupp, hsup, hlip⟩
  funext u
  simp only [D, S, hNB, sub_add_cancel]
  ring

#print axioms exists_recentred_tiltedUnitSpline_regularization_bounds
#print axioms fourthOrderSynthesis_of_uniform_regularizations
#print axioms exists_fourthOrderSynthesis

end GaloisForLFunctions.SpacingScaleHarmonicAnalysis
