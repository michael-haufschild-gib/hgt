import GaloisForLFunctions.ZeroConfigurationGeometry.BlindWindowsForPerturbedLattices
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.AnnihilatingTestsForSparseSpectra

/-!
# Spline bumps decay at an explicit rate

A smooth bump with an explicit decay constant. For `ε > 0` and `m ≥ 1`, convolve the normalized
smooth bump of radius `ε/2` with `m` normalized boxes of half-width `δ = ε/(2m)`
(`splineBump`). The result is smooth, nonnegative in spirit and even, supported in `[−ε, ε]`, and
its transform is `φ̂(w) (sin δw/δw)^m` (`paperFT_splineStage`).

* **Nonnegative probability transforms** (`norm_paperFT_le_of_prob`). A nonnegative density of mass
  one supported in `[−r, r]` has `|f̂(w)| ≤ e^{r|Im w|}`.
* **The sinc factor** (`one_add_mul_norm_sincC_le`). `(1 + δ|w|) |sin(δw)/(δw)| ≤ 2 e^{δ|Im w|}`.
* **Explicit decay** (`one_add_norm_pow_mul_norm_paperFT_splineBump_le`).
  `(1 + |w|)^m |b̂(w)| ≤ (2 + 4m/ε)^m e^{ε|Im w|}` for every `w`.
* **No loss on the imaginary axis** (`one_le_norm_paperFT_splineBump_I`). `|b̂(iy)| ≥ 1` for every
  real `y`: the bump is even with mass one, so `φ̂(iy) = ∫ φ(u) cosh(yu) du ≥ 1`, and
  `sin(iδy)/(iδy) = sinh(δy)/(δy) ≥ 1`.

These are the uniform window constants the local camera needs at bandwidth `a = λ log X`: the
decay constant depends on `m` and `ε` only through `(2 + 4m/ε)^m`.
-/

open MeasureTheory Complex Set Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open Zeta23 ArithmeticCastelnuovoSeveri

/-- **Transforms of probability densities.** A nonnegative density of mass one supported in
`[−r, r]` has `|f̂(w)| ≤ e^{r |Im w|}`. -/
theorem norm_paperFT_le_of_prob {h : ℝ → ℝ} {r : ℝ} (hint : Integrable h)
    (h0 : ∀ u, 0 ≤ h u) (hsupp : ∀ u, h u ≠ 0 → |u| ≤ r) (h1 : ∫ u, h u = 1) (w : ℂ) :
    ‖paperFT (fun u => (h u : ℂ)) w‖ ≤ Real.exp (r * |w.im|) := by
  rw [paperFT_def]
  have hbound : ∀ u : ℝ, ‖(h u : ℂ) * cexp (I * w * u)‖ ≤ h u * Real.exp (r * |w.im|) := by
    intro u
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (h0 u), Complex.norm_exp]
    by_cases hu : h u = 0
    · rw [hu, zero_mul, zero_mul]
    · refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (h0 u)
      have hre : (I * w * (u : ℂ)).re = -(w.im * u) := by simp [Complex.mul_re]
      rw [hre]
      have := hsupp u hu
      have hwu : |w.im * u| ≤ r * |w.im| := by
        rw [abs_mul, mul_comm]; exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
      linarith [neg_abs_le (w.im * u)]
  calc ‖∫ u : ℝ, (h u : ℂ) * cexp (I * w * u)‖ ≤ ∫ u, h u * Real.exp (r * |w.im|) :=
        norm_integral_le_of_norm_le (hint.mul_const _) (Eventually.of_forall hbound)
    _ = Real.exp (r * |w.im|) := by rw [integral_mul_const, h1, one_mul]

theorem norm_sin_le_exp (v : ℂ) : ‖Complex.sin v‖ ≤ Real.exp |v.im| := by
  rw [Complex.sin]
  have h1 : ‖cexp (-v * I)‖ = Real.exp v.im := by rw [Complex.norm_exp]; simp
  have h2 : ‖cexp (v * I)‖ = Real.exp (-v.im) := by rw [Complex.norm_exp]; simp
  rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_two]
  have := norm_sub_le (cexp (-v * I)) (cexp (v * I))
  rw [h1, h2] at this
  have e1 : Real.exp v.im ≤ Real.exp |v.im| := Real.exp_le_exp.mpr (le_abs_self _)
  have e2 : Real.exp (-v.im) ≤ Real.exp |v.im| := Real.exp_le_exp.mpr (neg_le_abs _)
  linarith

/-- The box `1_{[−δ, δ]}/(2δ)` as a real density. -/
theorem boxTest_eq_ofReal {δ : ℝ} (u : ℝ) :
    boxTest δ u = ((Set.indicator (Icc (-δ) δ) (fun _ => (2 * δ)⁻¹) u : ℝ) : ℂ) := by
  unfold boxTest Set.indicator
  split_ifs <;> simp

/-- **The sinc factor.** `(1 + δ|w|) |sin(δw)/(δw)| ≤ 2 e^{δ|Im w|}`. -/
theorem one_add_mul_norm_sincC_le {δ : ℝ} (hδ : 0 < δ) (w : ℂ) :
    (1 + δ * ‖w‖) * ‖sincC (δ * w)‖ ≤ 2 * Real.exp (δ * |w.im|) := by
  -- the trivial bound from the box density
  have htriv : ‖sincC (δ * w)‖ ≤ Real.exp (δ * |w.im|) := by
    rw [← paperFT_boxTest hδ w]
    have hfun : boxTest δ = fun u => ((Set.indicator (Icc (-δ) δ) (fun _ => (2 * δ)⁻¹) u : ℝ) :
        ℂ) := funext boxTest_eq_ofReal
    rw [hfun]
    refine norm_paperFT_le_of_prob ?_ (fun u => ?_) (fun u hu => ?_) ?_ w
    · exact (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
    · unfold Set.indicator; split_ifs <;> positivity
    · unfold Set.indicator at hu; split_ifs at hu with hmem
      · exact abs_le.mpr hmem
      · exact absurd rfl hu
    · rw [integral_indicator measurableSet_Icc, setIntegral_const,
        Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
      field_simp
      ring
  by_cases hw : δ * ‖w‖ ≤ 1
  · have : 1 + δ * ‖w‖ ≤ 2 := by linarith
    calc (1 + δ * ‖w‖) * ‖sincC (δ * w)‖ ≤ 2 * ‖sincC (δ * w)‖ :=
          mul_le_mul_of_nonneg_right this (norm_nonneg _)
      _ ≤ 2 * Real.exp (δ * |w.im|) := by linarith
  · replace hw := not_le.mp hw
    have hw0 : (δ : ℂ) * w ≠ 0 := by
      intro h
      have : ‖(δ : ℂ) * w‖ = 0 := by rw [h, norm_zero]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ] at this
      linarith
    have hnorm : ‖(δ : ℂ) * w‖ = δ * ‖w‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
    have hsinc : ‖sincC (δ * w)‖ * (δ * ‖w‖) ≤ Real.exp (δ * |w.im|) := by
      rw [sincC, if_neg hw0, norm_div, hnorm, div_mul_cancel₀ _ (by linarith)]
      have := norm_sin_le_exp ((δ : ℂ) * w)
      have him : ((δ : ℂ) * w).im = δ * w.im := by simp
      rwa [him, abs_mul, abs_of_pos hδ] at this
    have h1 : 1 + δ * ‖w‖ ≤ 2 * (δ * ‖w‖) := by linarith
    calc (1 + δ * ‖w‖) * ‖sincC (δ * w)‖ ≤ 2 * (δ * ‖w‖) * ‖sincC (δ * w)‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = 2 * (‖sincC (δ * w)‖ * (δ * ‖w‖)) := by ring
      _ ≤ 2 * Real.exp (δ * |w.im|) := by linarith

/-! ### The spline bump -/

/-- The smooth bump of radius `ε/2` and mass one. -/
def smoothBumpOf {ε : ℝ} (hε : 0 < ε) : ContDiffBump (0 : ℝ) :=
  ⟨ε / 4, ε / 2, by linarith, by linarith⟩

/-- The stages `b_0 = φ`, `b_{n+1} = b_n ⋆ 1_{[−δ, δ]}/(2δ)`. -/
def splineStage {ε : ℝ} (hε : 0 < ε) (δ : ℝ) : ℕ → ℝ → ℂ
  | 0 => fun u => ((smoothBumpOf hε).normed volume u : ℂ)
  | n + 1 => convolution (splineStage hε δ n) (boxTest δ) (ContinuousLinearMap.mul ℝ ℂ) volume

theorem tsupport_boxTest_subset (δ : ℝ) : tsupport (boxTest δ) ⊆ Icc (-δ) δ :=
  closure_minimal (support_boxTest_subset δ) isClosed_Icc

theorem tsupport_smoothBump {ε : ℝ} (hε : 0 < ε) :
    tsupport (fun u => ((smoothBumpOf hε).normed volume u : ℂ)) ⊆ Icc (-(ε / 2)) (ε / 2) := by
  have hBs : tsupport ((smoothBumpOf hε).normed volume) ⊆ Icc (-(ε / 2)) (ε / 2) := by
    rw [(smoothBumpOf hε).tsupport_normed_eq]
    intro u hu
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, show (smoothBumpOf hε).rOut = ε / 2 from rfl]
      at hu
    exact abs_le.mp hu
  exact (tsupport_comp_subset (g := fun y : ℝ => (y : ℂ)) Complex.ofReal_zero _).trans hBs

/-- The stages are smooth, supported in `[−(ε/2 + nδ), ε/2 + nδ]`, and have transform
`φ̂(w) (sin δw/δw)^n`. -/
theorem splineStage_props {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (splineStage hε δ n) ∧
      tsupport (splineStage hε δ n) ⊆ Icc (-(ε / 2 + n * δ)) (ε / 2 + n * δ) ∧
      ∀ w, paperFT (splineStage hε δ n) w =
        paperFT (splineStage hε δ 0) w * sincC (δ * w) ^ n := by
  induction n with
  | zero =>
    refine ⟨?_, ?_, fun w => by simp⟩
    · exact Complex.ofRealCLM.contDiff.comp (smoothBumpOf hε).contDiff_normed
    · have h := tsupport_smoothBump hε
      simp only [Nat.cast_zero, zero_mul, add_zero]
      exact h
  | succ n ih =>
    obtain ⟨hs, hsupp, hft⟩ := ih
    have hc : HasCompactSupport (splineStage hε δ n) :=
      IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) hsupp
    refine ⟨?_, ?_, fun w => ?_⟩
    · exact hc.contDiff_convolution_left (ContinuousLinearMap.mul ℝ ℂ) hs
        (boxTest_integrable δ).locallyIntegrable
    · refine closure_minimal (fun u hu => ?_) isClosed_Icc
      by_contra hout
      apply hu
      refine convolution_eq_zero_of_lt hsupp (tsupport_boxTest_subset δ) ?_
      by_contra hle
      push Not at hle
      apply hout
      have := abs_le.mp hle
      push_cast
      constructor <;> linarith
    · show paperFT (convolution (splineStage hε δ n) (boxTest δ) (ContinuousLinearMap.mul ℝ ℂ)
        volume) w = _
      rw [_root_.RHTower.WeilHerglotz.paperFT_convolution
        (hs.continuous.integrable_of_hasCompactSupport hc) (boxTest_integrable δ) hc
        (boxTest_hasCompactSupport δ), hft, paperFT_boxTest hδ, pow_succ, mul_assoc]

/-- The spline bump `b = φ ⋆ box_δ^{⋆m}` with `δ = ε/(2m)`. -/
def splineBump {ε : ℝ} (hε : 0 < ε) (m : ℕ) : ℝ → ℂ := splineStage hε (ε / (2 * m)) m

theorem contDiff_splineBump {ε : ℝ} (hε : 0 < ε) {m : ℕ} (hm : 1 ≤ m) :
    ContDiff ℝ (⊤ : ℕ∞) (splineBump hε m) :=
  (splineStage_props hε (by positivity) m).1

theorem tsupport_splineBump {ε : ℝ} (hε : 0 < ε) {m : ℕ} (hm : 1 ≤ m) :
    tsupport (splineBump hε m) ⊆ Icc (-ε) ε := by
  have h := (splineStage_props hε (show 0 < ε / (2 * m) by positivity) m).2.1
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have e : ε / 2 + m * (ε / (2 * m)) = ε := by field_simp; ring
  rw [e] at h
  exact h

/-- The smooth bump's transform is at most `e^{(ε/2)|Im w|}`. -/
theorem norm_paperFT_smoothBump_le {ε : ℝ} (hε : 0 < ε) (w : ℂ) :
    ‖paperFT (splineStage hε 1 0) w‖ ≤ Real.exp (ε / 2 * |w.im|) := by
  refine norm_paperFT_le_of_prob (h := (smoothBumpOf hε).normed volume)
    (smoothBumpOf hε).integrable_normed (fun u => (smoothBumpOf hε).nonneg_normed u)
    (fun u hu => ?_) (smoothBumpOf hε).integral_normed w
  have hmem : u ∈ Function.support ((smoothBumpOf hε).normed volume) := hu
  rw [(smoothBumpOf hε).support_normed_eq, Metric.mem_ball, Real.dist_eq, sub_zero] at hmem
  exact hmem.le

theorem splineStage_zero_eq {ε : ℝ} (hε : 0 < ε) (δ δ' : ℝ) :
    splineStage hε δ 0 = splineStage hε δ' 0 := rfl

/-- **Explicit decay.** `(1 + |w|)^m |b̂(w)| ≤ (2 + 4m/ε)^m e^{ε|Im w|}`. -/
theorem one_add_norm_pow_mul_norm_paperFT_splineBump_le {ε : ℝ} (hε : 0 < ε) {m : ℕ}
    (hm : 1 ≤ m) (w : ℂ) :
    (1 + ‖w‖) ^ m * ‖paperFT (splineBump hε m) w‖ ≤
      (2 + 4 * m / ε) ^ m * Real.exp (ε * |w.im|) := by
  set δ := ε / (2 * m) with hδdef
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hδ : 0 < δ := by positivity
  have hft := (splineStage_props hε hδ m).2.2 w
  have hφ := norm_paperFT_smoothBump_le hε w
  rw [splineStage_zero_eq hε δ 1] at hft
  -- `1 + |w| ≤ c (1 + δ|w|)` with `c = max 1 (1/δ)`
  set c := max 1 δ⁻¹ with hc
  have hc1 : 1 ≤ c := le_max_left _ _
  have hcw : 1 + ‖w‖ ≤ c * (1 + δ * ‖w‖) := by
    rcases le_total 1 δ with h | h
    · have : 1 + ‖w‖ ≤ 1 + δ * ‖w‖ := by nlinarith [norm_nonneg w]
      linarith [mul_le_mul_of_nonneg_right hc1 (by positivity : (0 : ℝ) ≤ 1 + δ * ‖w‖)]
    · have hcd : δ⁻¹ ≤ c := le_max_right _ _
      have : 1 + ‖w‖ ≤ δ⁻¹ * (1 + δ * ‖w‖) := by
        rw [mul_add, inv_mul_cancel_left₀ hδ.ne', mul_one]
        have : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ).mpr h
        linarith
      exact this.trans (mul_le_mul_of_nonneg_right hcd (by positivity))
  have hsinc := one_add_mul_norm_sincC_le hδ w
  -- assemble
  have hstep : (1 + ‖w‖) * ‖sincC (δ * w)‖ ≤ c * (2 * Real.exp (δ * |w.im|)) := by
    calc (1 + ‖w‖) * ‖sincC (δ * w)‖ ≤ c * (1 + δ * ‖w‖) * ‖sincC (δ * w)‖ :=
          mul_le_mul_of_nonneg_right hcw (norm_nonneg _)
      _ = c * ((1 + δ * ‖w‖) * ‖sincC (δ * w)‖) := by ring
      _ ≤ c * (2 * Real.exp (δ * |w.im|)) := mul_le_mul_of_nonneg_left hsinc (by linarith)
  have hpow : ((1 + ‖w‖) * ‖sincC (δ * w)‖) ^ m ≤ (c * (2 * Real.exp (δ * |w.im|))) ^ m :=
    pow_le_pow_left₀ (by positivity) hstep m
  have hc2 : 2 * c ≤ 2 + 4 * m / ε := by
    have h1 : δ⁻¹ = 2 * m / ε := by rw [hδdef]; field_simp
    have hnn : 0 ≤ 2 * (m : ℝ) / ε := by positivity
    have : c ≤ 1 + 2 * m / ε := max_le (by linarith) (by rw [h1]; linarith)
    have e : 4 * (m : ℝ) / ε = 2 * (2 * m / ε) := by ring
    rw [e]; linarith
  have hexp : Real.exp (δ * |w.im|) ^ m = Real.exp (ε / 2 * |w.im|) := by
    rw [← Real.exp_nat_mul]; congr 1; rw [hδdef]; field_simp
  calc (1 + ‖w‖) ^ m * ‖paperFT (splineBump hε m) w‖
      = ‖paperFT (splineStage hε 1 0) w‖ * ((1 + ‖w‖) * ‖sincC (δ * w)‖) ^ m := by
        rw [splineBump, ← hδdef, hft, norm_mul, norm_pow, mul_pow]; ring
    _ ≤ Real.exp (ε / 2 * |w.im|) * (c * (2 * Real.exp (δ * |w.im|))) ^ m :=
        mul_le_mul hφ hpow (by positivity) (by positivity)
    _ = (2 * c) ^ m * (Real.exp (ε / 2 * |w.im|) * Real.exp (δ * |w.im|) ^ m) := by ring
    _ = (2 * c) ^ m * Real.exp (ε * |w.im|) := by
        rw [hexp, ← Real.exp_add]; congr 2; ring
    _ ≤ (2 + 4 * m / ε) ^ m * Real.exp (ε * |w.im|) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hc2 m) (by positivity)

/-! ### No loss on the imaginary axis -/

/-- On the imaginary axis the transform of the smooth bump is at least one. -/
theorem one_le_re_paperFT_smoothBump_I {ε : ℝ} (hε : 0 < ε) (y : ℝ) :
    1 ≤ (paperFT (splineStage hε 1 0) ((y : ℂ) * I)).re := by
  set φ := (smoothBumpOf hε).normed volume with hφ
  have hint : Integrable φ := (smoothBumpOf hε).integrable_normed
  -- the transform at `iy` is `∫ φ(u) e^{−yu}`
  have hval : ∀ t : ℝ, paperFT (splineStage hε 1 0) ((t : ℂ) * I) =
      ((∫ u, φ u * Real.exp (-(t * u)) : ℝ) : ℂ) := by
    intro t
    rw [paperFT_def, ← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    show (φ u : ℂ) * cexp (I * ((t : ℂ) * I) * u) = ((φ u * Real.exp (-(t * u)) : ℝ) : ℂ)
    rw [show I * ((t : ℂ) * I) * u = ((-(t * u) : ℝ) : ℂ) by push_cast; ring_nf; rw [I_sq]; ring,
      ← Complex.ofReal_exp]
    push_cast; ring
  have hcont : ∀ t : ℝ, Integrable fun u => φ u * Real.exp (-(t * u)) := fun t => by
    have hc : Continuous fun u => φ u * Real.exp (-(t * u)) :=
      (smoothBumpOf hε).continuous_normed.mul (by fun_prop)
    refine hc.integrable_of_hasCompactSupport ?_
    exact (smoothBumpOf hε).hasCompactSupport_normed.mul_right
  -- evenness: the value at `iy` equals the value at `−iy`
  have hsym : (∫ u, φ u * Real.exp (-(y * u))) = ∫ u, φ u * Real.exp (-(-y * u)) := by
    rw [← integral_neg_eq_self (fun u => φ u * Real.exp (-(-y * u))) volume]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [hφ, (smoothBumpOf hε).normed_neg]
    ring_nf
  have hsum : 2 ≤ (∫ u, φ u * Real.exp (-(y * u))) + ∫ u, φ u * Real.exp (-(-y * u)) := by
    rw [← integral_add (hcont y) (hcont (-y))]
    have h2 : ∫ u, φ u * 2 = 2 := by
      rw [integral_mul_const, (smoothBumpOf hε).integral_normed, one_mul]
    rw [← h2]
    refine integral_mono (hint.mul_const 2) ((hcont y).add (hcont (-y))) fun u => ?_
    have hφ0 : 0 ≤ φ u := (smoothBumpOf hε).nonneg_normed (μ := volume) u
    have hc : 2 ≤ Real.exp (-(y * u)) + Real.exp (-(-y * u)) := by
      have := Real.one_le_cosh (y * u)
      rw [Real.cosh_eq] at this
      have e : -(-y * u) = y * u := by ring
      rw [e]; linarith
    show φ u * 2 ≤ φ u * Real.exp (-(y * u)) + φ u * Real.exp (-(-y * u))
    nlinarith
  rw [hval, Complex.ofReal_re]
  linarith

/-- On the imaginary axis the sinc factor is at least one: `sin(iδy)/(iδy) = sinh(δy)/(δy)`. -/
theorem one_le_norm_sincC_I {δ : ℝ} (y : ℝ) : 1 ≤ ‖sincC (δ * ((y : ℂ) * I))‖ := by
  by_cases h0 : (δ : ℂ) * ((y : ℂ) * I) = 0
  · rw [h0, sincC_zero, norm_one]
  · set t := δ * y with ht
    have hz : (δ : ℂ) * ((y : ℂ) * I) = (t : ℂ) * I := by rw [ht]; push_cast; ring
    have ht0 : t ≠ 0 := by
      intro h; apply h0; rw [hz, h]; simp
    rw [sincC, if_neg h0, hz, Complex.sin_mul_I]
    have e : (Complex.sinh t * I) / ((t : ℂ) * I) = ((Real.sinh t / t : ℝ) : ℂ) := by
      rw [← Complex.ofReal_sinh, Complex.ofReal_div]
      field_simp
    rw [e, Complex.norm_real, Real.norm_eq_abs]
    rcases lt_or_gt_of_ne ht0 with hneg | hpos
    · have : Real.sinh t ≤ t := Real.sinh_le_self_iff.mpr hneg.le
      rw [abs_of_pos (div_pos_of_neg_of_neg (by linarith [Real.sinh_lt_self_iff.mpr hneg])
        hneg)]
      rw [le_div_iff_of_neg hneg]; linarith
    · have : t ≤ Real.sinh t := Real.self_le_sinh_iff.mpr hpos.le
      rw [abs_of_pos (div_pos (by linarith) hpos), le_div_iff₀ hpos]; linarith

/-- **No loss on the imaginary axis.** `|b̂(iy)| ≥ 1` for every real `y`. -/
theorem one_le_norm_paperFT_splineBump_I {ε : ℝ} (hε : 0 < ε) {m : ℕ} (hm : 1 ≤ m) (y : ℝ) :
    1 ≤ ‖paperFT (splineBump hε m) ((y : ℂ) * I)‖ := by
  set δ := ε / (2 * m) with hδdef
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hδ : 0 < δ := by positivity
  have hft := (splineStage_props hε hδ m).2.2 ((y : ℂ) * I)
  rw [splineStage_zero_eq hε δ 1] at hft
  rw [splineBump, ← hδdef, hft, norm_mul, norm_pow]
  have h1 : 1 ≤ ‖paperFT (splineStage hε 1 0) ((y : ℂ) * I)‖ :=
    (one_le_re_paperFT_smoothBump_I hε y).trans (Complex.re_le_norm _)
  have h2 : 1 ≤ ‖sincC (δ * ((y : ℂ) * I))‖ ^ m := one_le_pow₀ (one_le_norm_sincC_I y)
  nlinarith

end GaloisForLFunctions.ZeroConfigurationGeometry
