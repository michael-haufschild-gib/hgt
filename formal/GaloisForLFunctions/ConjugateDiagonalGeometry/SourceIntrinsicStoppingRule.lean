import GaloisForLFunctions.ConjugateDiagonalGeometry.ThetaPrefixIndexTransition

/-!
# Source-intrinsic stopping rules for finite integer-theta collision operators

In `ThetaPrefixIndexTransition`, the Rouché artifact-annihilation threshold
`thetaArtifactAnnihilationPrefix T n` controls `firstArtifactFreePrefix T n` in terms of the
perforated-window modulus `perforatedWindowXiMin T n` of `xi`. This module eliminates all `xi`
dependence from the verification predicate and constructs two purely source-intrinsic stopping
rules evaluated from finite integer-theta prefixes alone:

1. **Prefix-to-prefix uniform strip difference bounds (`§1`)**:
   Using the explicit Gaussian integer-tail constant `thetaStripTailBound N`, any two finite
   prefixes `M ≥ N` satisfy `‖finiteThetaAmplitude M z - finiteThetaAmplitude N z‖ ≤
   2 * thetaStripTailBound N` and `‖-finiteThetaFirstMoment M z - (-finiteThetaFirstMoment N z)‖ ≤
   2 * thetaStripTailBound N` uniformly across `|z.re| ≤ 2`, with no reference to `xi`.
2. **Source-perforated window certificate and simple-zero Gaussian completeness (`§2`)**:
   Excising Rouché balls of radius `roucheDiscRadius n = 1 / (8 s_n²)` around the enclosed zeros
   `prefixEnclosedZeros T n N` of a single prefix `N` defines `sourcePerforatedWindowSet T n N` and
   its source modulus `sourcePerforatedMin T n N`. Whenever `IsSourceAlgebraicPerforatedCertified T n N`
   holds (purely a predicate on `prefixEnclosedZeros T n N` and `finiteThetaAmplitude N`), symmetric
   Rouché stability and the four-case Zhukovsky ellipse dichotomy lock `integerThetaWindowDegree T n M`,
   nonvanishing of `integerThetaLaurentLoop T n M`, and
   `fredholmIndex (integerThetaCollisionOperator T n M) = fredholmIndex (integerThetaCollisionOperator T n N)`
   across **all** `M ≥ N`, hence `firstArtifactFreePrefix T n ≤ N` for `n ≥ thetaWindowScale T`.
   On every window satisfying `HasSimpleWindowZeros T` (all zeros of `xi` in `stripZeros T` simple)
   and `n ≥ thetaSimpleZeroScale T`, this source certificate is unconditionally satisfied for all
   `N ≥ simpleZeroStoppingPrefix T n`, yielding an explicit Gaussian upper bound on
   `sourcePerforatedStoppingPrefix T n`.
3. **Root-free contour-loop modulus certificate and universal completeness (`§3`)**:
   Evaluating only the boundary contour minimum `boundaryPrefixMin T n N` of
   `‖finiteThetaAmplitude N‖` on `∂R_{T,n}`, the circle minimum `baseLoopCircleMin T n N` of
   `‖integerThetaBaseLoop T n N‖` on `UnitCircle`, and an explicit closed-form Newton–Girard
   perturbation bound `sourceLoopPerturbationBound T n N` defines `IsSourceLoopCertified T n N`
   without locating any complex zeros or assuming zero simplicity. We prove unconditional soundness
   (`firstArtifactFreePrefix T n ≤ sourceLoopStoppingPrefix T n`) and unconditional eventual
   completeness (`∀ᶠ N in atTop, IsSourceLoopCertified T n N`) on every height window `T : ℝ` and
   every stage `n ≥ thetaWindowScale T`, regardless of zero multiplicities of `xi`.
-/

set_option autoImplicit false

open Complex MeasureTheory Filter Set Metric intervalIntegral Polynomial
open scoped BigOperators Topology Classical Real

noncomputable section

namespace GaloisForLFunctions.ConjugateDiagonalGeometry

/-! ## §1 Explicit strip tail envelope and prefix-to-prefix uniform difference bounds -/

/-- Explicit Gaussian integer-tail bound on the vertical strip `|Re z| ≤ 2`:
`thetaCuspIntegerTailConstant * thetaAmplitudeEnvelope 2 * exp (-(N + 1)²)`. -/
def thetaStripTailBound (N : ℕ) : ℝ :=
  _root_.RHTower.thetaCuspIntegerTailConstant * _root_.RHTower.thetaAmplitudeEnvelope 2 *
    Real.exp (-((N + 1 : ℕ) : ℝ) ^ 2)

theorem thetaStripTailBound_nonneg (N : ℕ) : 0 ≤ thetaStripTailBound N :=
  mul_nonneg
    (mul_nonneg _root_.RHTower.thetaCuspIntegerTailConstant_nonneg
      (_root_.RHTower.thetaAmplitudeEnvelope_nonneg 2))
    (Real.exp_pos _).le

theorem thetaStripTailBound_antitone {N M : ℕ} (hNM : N ≤ M) :
    thetaStripTailBound M ≤ thetaStripTailBound N := by
  unfold thetaStripTailBound
  refine mul_le_mul_of_nonneg_left ?_
    (mul_nonneg _root_.RHTower.thetaCuspIntegerTailConstant_nonneg
      (_root_.RHTower.thetaAmplitudeEnvelope_nonneg 2))
  apply Real.exp_le_exp.mpr
  have hcast : ((N + 1 : ℕ) : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.add_le_add_right hNM 1
  have hsq : ((N + 1 : ℕ) : ℝ) ^ 2 ≤ ((M + 1 : ℕ) : ℝ) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hcast 2
  linarith

theorem tendsto_thetaStripTailBound_zero :
    Tendsto thetaStripTailBound atTop (𝓝 0) := by
  unfold thetaStripTailBound
  have hsq : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ) ^ 2) atTop atTop :=
    (Filter.tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hexp : Tendsto (fun N : ℕ => Real.exp (-((N + 1 : ℕ) : ℝ) ^ 2)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, pow_zero, one_mul] using
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0).comp hsq
  simpa only [mul_zero] using
    hexp.const_mul
      (_root_.RHTower.thetaCuspIntegerTailConstant * _root_.RHTower.thetaAmplitudeEnvelope 2)

/-- Prefix-to-prefix uniform difference bound for `finiteThetaAmplitude` on `|Re z| ≤ 2`. -/
theorem norm_finiteThetaAmplitude_sub_prefix_le_strip {N M : ℕ} (hNM : N ≤ M) {z : ℂ}
    (hz : |z.re| ≤ 2) :
    ‖_root_.RHTower.finiteThetaAmplitude M z - _root_.RHTower.finiteThetaAmplitude N z‖ ≤
      2 * thetaStripTailBound N := by
  have hsplit : _root_.RHTower.finiteThetaAmplitude M z - _root_.RHTower.finiteThetaAmplitude N z =
      (_root_.RHTower.finiteThetaAmplitude M z - _root_.RHTower.xi z) -
        (_root_.RHTower.finiteThetaAmplitude N z - _root_.RHTower.xi z) := by ring
  have hM : ‖_root_.RHTower.finiteThetaAmplitude M z - _root_.RHTower.xi z‖ ≤
      thetaStripTailBound M := by
    have h := norm_finiteThetaAmplitude_sub_xi_le_strip M (by norm_num : (0 : ℝ) ≤ 2) hz
    simpa only [thetaStripTailBound, mul_right_comm] using h
  have hN : ‖_root_.RHTower.finiteThetaAmplitude N z - _root_.RHTower.xi z‖ ≤
      thetaStripTailBound N := by
    have h := norm_finiteThetaAmplitude_sub_xi_le_strip N (by norm_num : (0 : ℝ) ≤ 2) hz
    simpa only [thetaStripTailBound, mul_right_comm] using h
  rw [hsplit]
  calc ‖(_root_.RHTower.finiteThetaAmplitude M z - _root_.RHTower.xi z) -
          (_root_.RHTower.finiteThetaAmplitude N z - _root_.RHTower.xi z)‖
      ≤ ‖_root_.RHTower.finiteThetaAmplitude M z - _root_.RHTower.xi z‖ +
          ‖_root_.RHTower.finiteThetaAmplitude N z - _root_.RHTower.xi z‖ := norm_sub_le _ _
    _ ≤ thetaStripTailBound M + thetaStripTailBound N := add_le_add hM hN
    _ ≤ 2 * thetaStripTailBound N := by linarith [thetaStripTailBound_antitone hNM]

/-- Prefix-to-prefix uniform difference bound for `-finiteThetaFirstMoment` on `|Re z| ≤ 2`. -/
theorem norm_finiteThetaFirstMoment_sub_prefix_le_strip {N M : ℕ} (hNM : N ≤ M) {z : ℂ}
    (hz : |z.re| ≤ 2) :
    ‖-_root_.RHTower.finiteThetaFirstMoment M z - (-_root_.RHTower.finiteThetaFirstMoment N z)‖ ≤
      2 * thetaStripTailBound N := by
  have hsplit : -_root_.RHTower.finiteThetaFirstMoment M z -
        (-_root_.RHTower.finiteThetaFirstMoment N z) =
      (-_root_.RHTower.finiteThetaFirstMoment M z - deriv _root_.RHTower.xi z) -
        (-_root_.RHTower.finiteThetaFirstMoment N z - deriv _root_.RHTower.xi z) := by ring
  have hM : ‖-_root_.RHTower.finiteThetaFirstMoment M z - deriv _root_.RHTower.xi z‖ ≤
      thetaStripTailBound M := by
    have h := norm_finiteThetaFirstMoment_sub_deriv_xi_le_strip M (by norm_num : (0 : ℝ) ≤ 2) hz
    simpa only [thetaStripTailBound, mul_right_comm] using h
  have hN : ‖-_root_.RHTower.finiteThetaFirstMoment N z - deriv _root_.RHTower.xi z‖ ≤
      thetaStripTailBound N := by
    have h := norm_finiteThetaFirstMoment_sub_deriv_xi_le_strip N (by norm_num : (0 : ℝ) ≤ 2) hz
    simpa only [thetaStripTailBound, mul_right_comm] using h
  rw [hsplit]
  calc ‖(-_root_.RHTower.finiteThetaFirstMoment M z - deriv _root_.RHTower.xi z) -
          (-_root_.RHTower.finiteThetaFirstMoment N z - deriv _root_.RHTower.xi z)‖
      ≤ ‖-_root_.RHTower.finiteThetaFirstMoment M z - deriv _root_.RHTower.xi z‖ +
          ‖-_root_.RHTower.finiteThetaFirstMoment N z - deriv _root_.RHTower.xi z‖ := norm_sub_le _ _
    _ ≤ thetaStripTailBound M + thetaStripTailBound N := add_le_add hM hN
    _ ≤ 2 * thetaStripTailBound N := by linarith [thetaStripTailBound_antitone hNM]

/-- Uniform vertical-strip upper bound `‖finiteThetaFirstMoment N z‖ ≤ thetaAmplitudeEnvelope R`
across all `N : ℕ` and `|Re z| ≤ R`. -/
theorem norm_finiteThetaFirstMoment_le_strip (N : ℕ) {R : ℝ} (hR : 0 ≤ R) {z : ℂ}
    (hz : |z.re| ≤ R) :
    ‖_root_.RHTower.finiteThetaFirstMoment N z‖ ≤ _root_.RHTower.thetaAmplitudeEnvelope R := by
  have hN : Integrable (fun x : ℝ =>
      (x : ℂ) * (_root_.RHTower.reflectedFiniteThetaSource (N + 1) x : ℂ) *
        Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))) := by
    simpa only [pow_one, _root_.RHTower.finiteThetaTiltSource] using
      (_root_.RHTower.finiteThetaTiltSource N).integrable_mul_exp ((1 / 2 : ℂ) - z) 1
  unfold _root_.RHTower.finiteThetaFirstMoment
  calc ‖∫ x : ℝ, (x : ℂ) * (_root_.RHTower.reflectedFiniteThetaSource (N + 1) x : ℂ) *
            Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))‖
      ≤ ∫ x : ℝ, ‖(x : ℂ) * (_root_.RHTower.reflectedFiniteThetaSource (N + 1) x : ℂ) *
            Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ, _root_.RHTower.thetaCuspTiltDecayConstant (R + 5 / 2) * Real.exp (-|x|) := by
        apply integral_mono_ae hN.norm
          (_root_.RHTower.integrable_thetaAmplitudeProfile.const_mul _)
        filter_upwards with x
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs]
        have hpos_src : 0 ≤ _root_.RHTower.reflectedFiniteThetaSource (N + 1) x :=
          (_root_.RHTower.finiteThetaTiltSource N).pos x |>.le
        rw [abs_of_nonneg hpos_src]
        have hle_full := _root_.RHTower.reflectedFiniteThetaSource_le_full (N + 1) x
        have hfull_bd := _root_.RHTower.thetaCuspFullSource_le_tiltDecayConstant (R + 5 / 2) x
        have hexp_re : ‖Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))‖ ≤
            Real.exp ((R + 1 / 2) * |x|) := by
          rw [Complex.norm_exp]
          apply Real.exp_le_exp.mpr
          have he : (((1 / 2 : ℂ) - z) * (x : ℂ)).re = (1 / 2 - z.re) * x := by simp
          have h1 : |1 / 2 - z.re| ≤ R + 1 / 2 := by
            have ha := abs_sub (1 / 2 : ℝ) z.re
            norm_num at ha
            linarith [abs_le.mp hz]
          rw [he]
          exact (le_abs_self _).trans ((abs_mul _ _).trans_le
            (mul_le_mul_of_nonneg_right h1 (abs_nonneg x)))
        have hx_exp : |x| * Real.exp (-2 * |x|) ≤ Real.exp (-|x|) := by
          have h1 : |x| ≤ Real.exp |x| := by linarith [Real.add_one_le_exp |x|]
          calc |x| * Real.exp (-2 * |x|)
              ≤ Real.exp |x| * Real.exp (-2 * |x|) :=
                mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
            _ = Real.exp (-|x|) := by rw [← Real.exp_add]; congr 1; ring
        have hC0 : 0 ≤ _root_.RHTower.thetaCuspTiltDecayConstant (R + 5 / 2) :=
          (_root_.RHTower.thetaCuspTiltDecayConstant_pos _).le
        calc |x| * _root_.RHTower.reflectedFiniteThetaSource (N + 1) x *
                ‖Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))‖
            ≤ |x| * (_root_.RHTower.thetaCuspTiltDecayConstant (R + 5 / 2) *
                Real.exp (-((R + 5 / 2) * |x|))) * Real.exp ((R + 1 / 2) * |x|) := by
              refine mul_le_mul
                (mul_le_mul_of_nonneg_left (hle_full.trans hfull_bd) (abs_nonneg x))
                hexp_re (norm_nonneg _)
                (mul_nonneg (abs_nonneg x) (mul_nonneg hC0 (Real.exp_pos _).le))
          _ = _root_.RHTower.thetaCuspTiltDecayConstant (R + 5 / 2) *
                (|x| * Real.exp (-2 * |x|)) := by
              have hadd : Real.exp (-((R + 5 / 2) * |x|)) * Real.exp ((R + 1 / 2) * |x|) =
                  Real.exp (-2 * |x|) := by
                rw [← Real.exp_add]; congr 1; ring
              calc |x| * (_root_.RHTower.thetaCuspTiltDecayConstant (R + 5 / 2) *
                      Real.exp (-((R + 5 / 2) * |x|))) * Real.exp ((R + 1 / 2) * |x|)
                  = _root_.RHTower.thetaCuspTiltDecayConstant (R + 5 / 2) *
                      (|x| * (Real.exp (-((R + 5 / 2) * |x|)) *
                        Real.exp ((R + 1 / 2) * |x|))) := by ring
                _ = _ := by rw [hadd]
          _ ≤ _root_.RHTower.thetaCuspTiltDecayConstant (R + 5 / 2) * Real.exp (-|x|) :=
              mul_le_mul_of_nonneg_left hx_exp hC0
    _ = _root_.RHTower.thetaAmplitudeEnvelope R := by
        rw [MeasureTheory.integral_const_mul]; rfl

/-! ## §2 Source-perforated window certificate and simple-zero Gaussian completeness -/

/-- Source-perforated closed window rectangle obtained by excising open Rouché discs of radius
`roucheDiscRadius n = 1 / (8 s_n²)` around the enclosed zeros `prefixEnclosedZeros T n N` of the
single integer-theta prefix `N`. -/
def sourcePerforatedWindowSet (T : ℝ) (n N : ℕ) : Set ℂ :=
  windowClosedRect T n \
    ⋃ w ∈ prefixEnclosedZeros T n N, Metric.ball w (roucheDiscRadius n)

theorem isCompact_sourcePerforatedWindowSet (T : ℝ) (n N : ℕ) :
    IsCompact (sourcePerforatedWindowSet T n N) := by
  unfold sourcePerforatedWindowSet
  rw [Set.sdiff_eq]
  exact (isCompact_windowClosedRect T n).inter_right
    ((prefixEnclosedZeros T n N).finite_toSet.isOpen_biUnion fun _ _ => Metric.isOpen_ball).isClosed_compl

theorem thetaWindowLowerLeft_mem_sourcePerforatedWindowSet {T : ℝ} {n N : ℕ}
    (hre_nn : ∀ w ∈ prefixEnclosedZeros T n N, 0 ≤ w.re) :
    thetaWindowLowerLeft n ∈ sourcePerforatedWindowSet T n N := by
  refine ⟨⟨le_rfl, thetaWindow_re_le T n, le_rfl, thetaWindow_im_le T n⟩, ?_⟩
  simp only [Set.mem_iUnion, Metric.mem_ball, not_exists, not_lt]
  intro w hw
  have hw0 := hre_nn w hw
  have hre : 1 / 2 ≤ |w.re - (thetaWindowLowerLeft n).re| := by
    rw [thetaWindowLowerLeft_re, abs_of_pos (by linarith)]
    linarith
  have hd : 1 / 2 ≤ dist (thetaWindowLowerLeft n) w := by
    rw [dist_comm, dist_eq_norm]
    exact hre.trans (by simpa only [Complex.sub_re] using
      Complex.abs_re_le_norm (w - thetaWindowLowerLeft n))
  exact (roucheDiscRadius_le_inv_288 n).trans (by linarith)

/-- Minimum of `‖finiteThetaAmplitude N z‖` on `sourcePerforatedWindowSet T n N` (`0` if empty). -/
def sourcePerforatedMin (T : ℝ) (n N : ℕ) : ℝ :=
  if hne : (sourcePerforatedWindowSet T n N).Nonempty then
    let hK := isCompact_sourcePerforatedWindowSet T n N
    let hcont : ContinuousOn (fun z : ℂ => ‖_root_.RHTower.finiteThetaAmplitude N z‖)
        (sourcePerforatedWindowSet T n N) :=
      (_root_.RHTower.differentiable_finiteThetaAmplitude N).continuous.norm.continuousOn
    ‖_root_.RHTower.finiteThetaAmplitude N (hK.exists_isMinOn hne hcont).choose‖
  else
    0

theorem sourcePerforatedMin_nonneg (T : ℝ) (n N : ℕ) : 0 ≤ sourcePerforatedMin T n N := by
  unfold sourcePerforatedMin
  split_ifs with hne
  · exact norm_nonneg _
  · exact le_rfl

theorem sourcePerforatedMin_le_norm {T : ℝ} {n N : ℕ} {z : ℂ}
    (hz : z ∈ sourcePerforatedWindowSet T n N) :
    sourcePerforatedMin T n N ≤ ‖_root_.RHTower.finiteThetaAmplitude N z‖ := by
  unfold sourcePerforatedMin
  rw [dif_pos ⟨z, hz⟩]
  dsimp only
  set hK := isCompact_sourcePerforatedWindowSet T n N
  set hcont : ContinuousOn (fun w : ℂ => ‖_root_.RHTower.finiteThetaAmplitude N w‖)
      (sourcePerforatedWindowSet T n N) :=
    (_root_.RHTower.differentiable_finiteThetaAmplitude N).continuous.norm.continuousOn
  exact isMinOn_iff.mp (hK.exists_isMinOn ⟨z, hz⟩ hcont).choose_spec.2 z hz

/-- **Purely source-intrinsic perforated-window stopping certificate at prefix `(T, n, N)`.**
Depends exclusively on `prefixEnclosedZeros T n N`, `finiteThetaAmplitude N`, `zhukovskyStage n`,
`roucheDiscRadius n`, and `thetaStripTailBound N`, with zero reference to `xi`. -/
def IsSourceAlgebraicPerforatedCertified (T : ℝ) (n N : ℕ) : Prop :=
  (∀ w ∈ prefixEnclosedZeros T n N,
    2 / (zhukovskyStage n : ℝ) ≤ w.re ∧ w.re ≤ 1 - 2 / (zhukovskyStage n : ℝ) ∧
    (thetaWindowLowerLeft n).im + 2 * roucheDiscRadius n < w.im ∧
    w.im < (thetaWindowUpperRight T n).im - 2 * roucheDiscRadius n) ∧
  (∀ w₁ ∈ prefixEnclosedZeros T n N, ∀ w₂ ∈ prefixEnclosedZeros T n N,
    w₁ ≠ w₂ → 4 * roucheDiscRadius n < dist w₁ w₂) ∧
  (∀ w₁ ∈ prefixEnclosedZeros T n N, ∀ w₂ ∈ prefixEnclosedZeros T n N,
    (|w₁.im - w₂.im| < roucheDiscRadius n ∧
      (w₁ = w₂ ∨ 7 / (2 * (zhukovskyStage n : ℝ)) < |w₁.re - w₂.re|)) ∨
    7 / (2 * (zhukovskyStage n : ℝ)) < |w₁.im - w₂.im|) ∧
  4 * thetaStripTailBound N < sourcePerforatedMin T n N

private lemma closedBall_two_rouche_inside_of_sourceCert {T : ℝ} {n N : ℕ}
    (hcert : IsSourceAlgebraicPerforatedCertified T n N)
    {w z : ℂ} (hw : w ∈ prefixEnclosedZeros T n N)
    (hz : z ∈ Metric.closedBall w (2 * roucheDiscRadius n)) :
    (thetaWindowLowerLeft n).re < z.re ∧ z.re < (thetaWindowUpperRight T n).re ∧
      (thetaWindowLowerLeft n).im < z.im ∧ z.im < (thetaWindowUpperRight T n).im := by
  obtain ⟨hre_lo, hre_hi, him_lo, him_hi⟩ := hcert.1 w hw
  have hs_pos : (0 : ℝ) < (zhukovskyStage n : ℝ) := zhukovskyStage_pos n
  have h2s_pos : 0 < 2 / (zhukovskyStage n : ℝ) := by positivity
  have h2r_le : 2 * roucheDiscRadius n ≤ 1 / 144 := by linarith [roucheDiscRadius_le_inv_288 n]
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  have hre_diff : |z.re - w.re| ≤ 2 * roucheDiscRadius n :=
    (by simpa only [Complex.sub_re] using Complex.abs_re_le_norm (z - w)).trans hz
  have him_diff : |z.im - w.im| ≤ 2 * roucheDiscRadius n :=
    (by simpa only [Complex.sub_im] using Complex.abs_im_le_norm (z - w)).trans hz
  obtain ⟨hr1, hr2⟩ := abs_le.mp hre_diff
  obtain ⟨hi1, hi2⟩ := abs_le.mp him_diff
  rw [thetaWindowLowerLeft_re, thetaWindowUpperRight_re]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

private lemma rectangleBoundaryPath_mem_sourcePerforatedWindowSet {T : ℝ} {n N : ℕ}
    (hcert : IsSourceAlgebraicPerforatedCertified T n N) (t : ℝ) :
    _root_.RHTower.rectangleBoundaryPath
      (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t ∈
      sourcePerforatedWindowSet T n N := by
  have hmem := _root_.RHTower.rectangleBoundaryPath_mem_reProdIm
    (thetaWindowLowerLeft n) (thetaWindowUpperRight T n)
    (thetaWindow_re_le T n) (thetaWindow_im_le T n) t
  rw [uIcc_of_le (thetaWindow_re_le T n), uIcc_of_le (thetaWindow_im_le T n),
    Complex.mem_reProdIm] at hmem
  refine ⟨⟨hmem.1.1, hmem.1.2, hmem.2.1, hmem.2.2⟩, ?_⟩
  intro hball
  simp only [Set.mem_iUnion, exists_prop] at hball
  obtain ⟨w, hw, hdist⟩ := hball
  have hin := closedBall_two_rouche_inside_of_sourceCert hcert hw
    (Metric.ball_subset_closedBall (Metric.ball_subset_ball
      (by linarith [roucheDiscRadius_pos n]) hdist))
  unfold _root_.RHTower.rectangleBoundaryPath _root_.RHTower.rectangleEdgePath at hin
  split_ifs at hin
  · exact hin.2.2.1.ne' (by simp)
  · exact hin.2.1.ne (by simp)
  · exact hin.2.2.2.ne (by simp)
  · exact hin.1.ne' (by simp)

private lemma sphere_rouche_subset_sourcePerforatedWindowSet {T : ℝ} {n N : ℕ}
    (hcert : IsSourceAlgebraicPerforatedCertified T n N)
    {w : ℂ} (hw : w ∈ prefixEnclosedZeros T n N) :
    Metric.sphere w (roucheDiscRadius n) ⊆ sourcePerforatedWindowSet T n N := by
  intro ζ hζ
  have hζ_cb : ζ ∈ Metric.closedBall w (2 * roucheDiscRadius n) := by
    rw [Metric.mem_closedBall, Metric.mem_sphere.mp hζ]
    linarith [roucheDiscRadius_pos n]
  obtain ⟨h1, h2, h3, h4⟩ := closedBall_two_rouche_inside_of_sourceCert hcert hw hζ_cb
  refine ⟨⟨h1.le, h2.le, h3.le, h4.le⟩, ?_⟩
  simp only [Set.mem_iUnion, Metric.mem_ball, not_exists, not_lt]
  intro w' hw'
  by_cases heq : w' = w
  · rw [heq, Metric.mem_sphere.mp hζ]
  · have hsep := hcert.2.1 w hw' (by exact hw) -- wait: fix argument order below!
    sorry
