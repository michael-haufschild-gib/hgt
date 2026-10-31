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
   Rouché stability and the quasi-horizontal Zhukovsky ellipse dichotomy lock
   `integerThetaWindowDegree T n M`, nonvanishing of `integerThetaLaurentLoop T n M`, and
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
   every stage `n ≥ thetaWindowScale T`, regardless of zero multiplicities of `xi`, together with
   the single-stopping-prefix `RiemannHypothesis` equivalence at `sourceLoopStoppingPrefix`.
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
  have hcast : ((N + 1 : ℕ) : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.add_le_add_right hNM 1
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
theorem norm_finiteThetaFirstMoment_le_strip (N : ℕ) {R : ℝ} (_hR : 0 ≤ R) {z : ℂ}
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
        MeasureTheory.norm_integral_le_integral_norm _
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
          have h1 : |x| ≤ Real.exp (|x|) := by linarith [Real.add_one_le_exp (|x|)]
          calc |x| * Real.exp (-2 * |x|)
              ≤ Real.exp (|x|) * Real.exp (-2 * |x|) :=
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
    (isOpen_biUnion fun _ _ => Metric.isOpen_ball).isClosed_compl

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

private lemma rectangleBoundaryPath_on_edges (z₁ z₂ : ℂ) (t : ℝ) :
    (_root_.RHTower.rectangleBoundaryPath z₁ z₂ t).re = z₁.re ∨
    (_root_.RHTower.rectangleBoundaryPath z₁ z₂ t).re = z₂.re ∨
    (_root_.RHTower.rectangleBoundaryPath z₁ z₂ t).im = z₁.im ∨
    (_root_.RHTower.rectangleBoundaryPath z₁ z₂ t).im = z₂.im := by
  unfold _root_.RHTower.rectangleBoundaryPath _root_.RHTower.rectangleEdgePath
  split_ifs
  · right; right; left; simp
  · right; left; simp
  · right; right; right; simp
  · left; simp

private lemma closedBall_two_rouche_inside_of_sourceCert {T : ℝ} {n N : ℕ}
    (hcert : IsSourceAlgebraicPerforatedCertified T n N)
    {w z : ℂ} (hw : w ∈ prefixEnclosedZeros T n N)
    (hz : z ∈ Metric.closedBall w (2 * roucheDiscRadius n)) :
    (thetaWindowLowerLeft n).re < z.re ∧ z.re < (thetaWindowUpperRight T n).re ∧
      (thetaWindowLowerLeft n).im < z.im ∧ z.im < (thetaWindowUpperRight T n).im := by
  have ⟨hmarg, _, _, _⟩ := hcert
  obtain ⟨hre_lo, hre_hi, him_lo, him_hi⟩ := hmarg w hw
  have hs_pos : (0 : ℝ) < (zhukovskyStage n : ℝ) := zhukovskyStage_pos n
  have h2s_pos : 0 < 2 / (zhukovskyStage n : ℝ) := by positivity
  have h2r_le : 2 * roucheDiscRadius n ≤ 1 / 144 := by linarith [roucheDiscRadius_le_inv_288 n]
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  have hre_diff : |z.re - w.re| ≤ 2 * roucheDiscRadius n := by
    calc |z.re - w.re| = |(z - w).re| := by rw [Complex.sub_re]
      _ ≤ ‖z - w‖ := Complex.abs_re_le_norm (z - w)
      _ ≤ 2 * roucheDiscRadius n := hz
  have him_diff : |z.im - w.im| ≤ 2 * roucheDiscRadius n := by
    calc |z.im - w.im| = |(z - w).im| := by rw [Complex.sub_im]
      _ ≤ ‖z - w‖ := Complex.abs_im_le_norm (z - w)
      _ ≤ 2 * roucheDiscRadius n := hz
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
  rcases rectangleBoundaryPath_on_edges
      (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t with h | h | h | h
  · exact hin.1.ne' h
  · exact hin.2.1.ne h
  · exact hin.2.2.1.ne' h
  · exact hin.2.2.2.ne h

private lemma sphere_rouche_subset_sourcePerforatedWindowSet {T : ℝ} {n N : ℕ}
    (hcert : IsSourceAlgebraicPerforatedCertified T n N)
    {w : ℂ} (hw : w ∈ prefixEnclosedZeros T n N) :
    Metric.sphere w (roucheDiscRadius n) ⊆ sourcePerforatedWindowSet T n N := by
  have ⟨_, hsep_all, _, _⟩ := hcert
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
  · have hsep := hsep_all w hw w' hw' (Ne.symm heq)
    have htri := dist_triangle w ζ w'
    have hdist_eq : dist w ζ = roucheDiscRadius n := by
      rw [dist_comm]; exact Metric.mem_sphere.mp hζ
    linarith [roucheDiscRadius_pos n]

/-- Quasi-horizontal Zhukovsky ellipse classification across Rouché discs of a certified source
prefix: ordered quasi-horizontal pairs (`|w₁.im - w₂.im| < r_n ∧ w₂.re < w₁.re`) satisfy
`zhukovskyEllipseForm n (z₁ - z₂) < 1`, while all complementary pairs satisfy
`1 < zhukovskyEllipseForm n (z₁ - z₂)`. -/
private lemma source_rouche_pair_zhukovsky_class {T : ℝ} {n N : ℕ}
    (hcert : IsSourceAlgebraicPerforatedCertified T n N)
    {w₁ w₂ z₁ z₂ : ℂ}
    (hw₁ : w₁ ∈ prefixEnclosedZeros T n N) (hw₂ : w₂ ∈ prefixEnclosedZeros T n N)
    (hb₁ : dist z₁ w₁ < roucheDiscRadius n) (hb₂ : dist z₂ w₂ < roucheDiscRadius n) :
    ((|w₁.im - w₂.im| < roucheDiscRadius n ∧ w₂.re < w₁.re) →
      zhukovskyEllipseForm n (z₁ - z₂) < 1) ∧
    (¬ (|w₁.im - w₂.im| < roucheDiscRadius n ∧ w₂.re < w₁.re) →
      1 < zhukovskyEllipseForm n (z₁ - z₂)) := by
  obtain ⟨hmarg, _, hcoord, _⟩ := hcert
  obtain ⟨hm₁_lo, hm₁_hi, _, _⟩ := hmarg w₁ hw₁
  obtain ⟨hm₂_lo, hm₂_hi, _, _⟩ := hmarg w₂ hw₂
  have hs6 : (6 : ℝ) ≤ (zhukovskyStage n : ℝ) := six_le_zhukovskyStage_real n
  have hs_pos : (0 : ℝ) < (zhukovskyStage n : ℝ) := zhukovskyStage_pos n
  have ha_pos : 0 < zhukovskyMajorAxis n := zhukovskyMajorAxis_pos n
  have hb_pos : 0 < zhukovskyMinorAxis n := zhukovskyMinorAxis_pos n
  have hinv_pos : 0 < 1 / (zhukovskyStage n : ℝ) := one_div_pos.mpr hs_pos
  have hinv_le : 1 / (zhukovskyStage n : ℝ) ≤ 1 / 6 :=
    one_div_le_one_div_of_le (by norm_num) hs6
  have hr_eq : roucheDiscRadius n = (1 / 8) * (1 / (zhukovskyStage n : ℝ)) ^ 2 := by
    unfold roucheDiscRadius; ring
  have hr_lt : roucheDiscRadius n < (1 / 4) * (1 / (zhukovskyStage n : ℝ)) := by
    rw [roucheDiscRadius,
      show (1 / 4 : ℝ) * (1 / (zhukovskyStage n : ℝ)) = 1 / (4 * (zhukovskyStage n : ℝ)) by ring]
    exact one_div_lt_one_div_of_lt (mul_pos (by norm_num) hs_pos) (by nlinarith [hs6])
  have h2_eq : 2 / (zhukovskyStage n : ℝ) = 2 * (1 / (zhukovskyStage n : ℝ)) := by ring
  have h3_eq : 3 / (zhukovskyStage n : ℝ) = 3 * (1 / (zhukovskyStage n : ℝ)) := by ring
  have h72_eq : 7 / (2 * (zhukovskyStage n : ℝ)) = (7 / 2) * (1 / (zhukovskyStage n : ℝ)) := by
    ring
  have hmaj_eq : zhukovskyMajorAxis n = 1 / 2 - (1 / 2) * (1 / (zhukovskyStage n : ℝ)) := by
    unfold zhukovskyMajorAxis; ring
  rw [dist_eq_norm] at hb₁ hb₂
  have hre₁ : |z₁.re - w₁.re| < roucheDiscRadius n :=
    lt_of_le_of_lt (by simpa only [Complex.sub_re] using Complex.abs_re_le_norm (z₁ - w₁)) hb₁
  have him₁ : |z₁.im - w₁.im| < roucheDiscRadius n :=
    lt_of_le_of_lt (by simpa only [Complex.sub_im] using Complex.abs_im_le_norm (z₁ - w₁)) hb₁
  have hre₂ : |z₂.re - w₂.re| < roucheDiscRadius n :=
    lt_of_le_of_lt (by simpa only [Complex.sub_re] using Complex.abs_re_le_norm (z₂ - w₂)) hb₂
  have him₂ : |z₂.im - w₂.im| < roucheDiscRadius n :=
    lt_of_le_of_lt (by simpa only [Complex.sub_im] using Complex.abs_im_le_norm (z₂ - w₂)) hb₂
  constructor
  · rintro ⟨him_near, hre_lt⟩
    have hw_ne : w₁ ≠ w₂ := fun heq => hre_lt.ne (congrArg Complex.re heq).symm
    have hgap_re : 3 / (zhukovskyStage n : ℝ) < w₁.re - w₂.re := by
      rcases hcoord w₁ hw₁ w₂ hw₂ with ⟨_, h_or⟩ | him_far
      · rcases h_or with heq | h72
        · exact absurd heq hw_ne
        · rw [abs_of_pos (sub_pos.mpr hre_lt)] at h72
          linarith [h3_eq, h72_eq, hinv_pos]
      · exfalso
        linarith [hr_lt, h72_eq, hinv_pos, him_near, him_far]
    have hu_abs : |(z₁ - z₂).re - 1 / 2| < 1 / 2 - 1 / (zhukovskyStage n : ℝ) := by
      rw [Complex.sub_re]
      exact abs_lt.mpr ⟨by linarith [(abs_lt.mp hre₁).1, (abs_lt.mp hre₂).2],
        by linarith [hm₁_hi, hm₂_lo, (abs_lt.mp hre₁).2, (abs_lt.mp hre₂).1]⟩
    have hu_sq : ((z₁ - z₂).re - 1 / 2) ^ 2 < (1 / 2 - 1 / (zhukovskyStage n : ℝ)) ^ 2 := by
      rw [← sq_abs ((z₁ - z₂).re - 1 / 2)]
      exact pow_lt_pow_left₀ hu_abs (abs_nonneg _) (by norm_num : 2 ≠ 0)
    have hmaj_gap_pos : 0 < (1 - 1 / (zhukovskyStage n : ℝ)) * zhukovskyMajorAxis n ^ 2 -
        (1 / 2 - 1 / (zhukovskyStage n : ℝ)) ^ 2 := by
      have hpoly_maj :
          (1 - 1 / (zhukovskyStage n : ℝ)) * zhukovskyMajorAxis n ^ 2 -
            (1 / 2 - 1 / (zhukovskyStage n : ℝ)) ^ 2 =
          (1 / (zhukovskyStage n : ℝ) / 4) *
            (1 - 1 / (zhukovskyStage n : ℝ) - (1 / (zhukovskyStage n : ℝ)) ^ 2) := by
        rw [hmaj_eq]; ring
      have hsq_le : (1 / (zhukovskyStage n : ℝ)) ^ 2 ≤ (1 / 6 : ℝ) ^ 2 :=
        pow_le_pow_left₀ hinv_pos.le hinv_le 2
      rw [hpoly_maj]
      exact mul_pos (div_pos hinv_pos (by norm_num)) (by linarith)
    have hmaj_term : ((z₁ - z₂).re - 1 / 2) ^ 2 / zhukovskyMajorAxis n ^ 2 <
        1 - 1 / (zhukovskyStage n : ℝ) :=
      (div_lt_iff₀ (sq_pos_of_pos ha_pos)).mpr (by linarith)
    have him_abs : |(z₁ - z₂).im| < (3 / 8) * (1 / (zhukovskyStage n : ℝ)) ^ 2 := by
      have hdiff : (z₁ - z₂).im = (z₁.im - w₁.im) + (w₁.im - w₂.im) - (z₂.im - w₂.im) := by
        rw [Complex.sub_im]; ring
      rw [hdiff]
      exact abs_lt.mpr
        ⟨by linarith [(abs_lt.mp him₁).1, (abs_lt.mp him_near).1, (abs_lt.mp him₂).2, hr_eq],
         by linarith [(abs_lt.mp him₁).2, (abs_lt.mp him_near).2, (abs_lt.mp him₂).1, hr_eq]⟩
    have him_sq : (z₁ - z₂).im ^ 2 < ((3 / 8) * (1 / (zhukovskyStage n : ℝ)) ^ 2) ^ 2 := by
      rw [← sq_abs ((z₁ - z₂).im)]
      exact pow_lt_pow_left₀ him_abs (abs_nonneg _) (by norm_num : 2 ≠ 0)
    have hmin_gap_pos :
        0 < (1 / (zhukovskyStage n : ℝ)) * zhukovskyMinorAxis n ^ 2 -
          ((3 / 8) * (1 / (zhukovskyStage n : ℝ)) ^ 2) ^ 2 := by
      have hident : (1 / (zhukovskyStage n : ℝ)) * zhukovskyMinorAxis n ^ 2 -
          ((3 / 8) * (1 / (zhukovskyStage n : ℝ)) ^ 2) ^ 2 =
          (1 / (zhukovskyStage n : ℝ)) ^ 3 *
            (1 - (9 / 64) * (1 / (zhukovskyStage n : ℝ))) := by
        unfold zhukovskyMinorAxis; ring
      rw [hident]
      exact mul_pos (pow_pos hinv_pos 3) (by linarith)
    have hmin_term : (z₁ - z₂).im ^ 2 / zhukovskyMinorAxis n ^ 2 <
        1 / (zhukovskyStage n : ℝ) :=
      (div_lt_iff₀ (sq_pos_of_pos hb_pos)).mpr (by linarith)
    unfold zhukovskyEllipseForm
    linarith
  · intro hnot
    by_cases him_near : |w₁.im - w₂.im| < roucheDiscRadius n
    · have hle_re : w₁.re ≤ w₂.re := not_lt.mp fun hlt => hnot ⟨him_near, hlt⟩
      have hsub_lt : (z₁ - z₂).re - 1 / 2 < -zhukovskyMajorAxis n := by
        rw [Complex.sub_re]
        linarith [(abs_lt.mp hre₁).2, (abs_lt.mp hre₂).1]
      have hsq : zhukovskyMajorAxis n ^ 2 < ((z₁ - z₂).re - 1 / 2) ^ 2 := by
        nlinarith [ha_pos, hsub_lt]
      unfold zhukovskyEllipseForm
      have hdiv : 1 < ((z₁ - z₂).re - 1 / 2) ^ 2 / zhukovskyMajorAxis n ^ 2 :=
        (one_lt_div (sq_pos_of_pos ha_pos)).mpr hsq
      have hnn : 0 ≤ (z₁ - z₂).im ^ 2 / zhukovskyMinorAxis n ^ 2 := by positivity
      linarith
    · have him_far : 7 / (2 * (zhukovskyStage n : ℝ)) < |w₁.im - w₂.im| := by
        rcases hcoord w₁ hw₁ w₂ hw₂ with ⟨hnear, _⟩ | hfar
        · exact absurd hnear him_near
        · exact hfar
      have him_gt : zhukovskyMinorAxis n < |(z₁ - z₂).im| := by
        unfold zhukovskyMinorAxis
        have htri : |w₁.im - w₂.im| - |z₁.im - w₁.im| - |z₂.im - w₂.im| ≤ |(z₁ - z₂).im| := by
          have h1 : w₁.im - w₂.im = (z₁ - z₂).im - (z₁.im - w₁.im) + (z₂.im - w₂.im) := by
            rw [Complex.sub_im]; ring
          have h2 := abs_add_le ((z₁ - z₂).im - (z₁.im - w₁.im)) (z₂.im - w₂.im)
          rw [← h1] at h2
          have h3 := abs_sub ((z₁ - z₂).im) (z₁.im - w₁.im)
          linarith
        linarith
      have hsq : zhukovskyMinorAxis n ^ 2 < (z₁ - z₂).im ^ 2 := by
        have h1 := pow_lt_pow_left₀ him_gt hb_pos.le (by norm_num : 2 ≠ 0)
        rwa [sq_abs] at h1
      unfold zhukovskyEllipseForm
      have hdiv : 1 < (z₁ - z₂).im ^ 2 / zhukovskyMinorAxis n ^ 2 :=
        (one_lt_div (sq_pos_of_pos hb_pos)).mpr hsq
      have hnn : 0 ≤ ((z₁ - z₂).re - 1 / 2) ^ 2 / zhukovskyMajorAxis n ^ 2 := by positivity
      linarith

/-- Symmetric Rouché zero-sum preservation on each open disc `ball w (roucheDiscRadius n)`
(`w ∈ prefixEnclosedZeros T n N`) between prefix `N` and any `M ≥ N`. -/
private lemma source_rouche_disc_multiplicity_eq {T : ℝ} {n N M : ℕ}
    (hcert : IsSourceAlgebraicPerforatedCertified T n N) (hNM : N ≤ M)
    {w : ℂ} (hw : w ∈ prefixEnclosedZeros T n N) :
    (∑ z ∈ (prefixEnclosedZeros T n M).filter (· ∈ Metric.ball w (roucheDiscRadius n)),
      (analyticOrderAt (_root_.RHTower.finiteThetaAmplitude M) z).toNat) =
      (analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) w).toNat := by
  have ⟨_, hsep_all, _, hmod⟩ := hcert
  have hr_pos : 0 < roucheDiscRadius n := roucheDiscRadius_pos n
  have hr_2r : roucheDiscRadius n < 2 * roucheDiscRadius n := by linarith
  have hμ_pos : 0 < sourcePerforatedMin T n N :=
    lt_of_le_of_lt (by positivity [thetaStripTailBound_nonneg N]) hmod
  have hsph_perf := sphere_rouche_subset_sourcePerforatedWindowSet hcert hw
  have happrox_perf : ∀ z ∈ sourcePerforatedWindowSet T n N,
      ‖_root_.RHTower.finiteThetaAmplitude M z - _root_.RHTower.finiteThetaAmplitude N z‖ <
        sourcePerforatedMin T n N / 2 := by
    intro z hz
    obtain ⟨hz1, hz2, _, _⟩ := hz.1
    rw [thetaWindowLowerLeft_re] at hz1
    rw [thetaWindowUpperRight_re] at hz2
    have hre2 : |z.re| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    exact (norm_finiteThetaAmplitude_sub_prefix_le_strip hNM hre2).trans_lt (by linarith)
  have hFN_perf : ∀ z ∈ sourcePerforatedWindowSet T n N,
      _root_.RHTower.finiteThetaAmplitude N z ≠ 0 := by
    intro z hz h0
    have hle := sourcePerforatedMin_le_norm hz
    rw [h0, norm_zero] at hle
    linarith
  have hFM_perf : ∀ z ∈ sourcePerforatedWindowSet T n N,
      _root_.RHTower.finiteThetaAmplitude M z ≠ 0 := by
    intro z hz h0
    have hlt := happrox_perf z hz
    rw [h0, zero_sub, norm_neg] at hlt
    linarith [sourcePerforatedMin_le_norm hz]
  have hFN_sph : ∀ ζ ∈ Metric.sphere w (roucheDiscRadius n),
      _root_.RHTower.finiteThetaAmplitude N ζ ≠ 0 :=
    fun ζ hζ => hFN_perf ζ (hsph_perf hζ)
  have hFM_sph : ∀ ζ ∈ Metric.sphere w (roucheDiscRadius n),
      _root_.RHTower.finiteThetaAmplitude M ζ ≠ 0 :=
    fun ζ hζ => hFM_perf ζ (hsph_perf hζ)
  have hslit : ∀ ζ ∈ Metric.sphere w (roucheDiscRadius n),
      _root_.RHTower.finiteThetaAmplitude M ζ / _root_.RHTower.finiteThetaAmplitude N ζ ∈
        Complex.slitPlane := by
    intro ζ hζ
    have hperf := hsph_perf hζ
    have hmin := sourcePerforatedMin_le_norm hperf
    have hdiff_lt : ‖_root_.RHTower.finiteThetaAmplitude M ζ -
        _root_.RHTower.finiteThetaAmplitude N ζ‖ < ‖_root_.RHTower.finiteThetaAmplitude N ζ‖ :=
      (happrox_perf ζ hperf).trans_le (by linarith)
    have hq : _root_.RHTower.finiteThetaAmplitude M ζ /
          _root_.RHTower.finiteThetaAmplitude N ζ - 1 =
        (_root_.RHTower.finiteThetaAmplitude M ζ - _root_.RHTower.finiteThetaAmplitude N ζ) /
          _root_.RHTower.finiteThetaAmplitude N ζ := by
      field_simp [hFN_sph ζ hζ]
    have hq_norm : ‖_root_.RHTower.finiteThetaAmplitude M ζ /
        _root_.RHTower.finiteThetaAmplitude N ζ - 1‖ < 1 := by
      rw [hq, norm_div, div_lt_one (norm_pos_iff.mpr (hFN_sph ζ hζ))]
      exact hdiff_lt
    have hre_lt : |(_root_.RHTower.finiteThetaAmplitude M ζ /
        _root_.RHTower.finiteThetaAmplitude N ζ - 1).re| < 1 :=
      (Complex.abs_re_le_norm _).trans_lt hq_norm
    rw [Complex.sub_re, Complex.one_re] at hre_lt
    exact Complex.mem_slitPlane_iff.mpr (Or.inl (by linarith [(abs_lt.mp hre_lt).1]))
  have hFM_diff : DifferentiableOn ℂ (_root_.RHTower.finiteThetaAmplitude M) Set.univ :=
    (_root_.RHTower.differentiable_finiteThetaAmplitude M).differentiableOn
  have hFN_diff : DifferentiableOn ℂ (_root_.RHTower.finiteThetaAmplitude N) Set.univ :=
    (_root_.RHTower.differentiable_finiteThetaAmplitude N).differentiableOn
  have hzsum := HTGeometry.zeroSumBall_eq_of_quotient_mem_slitPlane hr_pos hr_2r isOpen_univ
    (Set.subset_univ (Metric.closedBall w (2 * roucheDiscRadius n))) hFM_diff hFN_diff hFN_sph hslit
  obtain ⟨ZF, hZF_ball, hZF_zero, hZF_sum⟩ := HTGeometry.exists_zeroSet_zeroSumBall
    hr_pos hr_2r isOpen_univ (Set.subset_univ _) hFM_diff hFM_sph
  obtain ⟨ZG, hZG_ball, hZG_zero, hZG_sum⟩ := HTGeometry.exists_zeroSet_zeroSumBall
    hr_pos hr_2r isOpen_univ (Set.subset_univ _) hFN_diff hFN_sph
  have hZG_eq : ZG = {w} := by
    ext z
    rw [Finset.mem_singleton]
    constructor
    · intro hzG
      have hz_ball := hZG_ball z hzG
      have hz0 := (hZG_zero z hz_ball).2 hzG
      have hz_in := closedBall_two_rouche_inside_of_sourceCert hcert hw
        (Metric.ball_subset_closedBall (Metric.ball_subset_ball hr_2r.le hz_ball))
      have hzW : z ∈ prefixEnclosedZeros T n N :=
        (mem_prefixEnclosedZeros_iff T n N z).mpr ⟨hz_in, hz0⟩
      by_contra hne
      have hsep := hsep_all z hzW w hw hne
      have hd_lt : dist z w < roucheDiscRadius n := Metric.mem_ball.mp hz_ball
      linarith
    · rintro rfl
      exact (hZG_zero z (Metric.mem_ball_self hr_pos)).1
        ((mem_prefixEnclosedZeros_iff T n N z).mp hw).2
  have hZF_eq : ZF =
      (prefixEnclosedZeros T n M).filter (· ∈ Metric.ball w (roucheDiscRadius n)) := by
    ext z
    rw [Finset.mem_filter, mem_prefixEnclosedZeros_iff]
    constructor
    · intro hzF
      have hzb := hZF_ball z hzF
      exact ⟨⟨closedBall_two_rouche_inside_of_sourceCert hcert hw
        (Metric.ball_subset_closedBall (Metric.ball_subset_ball hr_2r.le hzb)),
        (hZF_zero z hzb).2 hzF⟩, hzb⟩
    · rintro ⟨⟨_, hz0⟩, hzb⟩
      exact (hZF_zero z hzb).1 hz0
  rw [hZF_sum, hZG_sum, hZG_eq, hZF_eq, Finset.sum_singleton] at hzsum
  have hcast : ((∑ z ∈ (prefixEnclosedZeros T n M).filter (· ∈ Metric.ball w (roucheDiscRadius n)),
      (analyticOrderAt (_root_.RHTower.finiteThetaAmplitude M) z).toNat : ℕ) : ℂ) =
      (((analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) w).toNat : ℕ) : ℂ) := by
    push_cast
    exact hzsum
  exact Nat.cast_injective hcast

/-- **Prefix-to-all-`M ≥ N` locking theorem for `IsSourceAlgebraicPerforatedCertified`.**
Whenever `IsSourceAlgebraicPerforatedCertified T n N` holds at a single prefix `N`, every prefix
`M ≥ N` is nonvanishing on `sourcePerforatedWindowSet T n N` (and on `∂R_{T,n}`), has the exact
same window degree `integerThetaWindowDegree T n M = integerThetaWindowDegree T n N`, has
nonvanishing `integerThetaLaurentLoop T n M` on `UnitCircle`, and has the exact same Fredholm index
`fredholmIndex (integerThetaCollisionOperator T n M) = fredholmIndex (integerThetaCollisionOperator T n N)`. -/
theorem sourceAlgebraicPerforatedCertified_locks_all_ge {T : ℝ} {n N : ℕ}
    (hcert : IsSourceAlgebraicPerforatedCertified T n N) :
    ∀ M ≥ N,
      (∀ z ∈ sourcePerforatedWindowSet T n N, _root_.RHTower.finiteThetaAmplitude M z ≠ 0) ∧
      (∀ t : ℝ, _root_.RHTower.finiteThetaAmplitude M
        (_root_.RHTower.rectangleBoundaryPath
          (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t) ≠ 0) ∧
      integerThetaWindowDegree T n M = integerThetaWindowDegree T n N ∧
      (∀ u : HTGeometry.UnitCircle, integerThetaLaurentLoop T n M u ≠ 0) ∧
      HTGeometry.fredholmIndex (integerThetaCollisionOperator T n M) =
        HTGeometry.fredholmIndex (integerThetaCollisionOperator T n N) := by
  let W := prefixEnclosedZeros T n N
  let mN : ℂ → ℕ := fun w => (analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) w).toNat
  let targetDeg : ℕ := ∑ w ∈ W, mN w
  let targetIdx : ℤ := 2 * ∑ w₁ ∈ W, ∑ w₂ ∈ W,
    (mN w₁ : ℤ) * (mN w₂ : ℤ) *
      (if |w₁.im - w₂.im| < roucheDiscRadius n ∧ w₂.re < w₁.re then 1 else 0)
  have hcore : ∀ M ≥ N,
      (∀ z ∈ sourcePerforatedWindowSet T n N, _root_.RHTower.finiteThetaAmplitude M z ≠ 0) ∧
      (∀ t : ℝ, _root_.RHTower.finiteThetaAmplitude M
        (_root_.RHTower.rectangleBoundaryPath
          (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t) ≠ 0) ∧
      integerThetaWindowDegree T n M = targetDeg ∧
      (∀ u : HTGeometry.UnitCircle, integerThetaLaurentLoop T n M u ≠ 0) ∧
      HTGeometry.fredholmIndex (integerThetaCollisionOperator T n M) = targetIdx := by
    intro M hNM
    have ⟨_, hsep_all, _, hmod⟩ := hcert
    have hFM_perf : ∀ z ∈ sourcePerforatedWindowSet T n N,
        _root_.RHTower.finiteThetaAmplitude M z ≠ 0 := by
      intro z hz h0
      obtain ⟨hz1, hz2, _, _⟩ := hz.1
      rw [thetaWindowLowerLeft_re] at hz1
      rw [thetaWindowUpperRight_re] at hz2
      have hre2 : |z.re| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
      have hdiff := norm_finiteThetaAmplitude_sub_prefix_le_strip hNM hre2
      rw [h0, zero_sub, norm_neg] at hdiff
      linarith [sourcePerforatedMin_le_norm hz, thetaStripTailBound_nonneg N]
    have hbdry : ∀ t : ℝ, _root_.RHTower.finiteThetaAmplitude M
        (_root_.RHTower.rectangleBoundaryPath
          (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t) ≠ 0 :=
      fun t => hFM_perf _ (rectangleBoundaryPath_mem_sourcePerforatedWindowSet hcert t)
    have hdisc_mult : ∀ w ∈ W,
        (∑ z ∈ (prefixEnclosedZeros T n M).filter (· ∈ Metric.ball w (roucheDiscRadius n)),
          (analyticOrderAt (_root_.RHTower.finiteThetaAmplitude M) z).toNat) = mN w :=
      fun _ hw => source_rouche_disc_multiplicity_eq hcert hNM hw
    let slice : ℂ → Finset ℂ :=
      fun w => (prefixEnclosedZeros T n M).filter (· ∈ Metric.ball w (roucheDiscRadius n))
    have hdisj : (W : Set ℂ).PairwiseDisjoint slice := by
      intro w₁ hw₁ w₂ hw₂ hne
      change Disjoint (slice w₁) (slice w₂)
      rw [Finset.disjoint_left]
      intro z hz₁ hz₂
      have hb₁ := Metric.mem_ball.mp (Finset.mem_filter.mp hz₁).2
      have hb₂ := Metric.mem_ball.mp (Finset.mem_filter.mp hz₂).2
      have hsep := hsep_all w₁ hw₁ w₂ hw₂ hne
      have htri := dist_triangle w₁ z w₂
      rw [dist_comm z w₁] at hb₁
      linarith [roucheDiscRadius_pos n]
    have hpart : prefixEnclosedZeros T n M = W.biUnion slice := by
      ext z
      rw [Finset.mem_biUnion]
      constructor
      · intro hz
        obtain ⟨hin, hz0⟩ := (mem_prefixEnclosedZeros_iff T n M z).mp hz
        have hrect : z ∈ windowClosedRect T n := ⟨hin.1.le, hin.2.1.le, hin.2.2.1.le, hin.2.2.2.le⟩
        by_contra hno
        have hperf : z ∈ sourcePerforatedWindowSet T n N := by
          refine ⟨hrect, ?_⟩
          simp only [Set.mem_iUnion, exists_prop, not_exists, not_and]
          intro w hw hzb
          exact hno ⟨w, hw, Finset.mem_filter.mpr ⟨hz, hzb⟩⟩
        exact hFM_perf z hperf hz0
      · rintro ⟨w, _, hzw⟩
        exact (Finset.mem_filter.mp hzw).1
    have hdeg_eq : integerThetaWindowDegree T n M = targetDeg := by
      have hbdry0 : ∀ t : ℝ, finiteThetaShellPencil M 0
          (_root_.RHTower.rectangleBoundaryPath
            (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t) ≠ 0 := by
        simpa only [finiteThetaShellPencil_zero] using hbdry
      have hd := (pencilWindowDegree_eq_sum T n M ⟨le_rfl, zero_le_one⟩ hbdry0).2
      rw [pencilWindowDegree_zero] at hd
      have hfun : finiteThetaShellPencil M 0 = _root_.RHTower.finiteThetaAmplitude M :=
        funext (finiteThetaShellPencil_zero M)
      rw [hfun] at hd
      have hd' : integerThetaWindowDegree T n M = ∑ z ∈ prefixEnclosedZeros T n M,
          (analyticOrderAt (_root_.RHTower.finiteThetaAmplitude M) z).toNat := hd
      rw [hd', hpart, Finset.sum_biUnion hdisj]
      exact Finset.sum_congr rfl fun w hw => hdisc_mult w hw
    have hpair_class : ∀ w₁ ∈ W, ∀ w₂ ∈ W, ∀ z₁ ∈ slice w₁, ∀ z₂ ∈ slice w₂,
        ((|w₁.im - w₂.im| < roucheDiscRadius n ∧ w₂.re < w₁.re) →
          zhukovskyEllipseForm n (z₁ - z₂) < 1) ∧
        (¬ (|w₁.im - w₂.im| < roucheDiscRadius n ∧ w₂.re < w₁.re) →
          1 < zhukovskyEllipseForm n (z₁ - z₂)) := by
      intro w₁ hw₁ w₂ hw₂ z₁ hz₁ z₂ hz₂
      exact source_rouche_pair_zhukovsky_class hcert hw₁ hw₂
        (Metric.mem_ball.mp (Finset.mem_filter.mp hz₁).2)
        (Metric.mem_ball.mp (Finset.mem_filter.mp hz₂).2)
    have hellipse_ne : ∀ z₁ ∈ prefixEnclosedZeros T n M, ∀ z₂ ∈ prefixEnclosedZeros T n M,
        zhukovskyEllipseForm n (z₁ - z₂) ≠ 1 := by
      intro z₁ hz₁ z₂ hz₂
      rw [hpart, Finset.mem_biUnion] at hz₁ hz₂
      obtain ⟨w₁, hw₁, hz₁_s⟩ := hz₁
      obtain ⟨w₂, hw₂, hz₂_s⟩ := hz₂
      have hcl := hpair_class w₁ hw₁ w₂ hw₂ z₁ hz₁_s z₂ hz₂_s
      by_cases h : |w₁.im - w₂.im| < roucheDiscRadius n ∧ w₂.re < w₁.re
      · exact (hcl.1 h).ne
      · exact (hcl.2 h).ne'
    obtain ⟨hL_nz, hind, _⟩ := fredholmIndex_integerThetaCollisionOperator_eq_pairSum T n M
      hbdry hellipse_ne
    refine ⟨hFM_perf, hbdry, hdeg_eq, hL_nz, ?_⟩
    rw [hind]
    dsimp only [targetIdx]
    congr 1
    rw [hpart, Finset.sum_biUnion hdisj]
    refine Finset.sum_congr rfl fun w₁ hw₁ => ?_
    have hinner : ∀ z₁ ∈ slice w₁,
        (∑ z₂ ∈ W.biUnion slice,
          ((analyticOrderAt (_root_.RHTower.finiteThetaAmplitude M) z₁).toNat : ℤ) *
            ((analyticOrderAt (_root_.RHTower.finiteThetaAmplitude M) z₂).toNat : ℤ) *
            (if zhukovskyEllipseForm n (z₁ - z₂) < 1 then 1 else 0)) =
        ∑ w₂ ∈ W,
          ((analyticOrderAt (_root_.RHTower.finiteThetaAmplitude M) z₁).toNat : ℤ) *
            (mN w₂ : ℤ) *
            (if |w₁.im - w₂.im| < roucheDiscRadius n ∧ w₂.re < w₁.re then 1 else 0) := by
      intro z₁ hz₁
      rw [Finset.sum_biUnion hdisj]
      refine Finset.sum_congr rfl fun w₂ hw₂ => ?_
      have hcond : ∀ z₂ ∈ slice w₂,
          (if zhukovskyEllipseForm n (z₁ - z₂) < 1 then (1 : ℤ) else 0) =
            if |w₁.im - w₂.im| < roucheDiscRadius n ∧ w₂.re < w₁.re then 1 else 0 := by
        intro z₂ hz₂
        have hcl := hpair_class w₁ hw₁ w₂ hw₂ z₁ hz₁ z₂ hz₂
        by_cases h : |w₁.im - w₂.im| < roucheDiscRadius n ∧ w₂.re < w₁.re
        · rw [if_pos h, if_pos (hcl.1 h)]
        · rw [if_neg h, if_neg (not_lt.mpr (hcl.2 h).le)]
      have hfactor : (∑ z₂ ∈ slice w₂,
            ((analyticOrderAt (_root_.RHTower.finiteThetaAmplitude M) z₁).toNat : ℤ) *
              ((analyticOrderAt (_root_.RHTower.finiteThetaAmplitude M) z₂).toNat : ℤ) *
              (if zhukovskyEllipseForm n (z₁ - z₂) < 1 then 1 else 0)) =
          ((analyticOrderAt (_root_.RHTower.finiteThetaAmplitude M) z₁).toNat : ℤ) *
            (∑ z₂ ∈ slice w₂,
              ((analyticOrderAt (_root_.RHTower.finiteThetaAmplitude M) z₂).toNat : ℤ)) *
            (if |w₁.im - w₂.im| < roucheDiscRadius n ∧ w₂.re < w₁.re then 1 else 0) := by
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun z₂ hz₂ => ?_
        rw [hcond z₂ hz₂]
      rw [hfactor, ← Nat.cast_sum, hdisc_mult w₂ hw₂]
    rw [Finset.sum_congr rfl hinner, Finset.sum_comm]
    refine Finset.sum_congr rfl fun w₂ _ => ?_
    have hfactor₁ : (∑ z₁ ∈ slice w₁,
          ((analyticOrderAt (_root_.RHTower.finiteThetaAmplitude M) z₁).toNat : ℤ) *
            (mN w₂ : ℤ) *
            (if |w₁.im - w₂.im| < roucheDiscRadius n ∧ w₂.re < w₁.re then 1 else 0)) =
        (∑ z₁ ∈ slice w₁,
          ((analyticOrderAt (_root_.RHTower.finiteThetaAmplitude M) z₁).toNat : ℤ)) *
          ((mN w₂ : ℤ) *
            (if |w₁.im - w₂.im| < roucheDiscRadius n ∧ w₂.re < w₁.re then 1 else 0)) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun z₁ _ => by ring
    rw [hfactor₁, ← Nat.cast_sum, hdisc_mult w₁ hw₁, mul_assoc]
  have hN := hcore N le_rfl
  intro M hNM
  have hM := hcore M hNM
  exact ⟨hM.1, hM.2.1, hM.2.2.1.trans hN.2.2.1.symm, hM.2.2.2.1,
    hM.2.2.2.2.trans hN.2.2.2.2.symm⟩

/-- **Unconditional soundness of `IsSourceAlgebraicPerforatedCertified`.**
On any stage `n ≥ thetaWindowScale T`, a single source-certified prefix `N` guarantees
`IsArtifactFreeFrom T n N` and `firstArtifactFreePrefix T n ≤ N`. -/
theorem sourceAlgebraicPerforatedCertified_sound {T : ℝ} {n N : ℕ}
    (hn : thetaWindowScale T ≤ n)
    (hcert : IsSourceAlgebraicPerforatedCertified T n N) :
    IsArtifactFreeFrom T n N ∧ firstArtifactFreePrefix T n ≤ N := by
  have hlocks := sourceAlgebraicPerforatedCertified_locks_all_ge hcert
  let M₀ := max N (thetaPrefixThreshold T n)
  have hM₀_lock := hlocks M₀ (le_max_left N (thetaPrefixThreshold T n))
  have hM₀_xi := integerThetaCollisionOperator_index_and_winding_eq_charge T hn
    (N := M₀) (le_max_right N (thetaPrefixThreshold T n))
  have hdeg_N : integerThetaWindowDegree T n N = _root_.RHTower.xiStripWindowTotalOrder T :=
    hM₀_lock.2.2.1.symm.trans hM₀_xi.2.1
  have hind_N : HTGeometry.fredholmIndex (integerThetaCollisionOperator T n N) =
      (_root_.RHTower.xiHorizontalCollisionCharge T : ℤ) :=
    hM₀_lock.2.2.2.2.symm.trans hM₀_xi.2.2.2.2.2
  have haf : IsArtifactFreeFrom T n N := by
    intro M hNM
    have hM := hlocks M hNM
    exact ⟨hM.2.1, hM.2.2.1.trans hdeg_N, hM.2.2.2.1, hM.2.2.2.2.trans hind_N⟩
  exact ⟨haf, Nat.sInf_le haf⟩

/-- Source-perforated stopping prefix `sInf {N | IsSourceAlgebraicPerforatedCertified T n N}`. -/
def sourcePerforatedStoppingPrefix (T : ℝ) (n : ℕ) : ℕ :=
  sInf {N : ℕ | IsSourceAlgebraicPerforatedCertified T n N}

/-! ### Simple-zero completeness and explicit Gaussian upper bound -/

/-- Simplicity of all zeros of `xi` in the height-`T` window `stripZeros T`. -/
def HasSimpleWindowZeros (T : ℝ) : Prop :=
  ∀ w ∈ (_root_.RHTower.stripZeros_finite T).toFinset,
    (analyticOrderAt _root_.RHTower.xi w).toNat = 1

/-- Refined Zhukovsky stage scale for simple-zero source certification, ensuring
`4 / s_n < collisionWindowGap T` and `3 / s_n ≤ windowStripLeftMargin T`. -/
def thetaSimpleZeroScale (T : ℝ) : ℕ :=
  max (thetaAnnihilationScale T)
    (max (Nat.ceil (4 / collisionWindowGap T) + 1)
      (Nat.ceil (3 / windowStripLeftMargin T)))

theorem thetaAnnihilationScale_le_simpleZeroScale (T : ℝ) :
    thetaAnnihilationScale T ≤ thetaSimpleZeroScale T :=
  le_max_left _ _

theorem thetaWindowScale_le_simpleZeroScale (T : ℝ) :
    thetaWindowScale T ≤ thetaSimpleZeroScale T :=
  (thetaWindowScale_le_annihilationScale T).trans (thetaAnnihilationScale_le_simpleZeroScale T)

private lemma four_div_stage_lt_collisionWindowGap {T : ℝ} {n : ℕ}
    (hn : thetaSimpleZeroScale T ≤ n) :
    4 / (zhukovskyStage n : ℝ) < collisionWindowGap T := by
  have hn6 : 6 ≤ n :=
    (six_le_thetaAnnihilationScale T).trans ((thetaAnnihilationScale_le_simpleZeroScale T).trans hn)
  have hceil : Nat.ceil (4 / collisionWindowGap T) + 1 ≤ n :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hn
  have hlt : 4 / collisionWindowGap T < (zhukovskyStage n : ℝ) := by
    rw [zhukovskyStage_eq_self hn6]
    have h1 := Nat.le_ceil (4 / collisionWindowGap T)
    have h2 : (Nat.ceil (4 / collisionWindowGap T) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hceil
    linarith
  have hgap := collisionWindowGap_pos T
  have hs := zhukovskyStage_pos n
  rwa [div_lt_iff₀ hs, mul_comm, ← div_lt_iff₀ hgap]

private lemma three_div_stage_le_windowStripLeftMargin {T : ℝ} {n : ℕ}
    (hn : thetaSimpleZeroScale T ≤ n) :
    3 / (zhukovskyStage n : ℝ) ≤ windowStripLeftMargin T := by
  have hn6 : 6 ≤ n :=
    (six_le_thetaAnnihilationScale T).trans ((thetaAnnihilationScale_le_simpleZeroScale T).trans hn)
  have hceil : Nat.ceil (3 / windowStripLeftMargin T) ≤ n :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hn
  have hle : 3 / windowStripLeftMargin T ≤ (zhukovskyStage n : ℝ) := by
    rw [zhukovskyStage_eq_self hn6]
    exact (Nat.le_ceil _).trans (by exact_mod_cast hceil)
  have hm := windowStripLeftMargin_pos T
  have hs := zhukovskyStage_pos n
  rw [div_le_iff₀ hs, mul_comm, ← div_le_iff₀ hm]
  exact hle

/-- Half-radius perforated window rectangle `windowClosedRect T n \ ⋃_{ρ ∈ stripZeros T} ball ρ (r_n / 2)`. -/
def halfPerforatedWindowSet (T : ℝ) (n : ℕ) : Set ℂ :=
  windowClosedRect T n \
    ⋃ w ∈ (_root_.RHTower.stripZeros_finite T).toFinset, Metric.ball w (roucheDiscRadius n / 2)

theorem isCompact_halfPerforatedWindowSet (T : ℝ) (n : ℕ) :
    IsCompact (halfPerforatedWindowSet T n) := by
  unfold halfPerforatedWindowSet
  rw [Set.sdiff_eq]
  exact (isCompact_windowClosedRect T n).inter_right
    (isOpen_biUnion fun _ _ => Metric.isOpen_ball).isClosed_compl

theorem thetaWindowLowerLeft_mem_halfPerforatedWindowSet (T : ℝ) (n : ℕ) :
    thetaWindowLowerLeft n ∈ halfPerforatedWindowSet T n := by
  refine ⟨⟨le_rfl, thetaWindow_re_le T n, le_rfl, thetaWindow_im_le T n⟩, ?_⟩
  simp only [Set.mem_iUnion, Metric.mem_ball, not_exists, not_lt]
  intro w hw
  have hw0 : 0 < w.re := ((_root_.RHTower.stripZeros_finite T).mem_toFinset.mp hw).1.1
  have hre : 1 / 2 ≤ |w.re - (thetaWindowLowerLeft n).re| := by
    rw [thetaWindowLowerLeft_re, abs_of_pos (by linarith)]
    linarith
  have hd : 1 / 2 ≤ dist (thetaWindowLowerLeft n) w := by
    rw [dist_comm, dist_eq_norm]
    exact hre.trans (by simpa only [Complex.sub_re] using
      Complex.abs_re_le_norm (w - thetaWindowLowerLeft n))
  have hr_le : roucheDiscRadius n ≤ 1 / 288 := roucheDiscRadius_le_inv_288 n
  linarith

theorem xi_ne_zero_on_halfPerforatedWindowSet {T : ℝ} {n : ℕ}
    (hn : thetaSimpleZeroScale T ≤ n) {z : ℂ} (hz : z ∈ halfPerforatedWindowSet T n) :
    _root_.RHTower.xi z ≠ 0 := by
  intro hz0
  have hzRect : z ∈ uIcc (thetaWindowLowerLeft n).re (thetaWindowUpperRight T n).re ×ℂ
      uIcc (thetaWindowLowerLeft n).im (thetaWindowUpperRight T n).im := by
    rw [uIcc_of_le (thetaWindow_re_le T n), uIcc_of_le (thetaWindow_im_le T n),
      Complex.mem_reProdIm]
    exact ⟨⟨hz.1.1, hz.1.2.1⟩, ⟨hz.1.2.2.1, hz.1.2.2.2⟩⟩
  have hzBox : z ∈ thetaWindowOpenBox T n := thetaWindowRect_subset_openBox T n hzRect
  have hzStrip : z ∈ (_root_.RHTower.stripZeros_finite T).toFinset :=
    xi_zero_in_openBox_mem_stripZeros ((thetaWindowScale_le_simpleZeroScale T).trans hn) hzBox hz0
  exact hz.2 (Set.mem_biUnion hzStrip (Metric.mem_ball_self (half_pos (roucheDiscRadius_pos n))))

/-- Minimum of `‖xi z‖` on `halfPerforatedWindowSet T n`. -/
def halfPerforatedXiMin (T : ℝ) (n : ℕ) : ℝ :=
  let hK := isCompact_halfPerforatedWindowSet T n
  let hne : (halfPerforatedWindowSet T n).Nonempty :=
    ⟨thetaWindowLowerLeft n, thetaWindowLowerLeft_mem_halfPerforatedWindowSet T n⟩
  let hcont : ContinuousOn (fun z : ℂ => ‖_root_.RHTower.xi z‖) (halfPerforatedWindowSet T n) :=
    _root_.RHTower.xi_differentiable.continuous.norm.continuousOn
  ‖_root_.RHTower.xi (hK.exists_isMinOn hne hcont).choose‖

theorem halfPerforatedXiMin_le_norm_xi {T : ℝ} {n : ℕ} {z : ℂ}
    (hz : z ∈ halfPerforatedWindowSet T n) :
    halfPerforatedXiMin T n ≤ ‖_root_.RHTower.xi z‖ := by
  unfold halfPerforatedXiMin
  dsimp only
  set hK := isCompact_halfPerforatedWindowSet T n
  set hne : (halfPerforatedWindowSet T n).Nonempty :=
    ⟨thetaWindowLowerLeft n, thetaWindowLowerLeft_mem_halfPerforatedWindowSet T n⟩
  set hcont : ContinuousOn (fun w : ℂ => ‖_root_.RHTower.xi w‖) (halfPerforatedWindowSet T n) :=
    _root_.RHTower.xi_differentiable.continuous.norm.continuousOn
  exact isMinOn_iff.mp (hK.exists_isMinOn hne hcont).choose_spec.2 z hz

theorem halfPerforatedXiMin_pos {T : ℝ} {n : ℕ} (hn : thetaSimpleZeroScale T ≤ n) :
    0 < halfPerforatedXiMin T n := by
  unfold halfPerforatedXiMin
  dsimp only
  set hK := isCompact_halfPerforatedWindowSet T n
  set hne : (halfPerforatedWindowSet T n).Nonempty :=
    ⟨thetaWindowLowerLeft n, thetaWindowLowerLeft_mem_halfPerforatedWindowSet T n⟩
  set hcont : ContinuousOn (fun w : ℂ => ‖_root_.RHTower.xi w‖) (halfPerforatedWindowSet T n) :=
    _root_.RHTower.xi_differentiable.continuous.norm.continuousOn
  exact norm_pos_iff.mpr
    (xi_ne_zero_on_halfPerforatedWindowSet hn (hK.exists_isMinOn hne hcont).choose_spec.1)

/-- Explicit Gaussian upper bound on `sourcePerforatedStoppingPrefix T n` on windows with simple
zeros of `xi`. -/
def simpleZeroStoppingPrefix (T : ℝ) (n : ℕ) : ℕ :=
  Nat.ceil (Real.sqrt (max 0 (Real.log
    (6 * (_root_.RHTower.thetaCuspIntegerTailConstant *
      _root_.RHTower.thetaAmplitudeEnvelope 2) / halfPerforatedXiMin T n))))

private lemma thetaStripTailBound_lt_sixth_halfPerforatedXiMin {T : ℝ} {n N : ℕ}
    (hn : thetaSimpleZeroScale T ≤ n) (hN : simpleZeroStoppingPrefix T n ≤ N) :
    thetaStripTailBound N < halfPerforatedXiMin T n / 6 := by
  unfold thetaStripTailBound
  set C_env : ℝ := _root_.RHTower.thetaCuspIntegerTailConstant *
    _root_.RHTower.thetaAmplitudeEnvelope 2
  set μ : ℝ := halfPerforatedXiMin T n
  have hμ : 0 < μ := halfPerforatedXiMin_pos hn
  have hC_nn : 0 ≤ C_env :=
    mul_nonneg _root_.RHTower.thetaCuspIntegerTailConstant_nonneg
      (_root_.RHTower.thetaAmplitudeEnvelope_nonneg 2)
  rcases eq_or_lt_of_le hC_nn with hC0 | hC_pos
  · rw [← hC0, zero_mul]
    linarith
  · by_cases hsmall : 6 * C_env ≤ μ
    · have hexp_lt1 : Real.exp (-((N + 1 : ℕ) : ℝ) ^ 2) < 1 := by
        rw [Real.exp_lt_one_iff]
        have h1 : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos N
        nlinarith
      calc C_env * Real.exp (-((N + 1 : ℕ) : ℝ) ^ 2)
          < C_env * 1 := mul_lt_mul_of_pos_left hexp_lt1 hC_pos
        _ ≤ μ / 6 := by linarith
    · replace hsmall : μ < 6 * C_env := not_le.mp hsmall
      have hX_gt1 : 1 < 6 * C_env / μ := (one_lt_div hμ).mpr hsmall
      have hlog_pos : 0 < Real.log (6 * C_env / μ) := Real.log_pos hX_gt1
      have hmax_eq : max 0 (Real.log (6 * C_env / μ)) = Real.log (6 * C_env / μ) :=
        max_eq_right hlog_pos.le
      have hsqrt_le : Real.sqrt (Real.log (6 * C_env / μ)) ≤ (N : ℝ) := by
        have hceil : (Nat.ceil (Real.sqrt (max 0 (Real.log (6 * C_env / μ)))) : ℝ) ≤ (N : ℝ) := by
          exact_mod_cast hN
        rw [hmax_eq] at hceil
        exact (Nat.le_ceil _).trans hceil
      have hsqrt_lt : Real.sqrt (Real.log (6 * C_env / μ)) < ((N + 1 : ℕ) : ℝ) := by
        push_cast; linarith
      have hlog_lt_sq : Real.log (6 * C_env / μ) < ((N + 1 : ℕ) : ℝ) ^ 2 := by
        have hsq := pow_lt_pow_left₀ hsqrt_lt (Real.sqrt_nonneg (Real.log (6 * C_env / μ)))
          (by norm_num : 2 ≠ 0)
        rwa [Real.sq_sqrt hlog_pos.le] at hsq
      have hexp_lt : Real.exp (-((N + 1 : ℕ) : ℝ) ^ 2) < μ / (6 * C_env) := by
        have hrhs : μ / (6 * C_env) = Real.exp (-Real.log (6 * C_env / μ)) := by
          rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
        rw [hrhs]
        exact Real.exp_lt_exp.mpr (by linarith)
      calc C_env * Real.exp (-((N + 1 : ℕ) : ℝ) ^ 2)
          < C_env * (μ / (6 * C_env)) := mul_lt_mul_of_pos_left hexp_lt hC_pos
        _ = μ / 6 := by field_simp [hC_pos.ne']

private lemma stripZeros_three_div_re_margins {T : ℝ} {n : ℕ}
    (hn : thetaSimpleZeroScale T ≤ n)
    {w : ℂ} (hw : w ∈ (_root_.RHTower.stripZeros_finite T).toFinset) :
    3 / (zhukovskyStage n : ℝ) ≤ w.re ∧ w.re ≤ 1 - 3 / (zhukovskyStage n : ℝ) := by
  have hleft : 3 / (zhukovskyStage n : ℝ) ≤ w.re :=
    (three_div_stage_le_windowStripLeftMargin hn).trans (windowStripLeftMargin_le_re hw)
  have hw_refl : _root_.RHTower.lineReflect w ∈ (_root_.RHTower.stripZeros_finite T).toFinset :=
    (_root_.RHTower.stripZeros_finite T).mem_toFinset.mpr
      (_root_.RHTower.lineReflect_mem_stripZeros
        ((_root_.RHTower.stripZeros_finite T).mem_toFinset.mp hw))
  have hrefl_le : 3 / (zhukovskyStage n : ℝ) ≤ (_root_.RHTower.lineReflect w).re :=
    (three_div_stage_le_windowStripLeftMargin hn).trans (windowStripLeftMargin_le_re hw_refl)
  rw [_root_.RHTower.lineReflect_re] at hrefl_le
  exact ⟨hleft, by linarith⟩

private lemma stripZeros_im_margins_three_rouche {T : ℝ} {n : ℕ}
    (hn : thetaSimpleZeroScale T ≤ n)
    {w : ℂ} (hw : w ∈ (_root_.RHTower.stripZeros_finite T).toFinset) :
    (thetaWindowLowerLeft n).im + 3 * roucheDiscRadius n < w.im ∧
      w.im < (thetaWindowUpperRight T n).im - 3 * roucheDiscRadius n := by
  have hwdata := (_root_.RHTower.stripZeros_finite T).mem_toFinset.mp hw
  have hTpos : 0 < T := lt_of_le_of_lt hwdata.1.2.2.1 hwdata.1.2.2.2
  have hmax : max 0 T = T := max_eq_right hTpos.le
  have hs6 : (6 : ℝ) ≤ (zhukovskyStage n : ℝ) := six_le_zhukovskyStage_real n
  have hs_pos : (0 : ℝ) < (zhukovskyStage n : ℝ) := zhukovskyStage_pos n
  have hgap4 := four_div_stage_lt_collisionWindowGap hn
  have hχ := sourceCutoff_collisionWindowRadius_eq_one hwdata.1
  have hsupp : w ∈ Function.support (sourceCutoff (collisionWindowRadius T) : ℂ → ℝ) := by
    change sourceCutoff (collisionWindowRadius T) w ≠ 0
    rw [hχ]; exact one_ne_zero
  rw [(sourceCutoff (collisionWindowRadius T)).support_eq] at hsupp
  change dist w 0 < (collisionWindowRadius T : ℝ) + 2 at hsupp
  have hwBall : w ∈ (_root_.RHTower.xi_zeros_closedBall_finite 0
      ((collisionWindowRadius T : ℝ) + 3)).toFinset := by
    apply (_root_.RHTower.xi_zeros_closedBall_finite 0
      ((collisionWindowRadius T : ℝ) + 3)).mem_toFinset.mpr
    refine ⟨?_, hwdata.2⟩
    rw [mem_closedBall]; linarith only [hsupp]
  have hwSep : w ∈ collisionWindowSeparationSet T :=
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hwBall)
  have htopSep : (⟨0, T⟩ : ℂ) ∈ collisionWindowSeparationSet T :=
    Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hgapT : collisionWindowGap T ≤ T - w.im := by
    have h1 : collisionWindowGap T ≤ |(⟨0, T⟩ : ℂ).im - w.im| :=
      (min_le_right _ _).trans
        (finiteCoordinateGap_le _ Complex.im htopSep hwSep hwdata.1.2.2.2.ne')
    simpa only [abs_of_pos (sub_pos.mpr hwdata.1.2.2.2)] using h1
  have h3r_lt_half_s : 3 * roucheDiscRadius n < 1 / (2 * (zhukovskyStage n : ℝ)) := by
    unfold roucheDiscRadius
    rw [show 3 * (1 / (8 * (zhukovskyStage n : ℝ) ^ 2)) =
      3 / (8 * (zhukovskyStage n : ℝ) ^ 2) by ring]
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have h1_lt_4 : 1 / (zhukovskyStage n : ℝ) < 4 / (zhukovskyStage n : ℝ) :=
    div_lt_div_of_pos_right (by norm_num) hs_pos
  have hhalf_add : 1 / (2 * (zhukovskyStage n : ℝ)) + 1 / (2 * (zhukovskyStage n : ℝ)) =
      1 / (zhukovskyStage n : ℝ) := by ring
  rw [thetaWindowLowerLeft_im, thetaWindowUpperRight_im, hmax]
  exact ⟨by linarith [hwdata.1.2.2.1], by linarith⟩

private lemma stripZeros_closedBall_rouche_inside {T : ℝ} {n : ℕ}
    (hn : thetaSimpleZeroScale T ≤ n)
    {w z : ℂ} (hw : w ∈ (_root_.RHTower.stripZeros_finite T).toFinset)
    (hz : z ∈ Metric.closedBall w (roucheDiscRadius n)) :
    (thetaWindowLowerLeft n).re < z.re ∧ z.re < (thetaWindowUpperRight T n).re ∧
      (thetaWindowLowerLeft n).im < z.im ∧ z.im < (thetaWindowUpperRight T n).im := by
  obtain ⟨hre_lo, hre_hi⟩ := stripZeros_three_div_re_margins hn hw
  obtain ⟨him_lo, him_hi⟩ := stripZeros_im_margins_three_rouche hn hw
  have hs_pos : (0 : ℝ) < (zhukovskyStage n : ℝ) := zhukovskyStage_pos n
  have h3s_pos : 0 < 3 / (zhukovskyStage n : ℝ) := by positivity
  have hr_le : roucheDiscRadius n ≤ 1 / 288 := roucheDiscRadius_le_inv_288 n
  have hr_pos : 0 < roucheDiscRadius n := roucheDiscRadius_pos n
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  have hre_diff : |z.re - w.re| ≤ roucheDiscRadius n := by
    calc |z.re - w.re| = |(z - w).re| := by rw [Complex.sub_re]
      _ ≤ ‖z - w‖ := Complex.abs_re_le_norm (z - w)
      _ ≤ roucheDiscRadius n := hz
  have him_diff : |z.im - w.im| ≤ roucheDiscRadius n := by
    calc |z.im - w.im| = |(z - w).im| := by rw [Complex.sub_im]
      _ ≤ ‖z - w‖ := Complex.abs_im_le_norm (z - w)
      _ ≤ roucheDiscRadius n := hz
  obtain ⟨hr1, hr2⟩ := abs_le.mp hre_diff
  obtain ⟨hi1, hi2⟩ := abs_le.mp him_diff
  rw [thetaWindowLowerLeft_re, thetaWindowUpperRight_re]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

private lemma stripZeros_dist_gt_four_div_stage {T : ℝ} {n : ℕ}
    (hn : thetaSimpleZeroScale T ≤ n)
    {w₁ w₂ : ℂ} (hw₁ : w₁ ∈ (_root_.RHTower.stripZeros_finite T).toFinset)
    (hw₂ : w₂ ∈ (_root_.RHTower.stripZeros_finite T).toFinset) (hne : w₁ ≠ w₂) :
    4 / (zhukovskyStage n : ℝ) < dist w₁ w₂ := by
  set S := (_root_.RHTower.stripZeros_finite T).toFinset
  have hd : collisionWindowGap T ≤ finiteCollisionGap S := min_le_left _ _
  have hgap_dist : collisionWindowGap T ≤ dist w₁ w₂ := by
    rw [dist_eq_norm]
    by_cases hre : w₁.re = w₂.re
    · have him : w₁.im ≠ w₂.im := fun hi => hne (Complex.ext hre hi)
      have hg : collisionWindowGap T ≤ |w₁.im - w₂.im| :=
        hd.trans ((min_le_right _ _).trans (finiteCoordinateGap_le S Complex.im hw₁ hw₂ him))
      exact hg.trans (by simpa only [Complex.sub_im] using Complex.abs_im_le_norm (w₁ - w₂))
    · have hg : collisionWindowGap T ≤ |w₁.re - w₂.re| :=
        hd.trans ((min_le_left _ _).trans (finiteCoordinateGap_le S Complex.re hw₁ hw₂ hre))
      exact hg.trans (by simpa only [Complex.sub_re] using Complex.abs_re_le_norm (w₁ - w₂))
  exact (four_div_stage_lt_collisionWindowGap hn).trans_le hgap_dist

private lemma five_rouche_lt_four_div_stage (n : ℕ) :
    5 * roucheDiscRadius n < 4 / (zhukovskyStage n : ℝ) := by
  have hs6 : (6 : ℝ) ≤ (zhukovskyStage n : ℝ) := six_le_zhukovskyStage_real n
  have hs_pos : (0 : ℝ) < (zhukovskyStage n : ℝ) := zhukovskyStage_pos n
  unfold roucheDiscRadius
  rw [show 5 * (1 / (8 * (zhukovskyStage n : ℝ) ^ 2)) =
    5 / (8 * (zhukovskyStage n : ℝ) ^ 2) by ring]
  rw [div_lt_div_iff₀ (by positivity) hs_pos]
  nlinarith

private lemma sphere_half_rouche_subset_halfPerforatedWindowSet {T : ℝ} {n : ℕ}
    (hn : thetaSimpleZeroScale T ≤ n)
    {w : ℂ} (hw : w ∈ (_root_.RHTower.stripZeros_finite T).toFinset) :
    Metric.sphere w (roucheDiscRadius n / 2) ⊆ halfPerforatedWindowSet T n := by
  intro ζ hζ
  have hζ_cb : ζ ∈ Metric.closedBall w (roucheDiscRadius n) := by
    rw [Metric.mem_closedBall, Metric.mem_sphere.mp hζ]
    linarith [roucheDiscRadius_pos n]
  obtain ⟨h1, h2, h3, h4⟩ := stripZeros_closedBall_rouche_inside hn hw hζ_cb
  refine ⟨⟨h1.le, h2.le, h3.le, h4.le⟩, ?_⟩
  simp only [Set.mem_iUnion, Metric.mem_ball, not_exists, not_lt]
  intro w' hw'
  by_cases heq : w' = w
  · rw [heq, Metric.mem_sphere.mp hζ]
  · have hsep := (five_rouche_lt_four_div_stage n).trans
      (stripZeros_dist_gt_four_div_stage hn hw hw' (Ne.symm heq))
    have htri := dist_triangle w ζ w'
    have hdist_eq : dist w ζ = roucheDiscRadius n / 2 := by
      rw [dist_comm]; exact Metric.mem_sphere.mp hζ
    linarith [roucheDiscRadius_pos n]

private lemma finiteThetaAmplitude_order_toNat_pos {N : ℕ} {z : ℂ}
    (hzero : _root_.RHTower.finiteThetaAmplitude N z = 0) :
    1 ≤ (analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) z).toNat := by
  have hfun : finiteThetaShellPencil N 0 = _root_.RHTower.finiteThetaAmplitude N :=
    funext (finiteThetaShellPencil_zero N)
  have han : AnalyticAt ℂ (_root_.RHTower.finiteThetaAmplitude N) z := by
    rw [← hfun]
    exact analyticOnNhd_finiteThetaShellPencil N 0 z (Set.mem_univ z)
  have htop : analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) z ≠ ⊤ := by
    rw [← hfun]
    exact finiteThetaShellPencil_orderAt_ne_top N ⟨le_rfl, zero_le_one⟩ z
  have h1 : analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) z ≠ 0 :=
    analyticOrderAt_ne_zero.mpr ⟨han, hzero⟩
  refine Nat.pos_of_ne_zero fun h0 => ?_
  rcases ENat.toNat_eq_zero.mp h0 with h | h
  · exact h1 h
  · exact htop h

private lemma finset_eq_singleton_of_sum_eq_one {α : Type*} [DecidableEq α] {S : Finset α}
    {f : α → ℕ} (hpos : ∀ x ∈ S, 1 ≤ f x) (hsum : ∑ x ∈ S, f x = 1) :
    ∃ w, S = {w} := by
  have hne : S.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty.mp hemp, Finset.sum_empty] at hsum
    omega
  obtain ⟨w, hw⟩ := hne
  refine ⟨w, Finset.eq_singleton_iff_unique_mem.mpr ⟨hw, fun z hz => ?_⟩⟩
  by_contra hzw
  have hsub : {z, w} ⊆ S := by
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu'
    · exact hz
    · rw [Finset.mem_singleton.mp hu']
      exact hw
  have hle : ∑ x ∈ ({z, w} : Finset α), f x ≤ ∑ x ∈ S, f x :=
    Finset.sum_le_sum_of_subset (f := f) hsub
  rw [Finset.sum_pair hzw] at hle
  have hz1 := hpos z hz
  have hw1 := hpos w hw
  omega

/-- **Simple-zero Gaussian completeness of `IsSourceAlgebraicPerforatedCertified`.**
On every height window `T : ℝ` whose `xi` zeros in `stripZeros T` are simple (`HasSimpleWindowZeros T`)
and every stage `n ≥ thetaSimpleZeroScale T`, `IsSourceAlgebraicPerforatedCertified T n N` holds
for all `N ≥ simpleZeroStoppingPrefix T n`. -/
theorem isSourceAlgebraicPerforatedCertified_of_simpleZeros {T : ℝ} {n N : ℕ}
    (hsimp : HasSimpleWindowZeros T) (hn : thetaSimpleZeroScale T ≤ n)
    (hN : simpleZeroStoppingPrefix T n ≤ N) :
    IsSourceAlgebraicPerforatedCertified T n N := by
  have htail := thetaStripTailBound_lt_sixth_halfPerforatedXiMin hn hN
  have hμ_pos : 0 < halfPerforatedXiMin T n := halfPerforatedXiMin_pos hn
  have hr_pos : 0 < roucheDiscRadius n := roucheDiscRadius_pos n
  have hr_half_pos : 0 < roucheDiscRadius n / 2 := half_pos hr_pos
  have hr_half_lt : roucheDiscRadius n / 2 < 2 * (roucheDiscRadius n / 2) := by linarith
  have hs6 : (6 : ℝ) ≤ (zhukovskyStage n : ℝ) := six_le_zhukovskyStage_real n
  have hs_pos : (0 : ℝ) < (zhukovskyStage n : ℝ) := zhukovskyStage_pos n
  have hr_lt_half_s : roucheDiscRadius n < 1 / (2 * (zhukovskyStage n : ℝ)) := by
    unfold roucheDiscRadius
    exact one_div_lt_one_div_of_lt (by positivity) (by nlinarith)
  -- Uniform error `< halfPerforatedXiMin / 6` across `windowClosedRect T n`.
  have happrox_rect : ∀ z ∈ windowClosedRect T n,
      ‖_root_.RHTower.finiteThetaAmplitude N z - _root_.RHTower.xi z‖ ≤
        thetaStripTailBound N := by
    intro z hz
    obtain ⟨hz1, hz2, _, _⟩ := hz
    rw [thetaWindowLowerLeft_re] at hz1
    rw [thetaWindowUpperRight_re] at hz2
    have hre2 : |z.re| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hbd := norm_finiteThetaAmplitude_sub_xi_le_strip N (by norm_num : (0 : ℝ) ≤ 2) hre2
    simpa only [thetaStripTailBound, mul_right_comm] using hbd
  -- Lower bound on `‖finiteThetaAmplitude N‖` across `halfPerforatedWindowSet T n`.
  have hFN_lower_half : ∀ z ∈ halfPerforatedWindowSet T n,
      halfPerforatedXiMin T n - thetaStripTailBound N ≤
        ‖_root_.RHTower.finiteThetaAmplitude N z‖ := by
    intro z hz
    have h1 := halfPerforatedXiMin_le_norm_xi hz
    have h2 := happrox_rect z hz.1
    have htri := norm_sub_norm_le (_root_.RHTower.xi z) (_root_.RHTower.finiteThetaAmplitude N z)
    rw [norm_sub_rev] at htri
    linarith
  have hFN_ne_half : ∀ z ∈ halfPerforatedWindowSet T n,
      _root_.RHTower.finiteThetaAmplitude N z ≠ 0 := by
    intro z hz h0
    have hle := hFN_lower_half z hz
    rw [h0, norm_zero] at hle
    linarith
  -- Each half-radius disc around `ρ ∈ stripZeros T` contains a unique enclosed zero of `A_N`.
  let S_xi := (_root_.RHTower.stripZeros_finite T).toFinset
  let halfSlice : ℂ → Finset ℂ :=
    fun ρ => (prefixEnclosedZeros T n N).filter (· ∈ Metric.ball ρ (roucheDiscRadius n / 2))
  have hsingleton : ∀ ρ ∈ S_xi, ∃ w, halfSlice ρ = {w} := by
    intro ρ hρ
    have hsph := sphere_half_rouche_subset_halfPerforatedWindowSet hn hρ
    have hxi_sph : ∀ ζ ∈ Metric.sphere ρ (roucheDiscRadius n / 2), _root_.RHTower.xi ζ ≠ 0 :=
      fun ζ hζ => xi_ne_zero_on_halfPerforatedWindowSet hn (hsph hζ)
    have hF_sph : ∀ ζ ∈ Metric.sphere ρ (roucheDiscRadius n / 2),
        _root_.RHTower.finiteThetaAmplitude N ζ ≠ 0 :=
      fun ζ hζ => hFN_ne_half ζ (hsph hζ)
    have hslit : ∀ ζ ∈ Metric.sphere ρ (roucheDiscRadius n / 2),
        _root_.RHTower.finiteThetaAmplitude N ζ / _root_.RHTower.xi ζ ∈ Complex.slitPlane := by
      intro ζ hζ
      have hperf := hsph hζ
      have hxi_min := halfPerforatedXiMin_le_norm_xi hperf
      have hdiff_lt : ‖_root_.RHTower.finiteThetaAmplitude N ζ - _root_.RHTower.xi ζ‖ <
          ‖_root_.RHTower.xi ζ‖ :=
        (happrox_rect ζ hperf.1).trans_lt (by linarith)
      have hq : _root_.RHTower.finiteThetaAmplitude N ζ / _root_.RHTower.xi ζ - 1 =
          (_root_.RHTower.finiteThetaAmplitude N ζ - _root_.RHTower.xi ζ) /
            _root_.RHTower.xi ζ := by
        field_simp [hxi_sph ζ hζ]
      have hq_norm : ‖_root_.RHTower.finiteThetaAmplitude N ζ / _root_.RHTower.xi ζ - 1‖ < 1 := by
        rw [hq, norm_div, div_lt_one (norm_pos_iff.mpr (hxi_sph ζ hζ))]
        exact hdiff_lt
      have hre_lt : |(_root_.RHTower.finiteThetaAmplitude N ζ / _root_.RHTower.xi ζ - 1).re| < 1 :=
        (Complex.abs_re_le_norm _).trans_lt hq_norm
      rw [Complex.sub_re, Complex.one_re] at hre_lt
      exact Complex.mem_slitPlane_iff.mpr (Or.inl (by linarith [(abs_lt.mp hre_lt).1]))
    have hF_diff : DifferentiableOn ℂ (_root_.RHTower.finiteThetaAmplitude N) Set.univ :=
      (_root_.RHTower.differentiable_finiteThetaAmplitude N).differentiableOn
    have hxi_diff : DifferentiableOn ℂ _root_.RHTower.xi Set.univ :=
      _root_.RHTower.xi_differentiable.differentiableOn
    have hzsum := HTGeometry.zeroSumBall_eq_of_quotient_mem_slitPlane hr_half_pos hr_half_lt
      isOpen_univ (Set.subset_univ _) hF_diff hxi_diff hxi_sph hslit
    obtain ⟨ZF, hZF_ball, hZF_zero, hZF_sum⟩ := HTGeometry.exists_zeroSet_zeroSumBall
      hr_half_pos hr_half_lt isOpen_univ (Set.subset_univ _) hF_diff hF_sph
    obtain ⟨ZG, hZG_ball, hZG_zero, hZG_sum⟩ := HTGeometry.exists_zeroSet_zeroSumBall
      hr_half_pos hr_half_lt isOpen_univ (Set.subset_univ _) hxi_diff hxi_sph
    have hZG_eq : ZG = {ρ} := by
      ext z
      rw [Finset.mem_singleton]
      constructor
      · intro hzG
        have hz_ball := hZG_ball z hzG
        have hz0 := (hZG_zero z hz_ball).2 hzG
        have hz_cb : z ∈ Metric.closedBall ρ (roucheDiscRadius n) :=
          Metric.ball_subset_closedBall (Metric.ball_subset_ball (by linarith) hz_ball)
        have hz_in := stripZeros_closedBall_rouche_inside hn hρ hz_cb
        have hzRect : z ∈ uIcc (thetaWindowLowerLeft n).re (thetaWindowUpperRight T n).re ×ℂ
            uIcc (thetaWindowLowerLeft n).im (thetaWindowUpperRight T n).im := by
          rw [uIcc_of_le (thetaWindow_re_le T n), uIcc_of_le (thetaWindow_im_le T n),
            Complex.mem_reProdIm]
          exact ⟨⟨hz_in.1.le, hz_in.2.1.le⟩, ⟨hz_in.2.2.1.le, hz_in.2.2.2.le⟩⟩
        have hzW : z ∈ S_xi :=
          xi_zero_in_openBox_mem_stripZeros
            ((thetaWindowScale_le_simpleZeroScale T).trans hn)
            (thetaWindowRect_subset_openBox T n hzRect) hz0
        by_contra hne
        have hsep := (five_rouche_lt_four_div_stage n).trans
          (stripZeros_dist_gt_four_div_stage hn hzW hρ hne)
        have hd_lt : dist z ρ < roucheDiscRadius n / 2 := Metric.mem_ball.mp hz_ball
        linarith
      · rintro rfl
        exact (hZG_zero z (Metric.mem_ball_self hr_half_pos)).1
          ((_root_.RHTower.stripZeros_finite T).mem_toFinset.mp hρ).2
    have hZF_eq : ZF = halfSlice ρ := by
      ext z
      rw [Finset.mem_filter, mem_prefixEnclosedZeros_iff]
      constructor
      · intro hzF
        have hzb := hZF_ball z hzF
        have hz_cb : z ∈ Metric.closedBall ρ (roucheDiscRadius n) :=
          Metric.ball_subset_closedBall (Metric.ball_subset_ball (by linarith) hzb)
        exact ⟨⟨stripZeros_closedBall_rouche_inside hn hρ hz_cb, (hZF_zero z hzb).2 hzF⟩, hzb⟩
      · rintro ⟨⟨_, hz0⟩, hzb⟩
        exact (hZF_zero z hzb).1 hz0
    rw [hZF_sum, hZG_sum, hZG_eq, hZF_eq, Finset.sum_singleton] at hzsum
    have hcast : ((∑ z ∈ halfSlice ρ,
        (analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) z).toNat : ℕ) : ℂ) =
        (((analyticOrderAt _root_.RHTower.xi ρ).toNat : ℕ) : ℂ) := by
      push_cast; exact hzsum
    have hsum1 : (∑ z ∈ halfSlice ρ,
        (analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) z).toNat) = 1 :=
      (Nat.cast_injective hcast).trans (hsimp ρ hρ)
    exact finset_eq_singleton_of_sum_eq_one
      (fun z hz => finiteThetaAmplitude_order_toNat_pos
        ((mem_prefixEnclosedZeros_iff T n N z).mp (Finset.mem_filter.mp hz).1).2)
      hsum1
  -- Every `w ∈ prefixEnclosedZeros T n N` lies in `halfSlice ρ` for some `ρ ∈ S_xi`.
  have hcover : ∀ w ∈ prefixEnclosedZeros T n N, ∃ ρ ∈ S_xi, w ∈ halfSlice ρ := by
    intro w hw
    obtain ⟨hin, hw0⟩ := (mem_prefixEnclosedZeros_iff T n N w).mp hw
    have hrect : w ∈ windowClosedRect T n := ⟨hin.1.le, hin.2.1.le, hin.2.2.1.le, hin.2.2.2.le⟩
    by_contra hno
    have hperf : w ∈ halfPerforatedWindowSet T n := by
      refine ⟨hrect, ?_⟩
      simp only [Set.mem_iUnion, exists_prop, not_exists, not_and]
      intro ρ hρ hwb
      exact hno ⟨ρ, hρ, Finset.mem_filter.mpr ⟨hw, hwb⟩⟩
    exact hFN_ne_half w hperf hw0
  -- Conversely, `sourcePerforatedWindowSet T n N ⊆ halfPerforatedWindowSet T n`.
  have hsub_perf : sourcePerforatedWindowSet T n N ⊆ halfPerforatedWindowSet T n := by
    intro z hz
    refine ⟨hz.1, ?_⟩
    intro hball
    simp only [Set.mem_iUnion, exists_prop] at hball
    obtain ⟨ρ, hρ, hz_half⟩ := hball
    obtain ⟨w, hw_eq⟩ := hsingleton ρ hρ
    have hw_mem : w ∈ halfSlice ρ := by rw [hw_eq]; exact Finset.mem_singleton_self w
    have hw_enc : w ∈ prefixEnclosedZeros T n N := (Finset.mem_filter.mp hw_mem).1
    have hw_dist : dist w ρ < roucheDiscRadius n / 2 :=
      Metric.mem_ball.mp (Finset.mem_filter.mp hw_mem).2
    have hzw : dist z w < roucheDiscRadius n := by
      have htri := dist_triangle z ρ w
      rw [dist_comm ρ w] at htri
      linarith [Metric.mem_ball.mp hz_half]
    exact hz.2 (Set.mem_biUnion hw_enc (Metric.mem_ball.mpr hzw))
  -- Establish the four conjuncts of `IsSourceAlgebraicPerforatedCertified T n N`.
  have hmarg : ∀ w ∈ prefixEnclosedZeros T n N,
      2 / (zhukovskyStage n : ℝ) ≤ w.re ∧ w.re ≤ 1 - 2 / (zhukovskyStage n : ℝ) ∧
      (thetaWindowLowerLeft n).im + 2 * roucheDiscRadius n < w.im ∧
      w.im < (thetaWindowUpperRight T n).im - 2 * roucheDiscRadius n := by
    intro w hw
    obtain ⟨ρ, hρ, hw_sl⟩ := hcover w hw
    have hw_dist : dist w ρ < roucheDiscRadius n / 2 :=
      Metric.mem_ball.mp (Finset.mem_filter.mp hw_sl).2
    rw [dist_eq_norm] at hw_dist
    have hre_d : |w.re - ρ.re| < roucheDiscRadius n / 2 :=
      lt_of_le_of_lt (by simpa only [Complex.sub_re] using Complex.abs_re_le_norm (w - ρ)) hw_dist
    have him_d : |w.im - ρ.im| < roucheDiscRadius n / 2 :=
      lt_of_le_of_lt (by simpa only [Complex.sub_im] using Complex.abs_im_le_norm (w - ρ)) hw_dist
    obtain ⟨hρ_re1, hρ_re2⟩ := stripZeros_three_div_re_margins hn hρ
    obtain ⟨hρ_im1, hρ_im2⟩ := stripZeros_im_margins_three_rouche hn hρ
    have h23 : 2 / (zhukovskyStage n : ℝ) + 1 / (zhukovskyStage n : ℝ) =
        3 / (zhukovskyStage n : ℝ) := by ring
    have hhalf_eq : 1 / (2 * (zhukovskyStage n : ℝ)) = (1 / (zhukovskyStage n : ℝ)) / 2 := by ring
    exact ⟨by linarith [(abs_lt.mp hre_d).1, hr_lt_half_s, hhalf_eq],
      by linarith [(abs_lt.mp hre_d).2, hr_lt_half_s, hhalf_eq],
      by linarith [(abs_lt.mp him_d).1],
      by linarith [(abs_lt.mp him_d).2]⟩
  refine ⟨hmarg, ?_, ?_, ?_⟩
  · -- Pairwise separation `4 * r_n < dist w₁ w₂`.
    intro w₁ hw₁ w₂ hw₂ hne
    obtain ⟨ρ₁, hρ₁, hw₁_sl⟩ := hcover w₁ hw₁
    obtain ⟨ρ₂, hρ₂, hw₂_sl⟩ := hcover w₂ hw₂
    have hρ_ne : ρ₁ ≠ ρ₂ := by
      intro heq
      rw [← heq] at hw₂_sl
      obtain ⟨w₀, hw₀_eq⟩ := hsingleton ρ₁ hρ₁
      rw [hw₀_eq] at hw₁_sl hw₂_sl
      exact hne ((Finset.mem_singleton.mp hw₁_sl).trans (Finset.mem_singleton.mp hw₂_sl).symm)
    have hdist_ρ := (five_rouche_lt_four_div_stage n).trans
      (stripZeros_dist_gt_four_div_stage hn hρ₁ hρ₂ hρ_ne)
    have hd₁ : dist w₁ ρ₁ < roucheDiscRadius n / 2 :=
      Metric.mem_ball.mp (Finset.mem_filter.mp hw₁_sl).2
    have hd₂ : dist w₂ ρ₂ < roucheDiscRadius n / 2 :=
      Metric.mem_ball.mp (Finset.mem_filter.mp hw₂_sl).2
    have htri₁ := dist_triangle ρ₁ w₁ ρ₂
    have htri₂ := dist_triangle w₁ w₂ ρ₂
    rw [dist_comm ρ₁ w₁] at htri₁
    linarith
  · -- Quasi-horizontal / vertical coordinate dichotomy.
    intro w₁ hw₁ w₂ hw₂
    obtain ⟨ρ₁, hρ₁, hw₁_sl⟩ := hcover w₁ hw₁
    obtain ⟨ρ₂, hρ₂, hw₂_sl⟩ := hcover w₂ hw₂
    have hd₁ : dist w₁ ρ₁ < roucheDiscRadius n / 2 :=
      Metric.mem_ball.mp (Finset.mem_filter.mp hw₁_sl).2
    have hd₂ : dist w₂ ρ₂ < roucheDiscRadius n / 2 :=
      Metric.mem_ball.mp (Finset.mem_filter.mp hw₂_sl).2
    rw [dist_eq_norm] at hd₁ hd₂
    have hre₁ : |w₁.re - ρ₁.re| < roucheDiscRadius n / 2 :=
      lt_of_le_of_lt (by simpa only [Complex.sub_re] using Complex.abs_re_le_norm (w₁ - ρ₁)) hd₁
    have him₁ : |w₁.im - ρ₁.im| < roucheDiscRadius n / 2 :=
      lt_of_le_of_lt (by simpa only [Complex.sub_im] using Complex.abs_im_le_norm (w₁ - ρ₁)) hd₁
    have hre₂ : |w₂.re - ρ₂.re| < roucheDiscRadius n / 2 :=
      lt_of_le_of_lt (by simpa only [Complex.sub_re] using Complex.abs_re_le_norm (w₂ - ρ₂)) hd₂
    have him₂ : |w₂.im - ρ₂.im| < roucheDiscRadius n / 2 :=
      lt_of_le_of_lt (by simpa only [Complex.sub_im] using Complex.abs_im_le_norm (w₂ - ρ₂)) hd₂
    have hgap4 := four_div_stage_lt_collisionWindowGap hn
    have hd_gap : collisionWindowGap T ≤ finiteCollisionGap S_xi := min_le_left _ _
    have h72_ident : 4 / (zhukovskyStage n : ℝ) - 1 / (2 * (zhukovskyStage n : ℝ)) =
        7 / (2 * (zhukovskyStage n : ℝ)) := by ring
    by_cases hρ_eq : ρ₁ = ρ₂
    · left
      rw [← hρ_eq] at hw₂_sl
      obtain ⟨w₀, hw₀_eq⟩ := hsingleton ρ₁ hρ₁
      rw [hw₀_eq] at hw₁_sl hw₂_sl
      have hweq : w₁ = w₂ :=
        (Finset.mem_singleton.mp hw₁_sl).trans (Finset.mem_singleton.mp hw₂_sl).symm
      exact ⟨by rw [hweq, sub_self, abs_zero]; exact hr_pos, Or.inl hweq⟩
    · by_cases him_eq : ρ₁.im = ρ₂.im
      · left
        have him_near : |w₁.im - w₂.im| < roucheDiscRadius n := by
          have hsplit : w₁.im - w₂.im = (w₁.im - ρ₁.im) - (w₂.im - ρ₂.im) := by linarith
          rw [hsplit]
          exact lt_of_le_of_lt (abs_sub _ _) (by linarith)
        have hre_ne : ρ₁.re ≠ ρ₂.re := fun hre => hρ_eq (Complex.ext hre him_eq)
        have hgap_re : collisionWindowGap T ≤ |ρ₁.re - ρ₂.re| :=
          hd_gap.trans ((min_le_left _ _).trans
            (finiteCoordinateGap_le S_xi Complex.re hρ₁ hρ₂ hre_ne))
        have htri_re : |ρ₁.re - ρ₂.re| - |w₁.re - ρ₁.re| - |w₂.re - ρ₂.re| ≤ |w₁.re - w₂.re| := by
          have h1 : ρ₁.re - ρ₂.re = (w₁.re - w₂.re) - (w₁.re - ρ₁.re) + (w₂.re - ρ₂.re) := by ring
          have h2 := abs_add_le ((w₁.re - w₂.re) - (w₁.re - ρ₁.re)) (w₂.re - ρ₂.re)
          rw [← h1] at h2
          have h3 := abs_sub (w₁.re - w₂.re) (w₁.re - ρ₁.re)
          linarith
        exact ⟨him_near, Or.inr (by linarith)⟩
      · right
        have hgap_im : collisionWindowGap T ≤ |ρ₁.im - ρ₂.im| :=
          hd_gap.trans ((min_le_right _ _).trans
            (finiteCoordinateGap_le S_xi Complex.im hρ₁ hρ₂ him_eq))
        have htri_im : |ρ₁.im - ρ₂.im| - |w₁.im - ρ₁.im| - |w₂.im - ρ₂.im| ≤ |w₁.im - w₂.im| := by
          have h1 : ρ₁.im - ρ₂.im = (w₁.im - w₂.im) - (w₁.im - ρ₁.im) + (w₂.im - ρ₂.im) := by ring
          have h2 := abs_add_le ((w₁.im - w₂.im) - (w₁.im - ρ₁.im)) (w₂.im - ρ₂.im)
          rw [← h1] at h2
          have h3 := abs_sub (w₁.im - w₂.im) (w₁.im - ρ₁.im)
          linarith
        linarith
  · -- Source modulus inequality `4 * thetaStripTailBound N < sourcePerforatedMin T n N`.
    have hll_mem : thetaWindowLowerLeft n ∈ sourcePerforatedWindowSet T n N :=
      thetaWindowLowerLeft_mem_sourcePerforatedWindowSet fun w hw => by
        have h1 := (hmarg w hw).1
        have hpos : 0 < 2 / (zhukovskyStage n : ℝ) := by positivity
        linarith
    have hne_src : (sourcePerforatedWindowSet T n N).Nonempty := ⟨thetaWindowLowerLeft n, hll_mem⟩
    unfold sourcePerforatedMin
    rw [dif_pos hne_src]
    dsimp only
    set hK := isCompact_sourcePerforatedWindowSet T n N
    set hcont : ContinuousOn (fun z : ℂ => ‖_root_.RHTower.finiteThetaAmplitude N z‖)
        (sourcePerforatedWindowSet T n N) :=
      (_root_.RHTower.differentiable_finiteThetaAmplitude N).continuous.norm.continuousOn
    set z₀ := (hK.exists_isMinOn hne_src hcont).choose
    have hz₀_mem : z₀ ∈ sourcePerforatedWindowSet T n N :=
      (hK.exists_isMinOn hne_src hcont).choose_spec.1
    have hlow := hFN_lower_half z₀ (hsub_perf hz₀_mem)
    linarith [thetaStripTailBound_nonneg N]

/-- **Simple-zero stopping rule theorem.**
Under `HasSimpleWindowZeros T` and `thetaSimpleZeroScale T ≤ n`, the purely source-intrinsic
stopping prefix `sourcePerforatedStoppingPrefix T n` satisfies `IsSourceAlgebraicPerforatedCertified`,
is bounded above by the explicit Gaussian formula `simpleZeroStoppingPrefix T n`, and certifies
`IsArtifactFreeFrom T n (sourcePerforatedStoppingPrefix T n)` and
`firstArtifactFreePrefix T n ≤ sourcePerforatedStoppingPrefix T n`. -/
theorem sourcePerforatedStoppingPrefix_complete_of_simpleZeros {T : ℝ} {n : ℕ}
    (hsimp : HasSimpleWindowZeros T) (hn : thetaSimpleZeroScale T ≤ n) :
    IsSourceAlgebraicPerforatedCertified T n (sourcePerforatedStoppingPrefix T n) ∧
    sourcePerforatedStoppingPrefix T n ≤ simpleZeroStoppingPrefix T n ∧
    IsArtifactFreeFrom T n (sourcePerforatedStoppingPrefix T n) ∧
    firstArtifactFreePrefix T n ≤ sourcePerforatedStoppingPrefix T n := by
  have hwit : simpleZeroStoppingPrefix T n ∈ {N : ℕ | IsSourceAlgebraicPerforatedCertified T n N} :=
    isSourceAlgebraicPerforatedCertified_of_simpleZeros hsimp hn le_rfl
  have hcert : IsSourceAlgebraicPerforatedCertified T n (sourcePerforatedStoppingPrefix T n) :=
    Nat.sInf_mem ⟨_, hwit⟩
  have hle : sourcePerforatedStoppingPrefix T n ≤ simpleZeroStoppingPrefix T n :=
    Nat.sInf_le hwit
  obtain ⟨haf, hfirst⟩ := sourceAlgebraicPerforatedCertified_sound
    ((thetaWindowScale_le_simpleZeroScale T).trans hn) hcert
  exact ⟨hcert, hle, haf, hfirst⟩

/-! ## §3 Root-free contour-loop modulus certificate and universal completeness -/

/-- Explicit norm ceiling `max 0 T + 3` for `rectangleBoundaryPath` on the `(T, n)` window. -/
def windowNormUpper (T : ℝ) : ℝ := max 0 T + 3

theorem one_le_windowNormUpper (T : ℝ) : 1 ≤ windowNormUpper T := by
  unfold windowNormUpper
  linarith [le_max_left (0 : ℝ) T]

theorem norm_rectangleBoundaryPath_le_windowNormUpper (T : ℝ) (n : ℕ) (t : ℝ) :
    ‖_root_.RHTower.rectangleBoundaryPath
        (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t‖ ≤ windowNormUpper T := by
  set z := _root_.RHTower.rectangleBoundaryPath
    (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t
  have hmem := _root_.RHTower.rectangleBoundaryPath_mem_reProdIm
    (thetaWindowLowerLeft n) (thetaWindowUpperRight T n)
    (thetaWindow_re_le T n) (thetaWindow_im_le T n) t
  rw [uIcc_of_le (thetaWindow_re_le T n), uIcc_of_le (thetaWindow_im_le T n),
    Complex.mem_reProdIm, thetaWindowLowerLeft_re, thetaWindowUpperRight_re,
    thetaWindowLowerLeft_im, thetaWindowUpperRight_im] at hmem
  have hs6 : (6 : ℝ) ≤ (zhukovskyStage n : ℝ) := six_le_zhukovskyStage_real n
  have hhalf_pos : 0 < 1 / (2 * (zhukovskyStage n : ℝ)) := by positivity
  have hhalf_le : 1 / (2 * (zhukovskyStage n : ℝ)) ≤ 1 / 12 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hre : |z.re| ≤ 3 / 2 := abs_le.mpr ⟨by linarith [hmem.1.1], by linarith [hmem.1.2]⟩
  have him : |z.im| ≤ max 0 T + 1 :=
    abs_le.mpr ⟨by linarith [hmem.2.1, le_max_left (0 : ℝ) T], by linarith [hmem.2.2]⟩
  unfold windowNormUpper
  linarith [Complex.norm_le_abs_re_add_abs_im z]

/-- Explicit velocity ceiling `4 * max 0 T + 9` for `rectangleBoundaryVelocity` on `(T, n)`. -/
def windowVelocityUpper (T : ℝ) : ℝ := 4 * max 0 T + 9

theorem windowVelocityUpper_pos (T : ℝ) : 0 < windowVelocityUpper T := by
  unfold windowVelocityUpper
  linarith [le_max_left (0 : ℝ) T]

theorem norm_rectangleBoundaryVelocity_le_windowVelocityUpper (T : ℝ) (n : ℕ) (t : ℝ) :
    ‖_root_.RHTower.rectangleBoundaryVelocity
        (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t‖ ≤ windowVelocityUpper T := by
  have hbd := _root_.RHTower.norm_rectangleBoundaryVelocity_le
    (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t
  have hre_sub : (thetaWindowUpperRight T n).re - (thetaWindowLowerLeft n).re = 2 := by
    rw [thetaWindowUpperRight_re, thetaWindowLowerLeft_re]; norm_num
  have him_sub : (thetaWindowUpperRight T n).im - (thetaWindowLowerLeft n).im = max 0 T := by
    rw [thetaWindowUpperRight_im, thetaWindowLowerLeft_im]; ring
  rw [hre_sub, him_sub, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_nonneg (le_max_left 0 T)] at hbd
  unfold windowVelocityUpper
  linarith

private lemma norm_inv_two_pi_I_le_one : ‖(2 * Real.pi * I : ℂ)⁻¹‖ ≤ 1 := by
  rw [norm_inv, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_I, mul_one]
  exact inv_le_one_of_one_le₀ (by linarith [Real.pi_gt_three])

private lemma abs_re_boundary_le_two (T : ℝ) (n : ℕ) (t : ℝ) :
    |(_root_.RHTower.rectangleBoundaryPath
        (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t).re| ≤ 2 := by
  have hmem := _root_.RHTower.rectangleBoundaryPath_mem_reProdIm
    (thetaWindowLowerLeft n) (thetaWindowUpperRight T n)
    (thetaWindow_re_le T n) (thetaWindow_im_le T n) t
  rw [uIcc_of_le (thetaWindow_re_le T n), Complex.mem_reProdIm,
    thetaWindowLowerLeft_re, thetaWindowUpperRight_re] at hmem
  exact abs_le.mpr ⟨by linarith [hmem.1.1], by linarith [hmem.1.2]⟩

/-- Source-intrinsic minimum of `‖finiteThetaAmplitude N‖` along `∂R_{T,n}`. -/
def boundaryPrefixMin (T : ℝ) (n N : ℕ) : ℝ :=
  let γ := _root_.RHTower.rectangleBoundaryPath
    (thetaWindowLowerLeft n) (thetaWindowUpperRight T n)
  let hK : IsCompact (Icc (0 : ℝ) 1) := isCompact_Icc
  let hne : (Icc (0 : ℝ) 1).Nonempty := nonempty_Icc.mpr zero_le_one
  let hcont : ContinuousOn (fun t : ℝ => ‖_root_.RHTower.finiteThetaAmplitude N (γ t)‖)
      (Icc (0 : ℝ) 1) :=
    (((_root_.RHTower.differentiable_finiteThetaAmplitude N).continuous.comp
      (_root_.RHTower.continuous_rectangleBoundaryPath _ _)).norm).continuousOn
  ‖_root_.RHTower.finiteThetaAmplitude N (γ (hK.exists_isMinOn hne hcont).choose)‖

theorem boundaryPrefixMin_nonneg (T : ℝ) (n N : ℕ) : 0 ≤ boundaryPrefixMin T n N :=
  norm_nonneg _

theorem boundaryPrefixMin_le_norm (T : ℝ) (n N : ℕ) (t : ℝ) :
    boundaryPrefixMin T n N ≤
      ‖_root_.RHTower.finiteThetaAmplitude N
        (_root_.RHTower.rectangleBoundaryPath
          (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t)‖ := by
  unfold boundaryPrefixMin
  dsimp only
  set γ := _root_.RHTower.rectangleBoundaryPath
    (thetaWindowLowerLeft n) (thetaWindowUpperRight T n)
  set hK : IsCompact (Icc (0 : ℝ) 1) := isCompact_Icc
  set hne : (Icc (0 : ℝ) 1).Nonempty := nonempty_Icc.mpr zero_le_one
  set hcont : ContinuousOn (fun s : ℝ => ‖_root_.RHTower.finiteThetaAmplitude N (γ s)‖)
      (Icc (0 : ℝ) 1) :=
    (((_root_.RHTower.differentiable_finiteThetaAmplitude N).continuous.comp
      (_root_.RHTower.continuous_rectangleBoundaryPath _ _)).norm).continuousOn
  have hfrac : Int.fract t ∈ Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩
  have hmin := isMinOn_iff.mp (hK.exists_isMinOn hne hcont).choose_spec.2 (Int.fract t) hfrac
  have hper : γ (Int.fract t) = γ t := by
    simp [γ, _root_.RHTower.rectangleBoundaryPath, Int.fract_fract]
  rwa [hper] at hmin

/-- Source-intrinsic minimum of `‖integerThetaBaseLoop T n N‖` on `UnitCircle`. -/
def baseLoopCircleMin (T : ℝ) (n N : ℕ) : ℝ :=
  let hK : IsCompact (Set.univ : Set HTGeometry.UnitCircle) := isCompact_univ
  let hne : (Set.univ : Set HTGeometry.UnitCircle).Nonempty :=
    ⟨HTGeometry.circleExp 0, Set.mem_univ _⟩
  let hcont : ContinuousOn (fun u : HTGeometry.UnitCircle => ‖integerThetaBaseLoop T n N u‖)
      Set.univ :=
    (integerThetaBaseLoop T n N).continuous.norm.continuousOn
  ‖integerThetaBaseLoop T n N (hK.exists_isMinOn hne hcont).choose‖

theorem baseLoopCircleMin_nonneg (T : ℝ) (n N : ℕ) : 0 ≤ baseLoopCircleMin T n N :=
  norm_nonneg _

theorem baseLoopCircleMin_le_norm (T : ℝ) (n N : ℕ) (u : HTGeometry.UnitCircle) :
    baseLoopCircleMin T n N ≤ ‖integerThetaBaseLoop T n N u‖ := by
  unfold baseLoopCircleMin
  dsimp only
  set hK : IsCompact (Set.univ : Set HTGeometry.UnitCircle) := isCompact_univ
  set hne : (Set.univ : Set HTGeometry.UnitCircle).Nonempty :=
    ⟨HTGeometry.circleExp 0, Set.mem_univ _⟩
  set hcont : ContinuousOn (fun v : HTGeometry.UnitCircle => ‖integerThetaBaseLoop T n N v‖)
      Set.univ :=
    (integerThetaBaseLoop T n N).continuous.norm.continuousOn
  exact isMinOn_iff.mp (hK.exists_isMinOn hne hcont).choose_spec.2 u (Set.mem_univ u)

/-- Explicit closed-form upper bound on `‖integerThetaWindowPowerSum T n M r -
integerThetaWindowPowerSum T n N r‖` for all `M ≥ N`. -/
def sourcePowerSumPerturbationBound (T : ℝ) (n N r : ℕ) : ℝ :=
  (windowNormUpper T) ^ r * windowVelocityUpper T *
    (8 * _root_.RHTower.thetaAmplitudeEnvelope 2 / (boundaryPrefixMin T n N) ^ 2) *
    thetaStripTailBound N

/-- Uniform upper bound on `1 + M_N` and `‖integerThetaWindowPowerSum T n M r‖` (`1 ≤ r ≤ M_N²`,
`M ≥ N`). -/
def sourcePowerSumUpper (T : ℝ) (n N : ℕ) : ℝ :=
  max (1 + (integerThetaWindowDegree T n N : ℝ))
    ((windowNormUpper T) ^ (integerThetaWindowDegree T n N ^ 2) * windowVelocityUpper T *
      (2 * _root_.RHTower.thetaAmplitudeEnvelope 2 / boundaryPrefixMin T n N))

/-- Uniform upper bound on `‖pairDiffPowerSum M_N s_M K‖` (`1 ≤ K ≤ M_N²`, `M ≥ N`). -/
def sourcePairDiffMax (T : ℝ) (n N : ℕ) : ℝ :=
  (2 : ℝ) ^ (integerThetaWindowDegree T n N ^ 2) * (sourcePowerSumUpper T n N) ^ 2

/-- Uniform upper bound on `‖pairDiffPowerSum M_N s_M K - pairDiffPowerSum M_N s_N K‖`
(`1 ≤ K ≤ M_N²`, `M ≥ N`). -/
def sourcePairDiffPerturbation (T : ℝ) (n N : ℕ) : ℝ :=
  (2 : ℝ) ^ (integerThetaWindowDegree T n N ^ 2 + 1) * sourcePowerSumUpper T n N *
    sourcePowerSumPerturbationBound T n N (integerThetaWindowDegree T n N ^ 2)

/-- Explicit closed-form Rouché perturbation bound for `integerThetaBaseLoop T n M -
integerThetaBaseLoop T n N` on `UnitCircle` across all `M ≥ N`. -/
def sourceLoopPerturbationBound (T : ℝ) (n N : ℕ) : ℝ :=
  ((integerThetaWindowDegree T n N ^ 2 + 1 : ℕ) : ℝ) *
    ((integerThetaWindowDegree T n N ^ 2 : ℕ) : ℝ) *
    (2 * sourcePairDiffMax T n N) ^ (integerThetaWindowDegree T n N ^ 2) *
    sourcePairDiffPerturbation T n N

/-- **Root-free source-intrinsic contour-loop stopping certificate at `(T, n, N)`.**
Evaluated purely from boundary and circle moduli of prefix `N`, with zero root-finding, zero `xi`
dependence, and zero multiplicity assumptions. -/
def IsSourceLoopCertified (T : ℝ) (n N : ℕ) : Prop :=
  4 * thetaStripTailBound N < boundaryPrefixMin T n N ∧
  sourcePowerSumPerturbationBound T n N 0 < 1 / 2 ∧
  sourceLoopPerturbationBound T n N < baseLoopCircleMin T n N

/-- Root-free source-intrinsic stopping prefix `sInf {N | IsSourceLoopCertified T n N}`. -/
def sourceLoopStoppingPrefix (T : ℝ) (n : ℕ) : ℕ :=
  sInf {N : ℕ | IsSourceLoopCertified T n N}

private lemma continuous_neg_firstMoment (N : ℕ) :
    Continuous (fun z : ℂ => -_root_.RHTower.finiteThetaFirstMoment N z) := by
  have heq : (fun z : ℂ => -_root_.RHTower.finiteThetaFirstMoment N z) =
      deriv (_root_.RHTower.finiteThetaAmplitude N) :=
    funext fun z => (_root_.RHTower.deriv_finiteThetaAmplitude N z).symm
  rw [heq]
  exact continuousOn_univ.mp
    (((_root_.RHTower.differentiable_finiteThetaAmplitude N).differentiableOn.deriv
      isOpen_univ).continuousOn)

/-- Prefix-to-prefix contour power-sum perturbation and magnitude bounds across all `M ≥ N`. -/
private lemma norm_integerThetaWindowPowerSum_sub_and_le {T : ℝ} {n N M : ℕ}
    (hmod : 4 * thetaStripTailBound N < boundaryPrefixMin T n N) (hNM : N ≤ M) (r : ℕ) :
    (∀ t : ℝ, _root_.RHTower.finiteThetaAmplitude M
      (_root_.RHTower.rectangleBoundaryPath
        (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t) ≠ 0) ∧
    ‖integerThetaWindowPowerSum T n M r - integerThetaWindowPowerSum T n N r‖ ≤
      sourcePowerSumPerturbationBound T n N r ∧
    ‖integerThetaWindowPowerSum T n M r‖ ≤
      (windowNormUpper T) ^ r * windowVelocityUpper T *
        (2 * _root_.RHTower.thetaAmplitudeEnvelope 2 / boundaryPrefixMin T n N) := by
  set z₁ := thetaWindowLowerLeft n
  set z₂ := thetaWindowUpperRight T n
  set γ := _root_.RHTower.rectangleBoundaryPath z₁ z₂
  set vel := _root_.RHTower.rectangleBoundaryVelocity z₁ z₂
  set b := boundaryPrefixMin T n N
  set E := _root_.RHTower.thetaAmplitudeEnvelope 2
  have hb_pos : 0 < b := lt_of_le_of_lt (by positivity [thetaStripTailBound_nonneg N]) hmod
  have hE_nn : 0 ≤ E := _root_.RHTower.thetaAmplitudeEnvelope_nonneg 2
  have hγ_cont : Continuous γ := _root_.RHTower.continuous_rectangleBoundaryPath z₁ z₂
  have hBM_lower : ∀ t : ℝ, b / 2 ≤ ‖_root_.RHTower.finiteThetaAmplitude M (γ t)‖ := by
    intro t
    have hBN := boundaryPrefixMin_le_norm T n N t
    have hdiff := norm_finiteThetaAmplitude_sub_prefix_le_strip hNM (abs_re_boundary_le_two T n t)
    have htri := norm_sub_norm_le (_root_.RHTower.finiteThetaAmplitude N (γ t))
      (_root_.RHTower.finiteThetaAmplitude M (γ t))
    rw [norm_sub_rev] at htri
    linarith
  have hBM_nz : ∀ t : ℝ, _root_.RHTower.finiteThetaAmplitude M (γ t) ≠ 0 := by
    intro t h0
    have h := hBM_lower t
    rw [h0, norm_zero] at h
    linarith
  have hBN_nz : ∀ t : ℝ, _root_.RHTower.finiteThetaAmplitude N (γ t) ≠ 0 := by
    intro t h0
    have h := boundaryPrefixMin_le_norm T n N t
    rw [h0, norm_zero] at h
    linarith
  let g : ℕ → ℂ → ℂ := fun K z => z ^ r *
    (-_root_.RHTower.finiteThetaFirstMoment K z / _root_.RHTower.finiteThetaAmplitude K z)
  have hgM_cont : Continuous (fun t : ℝ => g M (γ t)) :=
    (hγ_cont.pow r).mul
      (((continuous_neg_firstMoment M).comp hγ_cont).div
        (((_root_.RHTower.differentiable_finiteThetaAmplitude M).continuous).comp hγ_cont)
        hBM_nz)
  have hgN_cont : Continuous (fun t : ℝ => g N (γ t)) :=
    (hγ_cont.pow r).mul
      (((continuous_neg_firstMoment N).comp hγ_cont).div
        (((_root_.RHTower.differentiable_finiteThetaAmplitude N).continuous).comp hγ_cont)
        hBN_nz)
  refine ⟨hBM_nz, ?_, ?_⟩
  · -- Perturbation bound `‖s_M(r) - s_N(r)‖ ≤ sourcePowerSumPerturbationBound T n N r`.
    unfold integerThetaWindowPowerSum
    rw [← mul_sub, norm_mul,
      ← _root_.RHTower.integral_rectangleBoundary_eq_rectIntegral z₁ z₂ (g M) hgM_cont,
      ← _root_.RHTower.integral_rectangleBoundary_eq_rectIntegral z₁ z₂ (g N) hgN_cont]
    have hIntM := _root_.RHTower.intervalIntegrable_mul_rectangleBoundaryVelocity
      z₁ z₂ hgM_cont 0 1
    have hIntN := _root_.RHTower.intervalIntegrable_mul_rectangleBoundaryVelocity
      z₁ z₂ hgN_cont 0 1
    rw [← intervalIntegral.integral_sub hIntM hIntN]
    have hpt : ∀ t ∈ uIoc (0 : ℝ) 1,
        ‖g M (γ t) * vel t - g N (γ t) * vel t‖ ≤ sourcePowerSumPerturbationBound T n N r := by
      intro t _ht
      have hre2 := abs_re_boundary_le_two T n t
      set A_M := -_root_.RHTower.finiteThetaFirstMoment M (γ t)
      set B_M := _root_.RHTower.finiteThetaAmplitude M (γ t)
      set A_N := -_root_.RHTower.finiteThetaFirstMoment N (γ t)
      set B_N := _root_.RHTower.finiteThetaAmplitude N (γ t)
      have hquot : A_M / B_M - A_N / B_N =
          ((A_M - A_N) * B_N + A_N * (B_N - B_M)) / (B_M * B_N) := by
        rw [div_sub_div _ _ (hBM_nz t) (hBN_nz t)]
        congr 1; ring
      have hAM_AN : ‖A_M - A_N‖ ≤ 2 * thetaStripTailBound N :=
        norm_finiteThetaFirstMoment_sub_prefix_le_strip hNM hre2
      have hBN_BM : ‖B_N - B_M‖ ≤ 2 * thetaStripTailBound N := by
        rw [norm_sub_rev]
        exact norm_finiteThetaAmplitude_sub_prefix_le_strip hNM hre2
      have hBN_le : ‖B_N‖ ≤ E :=
        _root_.RHTower.norm_finiteThetaAmplitude_le_strip N (by norm_num) hre2
      have hAN_le : ‖A_N‖ ≤ E := by
        simpa only [A_N, norm_neg] using
          norm_finiteThetaFirstMoment_le_strip N (by norm_num) hre2
      have hnum_le : ‖(A_M - A_N) * B_N + A_N * (B_N - B_M)‖ ≤
          4 * E * thetaStripTailBound N := by
        calc ‖(A_M - A_N) * B_N + A_N * (B_N - B_M)‖
            ≤ ‖A_M - A_N‖ * ‖B_N‖ + ‖A_N‖ * ‖B_N - B_M‖ := by
              simpa only [norm_mul] using norm_add_le ((A_M - A_N) * B_N) (A_N * (B_N - B_M))
          _ ≤ (2 * thetaStripTailBound N) * E + E * (2 * thetaStripTailBound N) :=
              add_le_add
                (mul_le_mul hAM_AN hBN_le (norm_nonneg _)
                  (mul_nonneg (by norm_num) (thetaStripTailBound_nonneg N)))
                (mul_le_mul hAN_le hBN_BM (norm_nonneg _) hE_nn)
          _ = 4 * E * thetaStripTailBound N := by ring
      have hdenom_pos : 0 < b ^ 2 / 2 := by positivity
      have hdenom_le : b ^ 2 / 2 ≤ ‖B_M * B_N‖ := by
        rw [norm_mul]
        calc b ^ 2 / 2 = (b / 2) * b := by ring
          _ ≤ ‖B_M‖ * ‖B_N‖ :=
            mul_le_mul (hBM_lower t) (boundaryPrefixMin_le_norm T n N t)
              (by positivity) (norm_nonneg _)
      have hquot_le : ‖A_M / B_M - A_N / B_N‖ ≤ (8 * E / b ^ 2) * thetaStripTailBound N := by
        rw [hquot, norm_div]
        have hBB_pos : 0 < ‖B_M * B_N‖ := lt_of_lt_of_le hdenom_pos hdenom_le
        calc ‖(A_M - A_N) * B_N + A_N * (B_N - B_M)‖ / ‖B_M * B_N‖
            ≤ (4 * E * thetaStripTailBound N) / (b ^ 2 / 2) := by
              rw [div_le_div_iff₀ hBB_pos hdenom_pos]
              exact mul_le_mul hnum_le hdenom_le hdenom_pos.le
                (mul_nonneg (mul_nonneg (by norm_num) hE_nn) (thetaStripTailBound_nonneg N))
          _ = (8 * E / b ^ 2) * thetaStripTailBound N := by
              field_simp [hb_pos.ne']; ring
      have halg : g M (γ t) * vel t - g N (γ t) * vel t =
          (γ t) ^ r * (A_M / B_M - A_N / B_N) * vel t := by
        dsimp [g]; ring
      rw [halg, norm_mul, norm_mul, norm_pow]
      have hpow_le : ‖γ t‖ ^ r ≤ (windowNormUpper T) ^ r :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_rectangleBoundaryPath_le_windowNormUpper T n t) r
      have hvel_le := norm_rectangleBoundaryVelocity_le_windowVelocityUpper T n t
      calc ‖γ t‖ ^ r * ‖A_M / B_M - A_N / B_N‖ * ‖vel t‖
          ≤ ((windowNormUpper T) ^ r * ((8 * E / b ^ 2) * thetaStripTailBound N)) *
              windowVelocityUpper T := by
            refine mul_le_mul ?_ hvel_le (norm_nonneg _)
              (mul_nonneg (pow_nonneg (zero_le_one.trans (one_le_windowNormUpper T)) r)
                (mul_nonneg (div_nonneg (mul_nonneg (by norm_num) hE_nn) (sq_nonneg b))
                  (thetaStripTailBound_nonneg N)))
            exact mul_le_mul hpow_le hquot_le (norm_nonneg _)
              (pow_nonneg (zero_le_one.trans (one_le_windowNormUpper T)) r)
        _ = sourcePowerSumPerturbationBound T n N r := by
            unfold sourcePowerSumPerturbationBound; ring
    have hint := intervalIntegral.norm_integral_le_of_norm_le_const hpt
    have h10 : |(1 : ℝ) - 0| = 1 := by norm_num
    rw [h10, mul_one] at hint
    have hpert_nn : 0 ≤ sourcePowerSumPerturbationBound T n N r := by
      unfold sourcePowerSumPerturbationBound
      exact mul_nonneg (mul_nonneg (mul_nonneg
        (pow_nonneg (zero_le_one.trans (one_le_windowNormUpper T)) r)
        (windowVelocityUpper_pos T).le) (by positivity)) (thetaStripTailBound_nonneg N)
    calc ‖(2 * Real.pi * I : ℂ)⁻¹‖ *
            ‖∫ t in (0 : ℝ)..1, (g M (γ t) * vel t - g N (γ t) * vel t)‖
        ≤ 1 * sourcePowerSumPerturbationBound T n N r :=
          mul_le_mul norm_inv_two_pi_I_le_one hint (norm_nonneg _) zero_le_one
      _ = sourcePowerSumPerturbationBound T n N r := one_mul _
  · -- Magnitude bound `‖s_M(r)‖ ≤ (windowNormUpper T)^r * windowVelocityUpper T * (2 * E / b)`.
    unfold integerThetaWindowPowerSum
    rw [norm_mul, ← _root_.RHTower.integral_rectangleBoundary_eq_rectIntegral z₁ z₂ (g M) hgM_cont]
    have hpt : ∀ t ∈ uIoc (0 : ℝ) 1,
        ‖g M (γ t) * vel t‖ ≤
          (windowNormUpper T) ^ r * windowVelocityUpper T * (2 * E / b) := by
      intro t _ht
      have hre2 := abs_re_boundary_le_two T n t
      have hAM_le : ‖-_root_.RHTower.finiteThetaFirstMoment M (γ t)‖ ≤ E := by
        rw [norm_neg]
        exact norm_finiteThetaFirstMoment_le_strip M (by norm_num) hre2
      have hBM_pos : 0 < ‖_root_.RHTower.finiteThetaAmplitude M (γ t)‖ :=
        lt_of_lt_of_le (half_pos hb_pos) (hBM_lower t)
      have hquot_le :
          ‖-_root_.RHTower.finiteThetaFirstMoment M (γ t) /
            _root_.RHTower.finiteThetaAmplitude M (γ t)‖ ≤ 2 * E / b := by
        rw [norm_div]
        calc ‖-_root_.RHTower.finiteThetaFirstMoment M (γ t)‖ /
              ‖_root_.RHTower.finiteThetaAmplitude M (γ t)‖
            ≤ E / (b / 2) := by
              rw [div_le_div_iff₀ hBM_pos (half_pos hb_pos)]
              exact mul_le_mul hAM_le (hBM_lower t) (half_pos hb_pos).le hE_nn
          _ = 2 * E / b := by field_simp [hb_pos.ne']
      dsimp only [g]
      rw [norm_mul, norm_mul, norm_pow]
      have hpow_le : ‖γ t‖ ^ r ≤ (windowNormUpper T) ^ r :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_rectangleBoundaryPath_le_windowNormUpper T n t) r
      have hvel_le := norm_rectangleBoundaryVelocity_le_windowVelocityUpper T n t
      calc ‖γ t‖ ^ r *
            ‖-_root_.RHTower.finiteThetaFirstMoment M (γ t) /
              _root_.RHTower.finiteThetaAmplitude M (γ t)‖ * ‖vel t‖
          ≤ ((windowNormUpper T) ^ r * (2 * E / b)) * windowVelocityUpper T := by
            refine mul_le_mul ?_ hvel_le (norm_nonneg _)
              (mul_nonneg (pow_nonneg (zero_le_one.trans (one_le_windowNormUpper T)) r)
                (div_nonneg (mul_nonneg (by norm_num) hE_nn) hb_pos.le))
            exact mul_le_mul hpow_le hquot_le (norm_nonneg _)
              (pow_nonneg (zero_le_one.trans (one_le_windowNormUpper T)) r)
        _ = (windowNormUpper T) ^ r * windowVelocityUpper T * (2 * E / b) := by ring
    have hint := intervalIntegral.norm_integral_le_of_norm_le_const hpt
    have h10 : |(1 : ℝ) - 0| = 1 := by norm_num
    rw [h10, mul_one] at hint
    calc ‖(2 * Real.pi * I : ℂ)⁻¹‖ * ‖∫ t in (0 : ℝ)..1, g M (γ t) * vel t‖
        ≤ 1 * ((windowNormUpper T) ^ r * windowVelocityUpper T * (2 * E / b)) :=
          mul_le_mul norm_inv_two_pi_I_le_one hint (norm_nonneg _) zero_le_one
      _ = (windowNormUpper T) ^ r * windowVelocityUpper T * (2 * E / b) := one_mul _

/-- Exact `(k + 1)⁻¹`-cancelling magnitude bound for Newton elementary symmetric values. -/
private lemma norm_newtonElem_le_pow {d : ℕ → ℂ} {L : ℕ} {D : ℝ}
    (hD : 1 ≤ D) (hd : ∀ j, 1 ≤ j → j ≤ L → ‖d j‖ ≤ D) :
    ∀ k ≤ L, ‖newtonElem d k‖ ≤ D ^ k := by
  intro k hk
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases k with _ | k
    · simp [newtonElem]
    · have hinv_norm : ‖((k : ℂ) + 1)⁻¹‖ = (((k + 1 : ℕ) : ℝ))⁻¹ := by
        have hcast : ((k : ℂ) + 1) = (((k + 1 : ℕ) : ℝ) : ℂ) := by push_cast; ring
        rw [hcast, norm_inv, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by exact_mod_cast Nat.succ_pos k)]
      rw [newtonElem, norm_mul, hinv_norm]
      have hsum_le :
          ‖∑ j ∈ Finset.range (k + 1), (-1 : ℂ) ^ j * newtonElem d (k - j) * d (j + 1)‖ ≤
            ((k + 1 : ℕ) : ℝ) * D ^ (k + 1) := by
        calc ‖∑ j ∈ Finset.range (k + 1), (-1 : ℂ) ^ j * newtonElem d (k - j) * d (j + 1)‖
            ≤ ∑ j ∈ Finset.range (k + 1),
                ‖(-1 : ℂ) ^ j * newtonElem d (k - j) * d (j + 1)‖ := norm_sum_le _ _
          _ ≤ ∑ _j ∈ Finset.range (k + 1), D ^ (k + 1) := by
              refine Finset.sum_le_sum fun j hj => ?_
              have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
              rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
              calc ‖newtonElem d (k - j)‖ * ‖d (j + 1)‖
                  ≤ D ^ (k - j) * D :=
                    mul_le_mul (ih (k - j) (by omega) (by omega))
                      (hd (j + 1) (by omega) (by omega))
                      (norm_nonneg _) (pow_nonneg (zero_le_one.trans hD) _)
                _ = D ^ (k - j + 1) := (pow_succ D (k - j)).symm
                _ ≤ D ^ (k + 1) := pow_le_pow_right₀ hD (by omega)
          _ = ((k + 1 : ℕ) : ℝ) * D ^ (k + 1) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hk1_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
      calc (((k + 1 : ℕ) : ℝ))⁻¹ *
            ‖∑ j ∈ Finset.range (k + 1), (-1 : ℂ) ^ j * newtonElem d (k - j) * d (j + 1)‖
          ≤ (((k + 1 : ℕ) : ℝ))⁻¹ * (((k + 1 : ℕ) : ℝ) * D ^ (k + 1)) :=
            mul_le_mul_of_nonneg_left hsum_le (inv_nonneg.mpr hk1_pos.le)
        _ = D ^ (k + 1) := inv_mul_cancel_left₀ hk1_pos.ne' _

/-- Exact `(k + 1)⁻¹`-cancelling Lipschitz bound for Newton elementary symmetric values. -/
private lemma norm_newtonElem_sub_le {d₁ d₂ : ℕ → ℂ} {L : ℕ} {D δ : ℝ}
    (hD : 1 ≤ D) (hδ : 0 ≤ δ)
    (hd₁ : ∀ j, 1 ≤ j → j ≤ L → ‖d₁ j‖ ≤ D)
    (hd₂ : ∀ j, 1 ≤ j → j ≤ L → ‖d₂ j‖ ≤ D)
    (hsub : ∀ j, 1 ≤ j → j ≤ L → ‖d₁ j - d₂ j‖ ≤ δ) :
    ∀ k ≤ L, ‖newtonElem d₁ k - newtonElem d₂ k‖ ≤ (k : ℝ) * D ^ k * δ := by
  intro k hk
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases k with _ | k
    · simp [newtonElem]
    · have hinv_norm : ‖((k : ℂ) + 1)⁻¹‖ = (((k + 1 : ℕ) : ℝ))⁻¹ := by
        have hcast : ((k : ℂ) + 1) = (((k + 1 : ℕ) : ℝ) : ℂ) := by push_cast; ring
        rw [hcast, norm_inv, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by exact_mod_cast Nat.succ_pos k)]
      rw [newtonElem, newtonElem, ← mul_sub, norm_mul, hinv_norm, ← Finset.sum_sub_distrib]
      have hD_nn : 0 ≤ D := zero_le_one.trans hD
      have hsum_le :
          ‖∑ j ∈ Finset.range (k + 1),
              ((-1 : ℂ) ^ j * newtonElem d₁ (k - j) * d₁ (j + 1) -
                (-1 : ℂ) ^ j * newtonElem d₂ (k - j) * d₂ (j + 1))‖ ≤
            ((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) * D ^ (k + 1) * δ) := by
        calc ‖∑ j ∈ Finset.range (k + 1),
                ((-1 : ℂ) ^ j * newtonElem d₁ (k - j) * d₁ (j + 1) -
                  (-1 : ℂ) ^ j * newtonElem d₂ (k - j) * d₂ (j + 1))‖
            ≤ ∑ j ∈ Finset.range (k + 1),
                ‖(-1 : ℂ) ^ j * newtonElem d₁ (k - j) * d₁ (j + 1) -
                  (-1 : ℂ) ^ j * newtonElem d₂ (k - j) * d₂ (j + 1)‖ := norm_sum_le _ _
          _ ≤ ∑ _j ∈ Finset.range (k + 1), (((k + 1 : ℕ) : ℝ) * D ^ (k + 1) * δ) := by
              refine Finset.sum_le_sum fun j hj => ?_
              have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
              have hsplit :
                  (-1 : ℂ) ^ j * newtonElem d₁ (k - j) * d₁ (j + 1) -
                    (-1 : ℂ) ^ j * newtonElem d₂ (k - j) * d₂ (j + 1) =
                  (-1 : ℂ) ^ j *
                    ((newtonElem d₁ (k - j) - newtonElem d₂ (k - j)) * d₁ (j + 1) +
                      newtonElem d₂ (k - j) * (d₁ (j + 1) - d₂ (j + 1))) := by ring
              rw [hsplit, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
              have hterm1 :
                  ‖(newtonElem d₁ (k - j) - newtonElem d₂ (k - j)) * d₁ (j + 1)‖ ≤
                    (k : ℝ) * D ^ (k + 1) * δ := by
                rw [norm_mul]
                have hrec := ih (k - j) (by omega) (by omega)
                have hd₁_j := hd₁ (j + 1) (by omega) (by omega)
                have hk_le : ((k - j : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.sub_le k j
                have hpow_le : D ^ (k - j + 1) ≤ D ^ (k + 1) := pow_le_pow_right₀ hD (by omega)
                calc ‖newtonElem d₁ (k - j) - newtonElem d₂ (k - j)‖ * ‖d₁ (j + 1)‖
                    ≤ (((k - j : ℕ) : ℝ) * D ^ (k - j) * δ) * D :=
                      mul_le_mul hrec hd₁_j (norm_nonneg _) (by positivity)
                  _ = ((k - j : ℕ) : ℝ) * D ^ (k - j + 1) * δ := by rw [pow_succ]; ring
                  _ ≤ (k : ℝ) * D ^ (k + 1) * δ := by
                      refine mul_le_mul_of_nonneg_right ?_ hδ
                      exact mul_le_mul hk_le hpow_le (pow_nonneg hD_nn _) (Nat.cast_nonneg k)
              have hterm2 :
                  ‖newtonElem d₂ (k - j) * (d₁ (j + 1) - d₂ (j + 1))‖ ≤ D ^ (k + 1) * δ := by
                rw [norm_mul]
                have he₂ := norm_newtonElem_le_pow hD hd₂ (k - j) (by omega)
                have hpow_le : D ^ (k - j) ≤ D ^ (k + 1) := pow_le_pow_right₀ hD (by omega)
                calc ‖newtonElem d₂ (k - j)‖ * ‖d₁ (j + 1) - d₂ (j + 1)‖
                    ≤ D ^ (k - j) * δ :=
                      mul_le_mul he₂ (hsub (j + 1) (by omega) (by omega))
                        (norm_nonneg _) (pow_nonneg hD_nn _)
                  _ ≤ D ^ (k + 1) * δ := mul_le_mul_of_nonneg_right hpow_le hδ
              calc ‖(newtonElem d₁ (k - j) - newtonElem d₂ (k - j)) * d₁ (j + 1) +
                      newtonElem d₂ (k - j) * (d₁ (j + 1) - d₂ (j + 1))‖
                  ≤ (k : ℝ) * D ^ (k + 1) * δ + D ^ (k + 1) * δ :=
                    (norm_add_le _ _).trans (add_le_add hterm1 hterm2)
                _ = ((k + 1 : ℕ) : ℝ) * D ^ (k + 1) * δ := by push_cast; ring
          _ = ((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) * D ^ (k + 1) * δ) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hk1_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
      calc (((k + 1 : ℕ) : ℝ))⁻¹ *
            ‖∑ j ∈ Finset.range (k + 1),
              ((-1 : ℂ) ^ j * newtonElem d₁ (k - j) * d₁ (j + 1) -
                (-1 : ℂ) ^ j * newtonElem d₂ (k - j) * d₂ (j + 1))‖
          ≤ (((k + 1 : ℕ) : ℝ))⁻¹ * (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) * D ^ (k + 1) * δ)) :=
            mul_le_mul_of_nonneg_left hsum_le (inv_nonneg.mpr hk1_pos.le)
        _ = ((k + 1 : ℕ) : ℝ) * D ^ (k + 1) * δ := inv_mul_cancel_left₀ hk1_pos.ne' _

private lemma sum_range_choose_real (K : ℕ) :
    (∑ r ∈ Finset.range (K + 1), (Nat.choose K r : ℝ)) = (2 : ℝ) ^ K := by
  exact_mod_cast Nat.sum_range_choose K

/-- Binomial convolution magnitude bound `‖pairDiffPowerSum M s K‖ ≤ 2^(M²) S²`. -/
private lemma norm_pairDiffPowerSum_le {M : ℕ} {s : ℕ → ℂ} {S : ℝ}
    (hS : (M : ℝ) ≤ S) (hS_nn : 0 ≤ S)
    (hs : ∀ r, 1 ≤ r → r ≤ M ^ 2 → ‖s r‖ ≤ S) :
    ∀ K, 1 ≤ K → K ≤ M ^ 2 → ‖pairDiffPowerSum M s K‖ ≤ (2 : ℝ) ^ (M ^ 2) * S ^ 2 := by
  intro K _hK1 hKL
  let s₀ : ℕ → ℂ := fun r => if r = 0 then (M : ℂ) else s r
  have hs₀ : ∀ r ≤ K, ‖s₀ r‖ ≤ S := by
    intro r hr
    dsimp only [s₀]
    by_cases hr0 : r = 0
    · rw [if_pos hr0, Complex.norm_natCast]
      exact hS
    · rw [if_neg hr0]
      exact hs r (Nat.pos_of_ne_zero hr0) (hr.trans hKL)
  unfold pairDiffPowerSum
  dsimp only
  calc ‖∑ r ∈ Finset.range (K + 1),
          (-1 : ℂ) ^ (K - r) * (Nat.choose K r : ℂ) * s₀ r * s₀ (K - r)‖
      ≤ ∑ r ∈ Finset.range (K + 1),
          ‖(-1 : ℂ) ^ (K - r) * (Nat.choose K r : ℂ) * s₀ r * s₀ (K - r)‖ := norm_sum_le _ _
    _ ≤ ∑ r ∈ Finset.range (K + 1), (Nat.choose K r : ℝ) * S ^ 2 := by
        refine Finset.sum_le_sum fun r hr => ?_
        have hrK : r ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
        rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
          Complex.norm_natCast, mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        rw [sq]
        exact mul_le_mul (hs₀ r hrK) (hs₀ (K - r) (Nat.sub_le K r)) (norm_nonneg _) hS_nn
    _ = ((∑ r ∈ Finset.range (K + 1), (Nat.choose K r : ℝ))) * S ^ 2 :=
        (Finset.sum_mul _ _ _).symm
    _ = (2 : ℝ) ^ K * S ^ 2 := by rw [sum_range_choose_real]
    _ ≤ (2 : ℝ) ^ (M ^ 2) * S ^ 2 :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hKL) (sq_nonneg S)

/-- Binomial convolution Lipschitz bound `‖pairDiffPowerSum M s₁ K - pairDiffPowerSum M s₂ K‖ ≤
2^(M² + 1) S Δ`. -/
private lemma norm_pairDiffPowerSum_sub_le {M : ℕ} {s₁ s₂ : ℕ → ℂ} {S Δ : ℝ}
    (hS : (M : ℝ) ≤ S) (hS_nn : 0 ≤ S) (hΔ_nn : 0 ≤ Δ)
    (hs₁ : ∀ r, 1 ≤ r → r ≤ M ^ 2 → ‖s₁ r‖ ≤ S)
    (hs₂ : ∀ r, 1 ≤ r → r ≤ M ^ 2 → ‖s₂ r‖ ≤ S)
    (hsub : ∀ r, 1 ≤ r → r ≤ M ^ 2 → ‖s₁ r - s₂ r‖ ≤ Δ) :
    ∀ K, 1 ≤ K → K ≤ M ^ 2 →
      ‖pairDiffPowerSum M s₁ K - pairDiffPowerSum M s₂ K‖ ≤
        (2 : ℝ) ^ (M ^ 2 + 1) * S * Δ := by
  intro K _hK1 hKL
  let a₁ : ℕ → ℂ := fun r => if r = 0 then (M : ℂ) else s₁ r
  let a₂ : ℕ → ℂ := fun r => if r = 0 then (M : ℂ) else s₂ r
  have ha₁ : ∀ r ≤ K, ‖a₁ r‖ ≤ S := by
    intro r hr
    dsimp only [a₁]
    by_cases hr0 : r = 0
    · rw [if_pos hr0, Complex.norm_natCast]; exact hS
    · rw [if_neg hr0]; exact hs₁ r (Nat.pos_of_ne_zero hr0) (hr.trans hKL)
  have ha₂ : ∀ r ≤ K, ‖a₂ r‖ ≤ S := by
    intro r hr
    dsimp only [a₂]
    by_cases hr0 : r = 0
    · rw [if_pos hr0, Complex.norm_natCast]; exact hS
    · rw [if_neg hr0]; exact hs₂ r (Nat.pos_of_ne_zero hr0) (hr.trans hKL)
  have ha_sub : ∀ r ≤ K, ‖a₁ r - a₂ r‖ ≤ Δ := by
    intro r hr
    dsimp only [a₁, a₂]
    by_cases hr0 : r = 0
    · rw [if_pos hr0, if_pos hr0, sub_self, norm_zero]; exact hΔ_nn
    · rw [if_neg hr0, if_neg hr0]; exact hsub r (Nat.pos_of_ne_zero hr0) (hr.trans hKL)
  unfold pairDiffPowerSum
  dsimp only
  rw [← Finset.sum_sub_distrib]
  calc ‖∑ r ∈ Finset.range (K + 1),
          ((-1 : ℂ) ^ (K - r) * (Nat.choose K r : ℂ) * a₁ r * a₁ (K - r) -
            (-1 : ℂ) ^ (K - r) * (Nat.choose K r : ℂ) * a₂ r * a₂ (K - r))‖
      ≤ ∑ r ∈ Finset.range (K + 1),
          ‖(-1 : ℂ) ^ (K - r) * (Nat.choose K r : ℂ) * a₁ r * a₁ (K - r) -
            (-1 : ℂ) ^ (K - r) * (Nat.choose K r : ℂ) * a₂ r * a₂ (K - r)‖ := norm_sum_le _ _
    _ ≤ ∑ r ∈ Finset.range (K + 1), (Nat.choose K r : ℝ) * (2 * S * Δ) := by
        refine Finset.sum_le_sum fun r hr => ?_
        have hrK : r ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
        have hsplit :
            (-1 : ℂ) ^ (K - r) * (Nat.choose K r : ℂ) * a₁ r * a₁ (K - r) -
              (-1 : ℂ) ^ (K - r) * (Nat.choose K r : ℂ) * a₂ r * a₂ (K - r) =
            (-1 : ℂ) ^ (K - r) * (Nat.choose K r : ℂ) *
              ((a₁ r - a₂ r) * a₁ (K - r) + a₂ r * (a₁ (K - r) - a₂ (K - r))) := by ring
        rw [hsplit, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
          Complex.norm_natCast]
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        have h1 : ‖(a₁ r - a₂ r) * a₁ (K - r)‖ ≤ Δ * S := by
          rw [norm_mul]
          exact mul_le_mul (ha_sub r hrK) (ha₁ (K - r) (Nat.sub_le K r)) (norm_nonneg _) hΔ_nn
        have h2 : ‖a₂ r * (a₁ (K - r) - a₂ (K - r))‖ ≤ S * Δ := by
          rw [norm_mul]
          exact mul_le_mul (ha₂ r hrK) (ha_sub (K - r) (Nat.sub_le K r)) (norm_nonneg _) hS_nn
        calc ‖(a₁ r - a₂ r) * a₁ (K - r) + a₂ r * (a₁ (K - r) - a₂ (K - r))‖
            ≤ Δ * S + S * Δ := (norm_add_le _ _).trans (add_le_add h1 h2)
          _ = 2 * S * Δ := by ring
    _ = (∑ r ∈ Finset.range (K + 1), (Nat.choose K r : ℝ)) * (2 * S * Δ) :=
        (Finset.sum_mul _ _ _).symm
    _ = (2 : ℝ) ^ K * (2 * S * Δ) := by rw [sum_range_choose_real]
    _ = (2 : ℝ) ^ (K + 1) * S * Δ := by rw [pow_succ]; ring
    _ ≤ (2 : ℝ) ^ (M ^ 2 + 1) * S * Δ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (pow_le_pow_right₀ (by norm_num) (Nat.add_le_add_right hKL 1)) hS_nn) hΔ_nn

private lemma norm_zhukovskyLoop_le_two' (n : ℕ) (u : HTGeometry.UnitCircle) :
    ‖zhukovskyLoop n u‖ ≤ 2 := by
  have h1 := norm_zhukovskyLoop_sub_half_le n u
  have ha := (zhukovskyMajorAxis_lt_half n).le
  have hb := zhukovskyMinorAxis_le_sixth n
  have htri : ‖zhukovskyLoop n u‖ ≤ ‖zhukovskyLoop n u - (1 / 2 : ℂ)‖ + ‖(1 / 2 : ℂ)‖ := by
    simpa using norm_add_le (zhukovskyLoop n u - (1 / 2 : ℂ)) (1 / 2 : ℂ)
  have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  linarith

private lemma norm_eval_newtonPoly_sub_le_explicit (L n : ℕ) {d₁ d₂ : ℕ → ℂ} {D δ : ℝ}
    (hD : 1 ≤ D) (hδ : 0 ≤ δ)
    (hd₁ : ∀ j, 1 ≤ j → j ≤ L → ‖d₁ j‖ ≤ D)
    (hd₂ : ∀ j, 1 ≤ j → j ≤ L → ‖d₂ j‖ ≤ D)
    (hsub : ∀ j, 1 ≤ j → j ≤ L → ‖d₁ j - d₂ j‖ ≤ δ)
    (u : HTGeometry.UnitCircle) :
    ‖(newtonPoly L d₁).eval (zhukovskyLoop n u) -
        (newtonPoly L d₂).eval (zhukovskyLoop n u)‖ ≤
      ((L + 1 : ℕ) : ℝ) * (L : ℝ) * (2 * D) ^ L * δ := by
  have h2D_one : 1 ≤ 2 * D := by linarith
  unfold newtonPoly
  rw [Polynomial.eval_finsetSum, Polynomial.eval_finsetSum, ← Finset.sum_sub_distrib]
  calc ‖∑ k ∈ Finset.range (L + 1),
          ((C ((-1 : ℂ) ^ k * newtonElem d₁ k) * X ^ (L - k)).eval (zhukovskyLoop n u) -
            (C ((-1 : ℂ) ^ k * newtonElem d₂ k) * X ^ (L - k)).eval (zhukovskyLoop n u))‖
      ≤ ∑ k ∈ Finset.range (L + 1),
          ‖(C ((-1 : ℂ) ^ k * newtonElem d₁ k) * X ^ (L - k)).eval (zhukovskyLoop n u) -
            (C ((-1 : ℂ) ^ k * newtonElem d₂ k) * X ^ (L - k)).eval (zhukovskyLoop n u)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range (L + 1), ((L : ℝ) * (2 * D) ^ L * δ) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hkL : k ≤ L := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
        have hdiff : (-1 : ℂ) ^ k * newtonElem d₁ k * (zhukovskyLoop n u) ^ (L - k) -
            (-1 : ℂ) ^ k * newtonElem d₂ k * (zhukovskyLoop n u) ^ (L - k) =
            (-1 : ℂ) ^ k * (newtonElem d₁ k - newtonElem d₂ k) *
              (zhukovskyLoop n u) ^ (L - k) := by ring
        rw [hdiff, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow]
        have he_sub := norm_newtonElem_sub_le hD hδ hd₁ hd₂ hsub k hkL
        have hloop_pow : ‖zhukovskyLoop n u‖ ^ (L - k) ≤ (2 : ℝ) ^ (L - k) :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_zhukovskyLoop_le_two' n u) (L - k)
        have hpow_comb : D ^ k * (2 : ℝ) ^ (L - k) ≤ (2 * D) ^ L := by
          have hDk : D ^ k ≤ (2 * D) ^ k :=
            pow_le_pow_left₀ (zero_le_one.trans hD) (by linarith) k
          have h2Lk : (2 : ℝ) ^ (L - k) ≤ (2 * D) ^ (L - k) :=
            pow_le_pow_left₀ (by norm_num) (by linarith) (L - k)
          calc D ^ k * (2 : ℝ) ^ (L - k)
              ≤ (2 * D) ^ k * (2 * D) ^ (L - k) :=
                mul_le_mul hDk h2Lk (by positivity) (pow_nonneg (by positivity) k)
            _ = (2 * D) ^ (k + (L - k)) := (pow_add (2 * D) k (L - k)).symm
            _ = (2 * D) ^ L := by rw [Nat.add_sub_of_le hkL]
        calc ‖newtonElem d₁ k - newtonElem d₂ k‖ * ‖zhukovskyLoop n u‖ ^ (L - k)
            ≤ ((k : ℝ) * D ^ k * δ) * (2 : ℝ) ^ (L - k) :=
              mul_le_mul he_sub hloop_pow (pow_nonneg (norm_nonneg _) _)
                (mul_nonneg (mul_nonneg (Nat.cast_nonneg k)
                  (pow_nonneg (zero_le_one.trans hD) k)) hδ)
          _ = (k : ℝ) * (D ^ k * (2 : ℝ) ^ (L - k)) * δ := by ring
          _ ≤ (L : ℝ) * (2 * D) ^ L * δ := by
              refine mul_le_mul_of_nonneg_right ?_ hδ
              exact mul_le_mul (by exact_mod_cast hkL) hpow_comb
                (mul_nonneg (pow_nonneg (zero_le_one.trans hD) k) (by positivity))
                (Nat.cast_nonneg L)
    _ = ((L + 1 : ℕ) : ℝ) * (L : ℝ) * (2 * D) ^ L * δ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- **Prefix-to-all-`M ≥ N` locking theorem for `IsSourceLoopCertified`.**
Whenever `IsSourceLoopCertified T n N` holds at a single prefix `N`, every prefix `M ≥ N` avoids
`∂R_{T,n}`, has the exact same window degree `integerThetaWindowDegree T n M =
integerThetaWindowDegree T n N`, has everywhere nonvanishing `integerThetaLaurentLoop T n M` on
`UnitCircle`, and has the exact same Fredholm index `fredholmIndex (integerThetaCollisionOperator T n M) =
fredholmIndex (integerThetaCollisionOperator T n N)`. -/
theorem sourceLoopCertified_locks_all_ge {T : ℝ} {n N : ℕ}
    (hcert : IsSourceLoopCertified T n N) :
    ∀ M ≥ N,
      (∀ t : ℝ, _root_.RHTower.finiteThetaAmplitude M
        (_root_.RHTower.rectangleBoundaryPath
          (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t) ≠ 0) ∧
      integerThetaWindowDegree T n M = integerThetaWindowDegree T n N ∧
      (∀ u : HTGeometry.UnitCircle, integerThetaLaurentLoop T n M u ≠ 0) ∧
      HTGeometry.fredholmIndex (integerThetaCollisionOperator T n M) =
        HTGeometry.fredholmIndex (integerThetaCollisionOperator T n N) := by
  obtain ⟨hmod, hdeg_pert, hloop_pert⟩ := hcert
  intro M hNM
  have h0_bounds := norm_integerThetaWindowPowerSum_sub_and_le hmod hNM 0
  have hN0_bounds := norm_integerThetaWindowPowerSum_sub_and_le hmod le_rfl 0
  have hbdry_M := h0_bounds.1
  have hbdry_N := hN0_bounds.1
  -- Step 1: Exact integer degree locking `integerThetaWindowDegree T n M = integerThetaWindowDegree T n N`.
  have hp0_eq_deg : ∀ K : ℕ,
      (∀ t : ℝ, _root_.RHTower.finiteThetaAmplitude K
        (_root_.RHTower.rectangleBoundaryPath
          (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t) ≠ 0) →
      integerThetaWindowPowerSum T n K 0 = (integerThetaWindowDegree T n K : ℂ) := by
    intro K hbdry_K
    have hbdry_K0 : ∀ t : ℝ, finiteThetaShellPencil K 0
        (_root_.RHTower.rectangleBoundaryPath
          (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t) ≠ 0 := by
      simpa only [finiteThetaShellPencil_zero] using hbdry_K
    have hd := pencilWindowDegree_eq_sum T n K ⟨le_rfl, zero_le_one⟩ hbdry_K0
    rw [pencilWindowPowerSum_zero, pencilWindowDegree_zero] at hd
    exact hd.1.trans (congrArg Nat.cast hd.2.symm)
  have hdeg_eq : integerThetaWindowDegree T n M = integerThetaWindowDegree T n N := by
    have hdiff_lt : ‖integerThetaWindowPowerSum T n M 0 - integerThetaWindowPowerSum T n N 0‖ <
        1 / 2 := h0_bounds.2.1.trans_lt hdeg_pert
    rw [hp0_eq_deg M hbdry_M, hp0_eq_deg N hbdry_N] at hdiff_lt
    have hcast : ((integerThetaWindowDegree T n M : ℂ) - (integerThetaWindowDegree T n N : ℂ)) =
        (((integerThetaWindowDegree T n M : ℝ) - (integerThetaWindowDegree T n N : ℝ) : ℝ) : ℂ) := by
      push_cast; ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs] at hdiff_lt
    obtain ⟨h1, h2⟩ := abs_lt.mp hdiff_lt
    have hlt1 : ((integerThetaWindowDegree T n M : ℤ) -
        (integerThetaWindowDegree T n N : ℤ) : ℝ) < 1 := by push_cast; linarith
    have hgt1 : (-1 : ℝ) < ((integerThetaWindowDegree T n M : ℤ) -
        (integerThetaWindowDegree T n N : ℤ) : ℝ) := by push_cast; linarith
    have hlt1' : (integerThetaWindowDegree T n M : ℤ) -
        (integerThetaWindowDegree T n N : ℤ) < 1 := by exact_mod_cast hlt1
    have hgt1' : -1 < (integerThetaWindowDegree T n M : ℤ) -
        (integerThetaWindowDegree T n N : ℤ) := by exact_mod_cast hgt1
    omega
  -- Step 2: Rouché approximation of `integerThetaDifferencePoly T n M` to `N` on `zhukovskyLoop n`.
  set M_deg := integerThetaWindowDegree T n N
  set S := sourcePowerSumUpper T n N
  set Δ := sourcePowerSumPerturbationBound T n N (M_deg ^ 2)
  set D := sourcePairDiffMax T n N
  set δ := sourcePairDiffPerturbation T n N
  have hS_one : 1 ≤ S := by
    dsimp only [S, sourcePowerSumUpper]
    exact le_trans (by linarith [Nat.cast_nonneg (α := ℝ) M_deg] : (1 : ℝ) ≤ 1 + (M_deg : ℝ))
      (le_max_left _ _)
  have hS_deg : (M_deg : ℝ) ≤ S := by
    dsimp only [S, sourcePowerSumUpper]
    exact le_trans (by linarith : (M_deg : ℝ) ≤ 1 + (M_deg : ℝ)) (le_max_left _ _)
  have hb_pos : 0 < boundaryPrefixMin T n N :=
    lt_of_le_of_lt (by positivity [thetaStripTailBound_nonneg N]) hmod
  have hΔ_nn : 0 ≤ Δ := by
    dsimp only [Δ, sourcePowerSumPerturbationBound]
    exact mul_nonneg (mul_nonneg (mul_nonneg
      (pow_nonneg (zero_le_one.trans (one_le_windowNormUpper T)) _)
      (windowVelocityUpper_pos T).le)
      (div_nonneg (mul_nonneg (by norm_num) (_root_.RHTower.thetaAmplitudeEnvelope_nonneg 2))
        (sq_nonneg _)))
      (thetaStripTailBound_nonneg N)
  have hs_M_le : ∀ r, 1 ≤ r → r ≤ M_deg ^ 2 → ‖integerThetaWindowPowerSum T n M r‖ ≤ S := by
    intro r _hr1 hrL
    have hb_r := (norm_integerThetaWindowPowerSum_sub_and_le hmod hNM r).2.2
    have hpow_le : (windowNormUpper T) ^ r ≤ (windowNormUpper T) ^ (M_deg ^ 2) :=
      pow_le_pow_right₀ (one_le_windowNormUpper T) hrL
    refine hb_r.trans ((mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hpow_le (windowVelocityUpper_pos T).le)
      (div_nonneg (mul_nonneg (by norm_num) (_root_.RHTower.thetaAmplitudeEnvelope_nonneg 2))
        hb_pos.le)).trans ?_)
    exact le_max_right _ _
  have hs_N_le : ∀ r, 1 ≤ r → r ≤ M_deg ^ 2 → ‖integerThetaWindowPowerSum T n N r‖ ≤ S := by
    intro r _hr1 hrL
    have hb_r := (norm_integerThetaWindowPowerSum_sub_and_le hmod le_rfl r).2.2
    have hpow_le : (windowNormUpper T) ^ r ≤ (windowNormUpper T) ^ (M_deg ^ 2) :=
      pow_le_pow_right₀ (one_le_windowNormUpper T) hrL
    refine hb_r.trans ((mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hpow_le (windowVelocityUpper_pos T).le)
      (div_nonneg (mul_nonneg (by norm_num) (_root_.RHTower.thetaAmplitudeEnvelope_nonneg 2))
        hb_pos.le)).trans ?_)
    exact le_max_right _ _
  have hs_sub_le : ∀ r, 1 ≤ r → r ≤ M_deg ^ 2 →
      ‖integerThetaWindowPowerSum T n M r - integerThetaWindowPowerSum T n N r‖ ≤ Δ := by
    intro r _hr1 hrL
    have hb_r := (norm_integerThetaWindowPowerSum_sub_and_le hmod hNM r).2.1
    refine hb_r.trans ?_
    dsimp only [Δ]
    unfold sourcePowerSumPerturbationBound
    have hpow_le : (windowNormUpper T) ^ r ≤ (windowNormUpper T) ^ (M_deg ^ 2) :=
      pow_le_pow_right₀ (one_le_windowNormUpper T) hrL
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hpow_le (windowVelocityUpper_pos T).le)
        (div_nonneg (mul_nonneg (by norm_num) (_root_.RHTower.thetaAmplitudeEnvelope_nonneg 2))
          (sq_nonneg _)))
      (thetaStripTailBound_nonneg N)
  have hD_one : 1 ≤ D := by
    dsimp only [D, sourcePairDiffMax]
    have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (M_deg ^ 2) := one_le_pow₀ (by norm_num)
    have hS2 : 1 ≤ S ^ 2 := by nlinarith [hS_one]
    exact one_le_mul_of_one_le_of_one_le h2 hS2
  have hδ_nn : 0 ≤ δ := by
    dsimp only [δ, sourcePairDiffPerturbation]
    exact mul_nonneg (mul_nonneg (by positivity) (zero_le_one.trans hS_one)) hΔ_nn
  have hd_M_le : ∀ K, 1 ≤ K → K ≤ M_deg ^ 2 →
      ‖pairDiffPowerSum M_deg (integerThetaWindowPowerSum T n M) K‖ ≤ D :=
    norm_pairDiffPowerSum_le hS_deg (zero_le_one.trans hS_one) hs_M_le
  have hd_N_le : ∀ K, 1 ≤ K → K ≤ M_deg ^ 2 →
      ‖pairDiffPowerSum M_deg (integerThetaWindowPowerSum T n N) K‖ ≤ D :=
    norm_pairDiffPowerSum_le hS_deg (zero_le_one.trans hS_one) hs_N_le
  have hd_sub_le : ∀ K, 1 ≤ K → K ≤ M_deg ^ 2 →
      ‖pairDiffPowerSum M_deg (integerThetaWindowPowerSum T n M) K -
        pairDiffPowerSum M_deg (integerThetaWindowPowerSum T n N) K‖ ≤ δ :=
    norm_pairDiffPowerSum_sub_le hS_deg (zero_le_one.trans hS_one) hΔ_nn hs_M_le hs_N_le hs_sub_le
  have hbase_pos : 0 < baseLoopCircleMin T n N := by
    have hpert_nn : 0 ≤ sourceLoopPerturbationBound T n N := by
      unfold sourceLoopPerturbationBound
      exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (pow_nonneg (by linarith [hD_one]) _)) hδ_nn
    exact lt_of_le_of_lt hpert_nn hloop_pert
  have hQN_nz : ∀ u : HTGeometry.UnitCircle,
      (integerThetaDifferencePoly T n N).eval (zhukovskyLoop n u) ≠ 0 := by
    intro u h0
    have hle := baseLoopCircleMin_le_norm T n N u
    change baseLoopCircleMin T n N ≤
      ‖(integerThetaDifferencePoly T n N).eval (zhukovskyLoop n u)‖ at hle
    rw [h0, norm_zero] at hle
    linarith
  have happrox : ∀ u : HTGeometry.UnitCircle,
      ‖(integerThetaDifferencePoly T n M).eval (zhukovskyLoop n u) -
          (integerThetaDifferencePoly T n N).eval (zhukovskyLoop n u)‖ <
        ‖(integerThetaDifferencePoly T n N).eval (zhukovskyLoop n u)‖ := by
    intro u
    have hpoly_M : integerThetaDifferencePoly T n M =
        newtonPoly (M_deg ^ 2) (pairDiffPowerSum M_deg (integerThetaWindowPowerSum T n M)) := by
      unfold integerThetaDifferencePoly pairDiffPoly
      rw [hdeg_eq]
    have hpoly_N : integerThetaDifferencePoly T n N =
        newtonPoly (M_deg ^ 2) (pairDiffPowerSum M_deg (integerThetaWindowPowerSum T n N)) := rfl
    rw [hpoly_M, hpoly_N]
    have heval_le := norm_eval_newtonPoly_sub_le_explicit (M_deg ^ 2) n hD_one hδ_nn
      hd_M_le hd_N_le hd_sub_le u
    have hle_pert : ((M_deg ^ 2 + 1 : ℕ) : ℝ) * ((M_deg ^ 2 : ℕ) : ℝ) *
        (2 * D) ^ (M_deg ^ 2) * δ = sourceLoopPerturbationBound T n N := rfl
    rw [hle_pert] at heval_le
    exact heval_le.trans_lt (hloop_pert.trans_le (baseLoopCircleMin_le_norm T n N u))
  obtain ⟨hLM_nz, hwind_eq⟩ := windingNumber_zhukovsky_poly_sq_of_approx n
    (integerThetaDifferencePoly T n M) (integerThetaDifferencePoly T n N) hQN_nz happrox
  have hLN_nz : ∀ u : HTGeometry.UnitCircle, integerThetaLaurentLoop T n N u ≠ 0 :=
    fun u => pow_ne_zero 2 (hQN_nz u)
  have hind_eq : HTGeometry.fredholmIndex (integerThetaCollisionOperator T n M) =
      HTGeometry.fredholmIndex (integerThetaCollisionOperator T n N) := by
    rw [fredholmIndex_integerThetaCollisionOperator_eq_circleWinding,
      fredholmIndex_integerThetaCollisionOperator_eq_circleWinding,
      integerThetaCollisionSymbol, integerThetaCollisionSymbol,
      circleWinding_unitNormalizeSymbol_of_ne_zero hLM_nz,
      circleWinding_unitNormalizeSymbol_of_ne_zero hLN_nz]
    exact hwind_eq
  exact ⟨hbdry_M, hdeg_eq, hLM_nz, hind_eq⟩

/-- **Unconditional soundness of `IsSourceLoopCertified`.**
On any stage `n ≥ thetaWindowScale T`, a single loop-certified prefix `N` guarantees
`IsArtifactFreeFrom T n N` and `firstArtifactFreePrefix T n ≤ N`. -/
theorem sourceLoopCertified_sound {T : ℝ} {n N : ℕ}
    (hn : thetaWindowScale T ≤ n) (hcert : IsSourceLoopCertified T n N) :
    IsArtifactFreeFrom T n N ∧ firstArtifactFreePrefix T n ≤ N := by
  have hlocks := sourceLoopCertified_locks_all_ge hcert
  let M₀ := max N (thetaPrefixThreshold T n)
  have hM₀_lock := hlocks M₀ (le_max_left N (thetaPrefixThreshold T n))
  have hM₀_xi := integerThetaCollisionOperator_index_and_winding_eq_charge T hn
    (N := M₀) (le_max_right N (thetaPrefixThreshold T n))
  have hdeg_N : integerThetaWindowDegree T n N = _root_.RHTower.xiStripWindowTotalOrder T :=
    hM₀_lock.2.1.symm.trans hM₀_xi.2.1
  have hind_N : HTGeometry.fredholmIndex (integerThetaCollisionOperator T n N) =
      (_root_.RHTower.xiHorizontalCollisionCharge T : ℤ) :=
    hM₀_lock.2.2.2.symm.trans hM₀_xi.2.2.2.2.2
  have haf : IsArtifactFreeFrom T n N := by
    intro M hNM
    have hM := hlocks M hNM
    exact ⟨hM.1, hM.2.1.trans hdeg_N, hM.2.2.1, hM.2.2.2.trans hind_N⟩
  exact ⟨haf, Nat.sInf_le haf⟩

private lemma exists_xi_boundary_lower_bound {T : ℝ} {n : ℕ} (hn : thetaWindowScale T ≤ n) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ t : ℝ,
      μ ≤ ‖_root_.RHTower.xi
        (_root_.RHTower.rectangleBoundaryPath
          (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t)‖ := by
  set γ := _root_.RHTower.rectangleBoundaryPath
    (thetaWindowLowerLeft n) (thetaWindowUpperRight T n)
  have hxi_nz : ∀ t : ℝ, _root_.RHTower.xi (γ t) ≠ 0 := by
    intro t hz0
    have hmemRect := _root_.RHTower.rectangleBoundaryPath_mem_reProdIm
      (thetaWindowLowerLeft n) (thetaWindowUpperRight T n)
      (thetaWindow_re_le T n) (thetaWindow_im_le T n) t
    have hmemBox := thetaWindowRect_subset_openBox T n hmemRect
    have hmemZ := xi_zero_in_openBox_mem_stripZeros hn hmemBox hz0
    obtain ⟨h1, h2, h3, h4⟩ := stripZeros_strictly_inside_thetaWindow hn hmemZ
    rcases rectangleBoundaryPath_on_edges
        (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t with h | h | h | h
    · exact h1.ne' h
    · exact h2.ne h
    · exact h3.ne' h
    · exact h4.ne h
  have hcont : Continuous (fun t : ℝ => ‖_root_.RHTower.xi (γ t)‖) :=
    (_root_.RHTower.xi_differentiable.continuous.comp
      (_root_.RHTower.continuous_rectangleBoundaryPath _ _)).norm
  obtain ⟨t₀, _, ht₀⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr (zero_le_one : (0 : ℝ) ≤ 1)) hcont.continuousOn
  refine ⟨‖_root_.RHTower.xi (γ t₀)‖, norm_pos_iff.mpr (hxi_nz t₀), fun t => ?_⟩
  have hfrac : Int.fract t ∈ Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩
  have hmin := isMinOn_iff.mp ht₀ (Int.fract t) hfrac
  have hper : γ (Int.fract t) = γ t := by
    simp [γ, _root_.RHTower.rectangleBoundaryPath, Int.fract_fract]
  rwa [hper] at hmin

private lemma tendsto_newtonElem_local {d : ℕ → ℕ → ℂ} {d₀ : ℕ → ℂ}
    (hd : ∀ j : ℕ, Tendsto (fun N => d N j) atTop (𝓝 (d₀ j))) :
    ∀ k : ℕ, Tendsto (fun N => newtonElem (d N) k) atTop (𝓝 (newtonElem d₀ k)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases k with _ | k
    · simp only [newtonElem, tendsto_const_nhds]
    · simp only [newtonElem]
      refine Tendsto.const_mul _ (tendsto_finsetSum _ fun j _ => ?_)
      exact ((ih (k - j) (by omega)).const_mul ((-1 : ℂ) ^ j)).mul (hd (j + 1))

private lemma tendsto_pairDiffPowerSum_local (M : ℕ) {s : ℕ → ℕ → ℂ} {s₀ : ℕ → ℂ}
    (hs : ∀ r : ℕ, Tendsto (fun N => s N r) atTop (𝓝 (s₀ r))) (K : ℕ) :
    Tendsto (fun N => pairDiffPowerSum M (s N) K) atTop (𝓝 (pairDiffPowerSum M s₀ K)) := by
  unfold pairDiffPowerSum
  dsimp only
  refine tendsto_finsetSum _ fun r _ => ?_
  have h1 : Tendsto (fun N => if r = 0 then (M : ℂ) else s N r) atTop
      (𝓝 (if r = 0 then (M : ℂ) else s₀ r)) := by
    by_cases hr : r = 0
    · simp [hr]
    · simpa [hr] using hs r
  have h2 : Tendsto (fun N => if K - r = 0 then (M : ℂ) else s N (K - r)) atTop
      (𝓝 (if K - r = 0 then (M : ℂ) else s₀ (K - r))) := by
    by_cases hKr : K - r = 0
    · simp [hKr]
    · simpa [hKr] using hs (K - r)
  exact (h1.const_mul _).mul h2

/-- **Universal eventual completeness of `IsSourceLoopCertified`.**
For **every** height `T : ℝ` and **every** stage `n ≥ thetaWindowScale T` (unconditionally, with
zero simplicity or multiplicity hypotheses on `xi`), `IsSourceLoopCertified T n N` holds for all
sufficiently large `N`. -/
theorem eventually_isSourceLoopCertified (T : ℝ) {n : ℕ} (hn : thetaWindowScale T ≤ n) :
    ∀ᶠ N : ℕ in atTop, IsSourceLoopCertified T n N := by
  -- 1. Uniform positive lower bound `μ / 2 ≤ boundaryPrefixMin T n N` eventually.
  obtain ⟨μ, hμ_pos, hμ_min⟩ := exists_xi_boundary_lower_bound hn
  have hev_tail_μ : ∀ᶠ N : ℕ in atTop, thetaStripTailBound N < μ / 2 :=
    tendsto_thetaStripTailBound_zero.eventually (gt_mem_nhds (half_pos hμ_pos))
  have hev_bmin : ∀ᶠ N : ℕ in atTop, μ / 2 ≤ boundaryPrefixMin T n N := by
    filter_upwards [hev_tail_μ] with N hN_tail
    unfold boundaryPrefixMin
    dsimp only
    set γ := _root_.RHTower.rectangleBoundaryPath
      (thetaWindowLowerLeft n) (thetaWindowUpperRight T n)
    set hK : IsCompact (Icc (0 : ℝ) 1) := isCompact_Icc
    set hne : (Icc (0 : ℝ) 1).Nonempty := nonempty_Icc.mpr zero_le_one
    set hcont : ContinuousOn (fun t : ℝ => ‖_root_.RHTower.finiteThetaAmplitude N (γ t)‖)
        (Icc (0 : ℝ) 1) :=
      (((_root_.RHTower.differentiable_finiteThetaAmplitude N).continuous.comp
        (_root_.RHTower.continuous_rectangleBoundaryPath _ _)).norm).continuousOn
    set t₀ := (hK.exists_isMinOn hne hcont).choose
    have hxi_t₀ := hμ_min t₀
    have hbd_raw := norm_finiteThetaAmplitude_sub_xi_le_strip N (by norm_num : (0 : ℝ) ≤ 2)
      (abs_re_boundary_le_two T n t₀)
    have hbd : ‖_root_.RHTower.finiteThetaAmplitude N (γ t₀) - _root_.RHTower.xi (γ t₀)‖ ≤
        thetaStripTailBound N := by
      simpa only [thetaStripTailBound, mul_right_comm] using hbd_raw
    have htri := norm_sub_norm_le (_root_.RHTower.xi (γ t₀))
      (_root_.RHTower.finiteThetaAmplitude N (γ t₀))
    rw [norm_sub_rev] at htri
    linarith
  -- 2. Uniform positive lower bound `η / 2 ≤ baseLoopCircleMin T n N` eventually.
  have hQ_nz := (exactWindowDifferencePoly_winding T hn).1
  have hU_ne : (Set.univ : Set HTGeometry.UnitCircle).Nonempty :=
    ⟨HTGeometry.circleExp 0, Set.mem_univ _⟩
  have hQ_cont : Continuous (fun u : HTGeometry.UnitCircle =>
      ‖(exactWindowDifferencePoly T).eval (zhukovskyLoop n u)‖) :=
    ((exactWindowDifferencePoly T).continuous.comp (zhukovskyLoop n).continuous).norm
  obtain ⟨u₀, _, hu₀⟩ := isCompact_univ.exists_isMinOn hU_ne hQ_cont.continuousOn
  set η : ℝ := ‖(exactWindowDifferencePoly T).eval (zhukovskyLoop n u₀)‖
  have hη_pos : 0 < η := norm_pos_iff.mpr (hQ_nz u₀)
  have hη_le : ∀ u : HTGeometry.UnitCircle,
      η ≤ ‖(exactWindowDifferencePoly T).eval (zhukovskyLoop n u)‖ :=
    fun u => isMinOn_iff.mp hu₀ u (Set.mem_univ u)
  set M₀ := _root_.RHTower.xiStripWindowTotalOrder T
  let s₀ : ℕ → ℂ := fun r => ∑ w ∈ (_root_.RHTower.stripZeros_finite T).toFinset,
    ((analyticOrderAt _root_.RHTower.xi w).toNat : ℂ) * w ^ r
  have hd_tendsto : ∀ K : ℕ, Tendsto
      (fun N => pairDiffPowerSum M₀ (integerThetaWindowPowerSum T n N) K) atTop
      (𝓝 (pairDiffPowerSum M₀ s₀ K)) :=
    tendsto_pairDiffPowerSum_local M₀ (fun r => tendsto_integerThetaWindowPowerSum T hn r)
  have helem_tendsto := tendsto_newtonElem_local hd_tendsto
  have hsum_tendsto : Tendsto
      (fun N : ℕ => ∑ k ∈ Finset.range (M₀ ^ 2 + 1),
        ‖newtonElem (pairDiffPowerSum M₀ (integerThetaWindowPowerSum T n N)) k -
          newtonElem (pairDiffPowerSum M₀ s₀) k‖ * 2 ^ (M₀ ^ 2 - k))
      atTop (𝓝 0) := by
    have h0 : (0 : ℝ) = ∑ _k ∈ Finset.range (M₀ ^ 2 + 1), (0 : ℝ) := by simp
    rw [h0]
    refine tendsto_finsetSum _ fun k _ => ?_
    have hnorm : Tendsto
        (fun N : ℕ => ‖newtonElem (pairDiffPowerSum M₀ (integerThetaWindowPowerSum T n N)) k -
          newtonElem (pairDiffPowerSum M₀ s₀) k‖) atTop (𝓝 0) := by
      simpa only [sub_self, norm_zero] using
        ((helem_tendsto k).sub
          (tendsto_const_nhds (x := newtonElem (pairDiffPowerSum M₀ s₀) k))).norm
    simpa only [zero_mul] using hnorm.mul_const (2 ^ (M₀ ^ 2 - k))
  have hev_deg : ∀ᶠ N : ℕ in atTop, integerThetaWindowDegree T n N = M₀ := by
    filter_upwards [eventually_ge_atTop (thetaPrefixThreshold T n)] with N hN
    exact (integerThetaCollisionOperator_index_and_winding_eq_charge T hn hN).2.1
  have hev_cmin : ∀ᶠ N : ℕ in atTop, η / 2 ≤ baseLoopCircleMin T n N := by
    filter_upwards [hev_deg, hsum_tendsto.eventually (gt_mem_nhds (half_pos hη_pos))] with
      N hdeg hsum_lt
    unfold baseLoopCircleMin
    dsimp only
    set hK : IsCompact (Set.univ : Set HTGeometry.UnitCircle) := isCompact_univ
    set hcont : ContinuousOn (fun v : HTGeometry.UnitCircle => ‖integerThetaBaseLoop T n N v‖)
        Set.univ :=
      (integerThetaBaseLoop T n N).continuous.norm.continuousOn
    set u_N := (hK.exists_isMinOn hU_ne hcont).choose
    have hQ_u := hη_le u_N
    have hpoly_eq : integerThetaDifferencePoly T n N =
        newtonPoly (M₀ ^ 2) (pairDiffPowerSum M₀ (integerThetaWindowPowerSum T n N)) := by
      unfold integerThetaDifferencePoly pairDiffPoly
      rw [hdeg]
    have hdiff_le : ‖integerThetaBaseLoop T n N u_N -
        (exactWindowDifferencePoly T).eval (zhukovskyLoop n u_N)‖ ≤
        ∑ k ∈ Finset.range (M₀ ^ 2 + 1),
          ‖newtonElem (pairDiffPowerSum M₀ (integerThetaWindowPowerSum T n N)) k -
            newtonElem (pairDiffPowerSum M₀ s₀) k‖ * 2 ^ (M₀ ^ 2 - k) := by
      change ‖(integerThetaDifferencePoly T n N).eval (zhukovskyLoop n u_N) -
        (newtonPoly (M₀ ^ 2) (pairDiffPowerSum M₀ s₀)).eval (zhukovskyLoop n u_N)‖ ≤ _
      rw [hpoly_eq]
      unfold newtonPoly
      rw [Polynomial.eval_finsetSum, Polynomial.eval_finsetSum, ← Finset.sum_sub_distrib]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
      have hsub : (-1 : ℂ) ^ k *
            newtonElem (pairDiffPowerSum M₀ (integerThetaWindowPowerSum T n N)) k *
            (zhukovskyLoop n u_N) ^ (M₀ ^ 2 - k) -
          (-1 : ℂ) ^ k * newtonElem (pairDiffPowerSum M₀ s₀) k *
            (zhukovskyLoop n u_N) ^ (M₀ ^ 2 - k) =
          (-1 : ℂ) ^ k *
            (newtonElem (pairDiffPowerSum M₀ (integerThetaWindowPowerSum T n N)) k -
              newtonElem (pairDiffPowerSum M₀ s₀) k) *
            (zhukovskyLoop n u_N) ^ (M₀ ^ 2 - k) := by ring
      rw [hsub, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (norm_zhukovskyLoop_le_two' n u_N) (M₀ ^ 2 - k))
        (norm_nonneg _)
    have htri := norm_sub_norm_le ((exactWindowDifferencePoly T).eval (zhukovskyLoop n u_N))
      (integerThetaBaseLoop T n N u_N)
    rw [norm_sub_rev] at htri
    linarith [hdiff_le.trans_lt hsum_lt]
  -- 3. Fixed envelope constants bounding the three perturbation terms by `const * thetaStripTailBound N`.
  set E := _root_.RHTower.thetaAmplitudeEnvelope 2
  have hE_nn : 0 ≤ E := _root_.RHTower.thetaAmplitudeEnvelope_nonneg 2
  set C_p0 : ℝ := windowVelocityUpper T * (8 * E / (μ / 2) ^ 2)
  set C_pL : ℝ := (windowNormUpper T) ^ (M₀ ^ 2) * windowVelocityUpper T * (8 * E / (μ / 2) ^ 2)
  set S_max : ℝ := max (1 + (M₀ : ℝ))
    ((windowNormUpper T) ^ (M₀ ^ 2) * windowVelocityUpper T * (2 * E / (μ / 2)))
  set D_max : ℝ := (2 : ℝ) ^ (M₀ ^ 2) * S_max ^ 2
  set C_loop : ℝ := ((M₀ ^ 2 + 1 : ℕ) : ℝ) * ((M₀ ^ 2 : ℕ) : ℝ) *
    (2 * D_max) ^ (M₀ ^ 2) * ((2 : ℝ) ^ (M₀ ^ 2 + 1) * S_max * C_pL)
  have hev1 : ∀ᶠ N : ℕ in atTop, 4 * thetaStripTailBound N < μ / 2 := by
    have ht : Tendsto (fun N => 4 * thetaStripTailBound N) atTop (𝓝 0) := by
      simpa only [mul_zero] using tendsto_thetaStripTailBound_zero.const_mul 4
    exact ht.eventually (gt_mem_nhds (half_pos hμ_pos))
  have hev2 : ∀ᶠ N : ℕ in atTop, C_p0 * thetaStripTailBound N < 1 / 2 := by
    have ht : Tendsto (fun N => C_p0 * thetaStripTailBound N) atTop (𝓝 0) := by
      simpa only [mul_zero] using tendsto_thetaStripTailBound_zero.const_mul C_p0
    exact ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hev3 : ∀ᶠ N : ℕ in atTop, C_loop * thetaStripTailBound N < η / 2 := by
    have ht : Tendsto (fun N => C_loop * thetaStripTailBound N) atTop (𝓝 0) := by
      simpa only [mul_zero] using tendsto_thetaStripTailBound_zero.const_mul C_loop
    exact ht.eventually (gt_mem_nhds (half_pos hη_pos))
  filter_upwards [hev_bmin, hev_deg, hev_cmin, hev1, hev2, hev3] with
    N hbmin hdeg hcmin h1 h2 h3
  have hb_pos : 0 < boundaryPrefixMin T n N := lt_of_lt_of_le (half_pos hμ_pos) hbmin
  have hb_sq_le : (μ / 2) ^ 2 ≤ (boundaryPrefixMin T n N) ^ 2 :=
    pow_le_pow_left₀ (half_pos hμ_pos).le hbmin 2
  have hdiv2_le : 8 * E / (boundaryPrefixMin T n N) ^ 2 ≤ 8 * E / (μ / 2) ^ 2 := by
    rw [div_le_div_iff₀ (sq_pos_of_pos hb_pos) (sq_pos_of_pos (half_pos hμ_pos))]
    exact mul_le_mul_of_nonneg_left hb_sq_le (by positivity)
  have hdiv1_le : 2 * E / boundaryPrefixMin T n N ≤ 2 * E / (μ / 2) := by
    rw [div_le_div_iff₀ hb_pos (half_pos hμ_pos)]
    exact mul_le_mul_of_nonneg_left hbmin (by positivity)
  refine ⟨h1.trans_le hbmin, ?_, ?_⟩
  · -- `sourcePowerSumPerturbationBound T n N 0 ≤ C_p0 * thetaStripTailBound N < 1 / 2`.
    have hle_p0 : sourcePowerSumPerturbationBound T n N 0 ≤ C_p0 * thetaStripTailBound N := by
      unfold sourcePowerSumPerturbationBound
      rw [pow_zero, one_mul]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hdiv2_le (windowVelocityUpper_pos T).le)
        (thetaStripTailBound_nonneg N)
    exact hle_p0.trans_lt h2
  · -- `sourceLoopPerturbationBound T n N ≤ C_loop * thetaStripTailBound N < η / 2 ≤ baseLoopCircleMin`.
    have hS_le : sourcePowerSumUpper T n N ≤ S_max := by
      unfold sourcePowerSumUpper
      rw [hdeg]
      refine max_le (le_max_left _ _) ((mul_le_mul_of_nonneg_left hdiv1_le
        (mul_nonneg (pow_nonneg (zero_le_one.trans (one_le_windowNormUpper T)) _)
          (windowVelocityUpper_pos T).le)).trans (le_max_right _ _))
    have hS_nn : 0 ≤ sourcePowerSumUpper T n N := by
      unfold sourcePowerSumUpper
      exact (by positivity : (0 : ℝ) ≤ 1 + (integerThetaWindowDegree T n N : ℝ)).trans
        (le_max_left _ _)
    have hS_max_nn : 0 ≤ S_max := hS_nn.trans hS_le
    have hD_le : sourcePairDiffMax T n N ≤ D_max := by
      unfold sourcePairDiffMax
      rw [hdeg]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hS_nn hS_le 2) (by positivity)
    have hD_nn : 0 ≤ sourcePairDiffMax T n N := by
      unfold sourcePairDiffMax; positivity
    have hpL_le : sourcePowerSumPerturbationBound T n N (M₀ ^ 2) ≤
        C_pL * thetaStripTailBound N := by
      unfold sourcePowerSumPerturbationBound
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hdiv2_le
          (mul_nonneg (pow_nonneg (zero_le_one.trans (one_le_windowNormUpper T)) _)
            (windowVelocityUpper_pos T).le))
        (thetaStripTailBound_nonneg N)
    have hδ_le : sourcePairDiffPerturbation T n N ≤
        ((2 : ℝ) ^ (M₀ ^ 2 + 1) * S_max * C_pL) * thetaStripTailBound N := by
      unfold sourcePairDiffPerturbation
      rw [hdeg]
      calc (2 : ℝ) ^ (M₀ ^ 2 + 1) * sourcePowerSumUpper T n N *
            sourcePowerSumPerturbationBound T n N (M₀ ^ 2)
          ≤ (2 : ℝ) ^ (M₀ ^ 2 + 1) * S_max * (C_pL * thetaStripTailBound N) := by
            refine mul_le_mul
              (mul_le_mul_of_nonneg_left hS_le (by positivity))
              hpL_le
              (by
                unfold sourcePowerSumPerturbationBound
                exact mul_nonneg (mul_nonneg (mul_nonneg
                  (pow_nonneg (zero_le_one.trans (one_le_windowNormUpper T)) _)
                  (windowVelocityUpper_pos T).le)
                  (div_nonneg (mul_nonneg (by norm_num) hE_nn) (sq_nonneg _)))
                  (thetaStripTailBound_nonneg N))
              (mul_nonneg (by positivity) hS_max_nn)
        _ = ((2 : ℝ) ^ (M₀ ^ 2 + 1) * S_max * C_pL) * thetaStripTailBound N := by ring
    have hδ_nn : 0 ≤ sourcePairDiffPerturbation T n N := by
      unfold sourcePairDiffPerturbation sourcePowerSumPerturbationBound
      exact mul_nonneg (mul_nonneg (by positivity) hS_nn)
        (mul_nonneg (mul_nonneg (mul_nonneg
          (pow_nonneg (zero_le_one.trans (one_le_windowNormUpper T)) _)
          (windowVelocityUpper_pos T).le) (by positivity))
          (thetaStripTailBound_nonneg N))
    have hloop_le : sourceLoopPerturbationBound T n N ≤ C_loop * thetaStripTailBound N := by
      unfold sourceLoopPerturbationBound
      rw [hdeg]
      have h2D_pow : (2 * sourcePairDiffMax T n N) ^ (M₀ ^ 2) ≤ (2 * D_max) ^ (M₀ ^ 2) :=
        pow_le_pow_left₀ (by positivity) (by linarith) (M₀ ^ 2)
      calc ((M₀ ^ 2 + 1 : ℕ) : ℝ) * ((M₀ ^ 2 : ℕ) : ℝ) *
            (2 * sourcePairDiffMax T n N) ^ (M₀ ^ 2) * sourcePairDiffPerturbation T n N
          ≤ (((M₀ ^ 2 + 1 : ℕ) : ℝ) * ((M₀ ^ 2 : ℕ) : ℝ) * (2 * D_max) ^ (M₀ ^ 2)) *
              (((2 : ℝ) ^ (M₀ ^ 2 + 1) * S_max * C_pL) * thetaStripTailBound N) :=
            mul_le_mul
              (mul_le_mul_of_nonneg_left h2D_pow
                (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
              hδ_le hδ_nn
              (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
                (pow_nonneg (by linarith [hD_nn, hD_le]) _))
        _ = C_loop * thetaStripTailBound N := by dsimp only [C_loop]; ring
    exact (hloop_le.trans_lt h3).trans_le hcmin

/-- **Universal source-intrinsic stopping rule theorem.**
On **every** height window `T : ℝ` and **every** stage `n ≥ thetaWindowScale T` (unconditionally,
with zero simplicity or multiplicity hypotheses on `xi`), `sourceLoopStoppingPrefix T n` satisfies
`IsSourceLoopCertified T n (sourceLoopStoppingPrefix T n)`, certifies
`IsArtifactFreeFrom T n (sourceLoopStoppingPrefix T n)` and
`firstArtifactFreePrefix T n ≤ sourceLoopStoppingPrefix T n`, and evaluates the exact horizontal
collision charge `(xiHorizontalCollisionCharge T : ℤ)` at the single prefix
`sourceLoopStoppingPrefix T n`. -/
theorem isArtifactFreeFrom_sourceLoopStoppingPrefix (T : ℝ) {n : ℕ}
    (hn : thetaWindowScale T ≤ n) :
    IsSourceLoopCertified T n (sourceLoopStoppingPrefix T n) ∧
    IsArtifactFreeFrom T n (sourceLoopStoppingPrefix T n) ∧
    firstArtifactFreePrefix T n ≤ sourceLoopStoppingPrefix T n ∧
    HTGeometry.fredholmIndex
      (integerThetaCollisionOperator T n (sourceLoopStoppingPrefix T n)) =
      (_root_.RHTower.xiHorizontalCollisionCharge T : ℤ) := by
  obtain ⟨N_wit, hN_wit⟩ := (eventually_isSourceLoopCertified T hn).exists
  have hwit : N_wit ∈ {N : ℕ | IsSourceLoopCertified T n N} := hN_wit
  have hcert : IsSourceLoopCertified T n (sourceLoopStoppingPrefix T n) :=
    Nat.sInf_mem (s := {N : ℕ | IsSourceLoopCertified T n N}) ⟨N_wit, hwit⟩
  obtain ⟨haf, hfirst⟩ := sourceLoopCertified_sound hn hcert
  exact ⟨hcert, haf, hfirst, (haf (sourceLoopStoppingPrefix T n) le_rfl).2.2.2⟩

/-- **Single-stopping-prefix `RiemannHypothesis` equivalence.**
`RiemannHypothesis` holds if and only if on every natural-height window `m : ℕ`, for all
sufficiently fine Zhukovsky scales `n`, the Fredholm index of `integerThetaCollisionOperator`
evaluated at the purely source-intrinsic stopping prefix `sourceLoopStoppingPrefix (m : ℝ) n`
vanishes (eliminating the existential inner prefix quantifier `∃ N₀, ∀ N ≥ N₀`). -/
theorem riemannHypothesis_iff_forall_nat_sourceLoopStoppingPrefix_index_eq_zero :
    RiemannHypothesis ↔
      ∀ m : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀,
        HTGeometry.fredholmIndex
          (integerThetaCollisionOperator (m : ℝ) n (sourceLoopStoppingPrefix (m : ℝ) n)) = 0 := by
  constructor
  · intro hRH m
    refine ⟨thetaWindowScale (m : ℝ), fun n hn => ?_⟩
    rw [(isArtifactFreeFrom_sourceLoopStoppingPrefix (m : ℝ) hn).2.2.2,
      _root_.RHTower.riemannHypothesis_iff_forall_horizontalCollisionCharge_eq_zero.mp hRH (m : ℝ)]
    rfl
  · intro h
    apply _root_.RHTower.riemannHypothesis_of_forall_nat_horizontalCollisionCharge_lt_two
    intro m
    obtain ⟨n₀, hn₀⟩ := h m
    set n := max n₀ (thetaWindowScale (m : ℝ))
    have hzero := hn₀ n (le_max_left _ _)
    rw [(isArtifactFreeFrom_sourceLoopStoppingPrefix (m : ℝ) (le_max_right _ _)).2.2.2] at hzero
    have hcharge0 : _root_.RHTower.xiHorizontalCollisionCharge (m : ℝ) = 0 := by
      exact_mod_cast hzero
    omega

end GaloisForLFunctions.ConjugateDiagonalGeometry

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.norm_finiteThetaAmplitude_sub_prefix_le_strip
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.norm_finiteThetaFirstMoment_sub_prefix_le_strip
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.sourceAlgebraicPerforatedCertified_locks_all_ge
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.sourceAlgebraicPerforatedCertified_sound
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.isSourceAlgebraicPerforatedCertified_of_simpleZeros
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.sourcePerforatedStoppingPrefix_complete_of_simpleZeros
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.sourceLoopCertified_locks_all_ge
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.sourceLoopCertified_sound
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.eventually_isSourceLoopCertified
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.isArtifactFreeFrom_sourceLoopStoppingPrefix
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.riemannHypothesis_iff_forall_nat_sourceLoopStoppingPrefix_index_eq_zero
