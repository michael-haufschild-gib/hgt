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
  obtain ⟨hmarg, _, _, _⟩ := hcert
  obtain ⟨hre_lo, hre_hi, him_lo, him_hi⟩ := hmarg w hw
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
  obtain ⟨_, hsep_all, _, _⟩ := hcert
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
  obtain ⟨_, hsep_all, _, hmod⟩ := hcert
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
    obtain ⟨_, hsep_all, _, hmod⟩ := hcert
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
  have hM₀_lock := hlocks M₀ (le_max_left _ _)
  have hM₀_xi := integerThetaCollisionOperator_index_and_winding_eq_charge T hn (le_max_right _ _)
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
    IsCompact (halfPerforatedWindowSet T T_n) := by
  sorry
