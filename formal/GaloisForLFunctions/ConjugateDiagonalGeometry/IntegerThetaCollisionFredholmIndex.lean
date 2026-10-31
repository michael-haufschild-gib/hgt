import GaloisForLFunctions.ConjugateDiagonalGeometry.ZhukovskyCollisionWinding
import GaloisForLFunctions.ConjugateDiagonalGeometry.EffectiveThetaCollisionRounding
import GaloisForLFunctions.RHTower.RectangleWeightedCauchyResidue
import GaloisForLFunctions.RHTower.RectangleBoundaryPhaseWinding
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspStripAmplitudeBounds
import GaloisForLFunctions.HTGeometry.Peeling

/-!
# Integer-theta Wiener–Hopf Fredholm operator and winding index for horizontal collision charge

From finite integer Jacobi-theta prefixes alone (`finiteThetaAmplitude N` and
`finiteThetaFirstMoment N`, integrating `reflectedFiniteThetaSource (N + 1)`), we construct on
every height window `T : ℝ` (and in particular on every natural-height window `(m : ℝ)`, `m : ℕ`)
a two-scale family of Laurent loops `integerThetaLaurentLoop T n N` on `UnitCircle` and their
Wiener–Hopf operators `integerThetaCollisionOperator T n N` on `L²(ℝ)`:

1. **Source-pure contour power sums and Newton–Girard difference polynomial**:
   Integrating `z^r (-finiteThetaFirstMoment N z / finiteThetaAmplitude N z)` around the shifted
   window rectangle `[-1 / 2, 3 / 2] × [-1 / (2 s_n), max 0 T - 1 / (2 s_n)]` produces source-pure
   approximants `integerThetaWindowPowerSum T n N r` without referencing any zero coordinates or
   evaluating `ζ` or `ξ`. Whenever `finiteThetaAmplitude N` has no zeros on the rectangle boundary,
   the `r = 0` contour integral is already an exact integer in `ℂ` by the rectangle boundary phase
   winding theorem.
2. **Zhukovsky Laurent symbol and Wiener–Hopf Fredholm operator**:
   Evaluating the squared Newton–Girard pair-difference polynomial along `zhukovskyLoop n` and
   unit-normalizing yields `integerThetaCollisionOperator T n N : L²(ℝ) →L[ℂ] L²(ℝ)`, which is
   unconditionally Fredholm with even Fredholm index for every `(T, n, N)`.
3. **Exact horizontal collision index theorem**:
   Using uniform Gaussian integer-tail convergence of both `finiteThetaAmplitude N → xi` and
   `-finiteThetaFirstMoment N → deriv xi` on vertical strips together with multi-zero peeling and
   Rouché stability on `UnitCircle`, for every `n ≥ thetaWindowScale T` and
   `N ≥ thetaPrefixThreshold T n`, `integerThetaLaurentLoop T n N` is everywhere nonvanishing on
   `UnitCircle` and both its winding number and the Fredholm index of
   `integerThetaCollisionOperator T n N` equal `(xiHorizontalCollisionCharge T : ℤ)` on the nose.
4. **Unconditional `RiemannHypothesis` equivalences**:
   `RiemannHypothesis` is equivalent to eventual vanishing (or `< 2` bound) of
   `fredholmIndex (integerThetaCollisionOperator (m : ℝ) n N)` on every natural-height window
   `m : ℕ`.
-/

set_option autoImplicit false

open Complex MeasureTheory Filter Set Metric intervalIntegral
open scoped BigOperators Topology Classical Polynomial Real

noncomputable section

namespace GaloisForLFunctions.ConjugateDiagonalGeometry

/-! ## §1 Explicit Gaussian strip convergence of the finite-theta first moment -/

private lemma abs_mul_exp_neg_two_abs_le (x : ℝ) :
    |x| * Real.exp (-2 * |x|) ≤ Real.exp (-|x|) := by
  have hx : |x| ≤ Real.exp |x| := by linarith [Real.add_one_le_exp |x|]
  calc |x| * Real.exp (-2 * |x|)
      ≤ Real.exp |x| * Real.exp (-2 * |x|) :=
        mul_le_mul_of_nonneg_right hx (Real.exp_pos _).le
    _ = Real.exp (|x| + -2 * |x|) := (Real.exp_add _ _).symm
    _ = Real.exp (-|x|) := by congr 1; ring

private lemma theta_firstMoment_integrand_strip_bound {R : ℝ} (_hR : 0 ≤ R) {z : ℂ}
    (hz : |z.re| ≤ R) (x : ℝ) :
    |x| * _root_.RHTower.thetaCuspFullSource x *
        ‖Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))‖ ≤
      _root_.RHTower.thetaCuspTiltDecayConstant (R + 5 / 2) * Real.exp (-|x|) := by
  have hre : (1 / 2 - z.re) * x ≤ (R + 1 / 2) * |x| := by
    have h1 : |1 / 2 - z.re| ≤ R + 1 / 2 := by
      have ha := abs_sub (1 / 2 : ℝ) z.re
      norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at ha
      linarith only [ha, hz]
    calc (1 / 2 - z.re) * x
        ≤ |(1 / 2 - z.re) * x| := le_abs_self _
      _ = |1 / 2 - z.re| * |x| := abs_mul _ _
      _ ≤ (R + 1 / 2) * |x| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  have hexp : ‖Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))‖ ≤
      Real.exp ((R + 1 / 2) * |x|) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have he : (((1 / 2 : ℂ) - z) * (x : ℂ)).re = (1 / 2 - z.re) * x := by simp
    simpa only [he] using hre
  have hfull := _root_.RHTower.thetaCuspFullSource_le_tiltDecayConstant (R + 5 / 2) x
  have hC0 : 0 ≤ _root_.RHTower.thetaCuspTiltDecayConstant (R + 5 / 2) :=
    (_root_.RHTower.thetaCuspTiltDecayConstant_pos _).le
  calc |x| * _root_.RHTower.thetaCuspFullSource x *
          ‖Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))‖
      = |x| * (_root_.RHTower.thetaCuspFullSource x *
          ‖Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))‖) := by ring
    _ ≤ |x| * ((_root_.RHTower.thetaCuspTiltDecayConstant (R + 5 / 2) *
          Real.exp (-((R + 5 / 2) * |x|))) * Real.exp ((R + 1 / 2) * |x|)) := by
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg x)
        exact mul_le_mul hfull hexp (norm_nonneg _) (mul_nonneg hC0 (Real.exp_pos _).le)
    _ = _root_.RHTower.thetaCuspTiltDecayConstant (R + 5 / 2) *
          (|x| * Real.exp (-2 * |x|)) := by
        have hadd : Real.exp (-((R + 5 / 2) * |x|)) * Real.exp ((R + 1 / 2) * |x|) =
            Real.exp (-2 * |x|) := by
          rw [← Real.exp_add]
          congr 1
          ring
        calc |x| * ((_root_.RHTower.thetaCuspTiltDecayConstant (R + 5 / 2) *
                Real.exp (-((R + 5 / 2) * |x|))) * Real.exp ((R + 1 / 2) * |x|))
            = _root_.RHTower.thetaCuspTiltDecayConstant (R + 5 / 2) *
                (|x| * (Real.exp (-((R + 5 / 2) * |x|)) *
                  Real.exp ((R + 1 / 2) * |x|))) := by ring
          _ = _root_.RHTower.thetaCuspTiltDecayConstant (R + 5 / 2) *
                (|x| * Real.exp (-2 * |x|)) := by rw [hadd]
    _ ≤ _root_.RHTower.thetaCuspTiltDecayConstant (R + 5 / 2) * Real.exp (-|x|) :=
      mul_le_mul_of_nonneg_left (abs_mul_exp_neg_two_abs_le x) hC0

/-- Uniform Gaussian integer-tail bound for `finiteThetaAmplitude N → xi` on vertical strips. -/
theorem norm_finiteThetaAmplitude_sub_xi_le_strip (N : ℕ) {R : ℝ} (hR : 0 ≤ R) {z : ℂ}
    (hz : |z.re| ≤ R) :
    ‖_root_.RHTower.finiteThetaAmplitude N z - _root_.RHTower.xi z‖ ≤
      _root_.RHTower.thetaCuspIntegerTailConstant * Real.exp (-((N + 1 : ℕ) : ℝ) ^ 2) *
        _root_.RHTower.thetaAmplitudeEnvelope R := by
  have h := _root_.RHTower.norm_finiteThetaAmplitude_sub_full_le_strip N hR hz
  rwa [bilateral_fullTheta_eq_xi] at h

/-- Uniform Gaussian integer-tail bound for `-finiteThetaFirstMoment N → deriv xi` on vertical
strips, with the identical envelope constant `thetaAmplitudeEnvelope R`. -/
theorem norm_finiteThetaFirstMoment_sub_deriv_xi_le_strip (N : ℕ) {R : ℝ} (hR : 0 ≤ R) {z : ℂ}
    (hz : |z.re| ≤ R) :
    ‖-_root_.RHTower.finiteThetaFirstMoment N z - deriv _root_.RHTower.xi z‖ ≤
      _root_.RHTower.thetaCuspIntegerTailConstant * Real.exp (-((N + 1 : ℕ) : ℝ) ^ 2) *
        _root_.RHTower.thetaAmplitudeEnvelope R := by
  have hrew : -_root_.RHTower.finiteThetaFirstMoment N z - deriv _root_.RHTower.xi z =
      thetaSourceFirstMoment z - _root_.RHTower.finiteThetaFirstMoment N z := by
    rw [thetaSourceFirstMoment_eq_neg_deriv_xi]
    ring
  rw [hrew]
  have hfull : Integrable (fun x : ℝ =>
      (x : ℂ) * (_root_.RHTower.thetaCuspFullSource x : ℂ) *
        Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))) := by
    simpa only [pow_one, _root_.RHTower.thetaCuspTiltSource_k] using
      _root_.RHTower.thetaCuspTiltSource.integrable_mul_exp ((1 / 2 : ℂ) - z) 1
  have hN : Integrable (fun x : ℝ =>
      (x : ℂ) * (_root_.RHTower.reflectedFiniteThetaSource (N + 1) x : ℂ) *
        Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))) := by
    simpa only [pow_one, _root_.RHTower.finiteThetaTiltSource] using
      (_root_.RHTower.finiteThetaTiltSource N).integrable_mul_exp ((1 / 2 : ℂ) - z) 1
  rw [thetaSourceFirstMoment, _root_.RHTower.finiteThetaFirstMoment, ← integral_sub hfull hN]
  have hC0 : 0 ≤ _root_.RHTower.thetaCuspIntegerTailConstant *
      Real.exp (-((N + 1 : ℕ) : ℝ) ^ 2) :=
    mul_nonneg _root_.RHTower.thetaCuspIntegerTailConstant_nonneg (Real.exp_pos _).le
  calc ‖∫ x : ℝ, (x : ℂ) * (_root_.RHTower.thetaCuspFullSource x : ℂ) *
            Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ)) -
          (x : ℂ) * (_root_.RHTower.reflectedFiniteThetaSource (N + 1) x : ℂ) *
            Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))‖
      ≤ ∫ x : ℝ, ‖(x : ℂ) * (_root_.RHTower.thetaCuspFullSource x : ℂ) *
            Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ)) -
          (x : ℂ) * (_root_.RHTower.reflectedFiniteThetaSource (N + 1) x : ℂ) *
            Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ, (_root_.RHTower.thetaCuspIntegerTailConstant *
            Real.exp (-((N + 1 : ℕ) : ℝ) ^ 2)) *
          (_root_.RHTower.thetaCuspTiltDecayConstant (R + 5 / 2) * Real.exp (-|x|)) := by
        apply integral_mono_ae (hfull.sub hN).norm
          ((_root_.RHTower.integrable_thetaAmplitudeProfile.const_mul _).const_mul _)
        filter_upwards with x
        have hfact : (x : ℂ) * (_root_.RHTower.thetaCuspFullSource x : ℂ) *
              Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ)) -
            (x : ℂ) * (_root_.RHTower.reflectedFiniteThetaSource (N + 1) x : ℂ) *
              Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ)) =
            (x : ℂ) *
              ((_root_.RHTower.thetaCuspFullSource x -
                _root_.RHTower.reflectedFiniteThetaSource (N + 1) x : ℝ) : ℂ) *
              Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ)) := by
          push_cast
          ring
        rw [hfact, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs]
        have htail := (_root_.RHTower.reflectedFiniteThetaSource_relative_tail (N + 1) x).2
        calc |x| * |_root_.RHTower.thetaCuspFullSource x -
                _root_.RHTower.reflectedFiniteThetaSource (N + 1) x| *
              ‖Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))‖
            ≤ |x| * ((_root_.RHTower.thetaCuspIntegerTailConstant *
                  Real.exp (-((N + 1 : ℕ) : ℝ) ^ 2)) *
                _root_.RHTower.thetaCuspFullSource x) *
              ‖Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))‖ := by
              refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
              exact mul_le_mul_of_nonneg_left htail (abs_nonneg x)
          _ = (_root_.RHTower.thetaCuspIntegerTailConstant *
                Real.exp (-((N + 1 : ℕ) : ℝ) ^ 2)) *
              (|x| * _root_.RHTower.thetaCuspFullSource x *
                ‖Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))‖) := by ring
          _ ≤ (_root_.RHTower.thetaCuspIntegerTailConstant *
                Real.exp (-((N + 1 : ℕ) : ℝ) ^ 2)) *
              (_root_.RHTower.thetaCuspTiltDecayConstant (R + 5 / 2) * Real.exp (-|x|)) :=
            mul_le_mul_of_nonneg_left (theta_firstMoment_integrand_strip_bound hR hz x) hC0
    _ = _root_.RHTower.thetaCuspIntegerTailConstant * Real.exp (-((N + 1 : ℕ) : ℝ) ^ 2) *
          _root_.RHTower.thetaAmplitudeEnvelope R := by
        rw [integral_const_mul, integral_const_mul]
        rfl

/-! ## §2 Source-pure window contour, Laurent loop, and Wiener–Hopf operator -/

/-- Lower-left corner `-1 / 2 - i / (2 * zhukovskyStage n)` of the shifted window rectangle. -/
def thetaWindowLowerLeft (n : ℕ) : ℂ :=
  (-1 / 2 : ℂ) - ((1 / (2 * (zhukovskyStage n : ℝ)) : ℝ) : ℂ) * I

/-- Upper-right corner `3 / 2 + i * (max 0 T - 1 / (2 * zhukovskyStage n))` of the shifted window
rectangle, enclosing `[0, T)` on the vertical axis without hitting zeros at `Im = 0` or `Im = T`. -/
def thetaWindowUpperRight (T : ℝ) (n : ℕ) : ℂ :=
  (3 / 2 : ℂ) + ((max 0 T - 1 / (2 * (zhukovskyStage n : ℝ)) : ℝ) : ℂ) * I

@[simp]
theorem thetaWindowLowerLeft_re (n : ℕ) : (thetaWindowLowerLeft n).re = -1 / 2 := by
  simp [thetaWindowLowerLeft]

@[simp]
theorem thetaWindowLowerLeft_im (n : ℕ) :
    (thetaWindowLowerLeft n).im = -1 / (2 * (zhukovskyStage n : ℝ)) := by
  simp [thetaWindowLowerLeft]
  ring

@[simp]
theorem thetaWindowUpperRight_re (T : ℝ) (n : ℕ) :
    (thetaWindowUpperRight T n).re = 3 / 2 := by
  simp [thetaWindowUpperRight]

@[simp]
theorem thetaWindowUpperRight_im (T : ℝ) (n : ℕ) :
    (thetaWindowUpperRight T n).im = max 0 T - 1 / (2 * (zhukovskyStage n : ℝ)) := by
  simp [thetaWindowUpperRight]

theorem thetaWindow_re_le (T : ℝ) (n : ℕ) :
    (thetaWindowLowerLeft n).re ≤ (thetaWindowUpperRight T n).re := by
  simp

theorem thetaWindow_im_le (T : ℝ) (n : ℕ) :
    (thetaWindowLowerLeft n).im ≤ (thetaWindowUpperRight T n).im := by
  rw [thetaWindowLowerLeft_im, thetaWindowUpperRight_im]
  have h0 : (0 : ℝ) ≤ max 0 T := le_max_left 0 T
  linarith

/-- Source-pure `r`-th power-sum contour integral around the `(T, n)` window rectangle, formed
exclusively from the `N`-th integer theta prefix (`finiteThetaAmplitude N` and
`finiteThetaFirstMoment N`). -/
def integerThetaWindowPowerSum (T : ℝ) (n N r : ℕ) : ℂ :=
  (2 * Real.pi * I)⁻¹ *
    _root_.RHTower.rectIntegral
      (fun z => z ^ r *
        (-_root_.RHTower.finiteThetaFirstMoment N z / _root_.RHTower.finiteThetaAmplitude N z))
      (thetaWindowLowerLeft n) (thetaWindowUpperRight T n)

/-- Integer degree extracted from the `r = 0` contour integral. Whenever `finiteThetaAmplitude N`
is zero-free on the rectangle boundary, `integerThetaWindowPowerSum T n N 0` is already an exact
integer `(k : ℂ)`. -/
def integerThetaWindowDegree (T : ℝ) (n N : ℕ) : ℕ :=
  Nat.floor ((integerThetaWindowPowerSum T n N 0).re + 1 / 2)

/-- Source-pure Newton–Girard pair-difference polynomial built from `integerThetaWindowDegree` and
`integerThetaWindowPowerSum`. -/
def integerThetaDifferencePoly (T : ℝ) (n N : ℕ) : Polynomial ℂ :=
  pairDiffPoly (integerThetaWindowDegree T n N) (integerThetaWindowPowerSum T n N)

/-- Base circle loop obtained by evaluating `integerThetaDifferencePoly T n N` along
`zhukovskyLoop n`. -/
def integerThetaBaseLoop (T : ℝ) (n N : ℕ) : C(HTGeometry.UnitCircle, ℂ) where
  toFun u := (integerThetaDifferencePoly T n N).eval (zhukovskyLoop n u)
  continuous_toFun := (integerThetaDifferencePoly T n N).continuous.comp (zhukovskyLoop n).continuous

/-- Squared Zhukovsky Laurent loop `(P_{T,n,N}(J_n(ρ_n u)))²` on `UnitCircle`. -/
def integerThetaLaurentLoop (T : ℝ) (n N : ℕ) : C(HTGeometry.UnitCircle, ℂ) :=
  integerThetaBaseLoop T n N ^ 2

@[simp]
theorem integerThetaLaurentLoop_apply (T : ℝ) (n N : ℕ) (u : HTGeometry.UnitCircle) :
    integerThetaLaurentLoop T n N u =
      ((integerThetaDifferencePoly T n N).eval (zhukovskyLoop n u)) ^ 2 := by
  rfl

/-- Unimodular circle symbol of the integer-theta collision loop. -/
def integerThetaCollisionSymbol (T : ℝ) (n N : ℕ) : C(HTGeometry.UnitCircle, ℂ) :=
  unitNormalizeSymbol (integerThetaLaurentLoop T n N)

/-- **Integer-theta Wiener–Hopf collision operator** on `L²(ℝ)`, constructed purely from finite
integer theta prefixes on the window `T` at Zhukovsky stage `n` and prefix cutoff `N`. -/
def integerThetaCollisionOperator (T : ℝ) (n N : ℕ) :
    HTGeometry.L2Real →L[ℂ] HTGeometry.L2Real :=
  HTGeometry.wienerHopfLift (integerThetaCollisionSymbol T n N)

/-- `integerThetaCollisionOperator T n N` is unconditionally Fredholm for every `(T, n, N)`. -/
theorem isFredholmOp_integerThetaCollisionOperator (T : ℝ) (n N : ℕ) :
    HTGeometry.IsFredholmOp (integerThetaCollisionOperator T n N) :=
  isFredholmOp_wienerHopfLift_unitNormalizeSymbol _

/-- Its Fredholm index unconditionally equals the circle winding of `integerThetaCollisionSymbol`. -/
theorem fredholmIndex_integerThetaCollisionOperator_eq_circleWinding (T : ℝ) (n N : ℕ) :
    HTGeometry.fredholmIndex (integerThetaCollisionOperator T n N) =
      HTGeometry.circleWinding (integerThetaCollisionSymbol T n N) :=
  fredholmIndex_wienerHopfLift_unitNormalizeSymbol _

/-- Its Fredholm index is unconditionally even for every `(T, n, N)` (reflecting the pair-exchange
quantum of horizontal collisions). -/
theorem even_fredholmIndex_integerThetaCollisionOperator (T : ℝ) (n N : ℕ) :
    2 ∣ HTGeometry.fredholmIndex (integerThetaCollisionOperator T n N) :=
  even_fredholmIndex_unitNormalizeSymbol_sq (integerThetaBaseLoop T n N)

/-- Whenever `finiteThetaAmplitude N` has no zeros on the `(T, n)` rectangle boundary, the `r = 0`
source contour integral `integerThetaWindowPowerSum T n N 0` is already an exact integer `(k : ℂ)`
by the rectangle boundary phase winding theorem. -/
theorem integerThetaWindowPowerSum_zero_is_int (T : ℝ) (n N : ℕ)
    (hne : ∀ t : ℝ, _root_.RHTower.finiteThetaAmplitude N
      (_root_.RHTower.rectangleBoundaryPath
        (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t) ≠ 0) :
    ∃ k : ℤ, integerThetaWindowPowerSum T n N 0 = (k : ℂ) := by
  let D : _root_.RHTower.RectangleArgumentDatum :=
    { F := _root_.RHTower.finiteThetaAmplitude N
      z₁ := thetaWindowLowerLeft n
      z₂ := thetaWindowUpperRight T n
      U := Set.univ
      isOpen := isOpen_univ
      differentiableOn := (_root_.RHTower.differentiable_finiteThetaAmplitude N).differentiableOn
      path_mem := fun _ => Set.mem_univ _
      ne_zero := hne }
  obtain ⟨k, hk⟩ := D.toPhase.windingNumber_eq_intCast
  refine ⟨k, ?_⟩
  rw [D.windingNumber_toPhase] at hk
  have hfun : (fun z : ℂ => z ^ 0 *
        (-_root_.RHTower.finiteThetaFirstMoment N z / _root_.RHTower.finiteThetaAmplitude N z)) =
      logDeriv (_root_.RHTower.finiteThetaAmplitude N) := by
    funext z
    rw [pow_zero, one_mul, logDeriv_apply, _root_.RHTower.deriv_finiteThetaAmplitude]
  unfold integerThetaWindowPowerSum
  rw [hfun]
  exact hk.symm

/-! ## §3 Window zero isolation and weighted Cauchy power sums of `xi` -/

/-- Open box neighbourhood around the closed `(T, n)` window rectangle. -/
def thetaWindowOpenBox (T : ℝ) (n : ℕ) : Set ℂ :=
  {z : ℂ | -1 < z.re ∧ z.re < 2 ∧
    -3 / (4 * (zhukovskyStage n : ℝ)) < z.im ∧
    z.im < max 0 T - 1 / (4 * (zhukovskyStage n : ℝ))}

theorem isOpen_thetaWindowOpenBox (T : ℝ) (n : ℕ) : IsOpen (thetaWindowOpenBox T n) := by
  unfold thetaWindowOpenBox
  exact (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_re continuous_const).inter
      ((isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt Complex.continuous_im continuous_const)))

theorem thetaWindowRect_subset_openBox (T : ℝ) (n : ℕ) :
    (uIcc (thetaWindowLowerLeft n).re (thetaWindowUpperRight T n).re ×ℂ
      uIcc (thetaWindowLowerLeft n).im (thetaWindowUpperRight T n).im) ⊆
    thetaWindowOpenBox T n := by
  intro z hz
  rw [uIcc_of_le (thetaWindow_re_le T n), uIcc_of_le (thetaWindow_im_le T n),
    Complex.mem_reProdIm, thetaWindowLowerLeft_re, thetaWindowUpperRight_re,
    thetaWindowLowerLeft_im, thetaWindowUpperRight_im] at hz
  have hs : (6 : ℝ) ≤ (zhukovskyStage n : ℝ) := six_le_zhukovskyStage_real n
  have hpos : (0 : ℝ) < (zhukovskyStage n : ℝ) := zhukovskyStage_pos n
  have hquarter : 1 / (4 * (zhukovskyStage n : ℝ)) < 1 / (2 * (zhukovskyStage n : ℝ)) := by
    exact one_div_lt_one_div_of_lt (by positivity) (by linarith)
  have hthree_quarter :
      -3 / (4 * (zhukovskyStage n : ℝ)) < -1 / (2 * (zhukovskyStage n : ℝ)) := by
    have hlt : 1 / (2 * (zhukovskyStage n : ℝ)) < 3 / (4 * (zhukovskyStage n : ℝ)) := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      linarith
    linarith
  exact ⟨by linarith [hz.1.1], by linarith [hz.1.2],
    by linarith [hz.2.1], by linarith [hz.2.2]⟩

/-- Positive left real-part margin of all `xi` zeros in the height-`T` strip window (`1 / 2` when
the window is empty). -/
def windowStripLeftMargin (T : ℝ) : ℝ :=
  if h : (_root_.RHTower.stripZeros_finite T).toFinset.Nonempty then
    (_root_.RHTower.stripZeros_finite T).toFinset.inf' h Complex.re
  else
    1 / 2

theorem windowStripLeftMargin_pos (T : ℝ) : 0 < windowStripLeftMargin T := by
  unfold windowStripLeftMargin
  split_ifs with h
  · rw [Finset.lt_inf'_iff]
    intro w hw
    exact ((_root_.RHTower.stripZeros_finite T).mem_toFinset.mp hw).1.1
  · norm_num

theorem windowStripLeftMargin_le_re {T : ℝ} {w : ℂ}
    (hw : w ∈ (_root_.RHTower.stripZeros_finite T).toFinset) :
    windowStripLeftMargin T ≤ w.re := by
  unfold windowStripLeftMargin
  rw [dif_pos ⟨w, hw⟩]
  exact Finset.inf'_le Complex.re hw

/-- Window resolution scale `thetaWindowScale T` ensuring simultaneous collar separation,
critical-strip left-margin containment, and pairwise Zhukovsky ellipse resolution. -/
def thetaWindowScale (T : ℝ) : ℕ :=
  max 6 (max (Nat.ceil (2 / collisionWindowGap T) + 1)
    (Nat.ceil (1 / (2 * windowStripLeftMargin T))))

theorem six_le_thetaWindowScale (T : ℝ) : 6 ≤ thetaWindowScale T := le_max_left 6 _

theorem two_div_stage_lt_collisionWindowGap {T : ℝ} {n : ℕ} (hn : thetaWindowScale T ≤ n) :
    2 / (zhukovskyStage n : ℝ) < collisionWindowGap T := by
  have hn6 : 6 ≤ n := (six_le_thetaWindowScale T).trans hn
  have hceil : Nat.ceil (2 / collisionWindowGap T) + 1 ≤ n :=
    ((le_max_left _ _).trans (le_max_right 6 _)).trans hn
  have hlt : 2 / collisionWindowGap T < (zhukovskyStage n : ℝ) := by
    rw [zhukovskyStage_eq_self hn6]
    have h1 := Nat.le_ceil (2 / collisionWindowGap T)
    have h2 : (Nat.ceil (2 / collisionWindowGap T) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hceil
    linarith
  have hgap := collisionWindowGap_pos T
  have hs := zhukovskyStage_pos n
  rwa [div_lt_iff₀ hs, mul_comm, ← div_lt_iff₀ hgap]

theorem half_inv_stage_le_windowStripLeftMargin {T : ℝ} {n : ℕ} (hn : thetaWindowScale T ≤ n) :
    1 / (2 * (zhukovskyStage n : ℝ)) ≤ windowStripLeftMargin T := by
  have hn6 : 6 ≤ n := (six_le_thetaWindowScale T).trans hn
  have hceil : Nat.ceil (1 / (2 * windowStripLeftMargin T)) ≤ n :=
    ((le_max_right _ _).trans (le_max_right 6 _)).trans hn
  have hle : 1 / (2 * windowStripLeftMargin T) ≤ (zhukovskyStage n : ℝ) := by
    rw [zhukovskyStage_eq_self hn6]
    exact (Nat.le_ceil _).trans (by exact_mod_cast hceil)
  have hm := windowStripLeftMargin_pos T
  have hs := zhukovskyStage_pos n
  rw [div_le_iff₀ (by positivity)]
  have hmul := (div_le_iff₀ (by positivity : 0 < 2 * windowStripLeftMargin T)).mp hle
  linarith

/-- Every `xi` zero in `stripZeros T` lies strictly inside the `(T, n)` window rectangle once
`thetaWindowScale T ≤ n`. -/
theorem stripZeros_strictly_inside_thetaWindow {T : ℝ} {n : ℕ} (hn : thetaWindowScale T ≤ n)
    {w : ℂ} (hw : w ∈ (_root_.RHTower.stripZeros_finite T).toFinset) :
    (thetaWindowLowerLeft n).re < w.re ∧ w.re < (thetaWindowUpperRight T n).re ∧
      (thetaWindowLowerLeft n).im < w.im ∧ w.im < (thetaWindowUpperRight T n).im := by
  have hwdata := (_root_.RHTower.stripZeros_finite T).mem_toFinset.mp hw
  have hTpos : 0 < T := lt_of_le_of_lt hwdata.1.2.2.1 hwdata.1.2.2.2
  have hmax : max 0 T = T := max_eq_right hTpos.le
  have hs_pos : (0 : ℝ) < (zhukovskyStage n : ℝ) := zhukovskyStage_pos n
  have hgap_lt := two_div_stage_lt_collisionWindowGap hn
  -- `w` belongs to `collisionWindowSeparationSet T` and `w.im < T`.
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
    rw [mem_closedBall]
    linarith only [hsupp]
  have hwSep : w ∈ collisionWindowSeparationSet T :=
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hwBall)
  have htopSep : (⟨0, T⟩ : ℂ) ∈ collisionWindowSeparationSet T :=
    Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hgapT : collisionWindowGap T ≤ T - w.im := by
    have h1 : collisionWindowGap T ≤ |(⟨0, T⟩ : ℂ).im - w.im| :=
      (min_le_right _ _).trans
        (finiteCoordinateGap_le _ Complex.im htopSep hwSep hwdata.1.2.2.2.ne')
    simpa only [abs_of_pos (sub_pos.mpr hwdata.1.2.2.2)] using h1
  have hhalf_lt : 1 / (2 * (zhukovskyStage n : ℝ)) < 2 / (zhukovskyStage n : ℝ) := by
    rw [div_lt_div_iff₀ (by positivity) hs_pos]
    linarith
  rw [thetaWindowLowerLeft_re, thetaWindowUpperRight_re,
    thetaWindowLowerLeft_im, thetaWindowUpperRight_im, hmax]
  refine ⟨by linarith [hwdata.1.1], by linarith [hwdata.1.2.1], ?_, ?_⟩
  · have hneg : -1 / (2 * (zhukovskyStage n : ℝ)) < 0 := by
      have : 0 < 1 / (2 * (zhukovskyStage n : ℝ)) := by positivity
      linarith
    linarith [hwdata.1.2.2.1]
  · linarith

/-- Conversely, every `xi` zero in `thetaWindowOpenBox T n` belongs to `stripZeros T` once
`thetaWindowScale T ≤ n`. -/
theorem xi_zero_in_openBox_mem_stripZeros {T : ℝ} {n : ℕ} (hn : thetaWindowScale T ≤ n)
    {z : ℂ} (hzBox : z ∈ thetaWindowOpenBox T n) (hz0 : _root_.RHTower.xi z = 0) :
    z ∈ (_root_.RHTower.stripZeros_finite T).toFinset := by
  have hstrip := _root_.RHTower.xi_zero_re_mem_open_unit hz0
  have hs6 : (6 : ℝ) ≤ (zhukovskyStage n : ℝ) := six_le_zhukovskyStage_real n
  have hs_pos : (0 : ℝ) < (zhukovskyStage n : ℝ) := zhukovskyStage_pos n
  have hgap_lt := two_div_stage_lt_collisionWindowGap hn
  have h34_lt_one : 3 / (4 * (zhukovskyStage n : ℝ)) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  -- First show `z` lies in the closed ball of radius `collisionWindowRadius T + 3`.
  have hz_im_abs : |z.im| ≤ |T| + 1 := by
    rw [abs_le]
    have hlow : -(|T| + 1) ≤ z.im := by
      have h1 : -1 < -3 / (4 * (zhukovskyStage n : ℝ)) := by linarith
      linarith [hzBox.2.2.1, abs_nonneg T]
    have hhigh : z.im ≤ |T| + 1 := by
      have hmax_le : max 0 T ≤ |T| := max_le (abs_nonneg T) (le_abs_self T)
      have hpos4 : 0 < 1 / (4 * (zhukovskyStage n : ℝ)) := by positivity
      linarith [hzBox.2.2.2]
    exact ⟨hlow, hhigh⟩
  have hzBall : z ∈ (_root_.RHTower.xi_zeros_closedBall_finite 0
      ((collisionWindowRadius T : ℝ) + 3)).toFinset := by
    apply (_root_.RHTower.xi_zeros_closedBall_finite 0
      ((collisionWindowRadius T : ℝ) + 3)).mem_toFinset.mpr
    refine ⟨?_, hz0⟩
    rw [mem_closedBall, dist_zero_right]
    have hnorm := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_pos hstrip.1] at hnorm
    have hceil := Nat.le_ceil |T|
    have hR : |T| + 2 ≤ (collisionWindowRadius T : ℝ) := by
      unfold collisionWindowRadius
      push_cast
      linarith
    linarith [hstrip.2]
  have hzSep : z ∈ collisionWindowSeparationSet T :=
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hzBall)
  have hzeroSep : (0 : ℂ) ∈ collisionWindowSeparationSet T := Finset.mem_insert_self _ _
  -- Rule out `z.im < 0` using the coordinate gap against `0`.
  have hzim_nonneg : 0 ≤ z.im := by
    by_contra hneg
    push_neg at hneg
    have hgap0 : collisionWindowGap T ≤ -z.im := by
      have h1 : collisionWindowGap T ≤ |z.im - (0 : ℂ).im| :=
        (min_le_right _ _).trans
          (finiteCoordinateGap_le _ Complex.im hzSep hzeroSep
            (by simpa only [Complex.zero_im] using hneg.ne))
      simpa only [Complex.zero_im, sub_zero, abs_of_neg hneg] using h1
    have hbound : -z.im < 3 / (4 * (zhukovskyStage n : ℝ)) := by linarith [hzBox.2.2.1]
    have h34_lt_2 : 3 / (4 * (zhukovskyStage n : ℝ)) < 2 / (zhukovskyStage n : ℝ) := by
      rw [div_lt_div_iff₀ (by positivity) hs_pos]
      linarith
    linarith
  -- Since `0 ≤ z.im < max 0 T - 1 / (4 s)`, `max 0 T` must be `T > 0` and `z.im < T`.
  have hmax_pos : 0 < max 0 T := by
    have hpos4 : 0 < 1 / (4 * (zhukovskyStage n : ℝ)) := by positivity
    linarith [hzBox.2.2.2]
  have hT_pos : 0 < T := by
    by_contra hle
    push_neg at hle
    rw [max_eq_left hle] at hmax_pos
    exact lt_irrefl 0 hmax_pos
  have hzim_lt_T : z.im < T := by
    have hpos4 : 0 < 1 / (4 * (zhukovskyStage n : ℝ)) := by positivity
    have hmax_eq : max 0 T = T := max_eq_right hT_pos.le
    linarith [hzBox.2.2.2]
  exact (_root_.RHTower.stripZeros_finite T).mem_toFinset.mpr
    ⟨⟨hstrip.1, hstrip.2, hzim_nonneg, hzim_lt_T⟩, hz0⟩

/-- **Weighted argument principle on the shifted window rectangle.** For `thetaWindowScale T ≤ n`
and every `r : ℕ`, the `r`-th logarithmic-derivative moment of `xi` around `R_{T,n}` equals the
exact power sum of `xi` zeros in `stripZeros T`. -/
theorem xi_rectIntegral_powerSum_eq_stripZeros_sum (T : ℝ) {n : ℕ} (hn : thetaWindowScale T ≤ n)
    (r : ℕ) :
    (2 * Real.pi * I)⁻¹ *
      _root_.RHTower.rectIntegral (fun z => z ^ r * logDeriv _root_.RHTower.xi z)
        (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) =
      ∑ w ∈ (_root_.RHTower.stripZeros_finite T).toFinset,
        ((analyticOrderAt _root_.RHTower.xi w).toNat : ℂ) * w ^ r := by
  set Z := (_root_.RHTower.stripZeros_finite T).toFinset
  set U := thetaWindowOpenBox T n
  have hUopen : IsOpen U := isOpen_thetaWindowOpenBox T n
  have hsub := thetaWindowRect_subset_openBox T n
  have hin : ∀ w ∈ Z,
      (thetaWindowLowerLeft n).re < w.re ∧ w.re < (thetaWindowUpperRight T n).re ∧
        (thetaWindowLowerLeft n).im < w.im ∧ w.im < (thetaWindowUpperRight T n).im :=
    fun _ hw => stripZeros_strictly_inside_thetaWindow hn hw
  have htU : ∀ w ∈ Z, w ∈ U := by
    intro w hw
    obtain ⟨h1, h2, h3, h4⟩ := hin w hw
    exact hsub (Complex.mem_reProdIm.mpr
      ⟨uIcc_of_le (thetaWindow_re_le T n) ▸ ⟨h1.le, h2.le⟩,
       uIcc_of_le (thetaWindow_im_le T n) ▸ ⟨h3.le, h4.le⟩⟩)
  have hzeros : ∀ z ∈ U, _root_.RHTower.xi z = 0 → z ∈ Z :=
    fun _ hzU hz0 => xi_zero_in_openBox_mem_stripZeros hn hzU hz0
  have hord : ∀ w ∈ Z, analyticOrderAt _root_.RHTower.xi w ≠ ⊤ :=
    fun w _ => _root_.RHTower.xi_orderAt_ne_top w
  obtain ⟨m₀, h, hhan, hh0, hfact⟩ :=
    _root_.RHTower.exists_multi_peel hUopen (_root_.RHTower.xi_analyticOnNhd U) Z htU hzeros hord
  -- Identify each peeled exponent `m₀ w₀` with `(analyticOrderAt xi w₀).toNat`.
  have hm_eq : ∀ w₀ ∈ Z, m₀ w₀ = (analyticOrderAt _root_.RHTower.xi w₀).toNat := by
    intro w₀ hw₀
    let G : ℂ → ℂ := fun z => (∏ w ∈ Z.erase w₀, (z - w) ^ m₀ w) * h z
    have hGan : AnalyticAt ℂ G w₀ := by
      refine AnalyticAt.mul ?_ (hhan w₀ (htU w₀ hw₀))
      have : ∀ w ∈ Z.erase w₀, AnalyticAt ℂ (fun z => (z - w) ^ m₀ w) w₀ :=
        fun w _ => (analyticAt_id.sub analyticAt_const).pow (m₀ w)
      simpa only [Finset.prod_apply] using Finset.analyticAt_prod (Z.erase w₀) this
    have hG0 : G w₀ ≠ 0 := by
      refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun w hw => ?_) (hh0 w₀ (htU w₀ hw₀))
      exact pow_ne_zero _ (sub_ne_zero.mpr (Finset.ne_of_mem_erase hw).symm)
    have hev : _root_.RHTower.xi =ᶠ[nhds w₀] (fun z => (z - w₀) ^ m₀ w₀) • G := by
      filter_upwards [hUopen.mem_nhds (htU w₀ hw₀)] with z hzU
      rw [Pi.smul_apply, smul_eq_mul, hfact z hzU, ← Finset.mul_prod_erase Z _ hw₀, mul_assoc]
    have hord_eq : analyticOrderAt _root_.RHTower.xi w₀ = (m₀ w₀ : ℕ∞) :=
      ((_root_.RHTower.xi_analyticOnNhd U w₀ (htU w₀ hw₀)).analyticOrderAt_eq_natCast).mpr
        ⟨G, hGan, hG0, hev⟩
    rw [hord_eq, ENat.toNat_coe]
  have hfact' : ∀ z ∈ U, _root_.RHTower.xi z =
      (∏ w ∈ Z, (z - w) ^ (analyticOrderAt _root_.RHTower.xi w).toNat) * h z := by
    intro z hzU
    rw [hfact z hzU]
    congr 1
    exact Finset.prod_congr rfl fun w hw => by rw [hm_eq w hw]
  have hg : AnalyticOnNhd ℂ (fun z : ℂ => z ^ r) Set.univ := fun _ _ => analyticAt_id.pow r
  have hrect := _root_.RHTower.rectIntegral_mul_logDeriv_boxCount
    Z id (fun w => (analyticOrderAt _root_.RHTower.xi w).toNat) hg hUopen hin hsub hhan hh0 hfact'
  have h2pi_ne : (2 * Real.pi * I : ℂ) ≠ 0 := by
    have : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    simp [this, Complex.I_ne_zero]
  rw [hrect, inv_mul_cancel_left₀ h2pi_ne]
  rfl

/-! ## §4 Boundary convergence `N → ∞` of source power sums and difference polynomial -/

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

private lemma xi_ne_zero_on_thetaWindowBoundary {T : ℝ} {n : ℕ} (hn : thetaWindowScale T ≤ n)
    (t : ℝ) :
    _root_.RHTower.xi
      (_root_.RHTower.rectangleBoundaryPath
        (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t) ≠ 0 := by
  intro hz0
  set γt := _root_.RHTower.rectangleBoundaryPath
    (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t
  have hmemRect := _root_.RHTower.rectangleBoundaryPath_mem_reProdIm
    (thetaWindowLowerLeft n) (thetaWindowUpperRight T n)
    (thetaWindow_re_le T n) (thetaWindow_im_le T n) t
  have hmemBox : γt ∈ thetaWindowOpenBox T n := thetaWindowRect_subset_openBox T n hmemRect
  have hmemZ := xi_zero_in_openBox_mem_stripZeros hn hmemBox hz0
  obtain ⟨h1, h2, h3, h4⟩ := stripZeros_strictly_inside_thetaWindow hn hmemZ
  rcases rectangleBoundaryPath_on_edges
      (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t with h | h | h | h
  · exact h1.ne' h
  · exact h2.ne h
  · exact h3.ne' h
  · exact h4.ne h

private lemma abs_re_thetaWindowBoundary_le_two (T : ℝ) (n : ℕ) (t : ℝ) :
    |(_root_.RHTower.rectangleBoundaryPath
        (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t).re| ≤ 2 := by
  have hmem := _root_.RHTower.rectangleBoundaryPath_mem_reProdIm
    (thetaWindowLowerLeft n) (thetaWindowUpperRight T n)
    (thetaWindow_re_le T n) (thetaWindow_im_le T n) t
  rw [uIcc_of_le (thetaWindow_re_le T n), Complex.mem_reProdIm,
    thetaWindowLowerLeft_re, thetaWindowUpperRight_re] at hmem
  rw [abs_le]
  exact ⟨by linarith [hmem.1.1], by linarith [hmem.1.2]⟩

private lemma exists_xi_norm_lower_bound_on_boundary {T : ℝ} {n : ℕ}
    (hn : thetaWindowScale T ≤ n) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ t : ℝ,
      μ ≤ ‖_root_.RHTower.xi
        (_root_.RHTower.rectangleBoundaryPath
          (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t)‖ := by
  set γ := _root_.RHTower.rectangleBoundaryPath
    (thetaWindowLowerLeft n) (thetaWindowUpperRight T n)
  have hcont : Continuous (fun t : ℝ => ‖_root_.RHTower.xi (γ t)‖) :=
    (_root_.RHTower.xi_differentiable.continuous.comp
      (_root_.RHTower.continuous_rectangleBoundaryPath _ _)).norm
  obtain ⟨t₀, _, ht₀⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr (zero_le_one : (0 : ℝ) ≤ 1)) hcont.continuousOn
  refine ⟨‖_root_.RHTower.xi (γ t₀)‖,
    norm_pos_iff.mpr (xi_ne_zero_on_thetaWindowBoundary hn t₀), fun t => ?_⟩
  have hfrac : Int.fract t ∈ Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩
  have hmin : ‖_root_.RHTower.xi (γ t₀)‖ ≤ ‖_root_.RHTower.xi (γ (Int.fract t))‖ :=
    isMinOn_iff.mp ht₀ (Int.fract t) hfrac
  have hper : γ (Int.fract t) = γ t := by
    simp [γ, _root_.RHTower.rectangleBoundaryPath, Int.fract_fract]
  rwa [hper] at hmin

private lemma continuous_neg_finiteThetaFirstMoment (N : ℕ) :
    Continuous (fun z : ℂ => -_root_.RHTower.finiteThetaFirstMoment N z) := by
  have heq : (fun z : ℂ => -_root_.RHTower.finiteThetaFirstMoment N z) =
      deriv (_root_.RHTower.finiteThetaAmplitude N) :=
    funext fun z => (_root_.RHTower.deriv_finiteThetaAmplitude N z).symm
  rw [heq]
  exact continuousOn_univ.mp
    (((_root_.RHTower.differentiable_finiteThetaAmplitude N).differentiableOn.deriv
      isOpen_univ).continuousOn)

private lemma tendsto_gaussian_tail_zero (C : ℝ) :
    Tendsto (fun N : ℕ => C * Real.exp (-((N + 1 : ℕ) : ℝ) ^ 2)) atTop (𝓝 0) := by
  have hsq : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ) ^ 2) atTop atTop :=
    (Filter.tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hexp : Tendsto (fun N : ℕ => Real.exp (-((N + 1 : ℕ) : ℝ) ^ 2)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, pow_zero, one_mul] using
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0).comp hsq
  simpa only [mul_zero] using hexp.const_mul C

/-- Eventually in `N`, `finiteThetaAmplitude N` has no zeros anywhere on the `(T, n)` window
rectangle boundary. -/
theorem eventually_finiteThetaAmplitude_ne_zero_on_boundary (T : ℝ) {n : ℕ}
    (hn : thetaWindowScale T ≤ n) :
    ∀ᶠ N : ℕ in atTop, ∀ t : ℝ,
      _root_.RHTower.finiteThetaAmplitude N
        (_root_.RHTower.rectangleBoundaryPath
          (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t) ≠ 0 := by
  obtain ⟨μ, hμ, hmin⟩ := exists_xi_norm_lower_bound_on_boundary hn
  let C_env := _root_.RHTower.thetaCuspIntegerTailConstant *
    _root_.RHTower.thetaAmplitudeEnvelope 2
  have hev := (tendsto_gaussian_tail_zero C_env).eventually (gt_mem_nhds (half_pos hμ))
  filter_upwards [hev] with N hN t hzero
  set z := _root_.RHTower.rectangleBoundaryPath
    (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t
  have hbd := norm_finiteThetaAmplitude_sub_xi_le_strip N (by norm_num : (0 : ℝ) ≤ 2)
    (abs_re_thetaWindowBoundary_le_two T n t)
  have hbd' : ‖_root_.RHTower.finiteThetaAmplitude N z - _root_.RHTower.xi z‖ < μ / 2 := by
    refine hbd.trans_lt ?_
    simpa only [C_env, mul_right_comm] using hN
  rw [hzero, zero_sub, norm_neg] at hbd'
  linarith [hmin t]

/-- **Source power-sum convergence theorem.** For every `T : ℝ`, `thetaWindowScale T ≤ n`, and
`r : ℕ`, the source-pure contour integral `integerThetaWindowPowerSum T n N r` converges as
`N → ∞` to the exact `r`-th power sum of `xi` zeros in `stripZeros T`. -/
theorem tendsto_integerThetaWindowPowerSum (T : ℝ) {n : ℕ} (hn : thetaWindowScale T ≤ n)
    (r : ℕ) :
    Tendsto (fun N : ℕ => integerThetaWindowPowerSum T n N r) atTop
      (𝓝 (∑ w ∈ (_root_.RHTower.stripZeros_finite T).toFinset,
        ((analyticOrderAt _root_.RHTower.xi w).toNat : ℂ) * w ^ r)) := by
  rw [← xi_rectIntegral_powerSum_eq_stripZeros_sum T hn r]
  unfold integerThetaWindowPowerSum
  refine Tendsto.const_mul _ ?_
  set z₁ := thetaWindowLowerLeft n
  set z₂ := thetaWindowUpperRight T n
  set γ := _root_.RHTower.rectangleBoundaryPath z₁ z₂
  set vel := _root_.RHTower.rectangleBoundaryVelocity z₁ z₂
  obtain ⟨μ, hμ, hmin⟩ := exists_xi_norm_lower_bound_on_boundary hn
  have hγ_cont : Continuous γ := _root_.RHTower.continuous_rectangleBoundaryPath z₁ z₂
  have hxi_deriv_cont : Continuous (deriv _root_.RHTower.xi) :=
    continuousOn_univ.mp
      ((_root_.RHTower.xi_differentiable.differentiableOn.deriv isOpen_univ).continuousOn)
  -- Uniform upper bounds on `‖(γ t)^r‖`, `‖xi (γ t)‖`, `‖deriv xi (γ t)‖`, and `‖vel t‖` on `[0, 1]`.
  obtain ⟨B_pow, hB_pow⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hγ_cont.pow r).continuousOn
  obtain ⟨B_xi, hB_xi⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (_root_.RHTower.xi_differentiable.continuous.comp hγ_cont).continuousOn
  obtain ⟨B_dxi, hB_dxi⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hxi_deriv_cont.comp hγ_cont).continuousOn
  set M_pow : ℝ := max 1 B_pow
  set M_xi : ℝ := max 1 B_xi
  set M_dxi : ℝ := max 1 B_dxi
  set L_vel : ℝ := 4 * (|z₂.re - z₁.re| + |z₂.im - z₁.im|)
  have hM_pow_pos : 0 < M_pow := lt_of_lt_of_le zero_lt_one (le_max_left 1 B_pow)
  have hM_xi_pos : 0 < M_xi := lt_of_lt_of_le zero_lt_one (le_max_left 1 B_xi)
  have hM_dxi_pos : 0 < M_dxi := lt_of_lt_of_le zero_lt_one (le_max_left 1 B_dxi)
  have hL_vel_nonneg : 0 ≤ L_vel := by positivity
  set C_env : ℝ := _root_.RHTower.thetaCuspIntegerTailConstant *
    _root_.RHTower.thetaAmplitudeEnvelope 2
  set err : ℕ → ℝ := fun N => C_env * Real.exp (-((N + 1 : ℕ) : ℝ) ^ 2)
  have herr_tendsto : Tendsto err atTop (𝓝 0) := tendsto_gaussian_tail_zero C_env
  have hxi_logDeriv_cont : Continuous (fun t : ℝ => (γ t) ^ r * logDeriv _root_.RHTower.xi (γ t)) :=
    (hγ_cont.pow r).mul
      ((hxi_deriv_cont.comp hγ_cont).div
        (_root_.RHTower.xi_differentiable.continuous.comp hγ_cont)
        (xi_ne_zero_on_thetaWindowBoundary hn))
  rw [← _root_.RHTower.integral_rectangleBoundary_eq_rectIntegral z₁ z₂ _ hxi_logDeriv_cont]
  rw [Metric.tendsto_atTop]
  intro ε hε
  set K_lip : ℝ := M_pow * ((M_xi + M_dxi + μ) / (μ ^ 2 / 2)) * (L_vel + 1)
  have hK_lip_pos : 0 < K_lip := by positivity
  have hev1 := herr_tendsto.eventually (gt_mem_nhds (half_pos hμ))
  have hev2 := herr_tendsto.eventually (gt_mem_nhds (div_pos hε hK_lip_pos))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hev1.and hev2)
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨hN_half, hN_eps⟩ := hN₀ N hN
  have hamp_bd : ∀ t : ℝ, ‖_root_.RHTower.finiteThetaAmplitude N (γ t) - _root_.RHTower.xi (γ t)‖ ≤
      err N := by
    intro t
    have h := norm_finiteThetaAmplitude_sub_xi_le_strip N (by norm_num : (0 : ℝ) ≤ 2)
      (abs_re_thetaWindowBoundary_le_two T n t)
    simpa only [err, C_env, mul_right_comm] using h
  have hmom_bd : ∀ t : ℝ,
      ‖-_root_.RHTower.finiteThetaFirstMoment N (γ t) - deriv _root_.RHTower.xi (γ t)‖ ≤
        err N := by
    intro t
    have h := norm_finiteThetaFirstMoment_sub_deriv_xi_le_strip N (by norm_num : (0 : ℝ) ≤ 2)
      (abs_re_thetaWindowBoundary_le_two T n t)
    simpa only [err, C_env, mul_right_comm] using h
  have hamp_lower : ∀ t : ℝ, μ / 2 ≤ ‖_root_.RHTower.finiteThetaAmplitude N (γ t)‖ := by
    intro t
    have h1 := hmin t
    have h2 := (hamp_bd t).trans_lt hN_half
    have htri := norm_sub_norm_le (_root_.RHTower.xi (γ t))
      (_root_.RHTower.finiteThetaAmplitude N (γ t))
    rw [norm_sub_rev] at htri
    linarith
  have hamp_nz : ∀ t : ℝ, _root_.RHTower.finiteThetaAmplitude N (γ t) ≠ 0 := by
    intro t h0
    have h := hamp_lower t
    rw [h0, norm_zero] at h
    linarith
  let gN : ℂ → ℂ := fun z => z ^ r *
    (-_root_.RHTower.finiteThetaFirstMoment N z / _root_.RHTower.finiteThetaAmplitude N z)
  have hgN_cont : Continuous (fun t : ℝ => gN (γ t)) :=
    (hγ_cont.pow r).mul
      (((continuous_neg_finiteThetaFirstMoment N).comp hγ_cont).div
        (((_root_.RHTower.differentiable_finiteThetaAmplitude N).continuous).comp hγ_cont)
        hamp_nz)
  rw [← _root_.RHTower.integral_rectangleBoundary_eq_rectIntegral z₁ z₂ gN hgN_cont,
    dist_eq_norm]
  have hIntN := _root_.RHTower.intervalIntegrable_mul_rectangleBoundaryVelocity z₁ z₂ hgN_cont 0 1
  have hIntXi := _root_.RHTower.intervalIntegrable_mul_rectangleBoundaryVelocity
    z₁ z₂ hxi_logDeriv_cont 0 1
  rw [← intervalIntegral.integral_sub hIntN hIntXi]
  have herr_nn : 0 ≤ err N :=
    mul_nonneg (mul_nonneg _root_.RHTower.thetaCuspIntegerTailConstant_nonneg
      (_root_.RHTower.thetaAmplitudeEnvelope_nonneg 2)) (Real.exp_pos _).le
  have hpt : ∀ t ∈ uIoc (0 : ℝ) 1,
      ‖gN (γ t) * vel t - ((γ t) ^ r * logDeriv _root_.RHTower.xi (γ t)) * vel t‖ ≤
        K_lip * err N := by
    intro t ht
    have htIcc : t ∈ Icc (0 : ℝ) 1 :=
      Ioc_subset_Icc_self (by rwa [uIoc_of_le zero_le_one] at ht)
    have hxi_nz : _root_.RHTower.xi (γ t) ≠ 0 := xi_ne_zero_on_thetaWindowBoundary hn t
    have hpow_le : ‖(γ t) ^ r‖ ≤ M_pow := (hB_pow t htIcc).trans (le_max_right 1 B_pow)
    have hxi_le : ‖_root_.RHTower.xi (γ t)‖ ≤ M_xi :=
      (hB_xi t htIcc).trans (le_max_right 1 B_xi)
    have hdxi_le : ‖deriv _root_.RHTower.xi (γ t)‖ ≤ M_dxi :=
      (hB_dxi t htIcc).trans (le_max_right 1 B_dxi)
    have hvel_le : ‖vel t‖ ≤ L_vel + 1 :=
      (_root_.RHTower.norm_rectangleBoundaryVelocity_le z₁ z₂ t).trans (by linarith)
    -- Bound the difference of logarithmic derivatives `A_N / B_N - A / B`.
    set A_N := -_root_.RHTower.finiteThetaFirstMoment N (γ t)
    set B_N := _root_.RHTower.finiteThetaAmplitude N (γ t)
    set A := deriv _root_.RHTower.xi (γ t)
    set B := _root_.RHTower.xi (γ t)
    have hquot : A_N / B_N - A / B = ((A_N - A) * B + A * (B - B_N)) / (B_N * B) := by
      field_simp [hamp_nz t, hxi_nz]
      ring
    have hdenom_pos : 0 < μ ^ 2 / 2 := by positivity
    have hdenom_le : μ ^ 2 / 2 ≤ ‖B_N * B‖ := by
      rw [norm_mul]
      calc μ ^ 2 / 2 = (μ / 2) * μ := by ring
        _ ≤ ‖B_N‖ * ‖B‖ :=
          mul_le_mul (hamp_lower t) (hmin t) (by positivity) (norm_nonneg _)
    have hnum_le : ‖(A_N - A) * B + A * (B - B_N)‖ ≤ (M_xi + M_dxi + μ) * err N := by
      calc ‖(A_N - A) * B + A * (B - B_N)‖
          ≤ ‖(A_N - A) * B‖ + ‖A * (B - B_N)‖ := norm_add_le _ _
        _ = ‖A_N - A‖ * ‖B‖ + ‖A‖ * ‖B_N - B‖ := by
            rw [norm_mul, norm_mul, norm_sub_rev B B_N]
        _ ≤ err N * M_xi + M_dxi * err N :=
            add_le_add
              (mul_le_mul (hmom_bd t) hxi_le (norm_nonneg _) herr_nn)
              (mul_le_mul hdxi_le (hamp_bd t) (norm_nonneg _) hM_dxi_pos.le)
        _ ≤ (M_xi + M_dxi + μ) * err N := by nlinarith
    have hquot_le : ‖A_N / B_N - logDeriv _root_.RHTower.xi (γ t)‖ ≤
        ((M_xi + M_dxi + μ) / (μ ^ 2 / 2)) * err N := by
      rw [logDeriv_apply, hquot, norm_div]
      calc ‖(A_N - A) * B + A * (B - B_N)‖ / ‖B_N * B‖
          ≤ ((M_xi + M_dxi + μ) * err N) / (μ ^ 2 / 2) := by
            have hBB_pos : 0 < ‖B_N * B‖ := lt_of_lt_of_le hdenom_pos hdenom_le
            rw [div_le_div_iff₀ hBB_pos hdenom_pos]
            nlinarith
        _ = ((M_xi + M_dxi + μ) / (μ ^ 2 / 2)) * err N := by ring
    have halg : gN (γ t) * vel t - ((γ t) ^ r * logDeriv _root_.RHTower.xi (γ t)) * vel t =
        (γ t) ^ r * (A_N / B_N - logDeriv _root_.RHTower.xi (γ t)) * vel t := by
      dsimp [gN]; ring
    rw [halg, norm_mul, norm_mul]
    calc ‖(γ t) ^ r‖ * ‖A_N / B_N - logDeriv _root_.RHTower.xi (γ t)‖ * ‖vel t‖
        ≤ (M_pow * (((M_xi + M_dxi + μ) / (μ ^ 2 / 2)) * err N)) * (L_vel + 1) := by
          refine mul_le_mul ?_ hvel_le (norm_nonneg _) (by positivity)
          exact mul_le_mul hpow_le hquot_le (norm_nonneg _) hM_pow_pos.le
      _ = K_lip * err N := by dsimp [K_lip]; ring
  have hint_le := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  have h10 : |(1 : ℝ) - 0| = 1 := by norm_num
  rw [h10, mul_one] at hint_le
  have hlt_eps : K_lip * err N < ε := by
    calc K_lip * err N < K_lip * (ε / K_lip) := mul_lt_mul_of_pos_left hN_eps hK_lip_pos
      _ = ε := mul_div_cancel₀ ε hK_lip_pos.ne'
  exact hint_le.trans_lt hlt_eps

/-- Eventually in `N`, `integerThetaWindowPowerSum T n N 0` equals `(xiStripWindowTotalOrder T : ℂ)`
literally in `ℂ`, and `integerThetaWindowDegree T n N` equals `xiStripWindowTotalOrder T`. -/
theorem eventually_integerThetaWindowDegree_eq (T : ℝ) {n : ℕ} (hn : thetaWindowScale T ≤ n) :
    ∀ᶠ N : ℕ in atTop,
      integerThetaWindowPowerSum T n N 0 = (_root_.RHTower.xiStripWindowTotalOrder T : ℂ) ∧
        integerThetaWindowDegree T n N = _root_.RHTower.xiStripWindowTotalOrder T := by
  have hsum0 : (∑ w ∈ (_root_.RHTower.stripZeros_finite T).toFinset,
      ((analyticOrderAt _root_.RHTower.xi w).toNat : ℂ) * w ^ 0) =
      (_root_.RHTower.xiStripWindowTotalOrder T : ℂ) := by
    simp [_root_.RHTower.xiStripWindowTotalOrder]
  have htend := tendsto_integerThetaWindowPowerSum T hn 0
  rw [hsum0] at htend
  have hclose := (Metric.tendsto_nhds.mp htend) (1 / 2 : ℝ) (by norm_num)
  filter_upwards [eventually_finiteThetaAmplitude_ne_zero_on_boundary T hn, hclose] with N hnz hdist
  obtain ⟨k, hk⟩ := integerThetaWindowPowerSum_zero_is_int T n N hnz
  rw [hk, dist_eq_norm] at hdist
  have hcast : (k : ℂ) - (_root_.RHTower.xiStripWindowTotalOrder T : ℂ) =
      (((k - (_root_.RHTower.xiStripWindowTotalOrder T : ℤ)) : ℤ) : ℂ) := by push_cast; ring
  rw [hcast, Complex.norm_intCast] at hdist
  have hk_eq : k = (_root_.RHTower.xiStripWindowTotalOrder T : ℤ) := by
    have habs : |(k : ℝ) - (_root_.RHTower.xiStripWindowTotalOrder T : ℝ)| < 1 / 2 := by
      exact_mod_cast hdist
    have hlt1 : (k : ℝ) - (_root_.RHTower.xiStripWindowTotalOrder T : ℝ) < 1 :=
      (abs_lt.mp habs).2.trans (by norm_num)
    have hgt1 : -1 < (k : ℝ) - (_root_.RHTower.xiStripWindowTotalOrder T : ℝ) :=
      (by norm_num : (-1 : ℝ) < -1 / 2).trans (abs_lt.mp habs).1
    have hk_le : k < (_root_.RHTower.xiStripWindowTotalOrder T : ℤ) + 1 := by exact_mod_cast hlt1
    have hk_ge : (_root_.RHTower.xiStripWindowTotalOrder T : ℤ) - 1 < k := by
      have : ((_root_.RHTower.xiStripWindowTotalOrder T : ℤ) - 1 : ℝ) < (k : ℝ) := by
        push_cast; linarith
      exact_mod_cast this
    omega
  have hp0 : integerThetaWindowPowerSum T n N 0 = (_root_.RHTower.xiStripWindowTotalOrder T : ℂ) := by
    rw [hk, hk_eq]
    norm_cast
  refine ⟨hp0, ?_⟩
  unfold integerThetaWindowDegree
  rw [hp0, Complex.natCast_re]
  apply (Nat.floor_eq_iff (by positivity)).mpr
  constructor <;> linarith

/-! ## §5 Continuity of Newton–Girard reconstruction and prefix threshold -/

private lemma tendsto_newtonElem {d : ℕ → ℕ → ℂ} {d₀ : ℕ → ℂ}
    (hd : ∀ j : ℕ, Tendsto (fun N => d N j) atTop (𝓝 (d₀ j))) :
    ∀ k : ℕ, Tendsto (fun N => newtonElem (d N) k) atTop (𝓝 (newtonElem d₀ k)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases k with _ | k
    · simp only [newtonElem, tendsto_const_nhds]
    · simp only [newtonElem]
      refine Tendsto.const_mul _ (tendsto_finset_sum _ fun j hj => ?_)
      have hjk : k - j < k + 1 := by omega
      exact ((ih (k - j) hjk).const_mul ((-1 : ℂ) ^ j)).mul (hd (j + 1))

private lemma tendsto_pairDiffPowerSum (M : ℕ) {s : ℕ → ℕ → ℂ} {s₀ : ℕ → ℂ}
    (hs : ∀ r : ℕ, Tendsto (fun N => s N r) atTop (𝓝 (s₀ r))) (K : ℕ) :
    Tendsto (fun N => pairDiffPowerSum M (s N) K) atTop (𝓝 (pairDiffPowerSum M s₀ K)) := by
  unfold pairDiffPowerSum
  dsimp only
  refine tendsto_finset_sum _ fun r _ => ?_
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

private lemma norm_zhukovskyLoop_le_two (n : ℕ) (u : HTGeometry.UnitCircle) :
    ‖zhukovskyLoop n u‖ ≤ 2 := by
  have h1 := norm_zhukovskyLoop_sub_half_le n u
  have ha := (zhukovskyMajorAxis_lt_half n).le
  have hb := zhukovskyMinorAxis_le_sixth n
  have htri : ‖zhukovskyLoop n u‖ ≤ ‖zhukovskyLoop n u - (1 / 2 : ℂ)‖ + ‖(1 / 2 : ℂ)‖ := by
    simpa using norm_add_le (zhukovskyLoop n u - (1 / 2 : ℂ)) (1 / 2 : ℂ)
  have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  linarith

private lemma norm_eval_newtonPoly_sub_le_on_zhukovsky (K n : ℕ) (d₁ d₂ : ℕ → ℂ)
    (u : HTGeometry.UnitCircle) :
    ‖(newtonPoly K d₁).eval (zhukovskyLoop n u) -
        (newtonPoly K d₂).eval (zhukovskyLoop n u)‖ ≤
      ∑ k ∈ Finset.range (K + 1), ‖newtonElem d₁ k - newtonElem d₂ k‖ * 2 ^ (K - k) := by
  unfold newtonPoly
  rw [Polynomial.eval_finsetSum, Polynomial.eval_finsetSum, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
  have hdiff : (-1 : ℂ) ^ k * newtonElem d₁ k * (zhukovskyLoop n u) ^ (K - k) -
      (-1 : ℂ) ^ k * newtonElem d₂ k * (zhukovskyLoop n u) ^ (K - k) =
      (-1 : ℂ) ^ k * (newtonElem d₁ k - newtonElem d₂ k) *
        (zhukovskyLoop n u) ^ (K - k) := by ring
  rw [hdiff, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (norm_zhukovskyLoop_le_two n u) (K - k))
    (norm_nonneg _)

/-- Exact divisor pair-difference polynomial of `xi` on `stripZeros T`. -/
def exactWindowDifferencePoly (T : ℝ) : Polynomial ℂ :=
  pairDiffPoly (_root_.RHTower.xiStripWindowTotalOrder T)
    (fun r => ∑ w ∈ (_root_.RHTower.stripZeros_finite T).toFinset,
      ((analyticOrderAt _root_.RHTower.xi w).toNat : ℂ) * w ^ r)

theorem exactWindowDifferencePoly_winding (T : ℝ) {n : ℕ} (hn : thetaWindowScale T ≤ n) :
    (∀ u : HTGeometry.UnitCircle,
        (exactWindowDifferencePoly T).eval (zhukovskyLoop n u) ≠ 0) ∧
      _root_.RHTower.windingNumber
        (fun θ => ((exactWindowDifferencePoly T).eval
          (zhukovskyLoop n (HTGeometry.circleExp θ))) ^ 2) 0 (2 * Real.pi) =
        (_root_.RHTower.xiHorizontalCollisionCharge T : ℤ) := by
  set Z := (_root_.RHTower.stripZeros_finite T).toFinset
  set m : ℂ → ℕ := fun w => (analyticOrderAt _root_.RHTower.xi w).toNat
  have hgap_lt := two_div_stage_lt_collisionWindowGap hn
  have hmargin := half_inv_stage_le_windowStripLeftMargin hn
  have hs_pos := zhukovskyStage_pos n
  have hstrip : ∀ w ∈ Z, 1 / (2 * (zhukovskyStage n : ℝ)) ≤ w.re ∧ w.re < 1 := by
    intro w hw
    exact ⟨hmargin.trans (windowStripLeftMargin_le_re hw),
      ((_root_.RHTower.stripZeros_finite T).mem_toFinset.mp hw).1.2.1⟩
  have hre : ∀ z ∈ Z, ∀ w ∈ Z, w.re < z.re →
      1 / (2 * (zhukovskyStage n : ℝ)) < z.re - w.re := by
    intro z hz w hw hlt
    have hgap_re : collisionWindowGap T ≤ |z.re - w.re| :=
      (min_le_left _ _).trans ((min_le_left _ _).trans
        (finiteCoordinateGap_le Z Complex.re hz hw hlt.ne'))
    rw [abs_of_pos (sub_pos.mpr hlt)] at hgap_re
    have hhalf_lt : 1 / (2 * (zhukovskyStage n : ℝ)) < 2 / (zhukovskyStage n : ℝ) := by
      rw [div_lt_div_iff₀ (by positivity) hs_pos]
      linarith
    linarith
  have him : ∀ z ∈ Z, ∀ w ∈ Z, z.im ≠ w.im →
      1 / (zhukovskyStage n : ℝ) < |z.im - w.im| := by
    intro z hz w hw hne
    have hgap_im : collisionWindowGap T ≤ |z.im - w.im| :=
      (min_le_left _ _).trans ((min_le_right _ _).trans
        (finiteCoordinateGap_le Z Complex.im hz hw hne))
    have h1_lt_2 : 1 / (zhukovskyStage n : ℝ) < 2 / (zhukovskyStage n : ℝ) := by
      rw [div_lt_div_iff₀ hs_pos hs_pos]
      linarith
    linarith
  obtain ⟨hQ_nz, hQ_wind⟩ := windingNumber_zhukovsky_pairDiffPoly_sq Z m n hstrip hre him
  refine ⟨hQ_nz, ?_⟩
  change _root_.RHTower.windingNumber
      (fun θ => ((pairDiffPoly (∑ w ∈ Z, m w) (fun r => ∑ w ∈ Z, (m w : ℂ) * w ^ r)).eval
        (zhukovskyLoop n (HTGeometry.circleExp θ))) ^ 2) 0 (2 * Real.pi) = _
  rw [hQ_wind, _root_.RHTower.xiHorizontalCollisionCharge_eq_sum_pairs,
    _root_.RHTower.xiHorizontalCollisionPairs, Finset.sum_filter, Finset.sum_product]
  push_cast
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun w _ => ?_
  by_cases h : z.im = w.im ∧ z ≠ w
  · simp [h, m]
  · simp [h, m]

private lemma eventually_integerThetaDifferencePoly_rouche (T : ℝ) {n : ℕ}
    (hn : thetaWindowScale T ≤ n) :
    ∀ᶠ N : ℕ in atTop,
      integerThetaWindowPowerSum T n N 0 = (_root_.RHTower.xiStripWindowTotalOrder T : ℂ) ∧
      integerThetaWindowDegree T n N = _root_.RHTower.xiStripWindowTotalOrder T ∧
      ∀ u : HTGeometry.UnitCircle,
        ‖(integerThetaDifferencePoly T n N).eval (zhukovskyLoop n u) -
            (exactWindowDifferencePoly T).eval (zhukovskyLoop n u)‖ <
          ‖(exactWindowDifferencePoly T).eval (zhukovskyLoop n u)‖ := by
  have hQ_nz := (exactWindowDifferencePoly_winding T hn).1
  have hU_nonempty : (Set.univ : Set HTGeometry.UnitCircle).Nonempty :=
    ⟨HTGeometry.circleExp 0, Set.mem_univ _⟩
  have hQ_cont : Continuous (fun u : HTGeometry.UnitCircle =>
      ‖(exactWindowDifferencePoly T).eval (zhukovskyLoop n u)‖) :=
    ((exactWindowDifferencePoly T).continuous.comp (zhukovskyLoop n).continuous).norm
  obtain ⟨u₀, _, hu₀⟩ := isCompact_univ.exists_isMinOn hU_nonempty hQ_cont.continuousOn
  set η : ℝ := ‖(exactWindowDifferencePoly T).eval (zhukovskyLoop n u₀)‖
  have hη_pos : 0 < η := norm_pos_iff.mpr (hQ_nz u₀)
  have hη_le : ∀ u : HTGeometry.UnitCircle,
      η ≤ ‖(exactWindowDifferencePoly T).eval (zhukovskyLoop n u)‖ :=
    fun u => isMinOn_iff.mp hu₀ u (Set.mem_univ u)
  set M := _root_.RHTower.xiStripWindowTotalOrder T
  let s₀ : ℕ → ℂ := fun r => ∑ w ∈ (_root_.RHTower.stripZeros_finite T).toFinset,
    ((analyticOrderAt _root_.RHTower.xi w).toNat : ℂ) * w ^ r
  have hd_tendsto : ∀ K : ℕ, Tendsto
      (fun N => pairDiffPowerSum M (integerThetaWindowPowerSum T n N) K) atTop
      (𝓝 (pairDiffPowerSum M s₀ K)) :=
    tendsto_pairDiffPowerSum M (fun r => tendsto_integerThetaWindowPowerSum T hn r)
  have helem_tendsto := tendsto_newtonElem hd_tendsto
  have hsum_tendsto : Tendsto
      (fun N : ℕ => ∑ k ∈ Finset.range (M ^ 2 + 1),
        ‖newtonElem (pairDiffPowerSum M (integerThetaWindowPowerSum T n N)) k -
          newtonElem (pairDiffPowerSum M s₀) k‖ * 2 ^ (M ^ 2 - k))
      atTop (𝓝 0) := by
    have h0 : (0 : ℝ) = ∑ _k ∈ Finset.range (M ^ 2 + 1), (0 : ℝ) := by simp
    rw [h0]
    refine tendsto_finset_sum _ fun k _ => ?_
    have hnorm : Tendsto
        (fun N : ℕ => ‖newtonElem (pairDiffPowerSum M (integerThetaWindowPowerSum T n N)) k -
          newtonElem (pairDiffPowerSum M s₀) k‖) atTop (𝓝 0) := by
      simpa only [sub_self, norm_zero] using
        ((helem_tendsto k).sub tendsto_const_nhds).norm
    simpa only [zero_mul] using hnorm.mul_const (2 ^ (M ^ 2 - k))
  filter_upwards [eventually_integerThetaWindowDegree_eq T hn,
    hsum_tendsto.eventually (gt_mem_nhds hη_pos)] with N hdeg hsum_lt
  refine ⟨hdeg.1, hdeg.2, fun u => ?_⟩
  have hpoly_eq : integerThetaDifferencePoly T n N =
      newtonPoly (M ^ 2) (pairDiffPowerSum M (integerThetaWindowPowerSum T n N)) := by
    unfold integerThetaDifferencePoly pairDiffPoly
    rw [hdeg.2]
  rw [hpoly_eq]
  exact (norm_eval_newtonPoly_sub_le_on_zhukovsky (M ^ 2) n _ _ u).trans_lt
    (hsum_lt.trans_le (hη_le u))

/-- Prefix stabilization threshold `thetaPrefixThreshold T n` above which the integer-theta
difference polynomial enters the Rouché basin of `exactWindowDifferencePoly T` on `zhukovskyLoop n`
(defined as `0` below `thetaWindowScale T`). -/
def thetaPrefixThreshold (T : ℝ) (n : ℕ) : ℕ :=
  if hn : thetaWindowScale T ≤ n then
    (eventually_atTop.mp (eventually_integerThetaDifferencePoly_rouche T hn)).choose
  else
    0

/-! ## §6 Main Fredholm index and winding theorem & unconditional `RiemannHypothesis` corollaries -/

/-- **Main Theorem: Integer-theta Wiener–Hopf Fredholm index & winding number equal horizontal
collision charge.**
For every height `T : ℝ`, every Zhukovsky stage `n ≥ thetaWindowScale T`, and every integer-theta
prefix length `N ≥ thetaPrefixThreshold T n`:
1. `integerThetaWindowPowerSum T n N 0 = (xiStripWindowTotalOrder T : ℂ)` literally in `ℂ`, and
   `integerThetaWindowDegree T n N = xiStripWindowTotalOrder T`;
2. the source-pure Zhukovsky Laurent loop `integerThetaLaurentLoop T n N` is everywhere nonzero on
   `UnitCircle`;
3. its winding number around `0` equals `(xiHorizontalCollisionCharge T : ℤ)`;
4. the Wiener–Hopf operator `integerThetaCollisionOperator T n N` on `L²(ℝ)` is Fredholm and its
   Fredholm index equals `(xiHorizontalCollisionCharge T : ℤ)`. -/
theorem integerThetaCollisionOperator_index_and_winding_eq_charge
    (T : ℝ) {n : ℕ} (hn : thetaWindowScale T ≤ n)
    {N : ℕ} (hN : thetaPrefixThreshold T n ≤ N) :
    integerThetaWindowPowerSum T n N 0 = (_root_.RHTower.xiStripWindowTotalOrder T : ℂ) ∧
    integerThetaWindowDegree T n N = _root_.RHTower.xiStripWindowTotalOrder T ∧
    (∀ u : HTGeometry.UnitCircle, integerThetaLaurentLoop T n N u ≠ 0) ∧
    _root_.RHTower.windingNumber
      (fun θ => integerThetaLaurentLoop T n N (HTGeometry.circleExp θ)) 0 (2 * Real.pi) =
      (_root_.RHTower.xiHorizontalCollisionCharge T : ℤ) ∧
    HTGeometry.circleWinding (integerThetaCollisionSymbol T n N) =
      (_root_.RHTower.xiHorizontalCollisionCharge T : ℤ) ∧
    HTGeometry.fredholmIndex (integerThetaCollisionOperator T n N) =
      (_root_.RHTower.xiHorizontalCollisionCharge T : ℤ) := by
  have hN' : (eventually_atTop.mp (eventually_integerThetaDifferencePoly_rouche T hn)).choose ≤ N := by
    simpa only [thetaPrefixThreshold, dif_pos hn] using hN
  obtain ⟨hp0, hdeg, happrox⟩ :=
    (eventually_atTop.mp (eventually_integerThetaDifferencePoly_rouche T hn)).choose_spec N hN'
  obtain ⟨hQ_nz, hQ_wind⟩ := exactWindowDifferencePoly_winding T hn
  obtain ⟨hL_nz, hL_wind⟩ := windingNumber_zhukovsky_poly_sq_of_approx n
    (integerThetaDifferencePoly T n N) (exactWindowDifferencePoly T) hQ_nz happrox
  have hwind_eq : _root_.RHTower.windingNumber
      (fun θ => integerThetaLaurentLoop T n N (HTGeometry.circleExp θ)) 0 (2 * Real.pi) =
      (_root_.RHTower.xiHorizontalCollisionCharge T : ℤ) := by
    simpa only [integerThetaLaurentLoop_apply, hQ_wind] using hL_wind
  have hsym_wind : HTGeometry.circleWinding (integerThetaCollisionSymbol T n N) =
      (_root_.RHTower.xiHorizontalCollisionCharge T : ℤ) := by
    rw [integerThetaCollisionSymbol, circleWinding_unitNormalizeSymbol_of_ne_zero hL_nz, hwind_eq]
  have hfred_ind : HTGeometry.fredholmIndex (integerThetaCollisionOperator T n N) =
      (_root_.RHTower.xiHorizontalCollisionCharge T : ℤ) := by
    rw [fredholmIndex_integerThetaCollisionOperator_eq_circleWinding, hsym_wind]
  exact ⟨hp0, hdeg, hL_nz, hwind_eq, hsym_wind, hfred_ind⟩

/-- Concise Fredholm index form on any real height window `T : ℝ`. -/
theorem fredholmIndex_integerThetaCollisionOperator_eq_charge
    (T : ℝ) {n : ℕ} (hn : thetaWindowScale T ≤ n)
    {N : ℕ} (hN : thetaPrefixThreshold T n ≤ N) :
    HTGeometry.fredholmIndex (integerThetaCollisionOperator T n N) =
      (_root_.RHTower.xiHorizontalCollisionCharge T : ℤ) :=
  (integerThetaCollisionOperator_index_and_winding_eq_charge T hn hN).2.2.2.2.2

/-- Concise winding number form on any real height window `T : ℝ`. -/
theorem windingNumber_integerThetaLaurentLoop_eq_charge
    (T : ℝ) {n : ℕ} (hn : thetaWindowScale T ≤ n)
    {N : ℕ} (hN : thetaPrefixThreshold T n ≤ N) :
    _root_.RHTower.windingNumber
      (fun θ => integerThetaLaurentLoop T n N (HTGeometry.circleExp θ)) 0 (2 * Real.pi) =
      (_root_.RHTower.xiHorizontalCollisionCharge T : ℤ) :=
  (integerThetaCollisionOperator_index_and_winding_eq_charge T hn hN).2.2.2.1

/-- Natural-height window specialization (`m : ℕ`) of the exact Fredholm index formula. -/
theorem fredholmIndex_integerThetaCollisionOperator_nat_eq_charge
    (m : ℕ) {n : ℕ} (hn : thetaWindowScale (m : ℝ) ≤ n)
    {N : ℕ} (hN : thetaPrefixThreshold (m : ℝ) n ≤ N) :
    HTGeometry.fredholmIndex (integerThetaCollisionOperator (m : ℝ) n N) =
      (_root_.RHTower.xiHorizontalCollisionCharge (m : ℝ) : ℤ) :=
  fredholmIndex_integerThetaCollisionOperator_eq_charge (m : ℝ) hn hN

/-- **Pure source-operator `RiemannHypothesis` equivalence on natural windows.**
`RiemannHypothesis` holds if and only if on every natural-height window `m : ℕ`, for all
sufficiently fine Zhukovsky scales `n` and sufficiently long integer theta prefixes `N`, the
Fredholm index of `integerThetaCollisionOperator (m : ℝ) n N` vanishes. Note that the right-hand
side references *only* `integerThetaCollisionOperator` (defined from finite integer theta prefixes
alone). -/
theorem riemannHypothesis_iff_forall_nat_integerThetaCollisionIndex_eq_zero :
    RiemannHypothesis ↔
      ∀ m : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ N₀ : ℕ, ∀ N ≥ N₀,
        HTGeometry.fredholmIndex (integerThetaCollisionOperator (m : ℝ) n N) = 0 := by
  constructor
  · intro hRH m
    refine ⟨thetaWindowScale (m : ℝ), fun n hn => ⟨thetaPrefixThreshold (m : ℝ) n, fun N hN => ?_⟩⟩
    rw [fredholmIndex_integerThetaCollisionOperator_nat_eq_charge m hn hN,
      _root_.RHTower.riemannHypothesis_iff_forall_horizontalCollisionCharge_eq_zero.mp hRH (m : ℝ)]
    rfl
  · intro h
    apply _root_.RHTower.riemannHypothesis_of_forall_nat_horizontalCollisionCharge_lt_two
    intro m
    obtain ⟨n₀, hn₀⟩ := h m
    set n := max n₀ (thetaWindowScale (m : ℝ))
    obtain ⟨N₀, hN₀⟩ := hn₀ n (le_max_left _ _)
    set N := max N₀ (thetaPrefixThreshold (m : ℝ) n)
    have hzero := hN₀ N (le_max_left _ _)
    rw [fredholmIndex_integerThetaCollisionOperator_nat_eq_charge m
      (le_max_right _ _) (le_max_right _ _)] at hzero
    have hcharge0 : _root_.RHTower.xiHorizontalCollisionCharge (m : ℝ) = 0 := by
      exact_mod_cast hzero
    omega

/-- **Two-unit quantized Fredholm index `RiemannHypothesis` equivalence.** Because off-line zero
pairs come in horizontal reflection pairs (and `integerThetaCollisionOperator` has unconditionally
even index), bounding the Fredholm index strictly below `2` on natural windows suffices for
`RiemannHypothesis`. -/
theorem riemannHypothesis_iff_forall_nat_integerThetaCollisionIndex_lt_two :
    RiemannHypothesis ↔
      ∀ m : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ N₀ : ℕ, ∀ N ≥ N₀,
        HTGeometry.fredholmIndex (integerThetaCollisionOperator (m : ℝ) n N) < 2 := by
  constructor
  · intro hRH m
    obtain ⟨n₀, hn₀⟩ :=
      (riemannHypothesis_iff_forall_nat_integerThetaCollisionIndex_eq_zero.mp hRH) m
    refine ⟨n₀, fun n hn => ?_⟩
    obtain ⟨N₀, hN₀⟩ := hn₀ n hn
    exact ⟨N₀, fun N hN => by rw [hN₀ N hN]; omega⟩
  · intro h
    apply _root_.RHTower.riemannHypothesis_of_forall_nat_horizontalCollisionCharge_lt_two
    intro m
    obtain ⟨n₀, hn₀⟩ := h m
    set n := max n₀ (thetaWindowScale (m : ℝ))
    obtain ⟨N₀, hN₀⟩ := hn₀ n (le_max_left _ _)
    set N := max N₀ (thetaPrefixThreshold (m : ℝ) n)
    have hlt := hN₀ N (le_max_left _ _)
    rw [fredholmIndex_integerThetaCollisionOperator_nat_eq_charge m
      (le_max_right _ _) (le_max_right _ _)] at hlt
    exact_mod_cast hlt

/-- Threshold-specialized `RiemannHypothesis` equivalence across all real windows `T : ℝ`. -/
theorem riemannHypothesis_iff_forall_integerThetaCollisionIndex_eq_zero_at_thresholds :
    RiemannHypothesis ↔
      ∀ T : ℝ, ∀ n ≥ thetaWindowScale T, ∀ N ≥ thetaPrefixThreshold T n,
        HTGeometry.fredholmIndex (integerThetaCollisionOperator T n N) = 0 := by
  constructor
  · intro hRH T n hn N hN
    rw [fredholmIndex_integerThetaCollisionOperator_eq_charge T hn hN,
      _root_.RHTower.riemannHypothesis_iff_forall_horizontalCollisionCharge_eq_zero.mp hRH T]
    rfl
  · intro h
    rw [riemannHypothesis_iff_forall_nat_integerThetaCollisionIndex_eq_zero]
    intro m
    exact ⟨thetaWindowScale (m : ℝ), fun n hn =>
      ⟨thetaPrefixThreshold (m : ℝ) n, fun N hN => h (m : ℝ) n hn N hN⟩⟩

end GaloisForLFunctions.ConjugateDiagonalGeometry

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.norm_finiteThetaFirstMoment_sub_deriv_xi_le_strip
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.isFredholmOp_integerThetaCollisionOperator
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.even_fredholmIndex_integerThetaCollisionOperator
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.integerThetaWindowPowerSum_zero_is_int
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.tendsto_integerThetaWindowPowerSum
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.integerThetaCollisionOperator_index_and_winding_eq_charge
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.riemannHypothesis_iff_forall_nat_integerThetaCollisionIndex_eq_zero
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.riemannHypothesis_iff_forall_nat_integerThetaCollisionIndex_lt_two
