import GaloisForLFunctions.ConjugateDiagonalGeometry.ThetaPrefixCuspAndSectoriality
import GaloisForLFunctions.HTGeometry.SlitPlaneQuotientDiscZeroFree
import GaloisForLFunctions.RHTower.GlobalParityWall

/-!
# Shell-pencil homotopy transition law and explicit Rouché artifact annihilation for theta prefixes

This module establishes the finite-`N` divisor index law, the continuous shell-pencil (`N → N + 1`)
double-wall homotopy transition theorem, and the explicit perforated-rectangle Rouché
artifact-annihilation threshold for `integerThetaLaurentLoop T n N` and
`integerThetaCollisionOperator T n N`:

1. **Exact finite-`N` & shell-pencil Zhukovsky–Wiener–Hopf index formula**:
   Whenever `finiteThetaShellPencil N θ` (`θ ∈ [0, 1]`) avoids the window boundary `∂R_{T,n}`,
   `pencilWindowPowerSum` and `pencilWindowDegree` equal the exact power sums and total multiplicity
   of the enclosed finite zero divisor `pencilEnclosedZeros T n N θ`. Whenever no ordered root
   difference `z - w` lies on the Zhukovsky ellipse `zhukovskyEllipseForm n (z - w) = 1`, the
   Fredholm index of `pencilCollisionOperator T n N θ` equals twice the multiplicity-weighted count
   of ordered pairs strictly inside the ellipse (`≥ 0`), and vanishes identically whenever all
   enclosed zeros lie in the critical-line collar `|Re z - 1 / 2| < 1 / (4 s_n)`.
2. **Shell-pencil double-wall homotopy transition law (`N → N + 1`) and mandatory boundary ingress**:
   Along `θ ∈ [0, 1]`, `fredholmIndex (integerThetaCollisionOperator T n N)` can change from `N` to
   `N + 1` only if at some `θ ∈ [0, 1]` either a zero crosses `∂R_{T,n}` (Wall A) or an enclosed
   ordered root difference hits `zhukovskyEllipseForm n (z - w) = 1` (Wall B). Moreover, because
   `integerThetaWindowDegree T n N ≤ prefixGlobalStripZeroBound N` globally in `(T, n)` while
   `xiStripWindowTotalOrder T` grows unboundedly, boundary zero ingress across `∂R_{T,n}` is
   mandatory whenever `xiStripWindowTotalOrder T > prefixGlobalStripZeroBound N₀`.
3. **Explicit perforated-rectangle Rouché artifact-annihilation threshold and first stabilization
   prefix**:
   Excising disjoint Rouché discs of radius `1 / (8 s_n²)` around `stripZeros T` defines a compact
   perforated rectangle on which `‖xi‖` has strictly positive minimum `perforatedWindowXiMin T n`.
   Above the explicit Gaussian prefix `thetaArtifactAnnihilationPrefix T n`, all spurious finite-`N`
   zeros are expelled from the window, each `xi` zero disc captures exact multiplicity
   `ord_w(xi)` whose internal Rouché splittings have `zhukovskyEllipseForm n > 1` (topologically
   invisible to `zhukovskyLoop n`), and `fredholmIndex (integerThetaCollisionOperator T n N) =
   (xiHorizontalCollisionCharge T : ℤ)` unconditionally.
-/

set_option autoImplicit false

open Complex MeasureTheory Filter Set Metric intervalIntegral Polynomial
open scoped BigOperators Topology Classical Real

noncomputable section

namespace GaloisForLFunctions.ConjugateDiagonalGeometry

/-! ## §1 Shell-pencil contour family and exact finite-`N` Zhukovsky–Wiener–Hopf index formula -/

/-- Source-pure `r`-th power-sum contour integral of `finiteThetaShellPencil N θ` around `R_{T,n}`. -/
def pencilWindowPowerSum (T : ℝ) (n N : ℕ) (θ : ℝ) (r : ℕ) : ℂ :=
  (2 * Real.pi * I)⁻¹ *
    _root_.RHTower.rectIntegral
      (fun z => z ^ r * (-finiteThetaPencilFirstMoment N θ z / finiteThetaShellPencil N θ z))
      (thetaWindowLowerLeft n) (thetaWindowUpperRight T n)

/-- Integer degree extracted from `pencilWindowPowerSum T n N θ 0`. -/
def pencilWindowDegree (T : ℝ) (n N : ℕ) (θ : ℝ) : ℕ :=
  Nat.floor ((pencilWindowPowerSum T n N θ 0).re + 1 / 2)

/-- Newton–Girard pair-difference polynomial of the `(T, n, N, θ)` shell pencil. -/
def pencilDifferencePoly (T : ℝ) (n N : ℕ) (θ : ℝ) : Polynomial ℂ :=
  pairDiffPoly (pencilWindowDegree T n N θ) (pencilWindowPowerSum T n N θ)

/-- Base circle loop obtained by evaluating `pencilDifferencePoly` along `zhukovskyLoop n`. -/
def pencilBaseLoop (T : ℝ) (n N : ℕ) (θ : ℝ) : C(HTGeometry.UnitCircle, ℂ) where
  toFun u := (pencilDifferencePoly T n N θ).eval (zhukovskyLoop n u)
  continuous_toFun :=
    (pencilDifferencePoly T n N θ).continuous.comp (zhukovskyLoop n).continuous

/-- Squared Zhukovsky Laurent loop of the `(T, n, N, θ)` shell pencil. -/
def pencilLaurentLoop (T : ℝ) (n N : ℕ) (θ : ℝ) : C(HTGeometry.UnitCircle, ℂ) :=
  pencilBaseLoop T n N θ ^ 2

@[simp]
theorem pencilLaurentLoop_apply (T : ℝ) (n N : ℕ) (θ : ℝ) (u : HTGeometry.UnitCircle) :
    pencilLaurentLoop T n N θ u =
      ((pencilDifferencePoly T n N θ).eval (zhukovskyLoop n u)) ^ 2 :=
  rfl

/-- Unimodular circle symbol of the `(T, n, N, θ)` shell pencil. -/
def pencilCollisionSymbol (T : ℝ) (n N : ℕ) (θ : ℝ) : C(HTGeometry.UnitCircle, ℂ) :=
  unitNormalizeSymbol (pencilLaurentLoop T n N θ)

/-- Wiener–Hopf operator on `L²(ℝ)` attached to the `(T, n, N, θ)` shell pencil. -/
def pencilCollisionOperator (T : ℝ) (n N : ℕ) (θ : ℝ) :
    HTGeometry.L2Real →L[ℂ] HTGeometry.L2Real :=
  HTGeometry.wienerHopfLift (pencilCollisionSymbol T n N θ)

@[simp]
theorem pencilWindowPowerSum_zero (T : ℝ) (n N r : ℕ) :
    pencilWindowPowerSum T n N 0 r = integerThetaWindowPowerSum T n N r := by
  unfold pencilWindowPowerSum integerThetaWindowPowerSum
  congr 2
  funext z
  simp

@[simp]
theorem pencilWindowPowerSum_one (T : ℝ) (n N r : ℕ) :
    pencilWindowPowerSum T n N 1 r = integerThetaWindowPowerSum T n (N + 1) r := by
  unfold pencilWindowPowerSum integerThetaWindowPowerSum
  congr 2
  funext z
  simp

@[simp]
theorem pencilWindowDegree_zero (T : ℝ) (n N : ℕ) :
    pencilWindowDegree T n N 0 = integerThetaWindowDegree T n N := by
  simp [pencilWindowDegree, integerThetaWindowDegree]

@[simp]
theorem pencilWindowDegree_one (T : ℝ) (n N : ℕ) :
    pencilWindowDegree T n N 1 = integerThetaWindowDegree T n (N + 1) := by
  simp [pencilWindowDegree, integerThetaWindowDegree]

@[simp]
theorem pencilDifferencePoly_zero (T : ℝ) (n N : ℕ) :
    pencilDifferencePoly T n N 0 = integerThetaDifferencePoly T n N := by
  unfold pencilDifferencePoly integerThetaDifferencePoly
  rw [pencilWindowDegree_zero]
  congr 1
  funext r
  exact pencilWindowPowerSum_zero T n N r

@[simp]
theorem pencilDifferencePoly_one (T : ℝ) (n N : ℕ) :
    pencilDifferencePoly T n N 1 = integerThetaDifferencePoly T n (N + 1) := by
  unfold pencilDifferencePoly integerThetaDifferencePoly
  rw [pencilWindowDegree_one]
  congr 1
  funext r
  exact pencilWindowPowerSum_one T n N r

@[simp]
theorem pencilBaseLoop_zero (T : ℝ) (n N : ℕ) :
    pencilBaseLoop T n N 0 = integerThetaBaseLoop T n N := by
  ext u
  change (pencilDifferencePoly T n N 0).eval (zhukovskyLoop n u) =
    (integerThetaDifferencePoly T n N).eval (zhukovskyLoop n u)
  rw [pencilDifferencePoly_zero]

@[simp]
theorem pencilBaseLoop_one (T : ℝ) (n N : ℕ) :
    pencilBaseLoop T n N 1 = integerThetaBaseLoop T n (N + 1) := by
  ext u
  change (pencilDifferencePoly T n N 1).eval (zhukovskyLoop n u) =
    (integerThetaDifferencePoly T n (N + 1)).eval (zhukovskyLoop n u)
  rw [pencilDifferencePoly_one]

@[simp]
theorem pencilLaurentLoop_zero (T : ℝ) (n N : ℕ) :
    pencilLaurentLoop T n N 0 = integerThetaLaurentLoop T n N := by
  unfold pencilLaurentLoop integerThetaLaurentLoop
  rw [pencilBaseLoop_zero]

@[simp]
theorem pencilLaurentLoop_one (T : ℝ) (n N : ℕ) :
    pencilLaurentLoop T n N 1 = integerThetaLaurentLoop T n (N + 1) := by
  unfold pencilLaurentLoop integerThetaLaurentLoop
  rw [pencilBaseLoop_one]

@[simp]
theorem pencilCollisionSymbol_zero (T : ℝ) (n N : ℕ) :
    pencilCollisionSymbol T n N 0 = integerThetaCollisionSymbol T n N := by
  unfold pencilCollisionSymbol integerThetaCollisionSymbol
  rw [pencilLaurentLoop_zero]

@[simp]
theorem pencilCollisionSymbol_one (T : ℝ) (n N : ℕ) :
    pencilCollisionSymbol T n N 1 = integerThetaCollisionSymbol T n (N + 1) := by
  unfold pencilCollisionSymbol integerThetaCollisionSymbol
  rw [pencilLaurentLoop_one]

@[simp]
theorem pencilCollisionOperator_zero (T : ℝ) (n N : ℕ) :
    pencilCollisionOperator T n N 0 = integerThetaCollisionOperator T n N := by
  unfold pencilCollisionOperator integerThetaCollisionOperator
  rw [pencilCollisionSymbol_zero]

@[simp]
theorem pencilCollisionOperator_one (T : ℝ) (n N : ℕ) :
    pencilCollisionOperator T n N 1 = integerThetaCollisionOperator T n (N + 1) := by
  unfold pencilCollisionOperator integerThetaCollisionOperator
  rw [pencilCollisionSymbol_one]

/-- Every point on any of the four boundary edges of `[z₁.re, z₂.re] × [z₁.im, z₂.im]` lies in the
image of `rectangleBoundaryPath z₁ z₂`. -/
private lemma exists_rectangleBoundaryPath_eq_of_mem_boundary {z₁ z₂ z : ℂ}
    (hre : z₁.re ≤ z₂.re) (him : z₁.im ≤ z₂.im)
    (hx : z₁.re ≤ z.re ∧ z.re ≤ z₂.re) (hy : z₁.im ≤ z.im ∧ z.im ≤ z₂.im)
    (hedge : z.re = z₁.re ∨ z.re = z₂.re ∨ z.im = z₁.im ∨ z.im = z₂.im) :
    ∃ t : ℝ, _root_.RHTower.rectangleBoundaryPath z₁ z₂ t = z := by
  by_cases hy1 : z.im = z₁.im
  · rcases eq_or_lt_of_le hre with hxeq | hxlt
    · refine ⟨0, ?_⟩
      rw [_root_.RHTower.rectangleBoundaryPath, Int.fract_zero, _root_.RHTower.rectangleEdgePath_zero]
      exact Complex.ext (by linarith [hx.1, hx.2]) hy1.symm
    · set τ : ℝ := (z.re - z₁.re) / (4 * (z₂.re - z₁.re))
      have hdx : 0 < z₂.re - z₁.re := sub_pos.mpr hxlt
      have hτ0 : 0 ≤ τ := div_nonneg (sub_nonneg.mpr hx.1) (by positivity)
      have hτ4 : τ ≤ 1 / 4 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith [hx.2]
      refine ⟨τ, ?_⟩
      rw [_root_.RHTower.rectangleBoundaryPath, Int.fract_eq_self.mpr ⟨hτ0, by linarith⟩,
        _root_.RHTower.rectangleEdgePath, if_pos hτ4]
      apply Complex.ext
      · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          Complex.ofReal_im, Complex.I_im, mul_zero, sub_zero, add_zero]
        dsimp [τ]; field_simp [hdx.ne']; ring
      · simp [hy1]
  · have hy1_lt : z₁.im < z.im := lt_of_le_of_ne hy.1 (Ne.symm hy1)
    have him_lt : z₁.im < z₂.im := hy1_lt.trans_le hy.2
    have hdy : 0 < z₂.im - z₁.im := sub_pos.mpr him_lt
    by_cases hx2 : z.re = z₂.re
    · set τ : ℝ := 1 / 4 + (z.im - z₁.im) / (4 * (z₂.im - z₁.im))
      have hτ_gt : 1 / 4 < τ := by
        dsimp [τ]
        linarith [div_pos (sub_pos.mpr hy1_lt) (by positivity : 0 < 4 * (z₂.im - z₁.im))]
      have hτ_le : τ ≤ 1 / 2 := by
        dsimp [τ]
        have h1 : (z.im - z₁.im) / (4 * (z₂.im - z₁.im)) ≤ 1 / 4 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith [hy.2]
        linarith
      refine ⟨τ, ?_⟩
      rw [_root_.RHTower.rectangleBoundaryPath, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩,
        _root_.RHTower.rectangleEdgePath, if_neg (not_le.mpr hτ_gt), if_pos hτ_le]
      apply Complex.ext
      · simp [hx2]
      · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
          Complex.ofReal_re, Complex.I_im, mul_one, add_zero, zero_add]
        dsimp [τ]; field_simp [hdy.ne']; ring
    · have hx2_lt : z.re < z₂.re := lt_of_le_of_ne hx.2 hx2
      have hre_lt : z₁.re < z₂.re := hx.1.trans_lt hx2_lt
      have hdx : 0 < z₂.re - z₁.re := sub_pos.mpr hre_lt
      by_cases hy2 : z.im = z₂.im
      · set τ : ℝ := 1 / 2 + (z₂.re - z.re) / (4 * (z₂.re - z₁.re))
        have hτ_gt : 1 / 2 < τ := by
          dsimp [τ]
          linarith [div_pos (sub_pos.mpr hx2_lt) (by positivity : 0 < 4 * (z₂.re - z₁.re))]
        have hτ_le : τ ≤ 3 / 4 := by
          dsimp [τ]
          have h1 : (z₂.re - z.re) / (4 * (z₂.re - z₁.re)) ≤ 1 / 4 := by
            rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith [hx.1]
          linarith
        refine ⟨τ, ?_⟩
        rw [_root_.RHTower.rectangleBoundaryPath, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩,
          _root_.RHTower.rectangleEdgePath, if_neg (by linarith), if_neg (not_le.mpr hτ_gt),
          if_pos hτ_le]
        apply Complex.ext
        · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
            Complex.ofReal_im, Complex.I_im, mul_zero, sub_zero, add_zero]
          dsimp [τ]; field_simp [hdx.ne']; ring
        · simp [hy2]
      · have hy2_lt : z.im < z₂.im := lt_of_le_of_ne hy.2 hy2
        have hx1 : z.re = z₁.re := by
          rcases hedge with h | h | h | h
          · exact h
          · exact absurd h hx2
          · exact absurd h hy1
          · exact absurd h hy2
        set τ : ℝ := 3 / 4 + (z₂.im - z.im) / (4 * (z₂.im - z₁.im))
        have hτ_gt : 3 / 4 < τ := by
          dsimp [τ]
          linarith [div_pos (sub_pos.mpr hy2_lt) (by positivity : 0 < 4 * (z₂.im - z₁.im))]
        have hτ_lt : τ < 1 := by
          dsimp [τ]
          have h1 : (z₂.im - z.im) / (4 * (z₂.im - z₁.im)) < 1 / 4 := by
            rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith [hy1_lt]
          linarith
        refine ⟨τ, ?_⟩
        rw [_root_.RHTower.rectangleBoundaryPath, Int.fract_eq_self.mpr ⟨by linarith, hτ_lt⟩,
          _root_.RHTower.rectangleEdgePath, if_neg (by linarith), if_neg (by linarith),
          if_neg (not_le.mpr hτ_gt)]
        apply Complex.ext
        · simp [hx1]
        · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
            Complex.ofReal_re, Complex.I_im, mul_one, add_zero, zero_add]
          dsimp [τ]; field_simp [hdy.ne']; ring

/-- Finite set of zeros of `finiteThetaShellPencil N θ` (`θ ∈ [0, 1]`) strictly enclosed by the
shifted `(T, n)` window rectangle. -/
def pencilEnclosedZeros (T : ℝ) (n N : ℕ) (θ : ℝ) : Finset ℂ :=
  if hθ : θ ∈ Icc (0 : ℝ) 1 then
    ((finiteThetaShellPencil_zeros_closedBall_finite N hθ 0 (max 0 T + 6)).toFinset).filter
      (fun w => (thetaWindowLowerLeft n).re < w.re ∧ w.re < (thetaWindowUpperRight T n).re ∧
        (thetaWindowLowerLeft n).im < w.im ∧ w.im < (thetaWindowUpperRight T n).im)
  else ∅

/-- Finite set of zeros of `finiteThetaAmplitude N` strictly enclosed by the `(T, n)` window
rectangle. -/
def prefixEnclosedZeros (T : ℝ) (n N : ℕ) : Finset ℂ :=
  pencilEnclosedZeros T n N 0

private lemma closedBall_six_mem_of_window_nhd (T : ℝ) (n : ℕ) {z : ℂ}
    (hx : (thetaWindowLowerLeft n).re - 1 / 2 ≤ z.re ∧
      z.re ≤ (thetaWindowUpperRight T n).re + 1 / 2)
    (hy : (thetaWindowLowerLeft n).im - 1 / 2 ≤ z.im ∧
      z.im ≤ (thetaWindowUpperRight T n).im + 1 / 2) :
    z ∈ Metric.closedBall (0 : ℂ) (max 0 T + 6) := by
  rw [thetaWindowLowerLeft_re, thetaWindowUpperRight_re] at hx
  rw [thetaWindowLowerLeft_im, thetaWindowUpperRight_im] at hy
  have hs6 : (6 : ℝ) ≤ (zhukovskyStage n : ℝ) := six_le_zhukovskyStage_real n
  have hhalf_pos : 0 < 1 / (2 * (zhukovskyStage n : ℝ)) := by positivity
  have hhalf_le : 1 / (2 * (zhukovskyStage n : ℝ)) ≤ 1 / 12 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hre_abs : |z.re| ≤ 2 := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have him_abs : |z.im| ≤ max 0 T + 1 :=
    abs_le.mpr ⟨by linarith [hy.1, le_max_left (0 : ℝ) T], by linarith [hy.2]⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  linarith [Complex.norm_le_abs_re_add_abs_im z]

theorem mem_pencilEnclosedZeros_iff (T : ℝ) (n N : ℕ) {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) (w : ℂ) :
    w ∈ pencilEnclosedZeros T n N θ ↔
      ((thetaWindowLowerLeft n).re < w.re ∧ w.re < (thetaWindowUpperRight T n).re ∧
        (thetaWindowLowerLeft n).im < w.im ∧ w.im < (thetaWindowUpperRight T n).im) ∧
      finiteThetaShellPencil N θ w = 0 := by
  unfold pencilEnclosedZeros
  rw [dif_pos hθ, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_sep_iff]
  constructor
  · rintro ⟨⟨_, hw0⟩, hin⟩
    exact ⟨hin, hw0⟩
  · rintro ⟨hin, hw0⟩
    refine ⟨⟨closedBall_six_mem_of_window_nhd T n
      ⟨by linarith [hin.1], by linarith [hin.2.1]⟩
      ⟨by linarith [hin.2.2.1], by linarith [hin.2.2.2]⟩, hw0⟩, hin⟩

theorem mem_prefixEnclosedZeros_iff (T : ℝ) (n N : ℕ) (w : ℂ) :
    w ∈ prefixEnclosedZeros T n N ↔
      ((thetaWindowLowerLeft n).re < w.re ∧ w.re < (thetaWindowUpperRight T n).re ∧
        (thetaWindowLowerLeft n).im < w.im ∧ w.im < (thetaWindowUpperRight T n).im) ∧
      _root_.RHTower.finiteThetaAmplitude N w = 0 := by
  unfold prefixEnclosedZeros
  rw [mem_pencilEnclosedZeros_iff T n N ⟨le_rfl, zero_le_one⟩, finiteThetaShellPencil_zero]

private def rectInfDist (T : ℝ) (n : ℕ) (w : ℂ) : ℝ :=
  max (max ((thetaWindowLowerLeft n).re - w.re) (w.re - (thetaWindowUpperRight T n).re))
    (max ((thetaWindowLowerLeft n).im - w.im) (w.im - (thetaWindowUpperRight T n).im))

private lemma rectInfDist_pos_of_zero_not_mem (T : ℝ) (n N : ℕ) {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1)
    (hbdry : ∀ t : ℝ, finiteThetaShellPencil N θ
      (_root_.RHTower.rectangleBoundaryPath
        (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t) ≠ 0)
    {w : ℂ} (hw0 : finiteThetaShellPencil N θ w = 0)
    (hnot : w ∉ pencilEnclosedZeros T n N θ) :
    0 < rectInfDist T n w := by
  by_contra hle
  replace hle : rectInfDist T n w ≤ 0 := not_lt.mp hle
  unfold rectInfDist at hle
  have hx1 : (thetaWindowLowerLeft n).re ≤ w.re := by
    linarith [(le_max_left _ _).trans ((le_max_left _ _).trans hle)]
  have hx2 : w.re ≤ (thetaWindowUpperRight T n).re := by
    linarith [(le_max_right _ _).trans ((le_max_left _ _).trans hle)]
  have hy1 : (thetaWindowLowerLeft n).im ≤ w.im := by
    linarith [(le_max_left _ _).trans ((le_max_right _ _).trans hle)]
  have hy2 : w.im ≤ (thetaWindowUpperRight T n).im := by
    linarith [(le_max_right _ _).trans ((le_max_right _ _).trans hle)]
  by_cases hin : (thetaWindowLowerLeft n).re < w.re ∧ w.re < (thetaWindowUpperRight T n).re ∧
      (thetaWindowLowerLeft n).im < w.im ∧ w.im < (thetaWindowUpperRight T n).im
  · exact hnot ((mem_pencilEnclosedZeros_iff T n N hθ w).mpr ⟨hin, hw0⟩)
  · have hedge : w.re = (thetaWindowLowerLeft n).re ∨ w.re = (thetaWindowUpperRight T n).re ∨
        w.im = (thetaWindowLowerLeft n).im ∨ w.im = (thetaWindowUpperRight T n).im := by
      rcases eq_or_lt_of_le hx1 with h | h1
      · exact Or.inl h.symm
      · rcases eq_or_lt_of_le hx2 with h | h2
        · exact Or.inr (Or.inl h)
        · rcases eq_or_lt_of_le hy1 with h | h3
          · exact Or.inr (Or.inr (Or.inl h.symm))
          · rcases eq_or_lt_of_le hy2 with h | h4
            · exact Or.inr (Or.inr (Or.inr h))
            · exact absurd ⟨h1, h2, h3, h4⟩ hin
    obtain ⟨t, ht⟩ := exists_rectangleBoundaryPath_eq_of_mem_boundary
      (thetaWindow_re_le T n) (thetaWindow_im_le T n) ⟨hx1, hx2⟩ ⟨hy1, hy2⟩ hedge
    exact hbdry t (ht.symm ▸ hw0)

/-- **Exact Cauchy power-sum formula for `finiteThetaShellPencil N θ`.**
Whenever `finiteThetaShellPencil N θ` (`θ ∈ [0, 1]`) has no zeros on `∂R_{T,n}`, every contour
moment `pencilWindowPowerSum T n N θ r` equals the exact weighted power sum of its enclosed zeros. -/
theorem pencilWindowPowerSum_eq_sum (T : ℝ) (n N : ℕ) {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1)
    (hbdry : ∀ t : ℝ, finiteThetaShellPencil N θ
      (_root_.RHTower.rectangleBoundaryPath
        (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t) ≠ 0)
    (r : ℕ) :
    pencilWindowPowerSum T n N θ r =
      ∑ w ∈ pencilEnclosedZeros T n N θ,
        ((analyticOrderAt (finiteThetaShellPencil N θ) w).toNat : ℂ) * w ^ r := by
  set Z := pencilEnclosedZeros T n N θ
  set Z_ball := (finiteThetaShellPencil_zeros_closedBall_finite N hθ 0 (max 0 T + 6)).toFinset
  set Z_out := Z_ball \ Z
  set δ : ℝ :=
    if h : Z_out.Nonempty then min (1 / 2) (Z_out.inf' h (rectInfDist T n) / 2) else 1 / 2
  have hδ_pos : 0 < δ := by
    dsimp only [δ]
    split_ifs with h
    · refine lt_min (by norm_num) (half_pos ?_)
      rw [Finset.lt_inf'_iff]
      intro w hw
      obtain ⟨hwB, hwNot⟩ := Finset.mem_sdiff.mp hw
      have hw0 := ((finiteThetaShellPencil_zeros_closedBall_finite N hθ 0
        (max 0 T + 6)).mem_toFinset.mp hwB).2
      exact rectInfDist_pos_of_zero_not_mem T n N hθ hbdry hw0 hwNot
    · norm_num
  have hδ_le : δ ≤ 1 / 2 := by
    dsimp only [δ]
    split_ifs with h
    · exact min_le_left _ _
    · exact le_rfl
  let U : Set ℂ := {z : ℂ |
    (thetaWindowLowerLeft n).re - δ < z.re ∧ z.re < (thetaWindowUpperRight T n).re + δ ∧
    (thetaWindowLowerLeft n).im - δ < z.im ∧ z.im < (thetaWindowUpperRight T n).im + δ}
  have hUopen : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
        ((isOpen_lt continuous_const Complex.continuous_im).inter
          (isOpen_lt Complex.continuous_im continuous_const)))
  have hsub : (uIcc (thetaWindowLowerLeft n).re (thetaWindowUpperRight T n).re ×ℂ
      uIcc (thetaWindowLowerLeft n).im (thetaWindowUpperRight T n).im) ⊆ U := by
    intro z hz
    rw [uIcc_of_le (thetaWindow_re_le T n), uIcc_of_le (thetaWindow_im_le T n),
      Complex.mem_reProdIm] at hz
    exact ⟨by linarith [hz.1.1], by linarith [hz.1.2],
      by linarith [hz.2.1], by linarith [hz.2.2]⟩
  have hin : ∀ w ∈ Z,
      (thetaWindowLowerLeft n).re < w.re ∧ w.re < (thetaWindowUpperRight T n).re ∧
        (thetaWindowLowerLeft n).im < w.im ∧ w.im < (thetaWindowUpperRight T n).im :=
    fun w hw => ((mem_pencilEnclosedZeros_iff T n N hθ w).mp hw).1
  have htU : ∀ w ∈ Z, w ∈ U := by
    intro w hw
    obtain ⟨h1, h2, h3, h4⟩ := hin w hw
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hzeros : ∀ z ∈ U, finiteThetaShellPencil N θ z = 0 → z ∈ Z := by
    intro z hzU hz0
    have hzBall : z ∈ Z_ball := by
      apply (finiteThetaShellPencil_zeros_closedBall_finite N hθ 0 (max 0 T + 6)).mem_toFinset.mpr
      exact ⟨closedBall_six_mem_of_window_nhd T n
        ⟨by linarith [hzU.1, hδ_le], by linarith [hzU.2.1, hδ_le]⟩
        ⟨by linarith [hzU.2.2.1, hδ_le], by linarith [hzU.2.2.2, hδ_le]⟩, hz0⟩
    by_contra hzNot
    have hzOut : z ∈ Z_out := Finset.mem_sdiff.mpr ⟨hzBall, hzNot⟩
    have hinf_le : δ ≤ rectInfDist T n z / 2 := by
      dsimp only [δ]
      rw [dif_pos ⟨z, hzOut⟩]
      exact (min_le_right _ _).trans (div_le_div_of_nonneg_right
        (Finset.inf'_le (rectInfDist T n) hzOut) (by norm_num))
    have hdist_lt : rectInfDist T n z < δ := by
      unfold rectInfDist
      exact max_lt (max_lt (by linarith [hzU.1]) (by linarith [hzU.2.1]))
        (max_lt (by linarith [hzU.2.2.1]) (by linarith [hzU.2.2.2]))
    linarith
  have hF_an : AnalyticOnNhd ℂ (finiteThetaShellPencil N θ) U :=
    fun z _ => analyticOnNhd_finiteThetaShellPencil N θ z (Set.mem_univ z)
  have hord : ∀ w ∈ Z, analyticOrderAt (finiteThetaShellPencil N θ) w ≠ ⊤ :=
    fun w _ => finiteThetaShellPencil_orderAt_ne_top N hθ w
  obtain ⟨m₀, h, hhan, hh0, hfact⟩ :=
    _root_.RHTower.exists_multi_peel hUopen hF_an Z htU hzeros hord
  have hm_eq : ∀ w₀ ∈ Z, m₀ w₀ = (analyticOrderAt (finiteThetaShellPencil N θ) w₀).toNat := by
    intro w₀ hw₀
    let G : ℂ → ℂ := fun z => (∏ w ∈ Z.erase w₀, (z - w) ^ m₀ w) * h z
    have hGan : AnalyticAt ℂ G w₀ := by
      refine AnalyticAt.mul ?_ (hhan w₀ (htU w₀ hw₀))
      have hprod_eq : (fun z => ∏ w ∈ Z.erase w₀, (z - w) ^ m₀ w) =
          ∏ w ∈ Z.erase w₀, fun z => (z - w) ^ m₀ w := by
        funext z; rw [Finset.prod_apply]
      rw [hprod_eq]
      exact Finset.analyticAt_prod (Z.erase w₀)
        (fun w _ => (analyticAt_id.sub analyticAt_const).pow (m₀ w))
    have hG0 : G w₀ ≠ 0 := by
      refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun w hw => ?_) (hh0 w₀ (htU w₀ hw₀))
      exact pow_ne_zero _ (sub_ne_zero.mpr (Finset.ne_of_mem_erase hw).symm)
    have hev : finiteThetaShellPencil N θ =ᶠ[nhds w₀] (fun z => (z - w₀) ^ m₀ w₀) • G := by
      filter_upwards [hUopen.mem_nhds (htU w₀ hw₀)] with z hzU
      change finiteThetaShellPencil N θ z = (z - w₀) ^ m₀ w₀ * G z
      dsimp only [G]
      rw [hfact z hzU, ← Finset.mul_prod_erase Z _ hw₀, mul_assoc]
    have hord_eq : analyticOrderAt (finiteThetaShellPencil N θ) w₀ = (m₀ w₀ : ℕ∞) :=
      (hF_an w₀ (htU w₀ hw₀)).analyticOrderAt_eq_natCast.mpr ⟨G, hGan, hG0, hev⟩
    rw [hord_eq, ENat.toNat_coe]
  have hfact' : ∀ z ∈ U, finiteThetaShellPencil N θ z =
      (∏ w ∈ Z, (z - w) ^ (analyticOrderAt (finiteThetaShellPencil N θ) w).toNat) * h z := by
    intro z hzU
    rw [hfact z hzU]
    congr 1
    exact Finset.prod_congr rfl fun w hw => by rw [hm_eq w hw]
  have hg : AnalyticOnNhd ℂ (fun z : ℂ => z ^ r) Set.univ := fun _ _ => analyticAt_id.pow r
  have hrect := _root_.RHTower.rectIntegral_mul_logDeriv_boxCount
    Z id (fun w => (analyticOrderAt (finiteThetaShellPencil N θ) w).toNat)
    hg hUopen hin hsub hhan hh0 hfact'
  have h2pi_ne : (2 * Real.pi * I : ℂ) ≠ 0 := by
    have : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    simp [this, Complex.I_ne_zero]
  have hfun : (fun z : ℂ => z ^ r *
        (-finiteThetaPencilFirstMoment N θ z / finiteThetaShellPencil N θ z)) =
      fun z : ℂ => z ^ r * logDeriv (finiteThetaShellPencil N θ) z := by
    funext z
    rw [logDeriv_apply, deriv_finiteThetaShellPencil]
  unfold pencilWindowPowerSum
  rw [hfun, hrect, inv_mul_cancel_left₀ h2pi_ne]
  rfl

/-- Exact enclosed multiplicity formula for `pencilWindowDegree` under boundary regularity. -/
theorem pencilWindowDegree_eq_sum (T : ℝ) (n N : ℕ) {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1)
    (hbdry : ∀ t : ℝ, finiteThetaShellPencil N θ
      (_root_.RHTower.rectangleBoundaryPath
        (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t) ≠ 0) :
    pencilWindowPowerSum T n N θ 0 =
        ((∑ w ∈ pencilEnclosedZeros T n N θ,
          (analyticOrderAt (finiteThetaShellPencil N θ) w).toNat : ℕ) : ℂ) ∧
      pencilWindowDegree T n N θ =
        ∑ w ∈ pencilEnclosedZeros T n N θ,
          (analyticOrderAt (finiteThetaShellPencil N θ) w).toNat := by
  have hp0 := pencilWindowPowerSum_eq_sum T n N hθ hbdry 0
  have hp0' : pencilWindowPowerSum T n N θ 0 =
      ((∑ w ∈ pencilEnclosedZeros T n N θ,
        (analyticOrderAt (finiteThetaShellPencil N θ) w).toNat : ℕ) : ℂ) := by
    rw [hp0, Nat.cast_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp
  refine ⟨hp0', ?_⟩
  unfold pencilWindowDegree
  rw [hp0', Complex.natCast_re]
  exact (Nat.floor_eq_iff (by positivity)).mpr ⟨by linarith, by linarith⟩

/-- Pointwise factorization of `pencilDifferencePoly` into enclosed root differences. -/
theorem eval_pencilDifferencePoly_eq_prod (T : ℝ) (n N : ℕ) {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1)
    (hbdry : ∀ t : ℝ, finiteThetaShellPencil N θ
      (_root_.RHTower.rectangleBoundaryPath
        (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t) ≠ 0)
    (x : ℂ) :
    (pencilDifferencePoly T n N θ).eval x =
      ∏ z ∈ pencilEnclosedZeros T n N θ, ∏ w ∈ pencilEnclosedZeros T n N θ,
        (x - (z - w)) ^ ((analyticOrderAt (finiteThetaShellPencil N θ) z).toNat *
          (analyticOrderAt (finiteThetaShellPencil N θ) w).toNat) := by
  unfold pencilDifferencePoly
  exact eval_pairDiffPoly_eq_finset_prod (pencilEnclosedZeros T n N θ) id
    (fun w => (analyticOrderAt (finiteThetaShellPencil N θ) w).toNat)
    (pencilWindowDegree_eq_sum T n N hθ hbdry).2
    (fun r _ _ => pencilWindowPowerSum_eq_sum T n N hθ hbdry r) x

/-- **Exact shell-pencil Zhukovsky–Wiener–Hopf Fredholm index formula.**
Whenever `finiteThetaShellPencil N θ` (`θ ∈ [0, 1]`) avoids `∂R_{T,n}` and no ordered difference of
enclosed zeros lies on `zhukovskyEllipseForm n (z - w) = 1`, `pencilLaurentLoop T n N θ` is
nonvanishing on `UnitCircle` and the Fredholm index of `pencilCollisionOperator T n N θ` is twice
the multiplicity-weighted count of ordered pairs strictly inside the `n`-th Zhukovsky ellipse. -/
theorem fredholmIndex_pencilCollisionOperator_eq_pairSum (T : ℝ) (n N : ℕ) {θ : ℝ}
    (hθ : θ ∈ Icc (0 : ℝ) 1)
    (hbdry : ∀ t : ℝ, finiteThetaShellPencil N θ
      (_root_.RHTower.rectangleBoundaryPath
        (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t) ≠ 0)
    (hellipse : ∀ z ∈ pencilEnclosedZeros T n N θ, ∀ w ∈ pencilEnclosedZeros T n N θ,
      zhukovskyEllipseForm n (z - w) ≠ 1) :
    let Z := pencilEnclosedZeros T n N θ
    let m : ℂ → ℕ := fun w => (analyticOrderAt (finiteThetaShellPencil N θ) w).toNat
    (∀ u : HTGeometry.UnitCircle, pencilLaurentLoop T n N θ u ≠ 0) ∧
      HTGeometry.fredholmIndex (pencilCollisionOperator T n N θ) =
        2 * ∑ z ∈ Z, ∑ w ∈ Z,
          (m z : ℤ) * (m w : ℤ) * (if zhukovskyEllipseForm n (z - w) < 1 then 1 else 0) ∧
      0 ≤ HTGeometry.fredholmIndex (pencilCollisionOperator T n N θ) := by
  intro Z m
  set P := pencilDifferencePoly T n N θ
  have heval : ∀ x : ℂ, P.eval x = ∏ z ∈ Z, ∏ w ∈ Z, (x - (z - w)) ^ (m z * m w) :=
    eval_pencilDifferencePoly_eq_prod T n N hθ hbdry
  have hP_nz : ∀ u : HTGeometry.UnitCircle, P.eval (zhukovskyLoop n u) ≠ 0 := by
    intro u
    rw [heval]
    refine Finset.prod_ne_zero_iff.mpr fun z hz => Finset.prod_ne_zero_iff.mpr fun w hw => ?_
    exact pow_ne_zero _ (zhukovskyLoop_sub_ne_zero (hellipse z hz w hw) u)
  have hL_nz : ∀ u : HTGeometry.UnitCircle, pencilLaurentLoop T n N θ u ≠ 0 :=
    fun u => pow_ne_zero 2 (hP_nz u)
  have hP_loop : _root_.RHTower.IsLoop
      (fun φ => P.eval (zhukovskyLoop n (HTGeometry.circleExp φ))) 0 (2 * Real.pi) :=
    ⟨(P.continuous.comp (zhukovskyLoop n).continuous).comp HTGeometry.continuous_circleExp,
      fun _ => hP_nz _,
      by rw [← HTGeometry.circleExp_add_two_pi 0, zero_add]⟩
  have hinner_loop : ∀ z ∈ Z, ∀ w ∈ Z,
      _root_.RHTower.IsLoop
        (fun φ => (zhukovskyLoop n (HTGeometry.circleExp φ) - (z - w)) ^ (m z * m w))
        0 (2 * Real.pi) := by
    intro z hz w hw
    have hl := isLoop_zhukovsky_sub (hellipse z hz w hw)
    exact ⟨hl.continuous.pow _, fun φ => pow_ne_zero _ (hl.nonzero φ), by simp only [hl.closed]⟩
  have houter_loop : ∀ z ∈ Z,
      _root_.RHTower.IsLoop
        (fun φ => ∏ w ∈ Z, (zhukovskyLoop n (HTGeometry.circleExp φ) - (z - w)) ^ (m z * m w))
        0 (2 * Real.pi) := by
    intro z hz
    refine ⟨continuous_finsetProd Z (fun w hw => (hinner_loop z hz w hw).continuous),
      fun φ => Finset.prod_ne_zero_iff.mpr (fun w hw => (hinner_loop z hz w hw).nonzero φ),
      Finset.prod_congr rfl (fun w hw => (hinner_loop z hz w hw).closed)⟩
  have hwind : _root_.RHTower.windingNumber
      (fun φ => pencilLaurentLoop T n N θ (HTGeometry.circleExp φ)) 0 (2 * Real.pi) =
      2 * ∑ z ∈ Z, ∑ w ∈ Z,
        (m z : ℤ) * (m w : ℤ) * (if zhukovskyEllipseForm n (z - w) < 1 then 1 else 0) := by
    change _root_.RHTower.windingNumber
      (fun φ => (P.eval (zhukovskyLoop n (HTGeometry.circleExp φ))) ^ 2) 0 (2 * Real.pi) = _
    rw [_root_.RHTower.windingNumber_pow hP_loop 2]
    congr 1
    have hfun : (fun φ => P.eval (zhukovskyLoop n (HTGeometry.circleExp φ))) =
        fun φ => ∏ z ∈ Z, ∏ w ∈ Z,
          (zhukovskyLoop n (HTGeometry.circleExp φ) - (z - w)) ^ (m z * m w) := by
      funext φ; exact heval _
    rw [hfun, _root_.RHTower.windingNumber_prod Z _ houter_loop]
    refine Finset.sum_congr rfl fun z hz => ?_
    rw [_root_.RHTower.windingNumber_prod Z _ (hinner_loop z hz)]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [_root_.RHTower.windingNumber_pow (isLoop_zhukovsky_sub (hellipse z hz w hw)) (m z * m w)]
    by_cases hlt : zhukovskyEllipseForm n (z - w) < 1
    · rw [if_pos hlt, windingNumber_zhukovsky_of_lt_one hlt]
      push_cast; ring
    · have hgt : 1 < zhukovskyEllipseForm n (z - w) :=
        lt_of_le_of_ne (not_lt.mp hlt) (hellipse z hz w hw).symm
      rw [if_neg hlt, windingNumber_zhukovsky_of_gt_one hgt]
      simp
  have hind : HTGeometry.fredholmIndex (pencilCollisionOperator T n N θ) =
      2 * ∑ z ∈ Z, ∑ w ∈ Z,
        (m z : ℤ) * (m w : ℤ) * (if zhukovskyEllipseForm n (z - w) < 1 then 1 else 0) := by
    unfold pencilCollisionOperator pencilCollisionSymbol
    rw [fredholmIndex_wienerHopfLift_unitNormalizeSymbol,
      circleWinding_unitNormalizeSymbol_of_ne_zero hL_nz, hwind]
  have hnn : 0 ≤ HTGeometry.fredholmIndex (pencilCollisionOperator T n N θ) := by
    rw [hind]
    refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun z _ => Finset.sum_nonneg fun w _ => ?_)
    refine mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) ?_
    split_ifs <;> norm_num
  exact ⟨hL_nz, hind, hnn⟩

/-- **Exact finite-`N` integer-theta Zhukovsky–Wiener–Hopf index formula.**
Specialization of `fredholmIndex_pencilCollisionOperator_eq_pairSum` at `θ = 0`. -/
theorem fredholmIndex_integerThetaCollisionOperator_eq_pairSum (T : ℝ) (n N : ℕ)
    (hbdry : ∀ t : ℝ, _root_.RHTower.finiteThetaAmplitude N
      (_root_.RHTower.rectangleBoundaryPath
        (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t) ≠ 0)
    (hellipse : ∀ z ∈ prefixEnclosedZeros T n N, ∀ w ∈ prefixEnclosedZeros T n N,
      zhukovskyEllipseForm n (z - w) ≠ 1) :
    let Z := prefixEnclosedZeros T n N
    let m : ℂ → ℕ := fun w => (analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) w).toNat
    (∀ u : HTGeometry.UnitCircle, integerThetaLaurentLoop T n N u ≠ 0) ∧
      HTGeometry.fredholmIndex (integerThetaCollisionOperator T n N) =
        2 * ∑ z ∈ Z, ∑ w ∈ Z,
          (m z : ℤ) * (m w : ℤ) * (if zhukovskyEllipseForm n (z - w) < 1 then 1 else 0) ∧
      0 ≤ HTGeometry.fredholmIndex (integerThetaCollisionOperator T n N) := by
  have hbdry0 : ∀ t : ℝ, finiteThetaShellPencil N 0
      (_root_.RHTower.rectangleBoundaryPath
        (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t) ≠ 0 := by
    simpa only [finiteThetaShellPencil_zero] using hbdry
  have hm_eq : (fun w => (analyticOrderAt (finiteThetaShellPencil N 0) w).toNat) =
      fun w => (analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) w).toNat := by
    have hfun : finiteThetaShellPencil N 0 = _root_.RHTower.finiteThetaAmplitude N :=
      funext (finiteThetaShellPencil_zero N)
    rw [hfun]
  have hmain := fredholmIndex_pencilCollisionOperator_eq_pairSum T n N ⟨le_rfl, zero_le_one⟩
    hbdry0 hellipse
  simpa only [pencilLaurentLoop_zero, pencilCollisionOperator_zero, hm_eq] using hmain

/-- **Critical-line collar zero-index theorem.**
Whenever `finiteThetaAmplitude N` avoids `∂R_{T,n}` and every enclosed zero lies in the collar
`|z.re - 1 / 2| < 1 / (4 s_n)` (allowing arbitrary critical-line multiplicities),
`integerThetaLaurentLoop T n N` is nonvanishing on `UnitCircle` and
`fredholmIndex (integerThetaCollisionOperator T n N) = 0`. -/
theorem fredholmIndex_integerThetaCollisionOperator_eq_zero_of_collar (T : ℝ) (n N : ℕ)
    (hbdry : ∀ t : ℝ, _root_.RHTower.finiteThetaAmplitude N
      (_root_.RHTower.rectangleBoundaryPath
        (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t) ≠ 0)
    (hcollar : ∀ z ∈ prefixEnclosedZeros T n N,
      |z.re - 1 / 2| < 1 / (4 * (zhukovskyStage n : ℝ))) :
    (∀ u : HTGeometry.UnitCircle, integerThetaLaurentLoop T n N u ≠ 0) ∧
      HTGeometry.fredholmIndex (integerThetaCollisionOperator T n N) = 0 := by
  have hgt : ∀ z ∈ prefixEnclosedZeros T n N, ∀ w ∈ prefixEnclosedZeros T n N,
      1 < zhukovskyEllipseForm n (z - w) := by
    intro z hz w hw
    have hz_c := abs_lt.mp (hcollar z hz)
    have hw_c := abs_lt.mp (hcollar w hw)
    have hdiff_re : (z - w).re - 1 / 2 < -zhukovskyMajorAxis n := by
      rw [Complex.sub_re, zhukovskyMajorAxis]
      linarith
    have ha_pos := zhukovskyMajorAxis_pos n
    have hsq : zhukovskyMajorAxis n ^ 2 < ((z - w).re - 1 / 2) ^ 2 := by nlinarith
    unfold zhukovskyEllipseForm
    have hdiv : 1 < ((z - w).re - 1 / 2) ^ 2 / zhukovskyMajorAxis n ^ 2 :=
      (one_lt_div (sq_pos_of_pos ha_pos)).mpr hsq
    have him_nn : 0 ≤ (z - w).im ^ 2 / zhukovskyMinorAxis n ^ 2 := by positivity
    linarith
  obtain ⟨hnz, hind, _⟩ := fredholmIndex_integerThetaCollisionOperator_eq_pairSum T n N hbdry
    (fun z hz w hw => (hgt z hz w hw).ne')
  refine ⟨hnz, ?_⟩
  rw [hind]
  have hsum0 : (∑ z ∈ prefixEnclosedZeros T n N, ∑ w ∈ prefixEnclosedZeros T n N,
      ((analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) z).toNat : ℤ) *
        ((analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) w).toNat : ℤ) *
        (if zhukovskyEllipseForm n (z - w) < 1 then 1 else 0)) = 0 := by
    refine Finset.sum_eq_zero fun z hz => Finset.sum_eq_zero fun w hw => ?_
    rw [if_neg (not_lt.mpr (hgt z hz w hw).le), mul_zero]
  rw [hsum0, mul_zero]

/-- Critical-line specialization: if all enclosed zeros of `finiteThetaAmplitude N` lie on
`Re z = 1 / 2`, then `fredholmIndex (integerThetaCollisionOperator T n N) = 0`. -/
theorem fredholmIndex_integerThetaCollisionOperator_eq_zero_of_criticalLine (T : ℝ) (n N : ℕ)
    (hbdry : ∀ t : ℝ, _root_.RHTower.finiteThetaAmplitude N
      (_root_.RHTower.rectangleBoundaryPath
        (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t) ≠ 0)
    (hcrit : ∀ z ∈ prefixEnclosedZeros T n N, z.re = 1 / 2) :
    (∀ u : HTGeometry.UnitCircle, integerThetaLaurentLoop T n N u ≠ 0) ∧
      HTGeometry.fredholmIndex (integerThetaCollisionOperator T n N) = 0 := by
  refine fredholmIndex_integerThetaCollisionOperator_eq_zero_of_collar T n N hbdry fun z hz => ?_
  rw [hcrit z hz, sub_self, abs_zero]
  have hs := zhukovskyStage_pos n
  positivity

/-- Finite set of all zeros of `finiteThetaAmplitude N` across the infinite strip
`{|Re z - 1 / 2| ≤ 1}` (`[-1 / 2, 3 / 2] × ℝ`). -/
def prefixGlobalStripZeroSet (N : ℕ) : Finset ℂ :=
  (finiteThetaAmplitude_strip_zeros_finite N 1).toFinset

/-- Global height-independent multiplicity ceiling of `finiteThetaAmplitude N` across all `(T, n)`. -/
def prefixGlobalStripZeroBound (N : ℕ) : ℕ :=
  ∑ w ∈ prefixGlobalStripZeroSet N,
    (analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) w).toNat

/-- Uniform height-independent bound on `integerThetaWindowDegree T n N` for every boundary-regular
window `(T, n)`. -/
theorem integerThetaWindowDegree_le_globalStripZeroBound (T : ℝ) (n N : ℕ)
    (hbdry : ∀ t : ℝ, _root_.RHTower.finiteThetaAmplitude N
      (_root_.RHTower.rectangleBoundaryPath
        (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t) ≠ 0) :
    integerThetaWindowDegree T n N ≤ prefixGlobalStripZeroBound N := by
  have hbdry0 : ∀ t : ℝ, finiteThetaShellPencil N 0
      (_root_.RHTower.rectangleBoundaryPath
        (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t) ≠ 0 := by
    simpa only [finiteThetaShellPencil_zero] using hbdry
  have hdeg := (pencilWindowDegree_eq_sum T n N ⟨le_rfl, zero_le_one⟩ hbdry0).2
  rw [pencilWindowDegree_zero] at hdeg
  have hfun : finiteThetaShellPencil N 0 = _root_.RHTower.finiteThetaAmplitude N :=
    funext (finiteThetaShellPencil_zero N)
  rw [hfun] at hdeg
  rw [hdeg]
  refine Finset.sum_le_sum_of_subset fun w hw => ?_
  obtain ⟨hin, hw0⟩ := (mem_prefixEnclosedZeros_iff T n N w).mp hw
  rw [thetaWindowLowerLeft_re, thetaWindowUpperRight_re] at hin
  exact (finiteThetaAmplitude_strip_zeros_finite N 1).mem_toFinset.mpr
    ⟨abs_le.mpr ⟨by linarith [hin.1], by linarith [hin.2.1]⟩, hw0⟩


/-! ## §2 Shell-pencil double-wall homotopy transition law and mandatory boundary ingress -/

private def clamp01 (σ : ℝ) : ℝ := max 0 (min 1 σ)

private lemma continuous_clamp01 : Continuous clamp01 :=
  continuous_const.max (continuous_const.min continuous_id)

private lemma clamp01_mem_Icc (σ : ℝ) : clamp01 σ ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left 0 _, max_le (by norm_num) (min_le_left 1 σ)⟩

private lemma clamp01_eq_self {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) : clamp01 θ = θ := by
  unfold clamp01
  rw [min_eq_right hθ.2, max_eq_right hθ.1]

private lemma clamp01_zero : clamp01 0 = 0 := clamp01_eq_self ⟨le_rfl, zero_le_one⟩

private lemma clamp01_one : clamp01 1 = 1 := clamp01_eq_self ⟨zero_le_one, le_rfl⟩

/-- Dominated-convergence continuity of `σ ↦ pencilWindowPowerSum T n N (clamp01 σ) r` along a
boundary-regular shell pencil. -/
private lemma continuous_pencilWindowPowerSum_clamp (T : ℝ) (n N : ℕ)
    (hbdry : ∀ θ ∈ Icc (0 : ℝ) 1, ∀ t : ℝ,
      finiteThetaShellPencil N θ
        (_root_.RHTower.rectangleBoundaryPath
          (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t) ≠ 0)
    (r : ℕ) :
    Continuous (fun σ : ℝ => pencilWindowPowerSum T n N (clamp01 σ) r) := by
  set z₁ := thetaWindowLowerLeft n
  set z₂ := thetaWindowUpperRight T n
  set γ := _root_.RHTower.rectangleBoundaryPath z₁ z₂
  set vel := _root_.RHTower.rectangleBoundaryVelocity z₁ z₂
  have hγ : Continuous γ := _root_.RHTower.continuous_rectangleBoundaryPath z₁ z₂
  have hmap : Continuous (fun p : ℝ × ℝ => (clamp01 p.1, γ p.2)) :=
    (continuous_clamp01.comp continuous_fst).prodMk (hγ.comp continuous_snd)
  let Q : ℝ × ℝ → ℂ := fun p =>
    (γ p.2) ^ r *
      (-finiteThetaPencilFirstMoment N (clamp01 p.1) (γ p.2) /
        finiteThetaShellPencil N (clamp01 p.1) (γ p.2))
  have hQc : Continuous Q :=
    ((hγ.comp continuous_snd).pow r).mul
      (((continuous_neg_finiteThetaPencilFirstMoment_uncurry N).comp hmap).div
        ((continuous_finiteThetaShellPencil_uncurry N).comp hmap)
        (fun p => hbdry (clamp01 p.1) (clamp01_mem_Icc p.1) p.2))
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hQc.continuousOn
  have hB0 : 0 ≤ B :=
    (norm_nonneg (Q (0, 0))).trans (hB (0, 0) ⟨⟨le_rfl, zero_le_one⟩, ⟨le_rfl, zero_le_one⟩⟩)
  set V : ℝ := 4 * (|z₂.re - z₁.re| + |z₂.im - z₁.im|)
  have hmeas : ∀ σ : ℝ, AEStronglyMeasurable (fun t : ℝ => Q (σ, t) * vel t)
      (volume.restrict (Ioc (0 : ℝ) 1)) := fun σ =>
    (_root_.RHTower.intervalIntegrable_mul_rectangleBoundaryVelocity z₁ z₂
      (hQc.comp (continuous_const.prodMk continuous_id)) 0 1).1.aestronglyMeasurable
  have hbound : ∀ σ : ℝ, ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) 1)),
      ‖Q (σ, t) * vel t‖ ≤ B * V := by
    intro σ
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hQeq : Q (σ, t) = Q (clamp01 σ, t) := by
      dsimp only [Q]
      rw [clamp01_eq_self (clamp01_mem_Icc σ)]
    have hQle : ‖Q (σ, t)‖ ≤ B := by
      rw [hQeq]
      exact hB (clamp01 σ, t) ⟨clamp01_mem_Icc σ, Ioc_subset_Icc_self ht⟩
    rw [norm_mul]
    exact mul_le_mul hQle (_root_.RHTower.norm_rectangleBoundaryVelocity_le z₁ z₂ t)
      (norm_nonneg _) hB0
  have hbint : Integrable (fun _ : ℝ => B * V) (volume.restrict (Ioc (0 : ℝ) 1)) :=
    ((continuousOn_const : ContinuousOn (fun _ : ℝ => B * V) (Icc 0 1)).integrableOn_compact
      isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hcont : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) 1)),
      Continuous (fun σ : ℝ => Q (σ, t) * vel t) :=
    Eventually.of_forall fun t =>
      (hQc.comp (continuous_id.prodMk continuous_const)).mul continuous_const
  have hint_cont : Continuous (fun σ : ℝ => ∫ t in Ioc (0 : ℝ) 1, Q (σ, t) * vel t) :=
    MeasureTheory.continuous_of_dominated hmeas hbound hbint hcont
  have hrew : (fun σ : ℝ => pencilWindowPowerSum T n N (clamp01 σ) r) =
      fun σ : ℝ => (2 * Real.pi * I)⁻¹ * ∫ t in Ioc (0 : ℝ) 1, Q (σ, t) * vel t := by
    funext σ
    unfold pencilWindowPowerSum
    congr 1
    let gσ : ℂ → ℂ := fun z => z ^ r *
      (-finiteThetaPencilFirstMoment N (clamp01 σ) z /
        finiteThetaShellPencil N (clamp01 σ) z)
    have hgσ : Continuous (fun t : ℝ => gσ (γ t)) :=
      hQc.comp (continuous_const.prodMk continuous_id)
    rw [← _root_.RHTower.integral_rectangleBoundary_eq_rectIntegral z₁ z₂ gσ hgσ,
      intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1)]
  rw [hrew]
  exact continuous_const.mul hint_cont

/-- Along any boundary-regular shell pencil on `[0, 1]`, the integer window degree is locally
constant and therefore identically equal to `integerThetaWindowDegree T n N`. -/
private lemma pencilWindowDegree_clamp_eq (T : ℝ) (n N : ℕ)
    (hbdry : ∀ θ ∈ Icc (0 : ℝ) 1, ∀ t : ℝ,
      finiteThetaShellPencil N θ
        (_root_.RHTower.rectangleBoundaryPath
          (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t) ≠ 0)
    (σ : ℝ) :
    pencilWindowDegree T n N (clamp01 σ) = integerThetaWindowDegree T n N := by
  let d : ℝ → ℕ := fun τ => pencilWindowDegree T n N (clamp01 τ)
  have hp_eq : ∀ τ : ℝ, pencilWindowPowerSum T n N (clamp01 τ) 0 = (d τ : ℂ) := by
    intro τ
    obtain ⟨hp, hd⟩ := pencilWindowDegree_eq_sum T n N (clamp01_mem_Icc τ)
      (hbdry (clamp01 τ) (clamp01_mem_Icc τ))
    dsimp only [d]
    rw [hp, hd]
  have hloc : IsLocallyConstant d := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro τ₀
    have hc := (continuous_pencilWindowPowerSum_clamp T n N hbdry 0).tendsto τ₀
    filter_upwards [hc.eventually (Metric.ball_mem_nhds _ (by norm_num : (0 : ℝ) < 1 / 2))]
      with τ hτ
    rw [Metric.mem_ball, dist_eq_norm, hp_eq τ, hp_eq τ₀] at hτ
    have hcast : (d τ : ℂ) - (d τ₀ : ℂ) = (((d τ : ℤ) - (d τ₀ : ℤ) : ℤ) : ℂ) := by
      push_cast; ring
    rw [hcast, Complex.norm_intCast] at hτ
    have habs : |((d τ : ℤ) : ℝ) - ((d τ₀ : ℤ) : ℝ)| < 1 / 2 := by exact_mod_cast hτ
    obtain ⟨h1, h2⟩ := abs_lt.mp habs
    have hlt : (((d τ : ℤ) - (d τ₀ : ℤ) : ℤ) : ℝ) < 1 := by push_cast; linarith
    have hgt : (-1 : ℝ) < (((d τ : ℤ) - (d τ₀ : ℤ) : ℤ) : ℝ) := by push_cast; linarith
    have hlt' : (d τ : ℤ) - (d τ₀ : ℤ) < 1 := by exact_mod_cast hlt
    have hgt' : -1 < (d τ : ℤ) - (d τ₀ : ℤ) := by exact_mod_cast hgt
    omega
  have heq := hloc.apply_eq_of_preconnectedSpace σ 0
  dsimp only [d] at heq
  rwa [clamp01_zero, pencilWindowDegree_zero] at heq

/-- If `finiteThetaShellPencil N θ` avoids `∂R_{T,n}` across `θ ∈ [0, 1]`, the enclosed window
degree is constant across `θ ∈ [0, 1]` and satisfies
`integerThetaWindowDegree T n (N + 1) = integerThetaWindowDegree T n N`. -/
theorem integerThetaWindowDegree_succ_eq_of_boundary_ne_zero (T : ℝ) (n N : ℕ)
    (hbdry : ∀ θ ∈ Icc (0 : ℝ) 1, ∀ t : ℝ,
      finiteThetaShellPencil N θ
        (_root_.RHTower.rectangleBoundaryPath
          (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t) ≠ 0) :
    (∀ θ ∈ Icc (0 : ℝ) 1, pencilWindowDegree T n N θ = integerThetaWindowDegree T n N) ∧
      integerThetaWindowDegree T n (N + 1) = integerThetaWindowDegree T n N := by
  have hall : ∀ θ ∈ Icc (0 : ℝ) 1, pencilWindowDegree T n N θ = integerThetaWindowDegree T n N := by
    intro θ hθ
    rw [← clamp01_eq_self hθ]
    exact pencilWindowDegree_clamp_eq T n N hbdry θ
  refine ⟨hall, ?_⟩
  have h1 := hall 1 ⟨zero_le_one, le_rfl⟩
  rwa [pencilWindowDegree_one] at h1

private lemma continuous_newtonElem_param {X : Type*} [TopologicalSpace X] {d : X → ℕ → ℂ}
    (hd : ∀ j : ℕ, Continuous (fun x => d x j)) :
    ∀ k : ℕ, Continuous (fun x => newtonElem (d x) k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases k with _ | k
    · simp only [newtonElem]
      exact continuous_const
    · simp only [newtonElem]
      refine continuous_const.mul (continuous_finsetSum _ fun j _ => ?_)
      have hjk : k - j < k + 1 := by omega
      exact (continuous_const.mul (ih (k - j) hjk)).mul (hd (j + 1))

private lemma continuous_pairDiffPowerSum_param {X : Type*} [TopologicalSpace X] (M : ℕ)
    {s : X → ℕ → ℂ} (hs : ∀ r : ℕ, Continuous (fun x => s x r)) (K : ℕ) :
    Continuous (fun x => pairDiffPowerSum M (s x) K) := by
  unfold pairDiffPowerSum
  dsimp only
  refine continuous_finsetSum _ fun r _ => ?_
  have h1 : Continuous (fun x => if r = 0 then (M : ℂ) else s x r) := by
    by_cases hr : r = 0
    · simp only [hr, ite_true]; exact continuous_const
    · simp only [hr, ite_false]; exact hs r
  have h2 : Continuous (fun x => if K - r = 0 then (M : ℂ) else s x (K - r)) := by
    by_cases hKr : K - r = 0
    · simp only [hKr, ite_true]; exact continuous_const
    · simp only [hKr, ite_false]; exact hs (K - r)
  exact (continuous_const.mul h1).mul h2

private lemma continuous_eval_pairDiffPoly_param {X : Type*} [TopologicalSpace X] (M : ℕ)
    {s : X → ℕ → ℂ} (hs : ∀ r : ℕ, Continuous (fun x => s x r))
    {w : X → ℂ} (hw : Continuous w) :
    Continuous (fun x => (pairDiffPoly M (s x)).eval (w x)) := by
  have heval : (fun x => (pairDiffPoly M (s x)).eval (w x)) =
      fun x => ∑ k ∈ Finset.range (M ^ 2 + 1),
        (-1 : ℂ) ^ k * newtonElem (pairDiffPowerSum M (s x)) k * (w x) ^ (M ^ 2 - k) := by
    funext x
    unfold pairDiffPoly newtonPoly
    rw [Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp
  rw [heval]
  refine continuous_finsetSum _ fun k _ => ?_
  exact (continuous_const.mul
    (continuous_newtonElem_param (continuous_pairDiffPowerSum_param M hs) k)).mul
    (hw.pow (M ^ 2 - k))

/-- **Shell-pencil homotopy invariance (`N → N + 1`).**
If across `θ ∈ [0, 1]` the linear shell pencil `finiteThetaShellPencil N θ` avoids `∂R_{T,n}` and
no ordered difference of enclosed zeros lies on `zhukovskyEllipseForm n (z - w) = 1`, then
`integerThetaCollisionOperator T n N` and `integerThetaCollisionOperator T n (N + 1)` have the
exact same Fredholm index. -/
theorem fredholmIndex_integerThetaCollisionOperator_succ_eq (T : ℝ) (n N : ℕ)
    (hbdry : ∀ θ ∈ Icc (0 : ℝ) 1, ∀ t : ℝ,
      finiteThetaShellPencil N θ
        (_root_.RHTower.rectangleBoundaryPath
          (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t) ≠ 0)
    (hellipse : ∀ θ ∈ Icc (0 : ℝ) 1,
      ∀ z ∈ pencilEnclosedZeros T n N θ, ∀ w ∈ pencilEnclosedZeros T n N θ,
        zhukovskyEllipseForm n (z - w) ≠ 1) :
    HTGeometry.fredholmIndex (integerThetaCollisionOperator T n N) =
      HTGeometry.fredholmIndex (integerThetaCollisionOperator T n (N + 1)) := by
  set M := integerThetaWindowDegree T n N
  have hHc : Continuous (fun p : ℝ × HTGeometry.UnitCircle =>
      pencilLaurentLoop T n N (clamp01 p.1) p.2) := by
    have hrew : (fun p : ℝ × HTGeometry.UnitCircle =>
          pencilLaurentLoop T n N (clamp01 p.1) p.2) =
        fun p : ℝ × HTGeometry.UnitCircle =>
          ((pairDiffPoly M (fun r => pencilWindowPowerSum T n N (clamp01 p.1) r)).eval
            (zhukovskyLoop n p.2)) ^ 2 := by
      funext p
      rw [pencilLaurentLoop_apply]
      unfold pencilDifferencePoly
      rw [pencilWindowDegree_clamp_eq T n N hbdry p.1]
    rw [hrew]
    exact (continuous_eval_pairDiffPoly_param M
      (fun r => (continuous_pencilWindowPowerSum_clamp T n N hbdry r).comp continuous_fst)
      ((zhukovskyLoop n).continuous.comp continuous_snd)).pow 2
  let H : C(ℝ × HTGeometry.UnitCircle, ℂ) :=
    ⟨fun p => pencilLaurentLoop T n N (clamp01 p.1) p.2, hHc⟩
  have hH_nz : ∀ (σ : ℝ) (u : HTGeometry.UnitCircle), H (σ, u) ≠ 0 := fun σ u =>
    (fredholmIndex_pencilCollisionOperator_eq_pairSum T n N (clamp01_mem_Icc σ)
      (hbdry (clamp01 σ) (clamp01_mem_Icc σ))
      (hellipse (clamp01 σ) (clamp01_mem_Icc σ))).1 u
  have h0 : H.curry 0 = integerThetaLaurentLoop T n N := by
    ext u
    change pencilLaurentLoop T n N (clamp01 0) u = integerThetaLaurentLoop T n N u
    rw [clamp01_zero, pencilLaurentLoop_zero]
  have h1 : H.curry 1 = integerThetaLaurentLoop T n (N + 1) := by
    ext u
    change pencilLaurentLoop T n N (clamp01 1) u = integerThetaLaurentLoop T n (N + 1) u
    rw [clamp01_one, pencilLaurentLoop_one]
  have hind := fredholmIndex_unitNormalizeSymbol_homotopy_invariant H hH_nz 0 1
  rw [h0, h1] at hind
  exact hind

/-- **Double-wall prefix transition dichotomy (`N → N + 1`).**
The Fredholm index of `integerThetaCollisionOperator T n N` can jump between prefix `N` and prefix
`N + 1` only if at some interpolation parameter `θ ∈ [0, 1]` either:
1. **Wall A (window boundary crossing)**: `finiteThetaShellPencil N θ` vanishes at a point of
   `∂R_{T,n}`, or
2. **Wall B (Zhukovsky ellipse crossing)**: two enclosed zeros `z, w ∈ pencilEnclosedZeros T n N θ`
   satisfy `zhukovskyEllipseForm n (z - w) = 1`. -/
theorem exists_pencil_wall_crossing_of_index_ne (T : ℝ) (n N : ℕ)
    (hne : HTGeometry.fredholmIndex (integerThetaCollisionOperator T n N) ≠
      HTGeometry.fredholmIndex (integerThetaCollisionOperator T n (N + 1))) :
    (∃ θ ∈ Icc (0 : ℝ) 1, ∃ t : ℝ,
      finiteThetaShellPencil N θ
        (_root_.RHTower.rectangleBoundaryPath
          (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t) = 0) ∨
    (∃ θ ∈ Icc (0 : ℝ) 1,
      ∃ z ∈ pencilEnclosedZeros T n N θ, ∃ w ∈ pencilEnclosedZeros T n N θ,
        zhukovskyEllipseForm n (z - w) = 1) := by
  by_contra h
  exact hne (fredholmIndex_integerThetaCollisionOperator_succ_eq T n N
    (fun θ hθ t h0 => h (Or.inl ⟨θ, hθ, t, h0⟩))
    (fun θ hθ z hz w hw he => h (Or.inr ⟨θ, hθ, z, hz, w, hw, he⟩)))

/-- **Mandatory boundary zero-ingress theorem.**
Whenever `thetaWindowScale T ≤ n` and `xiStripWindowTotalOrder T` exceeds the global strip zero
ceiling `prefixGlobalStripZeroBound N₀` of `finiteThetaAmplitude N₀`, at least one shell-pencil
transition `N → N + 1` (`N ≥ N₀`) is forced to cross the window boundary `∂R_{T,n}` (Wall A). -/
theorem exists_pencil_boundary_crossing_of_gt_globalBound (T : ℝ) {n : ℕ} (N₀ : ℕ)
    (hn : thetaWindowScale T ≤ n)
    (hgt : prefixGlobalStripZeroBound N₀ < _root_.RHTower.xiStripWindowTotalOrder T) :
    ∃ N ≥ N₀, ∃ θ ∈ Icc (0 : ℝ) 1, ∃ t : ℝ,
      finiteThetaShellPencil N θ
        (_root_.RHTower.rectangleBoundaryPath
          (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t) = 0 := by
  by_contra hno
  have hall : ∀ N ≥ N₀, ∀ θ ∈ Icc (0 : ℝ) 1, ∀ t : ℝ,
      finiteThetaShellPencil N θ
        (_root_.RHTower.rectangleBoundaryPath
          (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t) ≠ 0 :=
    fun N hN θ hθ t h0 => hno ⟨N, hN, θ, hθ, t, h0⟩
  have hbdry_N0 : ∀ t : ℝ, _root_.RHTower.finiteThetaAmplitude N₀
      (_root_.RHTower.rectangleBoundaryPath
        (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t) ≠ 0 := by
    intro t
    simpa only [finiteThetaShellPencil_zero] using hall N₀ le_rfl 0 ⟨le_rfl, zero_le_one⟩ t
  have hle0 : integerThetaWindowDegree T n N₀ ≤ prefixGlobalStripZeroBound N₀ :=
    integerThetaWindowDegree_le_globalStripZeroBound T n N₀ hbdry_N0
  have hconst : ∀ k : ℕ, integerThetaWindowDegree T n (N₀ + k) = integerThetaWindowDegree T n N₀ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show N₀ + (k + 1) = (N₀ + k) + 1 by omega,
        (integerThetaWindowDegree_succ_eq_of_boundary_ne_zero T n (N₀ + k)
          (hall (N₀ + k) (Nat.le_add_right N₀ k))).2, ih]
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (eventually_integerThetaWindowDegree_eq T hn)
  let M_idx := max N₀ N₁
  have hdeg_eq : integerThetaWindowDegree T n M_idx = _root_.RHTower.xiStripWindowTotalOrder T :=
    (hN₁ M_idx (le_max_right N₀ N₁)).2
  have hdeg_N0 : integerThetaWindowDegree T n M_idx = integerThetaWindowDegree T n N₀ := by
    have hadd : M_idx = N₀ + (M_idx - N₀) := (Nat.add_sub_of_le (le_max_left N₀ N₁)).symm
    rw [hadd, hconst]
  omega

/-- By Hardy's theorem (`exists_odd_order_line_zero_gt`), `xiStripWindowTotalOrder T` grows
unboundedly with `T`. -/
theorem exists_xiStripWindowTotalOrder_gt (M : ℕ) :
    ∃ T : ℝ, 0 < T ∧ M < _root_.RHTower.xiStripWindowTotalOrder T := by
  induction M with
  | zero =>
    obtain ⟨τ, hτ0, hzero, _⟩ := _root_.RHTower.exists_odd_order_line_zero_gt 0
    refine ⟨τ + 1, by linarith, ?_⟩
    unfold _root_.RHTower.xiStripWindowTotalOrder
    have hmem : _root_.RHTower.linePt τ ∈ (_root_.RHTower.stripZeros_finite (τ + 1)).toFinset := by
      rw [(_root_.RHTower.stripZeros_finite (τ + 1)).mem_toFinset]
      refine ⟨⟨?_, ?_, ?_, ?_⟩, hzero⟩
      · simp [_root_.RHTower.linePt]
      · simp [_root_.RHTower.linePt]; norm_num
      · simp [_root_.RHTower.linePt]; linarith
      · simp [_root_.RHTower.linePt]
    have hpos : 1 ≤ (analyticOrderAt _root_.RHTower.xi (_root_.RHTower.linePt τ)).toNat :=
      Nat.pos_of_ne_zero (_root_.RHTower.xi_order_toNat_ne_zero hzero)
    exact lt_of_lt_of_le (by omega)
      (hpos.trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem))
  | succ M ih =>
    obtain ⟨T, hT0, hM⟩ := ih
    obtain ⟨τ, hτT, hzero, _⟩ := _root_.RHTower.exists_odd_order_line_zero_gt T
    refine ⟨τ + 1, by linarith, ?_⟩
    unfold _root_.RHTower.xiStripWindowTotalOrder at hM ⊢
    set S₁ := (_root_.RHTower.stripZeros_finite T).toFinset
    set S₂ := (_root_.RHTower.stripZeros_finite (τ + 1)).toFinset
    have hsub : S₁ ⊆ S₂ := by
      intro w hw
      have hw' := (_root_.RHTower.stripZeros_finite T).mem_toFinset.mp hw
      exact (_root_.RHTower.stripZeros_finite (τ + 1)).mem_toFinset.mpr
        ⟨⟨hw'.1.1, hw'.1.2.1, hw'.1.2.2.1, by linarith [hw'.1.2.2.2]⟩, hw'.2⟩
    have hmem₂ : _root_.RHTower.linePt τ ∈ S₂ := by
      rw [(_root_.RHTower.stripZeros_finite (τ + 1)).mem_toFinset]
      refine ⟨⟨?_, ?_, ?_, ?_⟩, hzero⟩
      · simp [_root_.RHTower.linePt]
      · simp [_root_.RHTower.linePt]; norm_num
      · simp [_root_.RHTower.linePt]; linarith
      · simp [_root_.RHTower.linePt]
    have hnot₁ : _root_.RHTower.linePt τ ∉ S₁ := by
      intro hm
      have him := ((_root_.RHTower.stripZeros_finite T).mem_toFinset.mp hm).1.2.2.2
      simp [_root_.RHTower.linePt] at him
      linarith
    have hins : insert (_root_.RHTower.linePt τ) S₁ ⊆ S₂ :=
      Finset.insert_subset_iff.mpr ⟨hmem₂, hsub⟩
    have hle := Finset.sum_le_sum_of_subset
      (f := fun w => (analyticOrderAt _root_.RHTower.xi w).toNat) hins
    rw [Finset.sum_insert hnot₁] at hle
    have hpos : 1 ≤ (analyticOrderAt _root_.RHTower.xi (_root_.RHTower.linePt τ)).toNat :=
      Nat.pos_of_ne_zero (_root_.RHTower.xi_order_toNat_ne_zero hzero)
    omega

/-- **Unconditional mandatory boundary ingress for every starting prefix `N₀`.**
For every prefix cutoff `N₀ : ℕ`, there exists a window height `T > 0` such that on every stage
`n ≥ thetaWindowScale T`, at least one shell-pencil transition `N → N + 1` (`N ≥ N₀`) crosses the
window boundary `∂R_{T,n}`. -/
theorem forall_prefix_exists_window_pencil_boundary_crossing (N₀ : ℕ) :
    ∃ T : ℝ, 0 < T ∧ ∀ n : ℕ, thetaWindowScale T ≤ n →
      ∃ N ≥ N₀, ∃ θ ∈ Icc (0 : ℝ) 1, ∃ t : ℝ,
        finiteThetaShellPencil N θ
          (_root_.RHTower.rectangleBoundaryPath
            (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t) = 0 := by
  obtain ⟨T, hT0, hgt⟩ := exists_xiStripWindowTotalOrder_gt (prefixGlobalStripZeroBound N₀)
  exact ⟨T, hT0, fun n hn => exists_pencil_boundary_crossing_of_gt_globalBound T N₀ hn hgt⟩

/-! ## §3 Explicit perforated-rectangle Rouché artifact-annihilation threshold -/

/-- Refined Zhukovsky resolution scale `thetaAnnihilationScale T` ensuring `3 / s_n < collisionWindowGap T`
and `2 / s_n ≤ windowStripLeftMargin T`, so that Rouché discs of radius `1 / (8 s_n²)` around
`stripZeros T` are disjoint, strictly interior to `R_{T,n}`, and invisible to `zhukovskyLoop n`. -/
def thetaAnnihilationScale (T : ℝ) : ℕ :=
  max (thetaWindowScale T)
    (max (Nat.ceil (3 / collisionWindowGap T) + 1)
      (Nat.ceil (2 / windowStripLeftMargin T)))

theorem thetaWindowScale_le_annihilationScale (T : ℝ) :
    thetaWindowScale T ≤ thetaAnnihilationScale T :=
  le_max_left _ _

theorem six_le_thetaAnnihilationScale (T : ℝ) : 6 ≤ thetaAnnihilationScale T :=
  (six_le_thetaWindowScale T).trans (thetaWindowScale_le_annihilationScale T)

/-- Rouché perforation disc radius `1 / (8 s_n²)`. -/
def roucheDiscRadius (n : ℕ) : ℝ :=
  1 / (8 * (zhukovskyStage n : ℝ) ^ 2)

theorem roucheDiscRadius_pos (n : ℕ) : 0 < roucheDiscRadius n := by
  unfold roucheDiscRadius
  have hs := zhukovskyStage_pos n
  positivity

theorem roucheDiscRadius_le_inv_288 (n : ℕ) : roucheDiscRadius n ≤ 1 / 288 := by
  unfold roucheDiscRadius
  have hs : (6 : ℝ) ≤ (zhukovskyStage n : ℝ) := six_le_zhukovskyStage_real n
  exact one_div_le_one_div_of_le (by norm_num) (by nlinarith)

private lemma three_div_stage_lt_collisionWindowGap {T : ℝ} {n : ℕ}
    (hn : thetaAnnihilationScale T ≤ n) :
    3 / (zhukovskyStage n : ℝ) < collisionWindowGap T := by
  have hn6 : 6 ≤ n := (six_le_thetaAnnihilationScale T).trans hn
  have hceil : Nat.ceil (3 / collisionWindowGap T) + 1 ≤ n :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hn
  have hlt : 3 / collisionWindowGap T < (zhukovskyStage n : ℝ) := by
    rw [zhukovskyStage_eq_self hn6]
    have h1 := Nat.le_ceil (3 / collisionWindowGap T)
    have h2 : (Nat.ceil (3 / collisionWindowGap T) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hceil
    linarith
  have hgap := collisionWindowGap_pos T
  have hs := zhukovskyStage_pos n
  rwa [div_lt_iff₀ hs, mul_comm, ← div_lt_iff₀ hgap]

private lemma two_div_stage_le_windowStripLeftMargin {T : ℝ} {n : ℕ}
    (hn : thetaAnnihilationScale T ≤ n) :
    2 / (zhukovskyStage n : ℝ) ≤ windowStripLeftMargin T := by
  have hn6 : 6 ≤ n := (six_le_thetaAnnihilationScale T).trans hn
  have hceil : Nat.ceil (2 / windowStripLeftMargin T) ≤ n :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hn
  have hle : 2 / windowStripLeftMargin T ≤ (zhukovskyStage n : ℝ) := by
    rw [zhukovskyStage_eq_self hn6]
    exact (Nat.le_ceil _).trans (by exact_mod_cast hceil)
  have hm := windowStripLeftMargin_pos T
  have hs := zhukovskyStage_pos n
  rw [div_le_iff₀ hs, mul_comm, ← div_le_iff₀ hm]
  exact hle

private lemma stripZeros_re_margins {T : ℝ} {n : ℕ} (hn : thetaAnnihilationScale T ≤ n)
    {w : ℂ} (hw : w ∈ (_root_.RHTower.stripZeros_finite T).toFinset) :
    2 / (zhukovskyStage n : ℝ) ≤ w.re ∧ w.re ≤ 1 - 2 / (zhukovskyStage n : ℝ) := by
  have hleft : 2 / (zhukovskyStage n : ℝ) ≤ w.re :=
    (two_div_stage_le_windowStripLeftMargin hn).trans (windowStripLeftMargin_le_re hw)
  have hw_refl : _root_.RHTower.lineReflect w ∈ (_root_.RHTower.stripZeros_finite T).toFinset :=
    (_root_.RHTower.stripZeros_finite T).mem_toFinset.mpr
      (_root_.RHTower.lineReflect_mem_stripZeros
        ((_root_.RHTower.stripZeros_finite T).mem_toFinset.mp hw))
  have hrefl_le : 2 / (zhukovskyStage n : ℝ) ≤ (_root_.RHTower.lineReflect w).re :=
    (two_div_stage_le_windowStripLeftMargin hn).trans (windowStripLeftMargin_le_re hw_refl)
  rw [_root_.RHTower.lineReflect_re] at hrefl_le
  exact ⟨hleft, by linarith⟩

private lemma stripZeros_closedBall_two_rouche_inside {T : ℝ} {n : ℕ}
    (hn : thetaAnnihilationScale T ≤ n)
    {w z : ℂ} (hw : w ∈ (_root_.RHTower.stripZeros_finite T).toFinset)
    (hz : z ∈ Metric.closedBall w (2 * roucheDiscRadius n)) :
    (thetaWindowLowerLeft n).re < z.re ∧ z.re < (thetaWindowUpperRight T n).re ∧
      (thetaWindowLowerLeft n).im < z.im ∧ z.im < (thetaWindowUpperRight T n).im := by
  have hwdata := (_root_.RHTower.stripZeros_finite T).mem_toFinset.mp hw
  have hTpos : 0 < T := lt_of_le_of_lt hwdata.1.2.2.1 hwdata.1.2.2.2
  have hmax : max 0 T = T := max_eq_right hTpos.le
  have hs6 : (6 : ℝ) ≤ (zhukovskyStage n : ℝ) := six_le_zhukovskyStage_real n
  have hs_pos : (0 : ℝ) < (zhukovskyStage n : ℝ) := zhukovskyStage_pos n
  have hgap3 := three_div_stage_lt_collisionWindowGap hn
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
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  have hre_diff : |z.re - w.re| ≤ 2 * roucheDiscRadius n := by
    have : (z - w).re = z.re - w.re := Complex.sub_re z w
    rw [← this]; exact (Complex.abs_re_le_norm (z - w)).trans hz
  have him_diff : |z.im - w.im| ≤ 2 * roucheDiscRadius n := by
    have : (z - w).im = z.im - w.im := Complex.sub_im z w
    rw [← this]; exact (Complex.abs_im_le_norm (z - w)).trans hz
  have h2r_le : 2 * roucheDiscRadius n ≤ 1 / 144 := by linarith [roucheDiscRadius_le_inv_288 n]
  have h2r_lt_half_s : 2 * roucheDiscRadius n < 1 / (2 * (zhukovskyStage n : ℝ)) := by
    unfold roucheDiscRadius
    rw [show 2 * (1 / (8 * (zhukovskyStage n : ℝ) ^ 2)) =
      1 / (4 * (zhukovskyStage n : ℝ) ^ 2) by ring]
    exact one_div_lt_one_div_of_lt (by positivity) (by nlinarith)
  have h1_lt_3 : 1 / (zhukovskyStage n : ℝ) < 3 / (zhukovskyStage n : ℝ) :=
    div_lt_div_of_pos_right (by norm_num) hs_pos
  rw [thetaWindowLowerLeft_re, thetaWindowUpperRight_re,
    thetaWindowLowerLeft_im, thetaWindowUpperRight_im, hmax]
  obtain ⟨hre1, hre2⟩ := abs_le.mp hre_diff
  obtain ⟨him1, him2⟩ := abs_le.mp him_diff
  refine ⟨by linarith [hwdata.1.1], by linarith [hwdata.1.2.1],
    by linarith [hwdata.1.2.2.1], ?_⟩
  have hsub_half : 1 / (2 * (zhukovskyStage n : ℝ)) + 2 * roucheDiscRadius n <
      1 / (zhukovskyStage n : ℝ) := by
    linarith [show 1 / (2 * (zhukovskyStage n : ℝ)) + 1 / (2 * (zhukovskyStage n : ℝ)) =
      1 / (zhukovskyStage n : ℝ) by ring]
  linarith

private lemma stripZeros_dist_gt_four_rouche {T : ℝ} {n : ℕ}
    (hn : thetaAnnihilationScale T ≤ n)
    {w₁ w₂ : ℂ} (hw₁ : w₁ ∈ (_root_.RHTower.stripZeros_finite T).toFinset)
    (hw₂ : w₂ ∈ (_root_.RHTower.stripZeros_finite T).toFinset) (hne : w₁ ≠ w₂) :
    4 * roucheDiscRadius n < dist w₁ w₂ := by
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
  have hs6 : (6 : ℝ) ≤ (zhukovskyStage n : ℝ) := six_le_zhukovskyStage_real n
  have hs_pos : (0 : ℝ) < (zhukovskyStage n : ℝ) := zhukovskyStage_pos n
  have h4r_lt : 4 * roucheDiscRadius n < 3 / (zhukovskyStage n : ℝ) := by
    unfold roucheDiscRadius
    rw [show 4 * (1 / (8 * (zhukovskyStage n : ℝ) ^ 2)) =
      1 / (2 * (zhukovskyStage n : ℝ) ^ 2) by ring]
    rw [div_lt_div_iff₀ (by positivity) hs_pos]
    nlinarith
  exact (h4r_lt.trans (three_div_stage_lt_collisionWindowGap hn)).trans_le hgap_dist

/-- Closed `(T, n)` window rectangle `[-1 / 2, 3 / 2] × [-1 / (2 s_n), max 0 T - 1 / (2 s_n)]`. -/
def windowClosedRect (T : ℝ) (n : ℕ) : Set ℂ :=
  {z : ℂ | (thetaWindowLowerLeft n).re ≤ z.re ∧ z.re ≤ (thetaWindowUpperRight T n).re ∧
    (thetaWindowLowerLeft n).im ≤ z.im ∧ z.im ≤ (thetaWindowUpperRight T n).im}

/-- Compact perforated window rectangle obtained by excising open Rouché discs of radius
`1 / (8 s_n²)` around every zero of `xi` in `stripZeros T`. -/
def perforatedWindowSet (T : ℝ) (n : ℕ) : Set ℂ :=
  windowClosedRect T n \
    ⋃ w ∈ (_root_.RHTower.stripZeros_finite T).toFinset, Metric.ball w (roucheDiscRadius n)

theorem isCompact_windowClosedRect (T : ℝ) (n : ℕ) : IsCompact (windowClosedRect T n) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact (isClosed_le continuous_const Complex.continuous_re).inter
      ((isClosed_le Complex.continuous_re continuous_const).inter
        ((isClosed_le continuous_const Complex.continuous_im).inter
          (isClosed_le Complex.continuous_im continuous_const)))
  · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := max 0 T + 6)).subset fun z hz => ?_
    exact closedBall_six_mem_of_window_nhd T n
      ⟨by linarith [hz.1], by linarith [hz.2.1]⟩
      ⟨by linarith [hz.2.2.1], by linarith [hz.2.2.2]⟩

theorem isCompact_perforatedWindowSet (T : ℝ) (n : ℕ) : IsCompact (perforatedWindowSet T n) := by
  unfold perforatedWindowSet
  rw [Set.diff_eq]
  exact (isCompact_windowClosedRect T n).inter_right
    (isOpen_biUnion fun _ _ => Metric.isOpen_ball).isClosed_compl

theorem thetaWindowLowerLeft_mem_perforatedWindowSet (T : ℝ) (n : ℕ) :
    thetaWindowLowerLeft n ∈ perforatedWindowSet T n := by
  refine ⟨⟨le_rfl, thetaWindow_re_le T n, le_rfl, thetaWindow_im_le T n⟩, ?_⟩
  simp only [Set.mem_iUnion, Metric.mem_ball, not_exists, not_lt]
  intro w hw
  have hw0 : 0 < w.re := ((_root_.RHTower.stripZeros_finite T).mem_toFinset.mp hw).1.1
  have hre : 1 / 2 < |w.re - (thetaWindowLowerLeft n).re| := by
    rw [thetaWindowLowerLeft_re, abs_of_pos (by linarith)]
    linarith
  have hd : 1 / 2 < dist (thetaWindowLowerLeft n) w := by
    rw [dist_comm, dist_eq_norm]
    exact hre.trans_le (by simpa only [Complex.sub_re] using
      Complex.abs_re_le_norm (w - thetaWindowLowerLeft n))
  exact (roucheDiscRadius_le_inv_288 n).trans (by linarith)

theorem xi_ne_zero_on_perforatedWindowSet {T : ℝ} {n : ℕ} (hn : thetaAnnihilationScale T ≤ n)
    {z : ℂ} (hz : z ∈ perforatedWindowSet T n) :
    _root_.RHTower.xi z ≠ 0 := by
  intro hz0
  have hzRect : z ∈ uIcc (thetaWindowLowerLeft n).re (thetaWindowUpperRight T n).re ×ℂ
      uIcc (thetaWindowLowerLeft n).im (thetaWindowUpperRight T n).im := by
    rw [uIcc_of_le (thetaWindow_re_le T n), uIcc_of_le (thetaWindow_im_le T n),
      Complex.mem_reProdIm]
    exact ⟨⟨hz.1.1, hz.1.2.1⟩, ⟨hz.1.2.2.1, hz.1.2.2.2⟩⟩
  have hzBox : z ∈ thetaWindowOpenBox T n := thetaWindowRect_subset_openBox T n hzRect
  have hzStrip : z ∈ (_root_.RHTower.stripZeros_finite T).toFinset :=
    xi_zero_in_openBox_mem_stripZeros ((thetaWindowScale_le_annihilationScale T).trans hn) hzBox hz0
  exact hz.2 (Set.mem_biUnion hzStrip (Metric.mem_ball_self (roucheDiscRadius_pos n)))

/-- Minimum of `‖xi z‖` on the compact nonempty perforated window `perforatedWindowSet T n`. -/
def perforatedWindowXiMin (T : ℝ) (n : ℕ) : ℝ :=
  let hK := isCompact_perforatedWindowSet T n
  let hne : (perforatedWindowSet T n).Nonempty :=
    ⟨thetaWindowLowerLeft n, thetaWindowLowerLeft_mem_perforatedWindowSet T n⟩
  let hcont : ContinuousOn (fun z : ℂ => ‖_root_.RHTower.xi z‖) (perforatedWindowSet T n) :=
    _root_.RHTower.xi_differentiable.continuous.norm.continuousOn
  ‖_root_.RHTower.xi (hK.exists_isMinOn hne hcont).choose‖

theorem perforatedWindowXiMin_le_norm_xi {T : ℝ} {n : ℕ} {z : ℂ}
    (hz : z ∈ perforatedWindowSet T n) :
    perforatedWindowXiMin T n ≤ ‖_root_.RHTower.xi z‖ := by
  unfold perforatedWindowXiMin
  dsimp only
  set hK := isCompact_perforatedWindowSet T n
  set hne : (perforatedWindowSet T n).Nonempty :=
    ⟨thetaWindowLowerLeft n, thetaWindowLowerLeft_mem_perforatedWindowSet T n⟩
  set hcont : ContinuousOn (fun z : ℂ => ‖_root_.RHTower.xi z‖) (perforatedWindowSet T n) :=
    _root_.RHTower.xi_differentiable.continuous.norm.continuousOn
  exact isMinOn_iff.mp (hK.exists_isMinOn hne hcont).choose_spec.2 z hz

theorem perforatedWindowXiMin_pos {T : ℝ} {n : ℕ} (hn : thetaAnnihilationScale T ≤ n) :
    0 < perforatedWindowXiMin T n := by
  unfold perforatedWindowXiMin
  dsimp only
  set hK := isCompact_perforatedWindowSet T n
  set hne : (perforatedWindowSet T n).Nonempty :=
    ⟨thetaWindowLowerLeft n, thetaWindowLowerLeft_mem_perforatedWindowSet T n⟩
  set hcont : ContinuousOn (fun z : ℂ => ‖_root_.RHTower.xi z‖) (perforatedWindowSet T n) :=
    _root_.RHTower.xi_differentiable.continuous.norm.continuousOn
  exact norm_pos_iff.mpr
    (xi_ne_zero_on_perforatedWindowSet hn (hK.exists_isMinOn hne hcont).choose_spec.1)

/-- Explicit Gaussian Rouché prefix threshold `thetaArtifactAnnihilationPrefix T n` above which all
spurious finite-prefix zeros are expelled from `R_{T,n}` and every `xi` zero disc captures exact
multiplicity `ord_w(xi)`. -/
def thetaArtifactAnnihilationPrefix (T : ℝ) (n : ℕ) : ℕ :=
  Nat.ceil (Real.sqrt (max 0 (Real.log
    (2 * (_root_.RHTower.thetaCuspIntegerTailConstant *
      _root_.RHTower.thetaAmplitudeEnvelope 2) / perforatedWindowXiMin T n))))

private lemma gaussian_tail_lt_half_perforatedWindowXiMin {T : ℝ} {n N : ℕ}
    (hn : thetaAnnihilationScale T ≤ n) (hN : thetaArtifactAnnihilationPrefix T n ≤ N) :
    _root_.RHTower.thetaCuspIntegerTailConstant * _root_.RHTower.thetaAmplitudeEnvelope 2 *
      Real.exp (-((N + 1 : ℕ) : ℝ) ^ 2) < perforatedWindowXiMin T n / 2 := by
  set C_env : ℝ := _root_.RHTower.thetaCuspIntegerTailConstant *
    _root_.RHTower.thetaAmplitudeEnvelope 2
  set μ : ℝ := perforatedWindowXiMin T n
  have hμ : 0 < μ := perforatedWindowXiMin_pos hn
  have hC_nn : 0 ≤ C_env :=
    mul_nonneg _root_.RHTower.thetaCuspIntegerTailConstant_nonneg
      (_root_.RHTower.thetaAmplitudeEnvelope_nonneg 2)
  rcases eq_or_lt_of_le hC_nn with hC0 | hC_pos
  · rw [← hC0, zero_mul]
    linarith
  · by_cases hsmall : 2 * C_env ≤ μ
    · have hexp_lt1 : Real.exp (-((N + 1 : ℕ) : ℝ) ^ 2) < 1 := by
        rw [Real.exp_lt_one_iff]
        have h1 : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos N
        nlinarith
      calc C_env * Real.exp (-((N + 1 : ℕ) : ℝ) ^ 2)
          < C_env * 1 := mul_lt_mul_of_pos_left hexp_lt1 hC_pos
        _ ≤ μ / 2 := by linarith
    · replace hsmall : μ < 2 * C_env := not_le.mp hsmall
      have hX_gt1 : 1 < 2 * C_env / μ := (one_lt_div hμ).mpr hsmall
      have hlog_pos : 0 < Real.log (2 * C_env / μ) := Real.log_pos hX_gt1
      have hmax_eq : max 0 (Real.log (2 * C_env / μ)) = Real.log (2 * C_env / μ) :=
        max_eq_right hlog_pos.le
      have hsqrt_le : Real.sqrt (Real.log (2 * C_env / μ)) ≤ (N : ℝ) := by
        have hceil : (Nat.ceil (Real.sqrt (max 0 (Real.log (2 * C_env / μ)))) : ℝ) ≤ (N : ℝ) := by
          exact_mod_cast hN
        rw [hmax_eq] at hceil
        exact (Nat.le_ceil _).trans hceil
      have hsqrt_lt : Real.sqrt (Real.log (2 * C_env / μ)) < ((N + 1 : ℕ) : ℝ) := by
        push_cast; linarith
      have hlog_lt_sq : Real.log (2 * C_env / μ) < ((N + 1 : ℕ) : ℝ) ^ 2 := by
        have hsq := pow_lt_pow_left₀ hsqrt_lt (Real.sqrt_nonneg _) (by norm_num : 2 ≠ 0)
        rwa [Real.sq_sqrt hlog_pos.le] at hsq
      have hexp_lt : Real.exp (-((N + 1 : ℕ) : ℝ) ^ 2) < μ / (2 * C_env) := by
        have h1 : Real.exp (-((N + 1 : ℕ) : ℝ) ^ 2) < Real.exp (-Real.log (2 * C_env / μ)) :=
          Real.exp_lt_exp.mpr (by linarith)
        rw [Real.exp_neg, Real.exp_log (by positivity), inv_div] at h1
        exact h1
      calc C_env * Real.exp (-((N + 1 : ℕ) : ℝ) ^ 2)
          < C_env * (μ / (2 * C_env)) := mul_lt_mul_of_pos_left hexp_lt hC_pos
        _ = μ / 2 := by field_simp [hC_pos.ne']

private lemma rectangleBoundaryPath_mem_perforatedWindowSet {T : ℝ} {n : ℕ}
    (hn : thetaAnnihilationScale T ≤ n) (t : ℝ) :
    _root_.RHTower.rectangleBoundaryPath
      (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t ∈ perforatedWindowSet T n := by
  set γt := _root_.RHTower.rectangleBoundaryPath
    (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t
  have hmem := _root_.RHTower.rectangleBoundaryPath_mem_reProdIm
    (thetaWindowLowerLeft n) (thetaWindowUpperRight T n)
    (thetaWindow_re_le T n) (thetaWindow_im_le T n) t
  rw [uIcc_of_le (thetaWindow_re_le T n), uIcc_of_le (thetaWindow_im_le T n),
    Complex.mem_reProdIm] at hmem
  refine ⟨⟨hmem.1.1, hmem.1.2, hmem.2.1, hmem.2.2⟩, ?_⟩
  intro hball
  simp only [Set.mem_iUnion, exists_prop] at hball
  obtain ⟨w, hw, hdist⟩ := hball
  have hin := stripZeros_closedBall_two_rouche_inside hn hw
    (Metric.ball_subset_closedBall (Metric.ball_subset_ball
      (by linarith [roucheDiscRadius_pos n]) hdist))
  rcases rectangleBoundaryPath_on_edges
      (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t with h | h | h | h
  · exact hin.1.ne' h
  · exact hin.2.1.ne h
  · exact hin.2.2.1.ne' h
  · exact hin.2.2.2.ne h

private lemma sphere_rouche_subset_perforatedWindowSet {T : ℝ} {n : ℕ}
    (hn : thetaAnnihilationScale T ≤ n)
    {w : ℂ} (hw : w ∈ (_root_.RHTower.stripZeros_finite T).toFinset) :
    Metric.sphere w (roucheDiscRadius n) ⊆ perforatedWindowSet T n := by
  intro ζ hζ
  have hζ_cb : ζ ∈ Metric.closedBall w (2 * roucheDiscRadius n) := by
    rw [Metric.mem_closedBall, Metric.mem_sphere.mp hζ]
    linarith [roucheDiscRadius_pos n]
  obtain ⟨h1, h2, h3, h4⟩ := stripZeros_closedBall_two_rouche_inside hn hw hζ_cb
  refine ⟨⟨h1.le, h2.le, h3.le, h4.le⟩, ?_⟩
  simp only [Set.mem_iUnion, Metric.mem_ball, not_exists, not_lt]
  intro w' hw'
  by_cases heq : w' = w
  · rw [heq, Metric.mem_sphere.mp hζ]
  · have hsep := stripZeros_dist_gt_four_rouche hn hw hw' (Ne.symm heq)
    have htri := dist_triangle w w' ζ
    rw [dist_comm w' ζ] at htri
    rw [Metric.mem_sphere.mp hζ, dist_comm ζ w] at *
    have hdist_eq : dist w ζ = roucheDiscRadius n := by
      rw [dist_comm]; exact Metric.mem_sphere.mp hζ
    linarith [roucheDiscRadius_pos n]

/-- Two-times ordered horizontal sum identity on a finite zero set `W`. -/
private lemma two_mul_ordered_collision_sum_eq_charge (T : ℝ) :
    let W := (_root_.RHTower.stripZeros_finite T).toFinset
    let m : ℂ → ℕ := fun w => (analyticOrderAt _root_.RHTower.xi w).toNat
    2 * ∑ w₁ ∈ W, ∑ w₂ ∈ W,
        (m w₁ : ℤ) * (m w₂ : ℤ) * (if w₁.im = w₂.im ∧ w₂.re < w₁.re then 1 else 0) =
      (_root_.RHTower.xiHorizontalCollisionCharge T : ℤ) := by
  intro W m
  have hswap : (∑ w₁ ∈ W, ∑ w₂ ∈ W,
        (m w₁ : ℤ) * (m w₂ : ℤ) * (if w₁.im = w₂.im ∧ w₂.re < w₁.re then 1 else 0)) =
      ∑ w₁ ∈ W, ∑ w₂ ∈ W,
        (m w₁ : ℤ) * (m w₂ : ℤ) * (if w₁.im = w₂.im ∧ w₁.re < w₂.re then 1 else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun w₁ _ => Finset.sum_congr rfl fun w₂ _ => ?_
    by_cases h : w₂.im = w₁.im ∧ w₁.re < w₂.re
    · rw [if_pos h, if_pos ⟨h.1.symm, h.2⟩]; ring
    · rw [if_neg h, if_neg (fun h' => h ⟨h'.1.symm, h'.2⟩)]; ring
  have htwo : 2 * (∑ w₁ ∈ W, ∑ w₂ ∈ W,
        (m w₁ : ℤ) * (m w₂ : ℤ) * (if w₁.im = w₂.im ∧ w₂.re < w₁.re then 1 else 0)) =
      ∑ w₁ ∈ W, ∑ w₂ ∈ W,
        (m w₁ : ℤ) * (m w₂ : ℤ) * (if w₁.im = w₂.im ∧ w₁ ≠ w₂ then 1 else 0) := by
    have hadd : 2 * (∑ w₁ ∈ W, ∑ w₂ ∈ W,
          (m w₁ : ℤ) * (m w₂ : ℤ) * (if w₁.im = w₂.im ∧ w₂.re < w₁.re then 1 else 0)) =
        (∑ w₁ ∈ W, ∑ w₂ ∈ W,
          (m w₁ : ℤ) * (m w₂ : ℤ) * (if w₁.im = w₂.im ∧ w₂.re < w₁.re then 1 else 0)) +
        (∑ w₁ ∈ W, ∑ w₂ ∈ W,
          (m w₁ : ℤ) * (m w₂ : ℤ) * (if w₁.im = w₂.im ∧ w₁.re < w₂.re then 1 else 0)) := by
      linarith [hswap]
    rw [hadd, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w₁ _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w₂ _ => ?_
    by_cases him : w₁.im = w₂.im
    · by_cases hlt : w₂.re < w₁.re
      · have hgt : ¬ (w₁.re < w₂.re) := not_lt_of_gt hlt
        have hne : w₁ ≠ w₂ := fun h => hlt.ne (congrArg Complex.re h).symm
        rw [if_pos ⟨him, hlt⟩, if_neg (fun h => hgt h.2), if_pos ⟨him, hne⟩]; ring
      · by_cases hgt : w₁.re < w₂.re
        · have hne : w₁ ≠ w₂ := fun h => hgt.ne (congrArg Complex.re h)
          rw [if_neg (fun h => hlt h.2), if_pos ⟨him, hgt⟩, if_pos ⟨him, hne⟩]; ring
        · have heq : w₁ = w₂ := Complex.ext (le_antisymm (not_lt.mp hlt) (not_lt.mp hgt)) him
          rw [if_neg (fun h => hlt h.2), if_neg (fun h => hgt h.2), if_neg (fun h => h.2 heq)]
          ring
    · rw [if_neg (fun h => him h.1), if_neg (fun h => him h.1), if_neg (fun h => him h.1)]; ring
  rw [htwo, _root_.RHTower.xiHorizontalCollisionCharge_eq_sum_pairs,
    _root_.RHTower.xiHorizontalCollisionPairs, Finset.sum_filter, Finset.sum_product]
  push_cast
  refine Finset.sum_congr rfl fun w₁ _ => Finset.sum_congr rfl fun w₂ _ => ?_
  by_cases h : w₁.im = w₂.im ∧ w₁ ≠ w₂ <;> simp [h, m]

/-- **Perforated-rectangle Rouché artifact-annihilation theorem.**
For every height `T : ℝ`, every stage `n ≥ thetaAnnihilationScale T`, and every prefix
`N ≥ thetaArtifactAnnihilationPrefix T n`:
1. `finiteThetaAmplitude N` is strictly zero-free on the entire perforated window
   `perforatedWindowSet T n` (in particular on `∂R_{T,n}`), expelling all spurious finite-prefix
   artifacts from `R_{T,n}`;
2. Each open Rouché disc `ball w (roucheDiscRadius n)` around `w ∈ stripZeros T` contains total
   multiplicity of `finiteThetaAmplitude N` equal to `(analyticOrderAt xi w).toNat`;
3. Internal Rouché sub-disc splittings within any single disc satisfy `zhukovskyEllipseForm n > 1`
   (contributing `0` to `zhukovskyLoop n`), so `integerThetaWindowDegree T n N =
   xiStripWindowTotalOrder T`, `integerThetaLaurentLoop T n N` is everywhere nonvanishing on
   `UnitCircle`, and `fredholmIndex (integerThetaCollisionOperator T n N) =
   (xiHorizontalCollisionCharge T : ℤ)` unconditionally. -/
theorem integerThetaCollisionOperator_rouche_annihilation (T : ℝ) {n N : ℕ}
    (hn : thetaAnnihilationScale T ≤ n) (hN : thetaArtifactAnnihilationPrefix T n ≤ N) :
    (∀ z ∈ perforatedWindowSet T n, _root_.RHTower.finiteThetaAmplitude N z ≠ 0) ∧
    (∀ w ∈ (_root_.RHTower.stripZeros_finite T).toFinset,
      (∑ z ∈ (prefixEnclosedZeros T n N).filter (· ∈ Metric.ball w (roucheDiscRadius n)),
        (analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) z).toNat) =
        (analyticOrderAt _root_.RHTower.xi w).toNat) ∧
    integerThetaWindowDegree T n N = _root_.RHTower.xiStripWindowTotalOrder T ∧
    (∀ u : HTGeometry.UnitCircle, integerThetaLaurentLoop T n N u ≠ 0) ∧
    HTGeometry.fredholmIndex (integerThetaCollisionOperator T n N) =
      (_root_.RHTower.xiHorizontalCollisionCharge T : ℤ) := by
  set F := _root_.RHTower.finiteThetaAmplitude N
  set W := (_root_.RHTower.stripZeros_finite T).toFinset
  set r := roucheDiscRadius n
  have hr_pos : 0 < r := roucheDiscRadius_pos n
  have hr_2r : r < 2 * r := by linarith
  have htail := gaussian_tail_lt_half_perforatedWindowXiMin hn hN
  have hμ_pos : 0 < perforatedWindowXiMin T n := perforatedWindowXiMin_pos hn
  -- Uniform Rouché approximation on the closed rectangle `windowClosedRect T n`.
  have happrox_rect : ∀ z ∈ windowClosedRect T n,
      ‖F z - _root_.RHTower.xi z‖ < perforatedWindowXiMin T n / 2 := by
    intro z hz
    have hre_two : |z.re| ≤ 2 := by
      rw [thetaWindowLowerLeft_re] at hz
      have h2 := hz.2.1; rw [thetaWindowUpperRight_re] at h2
      exact abs_le.mpr ⟨by linarith [hz.1], by linarith [h2]⟩
    have hbd := norm_finiteThetaAmplitude_sub_xi_le_strip N (by norm_num : (0 : ℝ) ≤ 2) hre_two
    refine hbd.trans_lt ?_
    simpa only [mul_right_comm] using htail
  -- Part 1: `F` is nonvanishing on `perforatedWindowSet T n` and on `∂R_{T,n}`.
  have hF_perf : ∀ z ∈ perforatedWindowSet T n, F z ≠ 0 := by
    intro z hz h0
    have hlt := happrox_rect z hz.1
    rw [h0, zero_sub, norm_neg] at hlt
    linarith [perforatedWindowXiMin_le_norm_xi hz]
  have hbdry : ∀ t : ℝ, F (_root_.RHTower.rectangleBoundaryPath
      (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t) ≠ 0 :=
    fun t => hF_perf _ (rectangleBoundaryPath_mem_perforatedWindowSet hn t)
  -- Part 2: Symmetric Rouché zero-sum equality on each disc `ball w r` (`w ∈ W`).
  have hdisc_mult : ∀ w ∈ W,
      (∑ z ∈ (prefixEnclosedZeros T n N).filter (· ∈ Metric.ball w r),
        (analyticOrderAt F z).toNat) = (analyticOrderAt _root_.RHTower.xi w).toNat := by
    intro w hw
    have hsph_perf := sphere_rouche_subset_perforatedWindowSet hn hw
    have hxi_sph : ∀ ζ ∈ Metric.sphere w r, _root_.RHTower.xi ζ ≠ 0 :=
      fun ζ hζ => xi_ne_zero_on_perforatedWindowSet hn (hsph_perf hζ)
    have hF_sph : ∀ ζ ∈ Metric.sphere w r, F ζ ≠ 0 :=
      fun ζ hζ => hF_perf ζ (hsph_perf hζ)
    have hslit : ∀ ζ ∈ Metric.sphere w r, F ζ / _root_.RHTower.xi ζ ∈ Complex.slitPlane := by
      intro ζ hζ
      have hperf := hsph_perf hζ
      have hxi_min := perforatedWindowXiMin_le_norm_xi hperf
      have hdiff_lt : ‖F ζ - _root_.RHTower.xi ζ‖ < ‖_root_.RHTower.xi ζ‖ :=
        (happrox_rect ζ hperf.1).trans (by linarith)
      have hq : F ζ / _root_.RHTower.xi ζ - 1 =
          (F ζ - _root_.RHTower.xi ζ) / _root_.RHTower.xi ζ := by
        field_simp [hxi_sph ζ hζ]
      have hq_norm : ‖F ζ / _root_.RHTower.xi ζ - 1‖ < 1 := by
        rw [hq, norm_div, div_lt_one (norm_pos_iff.mpr (hxi_sph ζ hζ))]
        exact hdiff_lt
      have hre_lt : |(F ζ / _root_.RHTower.xi ζ - 1).re| < 1 :=
        (Complex.abs_re_le_norm _).trans_lt hq_norm
      rw [Complex.sub_re, Complex.one_re] at hre_lt
      exact Complex.mem_slitPlane_iff.mpr (Or.inl (by linarith [(abs_lt.mp hre_lt).1]))
    have hF_diff : DifferentiableOn ℂ F Set.univ :=
      (_root_.RHTower.differentiable_finiteThetaAmplitude N).differentiableOn
    have hxi_diff : DifferentiableOn ℂ _root_.RHTower.xi Set.univ :=
      _root_.RHTower.xi_differentiable.differentiableOn
    have hzsum := HTGeometry.zeroSumBall_eq_of_quotient_mem_slitPlane hr_pos hr_2r isOpen_univ
      (Set.subset_univ (Metric.closedBall w (2 * r))) hF_diff hxi_diff hxi_sph hslit
    obtain ⟨ZF, hZF_ball, hZF_zero, hZF_sum⟩ := HTGeometry.exists_zeroSet_zeroSumBall
      hr_pos hr_2r isOpen_univ (Set.subset_univ _) hF_diff hF_sph
    obtain ⟨ZG, hZG_ball, hZG_zero, hZG_sum⟩ := HTGeometry.exists_zeroSet_zeroSumBall
      hr_pos hr_2r isOpen_univ (Set.subset_univ _) hxi_diff hxi_sph
    have hZG_eq : ZG = {w} := by
      ext z
      rw [Finset.mem_singleton]
      constructor
      · intro hzG
        have hz_ball := hZG_ball z hzG
        have hz0 := (hZG_zero z hz_ball).2 hzG
        have hz_in := stripZeros_closedBall_two_rouche_inside hn hw
          (Metric.ball_subset_closedBall (Metric.ball_subset_ball hr_2r.le hz_ball))
        have hzRect : z ∈ uIcc (thetaWindowLowerLeft n).re (thetaWindowUpperRight T n).re ×ℂ
            uIcc (thetaWindowLowerLeft n).im (thetaWindowUpperRight T n).im := by
          rw [uIcc_of_le (thetaWindow_re_le T n), uIcc_of_le (thetaWindow_im_le T n),
            Complex.mem_reProdIm]
          exact ⟨⟨hz_in.1.le, hz_in.2.1.le⟩, ⟨hz_in.2.2.1.le, hz_in.2.2.2.le⟩⟩
        have hzW : z ∈ W := xi_zero_in_openBox_mem_stripZeros
          ((thetaWindowScale_le_annihilationScale T).trans hn)
          (thetaWindowRect_subset_openBox T n hzRect) hz0
        by_contra hne
        have hsep := stripZeros_dist_gt_four_rouche hn hzW hw hne
        have hd_lt : dist z w < r := Metric.mem_ball.mp hz_ball
        linarith
      · rintro rfl
        exact (hZG_zero w (Metric.mem_ball_self hr_pos)).1
          ((_root_.RHTower.stripZeros_finite T).mem_toFinset.mp hw).2
    have hZF_eq : ZF = (prefixEnclosedZeros T n N).filter (· ∈ Metric.ball w r) := by
      ext z
      rw [Finset.mem_filter, mem_prefixEnclosedZeros_iff]
      constructor
      · intro hzF
        have hzb := hZF_ball z hzF
        exact ⟨⟨stripZeros_closedBall_two_rouche_inside hn hw
          (Metric.ball_subset_closedBall (Metric.ball_subset_ball hr_2r.le hzb)),
          (hZF_zero z hzb).2 hzF⟩, hzb⟩
      · rintro ⟨⟨_, hz0⟩, hzb⟩
        exact (hZF_zero z hzb).1 hz0
    rw [hZF_sum, hZG_sum, hZG_eq, hZF_eq, Finset.sum_singleton] at hzsum
    have hcast : ((∑ z ∈ (prefixEnclosedZeros T n N).filter (· ∈ Metric.ball w r),
        (analyticOrderAt F z).toNat : ℕ) : ℂ) =
        (((analyticOrderAt _root_.RHTower.xi w).toNat : ℕ) : ℂ) := by
      push_cast
      exact hzsum
    exact Nat.cast_injective hcast
  -- Partition `prefixEnclosedZeros T n N` into the pairwise disjoint Rouché discs.
  set Z_N := prefixEnclosedZeros T n N
  let slice : ℂ → Finset ℂ := fun w => Z_N.filter (· ∈ Metric.ball w r)
  have hdisj : (W : Set ℂ).PairwiseDisjoint slice := by
    intro w₁ hw₁ w₂ hw₂ hne
    rw [Finset.disjoint_left]
    intro z hz₁ hz₂
    have hb₁ := (Finset.mem_filter.mp hz₁).2
    have hb₂ := (Finset.mem_filter.mp hz₂).2
    rw [Metric.mem_ball] at hb₁ hb₂
    have hsep := stripZeros_dist_gt_four_rouche hn hw₁ hw₂ hne
    have htri := dist_triangle w₁ z w₂
    rw [dist_comm z w₁] at hb₁
    linarith
  have hpart : Z_N = W.biUnion slice := by
    ext z
    rw [Finset.mem_biUnion]
    constructor
    · intro hz
      obtain ⟨hin, hz0⟩ := (mem_prefixEnclosedZeros_iff T n N z).mp hz
      have hrect : z ∈ windowClosedRect T n := ⟨hin.1.le, hin.2.1.le, hin.2.2.1.le, hin.2.2.2.le⟩
      by_contra hno
      have hperf : z ∈ perforatedWindowSet T n := by
        refine ⟨hrect, ?_⟩
        simp only [Set.mem_iUnion, exists_prop, not_exists, not_and]
        intro w hw hzb
        exact hno ⟨w, hw, Finset.mem_filter.mpr ⟨hz, hzb⟩⟩
      exact hF_perf z hperf hz0
    · rintro ⟨w, _, hzw⟩
      exact (Finset.mem_filter.mp hzw).1
  -- Part 3a: Exact window degree equality `integerThetaWindowDegree T n N = xiStripWindowTotalOrder T`.
  have hdeg_eq : integerThetaWindowDegree T n N = _root_.RHTower.xiStripWindowTotalOrder T := by
    have hbdry0 : ∀ t : ℝ, finiteThetaShellPencil N 0
        (_root_.RHTower.rectangleBoundaryPath
          (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t) ≠ 0 := by
      simpa only [finiteThetaShellPencil_zero] using hbdry
    have hd := (pencilWindowDegree_eq_sum T n N ⟨le_rfl, zero_le_one⟩ hbdry0).2
    rw [pencilWindowDegree_zero] at hd
    have hfun : finiteThetaShellPencil N 0 = F := funext (finiteThetaShellPencil_zero N)
    rw [hfun] at hd
    change integerThetaWindowDegree T n N = ∑ z ∈ Z_N, (analyticOrderAt F z).toNat at hd
    rw [hd, hpart, Finset.sum_biUnion hdisj]
    unfold _root_.RHTower.xiStripWindowTotalOrder
    exact Finset.sum_congr rfl fun w hw => hdisc_mult w hw
  -- Part 3b: Four-case Zhukovsky ellipse classification on pairs `(z₁ ∈ slice w₁, z₂ ∈ slice w₂)`.
  have hs6 : (6 : ℝ) ≤ (zhukovskyStage n : ℝ) := six_le_zhukovskyStage_real n
  have hs_pos : (0 : ℝ) < (zhukovskyStage n : ℝ) := zhukovskyStage_pos n
  have ha_pos : 0 < zhukovskyMajorAxis n := zhukovskyMajorAxis_pos n
  have hb_pos : 0 < zhukovskyMinorAxis n := zhukovskyMinorAxis_pos n
  have h2r_lt_s : 2 * r < 1 / (zhukovskyStage n : ℝ) := by
    dsimp only [r]
    unfold roucheDiscRadius
    rw [show 2 * (1 / (8 * (zhukovskyStage n : ℝ) ^ 2)) =
      1 / (4 * (zhukovskyStage n : ℝ) ^ 2) by ring]
    exact one_div_lt_one_div_of_lt hs_pos (by nlinarith)
  have h2r_lt_half_s : 2 * r < 1 / (2 * (zhukovskyStage n : ℝ)) := by
    dsimp only [r]
    unfold roucheDiscRadius
    rw [show 2 * (1 / (8 * (zhukovskyStage n : ℝ) ^ 2)) =
      1 / (4 * (zhukovskyStage n : ℝ) ^ 2) by ring]
    exact one_div_lt_one_div_of_lt (by positivity) (by nlinarith)
  have hpair_class : ∀ w₁ ∈ W, ∀ w₂ ∈ W, ∀ z₁ ∈ slice w₁, ∀ z₂ ∈ slice w₂,
      (w₁.im = w₂.im ∧ w₂.re < w₁.re → zhukovskyEllipseForm n (z₁ - z₂) < 1) ∧
      (¬ (w₁.im = w₂.im ∧ w₂.re < w₁.re) → 1 < zhukovskyEllipseForm n (z₁ - z₂)) := by
    intro w₁ hw₁ w₂ hw₂ z₁ hz₁ z₂ hz₂
    have hb₁ : dist z₁ w₁ < r := Metric.mem_ball.mp (Finset.mem_filter.mp hz₁).2
    have hb₂ : dist z₂ w₂ < r := Metric.mem_ball.mp (Finset.mem_filter.mp hz₂).2
    rw [dist_eq_norm] at hb₁ hb₂
    have hre₁ : |z₁.re - w₁.re| < r :=
      (by simpa only [Complex.sub_re] using Complex.abs_re_le_norm (z₁ - w₁)).trans_lt hb₁
    have him₁ : |z₁.im - w₁.im| < r :=
      (by simpa only [Complex.sub_im] using Complex.abs_im_le_norm (z₁ - w₁)).trans_lt hb₁
    have hre₂ : |z₂.re - w₂.re| < r :=
      (by simpa only [Complex.sub_re] using Complex.abs_re_le_norm (z₂ - w₂)).trans_lt hb₂
    have him₂ : |z₂.im - w₂.im| < r :=
      (by simpa only [Complex.sub_im] using Complex.abs_im_le_norm (z₂ - w₂)).trans_lt hb₂
    have hd_gap : collisionWindowGap T ≤ finiteCollisionGap W := min_le_left _ _
    have hgap3 := three_div_stage_lt_collisionWindowGap hn
    constructor
    · rintro ⟨him_eq, hre_lt⟩
      have hgap_re : collisionWindowGap T ≤ |w₁.re - w₂.re| :=
        hd_gap.trans ((min_le_left _ _).trans
          (finiteCoordinateGap_le W Complex.re hw₁ hw₂ hre_lt.ne'))
      rw [abs_of_pos (sub_pos.mpr hre_lt)] at hgap_re
      have hw₁_m := stripZeros_re_margins hn hw₁
      have hw₂_m := stripZeros_re_margins hn hw₂
      have hre_low : 2 / (zhukovskyStage n : ℝ) < (z₁ - z₂).re := by
        rw [Complex.sub_re]
        have h3_sub : 2 / (zhukovskyStage n : ℝ) =
            3 / (zhukovskyStage n : ℝ) - 1 / (zhukovskyStage n : ℝ) := by ring
        linarith [(abs_lt.mp hre₁).1, (abs_lt.mp hre₂).2]
      have hre_high : (z₁ - z₂).re < 1 - 1 / (zhukovskyStage n : ℝ) := by
        rw [Complex.sub_re]
        have h1 : (1 - 2 / (zhukovskyStage n : ℝ)) - 2 / (zhukovskyStage n : ℝ) +
            1 / (zhukovskyStage n : ℝ) ≤ 1 - 1 / (zhukovskyStage n : ℝ) := by
          have : 0 < 1 / (zhukovskyStage n : ℝ) := by positivity
          linarith
        linarith [hw₁_m.2, hw₂_m.1, (abs_lt.mp hre₁).2, (abs_lt.mp hre₂).1]
      set u : ℝ := (z₁ - z₂).re - 1 / 2
      have hu_abs : |u| < zhukovskyMajorAxis n - 1 / (2 * (zhukovskyStage n : ℝ)) := by
        dsimp only [u]
        unfold zhukovskyMajorAxis
        have hlow : 1 / (zhukovskyStage n : ℝ) < 2 / (zhukovskyStage n : ℝ) :=
          div_lt_div_of_pos_right (by norm_num) hs_pos
        exact abs_lt.mpr ⟨by linarith, by linarith⟩
      set δ : ℝ := 1 / (2 * (zhukovskyStage n : ℝ) * zhukovskyMajorAxis n)
      have hδ_pos : 0 < δ := by dsimp only [δ]; positivity
      have hδ_lt_one : δ < 1 := by
        dsimp only [δ]
        rw [div_lt_one (by positivity)]
        nlinarith [five_twelfths_le_zhukovskyMajorAxis n]
      have hinv_s_lt_δ : 1 / (zhukovskyStage n : ℝ) < δ := by
        dsimp only [δ]
        exact one_div_lt_one_div_of_lt (by positivity)
          (by nlinarith [zhukovskyMajorAxis_lt_half n])
      have hu_div : |u| / zhukovskyMajorAxis n < 1 - δ := by
        rw [div_lt_iff₀ ha_pos]
        have heq : (1 - δ) * zhukovskyMajorAxis n =
            zhukovskyMajorAxis n - 1 / (2 * (zhukovskyStage n : ℝ)) := by
          dsimp only [δ]
          field_simp [ha_pos.ne']
        rwa [heq]
      have hmaj_term : u ^ 2 / zhukovskyMajorAxis n ^ 2 < 1 - 1 / (zhukovskyStage n : ℝ) := by
        have h1 : u ^ 2 / zhukovskyMajorAxis n ^ 2 = (|u| / zhukovskyMajorAxis n) ^ 2 := by
          rw [div_pow, sq_abs]
        rw [h1]
        have hsq : (|u| / zhukovskyMajorAxis n) ^ 2 < (1 - δ) ^ 2 :=
          pow_lt_pow_left₀ hu_div (div_nonneg (abs_nonneg u) ha_pos.le) (by norm_num)
        nlinarith [sq_pos_of_pos hδ_pos]
      have him_abs : |(z₁ - z₂).im| < 1 / (4 * (zhukovskyStage n : ℝ) ^ 2) := by
        have hdiff : (z₁ - z₂).im = (z₁.im - w₁.im) - (z₂.im - w₂.im) := by
          rw [Complex.sub_im]; linarith [him_eq]
        have h2r_eq : 2 * r = 1 / (4 * (zhukovskyStage n : ℝ) ^ 2) := by
          dsimp only [r]; unfold roucheDiscRadius; ring
        rw [hdiff]
        exact abs_lt.mpr ⟨by linarith [(abs_lt.mp him₁).1, (abs_lt.mp him₂).2],
          by linarith [(abs_lt.mp him₁).2, (abs_lt.mp him₂).1]⟩
      have hmin_div : |(z₁ - z₂).im| / zhukovskyMinorAxis n < 1 / (4 * (zhukovskyStage n : ℝ)) := by
        unfold zhukovskyMinorAxis
        rw [div_lt_iff₀ (one_div_pos.mpr hs_pos)]
        have heq : 1 / (4 * (zhukovskyStage n : ℝ)) * (1 / (zhukovskyStage n : ℝ)) =
            1 / (4 * (zhukovskyStage n : ℝ) ^ 2) := by ring
        rwa [heq]
      have hmin_term : (z₁ - z₂).im ^ 2 / zhukovskyMinorAxis n ^ 2 <
          1 / (zhukovskyStage n : ℝ) := by
        have h1 : (z₁ - z₂).im ^ 2 / zhukovskyMinorAxis n ^ 2 =
            (|(z₁ - z₂).im| / zhukovskyMinorAxis n) ^ 2 := by rw [div_pow, sq_abs]
        rw [h1]
        have hsq : (|(z₁ - z₂).im| / zhukovskyMinorAxis n) ^ 2 <
            (1 / (4 * (zhukovskyStage n : ℝ))) ^ 2 :=
          pow_lt_pow_left₀ hmin_div (div_nonneg (abs_nonneg _) hb_pos.le) (by norm_num)
        have hsub : (1 / (4 * (zhukovskyStage n : ℝ))) ^ 2 < 1 / (zhukovskyStage n : ℝ) := by
          rw [show (1 / (4 * (zhukovskyStage n : ℝ))) ^ 2 =
            1 / (16 * (zhukovskyStage n : ℝ) ^ 2) by ring]
          exact one_div_lt_one_div_of_lt hs_pos (by nlinarith)
        exact hsq.trans hsub
      unfold zhukovskyEllipseForm
      change u ^ 2 / zhukovskyMajorAxis n ^ 2 + (z₁ - z₂).im ^ 2 / zhukovskyMinorAxis n ^ 2 < 1
      linarith
    · intro hnot
      by_cases him_eq : w₁.im = w₂.im
      · have hle_re : w₁.re ≤ w₂.re := not_lt.mp fun hlt => hnot ⟨him_eq, hlt⟩
        have hdiff_re : (z₁ - z₂).re < 1 / (2 * (zhukovskyStage n : ℝ)) := by
          rw [Complex.sub_re]
          linarith [(abs_lt.mp hre₁).2, (abs_lt.mp hre₂).1]
        have hsub_lt : (z₁ - z₂).re - 1 / 2 < -zhukovskyMajorAxis n := by
          unfold zhukovskyMajorAxis; linarith
        have hsq : zhukovskyMajorAxis n ^ 2 < ((z₁ - z₂).re - 1 / 2) ^ 2 := by nlinarith
        unfold zhukovskyEllipseForm
        have hdiv : 1 < ((z₁ - z₂).re - 1 / 2) ^ 2 / zhukovskyMajorAxis n ^ 2 :=
          (one_lt_div (sq_pos_of_pos ha_pos)).mpr hsq
        have hnn : 0 ≤ (z₁ - z₂).im ^ 2 / zhukovskyMinorAxis n ^ 2 := by positivity
        linarith
      · have hgap_im : collisionWindowGap T ≤ |w₁.im - w₂.im| :=
          hd_gap.trans ((min_le_right _ _).trans
            (finiteCoordinateGap_le W Complex.im hw₁ hw₂ him_eq))
        have him_gt : zhukovskyMinorAxis n < |(z₁ - z₂).im| := by
          unfold zhukovskyMinorAxis
          have htri : |w₁.im - w₂.im| - |z₁.im - w₁.im| - |z₂.im - w₂.im| ≤ |(z₁ - z₂).im| := by
            have h1 : w₁.im - w₂.im = (z₁ - z₂).im - (z₁.im - w₁.im) + (z₂.im - w₂.im) := by
              rw [Complex.sub_im]; ring
            have h2 := abs_add_le ((z₁ - z₂).im - (z₁.im - w₁.im)) (z₂.im - w₂.im)
            have h3 := abs_sub ((z₁ - z₂).im) (z₁.im - w₁.im)
            linarith
          have h3_gt : 1 / (zhukovskyStage n : ℝ) <
              3 / (zhukovskyStage n : ℝ) - 1 / (zhukovskyStage n : ℝ) := by
            rw [show 3 / (zhukovskyStage n : ℝ) - 1 / (zhukovskyStage n : ℝ) =
              2 / (zhukovskyStage n : ℝ) by ring]
            exact div_lt_div_of_pos_right (by norm_num) hs_pos
          linarith
        have hsq : zhukovskyMinorAxis n ^ 2 < (z₁ - z₂).im ^ 2 := by
          have h1 := pow_lt_pow_left₀ him_gt hb_pos.le (by norm_num : 2 ≠ 0)
          rwa [sq_abs] at h1
        unfold zhukovskyEllipseForm
        have hdiv : 1 < (z₁ - z₂).im ^ 2 / zhukovskyMinorAxis n ^ 2 :=
          (one_lt_div (sq_pos_of_pos hb_pos)).mpr hsq
        have hnn : 0 ≤ ((z₁ - z₂).re - 1 / 2) ^ 2 / zhukovskyMajorAxis n ^ 2 := by positivity
        linarith
  have hellipse_ne : ∀ z₁ ∈ Z_N, ∀ z₂ ∈ Z_N, zhukovskyEllipseForm n (z₁ - z₂) ≠ 1 := by
    intro z₁ hz₁ z₂ hz₂
    rw [hpart, Finset.mem_biUnion] at hz₁ hz₂
    obtain ⟨w₁, hw₁, hz₁_s⟩ := hz₁
    obtain ⟨w₂, hw₂, hz₂_s⟩ := hz₂
    have hcl := hpair_class w₁ hw₁ w₂ hw₂ z₁ hz₁_s z₂ hz₂_s
    by_cases h : w₁.im = w₂.im ∧ w₂.re < w₁.re
    · exact (hcl.1 h).ne
    · exact (hcl.2 h).ne'
  obtain ⟨hL_nz, hind, _⟩ := fredholmIndex_integerThetaCollisionOperator_eq_pairSum T n N
    hbdry hellipse_ne
  refine ⟨hF_perf, hdisc_mult, hdeg_eq, hL_nz, ?_⟩
  rw [hind]
  change 2 * (∑ z₁ ∈ Z_N, ∑ z₂ ∈ Z_N,
      ((analyticOrderAt F z₁).toNat : ℤ) * ((analyticOrderAt F z₂).toNat : ℤ) *
        (if zhukovskyEllipseForm n (z₁ - z₂) < 1 then 1 else 0)) = _
  have hsum_collapse :
      (∑ z₁ ∈ Z_N, ∑ z₂ ∈ Z_N,
        ((analyticOrderAt F z₁).toNat : ℤ) * ((analyticOrderAt F z₂).toNat : ℤ) *
          (if zhukovskyEllipseForm n (z₁ - z₂) < 1 then 1 else 0)) =
      ∑ w₁ ∈ W, ∑ w₂ ∈ W,
        ((analyticOrderAt _root_.RHTower.xi w₁).toNat : ℤ) *
          ((analyticOrderAt _root_.RHTower.xi w₂).toNat : ℤ) *
          (if w₁.im = w₂.im ∧ w₂.re < w₁.re then 1 else 0) := by
    rw [hpart, Finset.sum_biUnion hdisj]
    refine Finset.sum_congr rfl fun w₁ hw₁ => ?_
    have hinner : ∀ z₁ ∈ slice w₁,
        (∑ z₂ ∈ W.biUnion slice,
          ((analyticOrderAt F z₁).toNat : ℤ) * ((analyticOrderAt F z₂).toNat : ℤ) *
            (if zhukovskyEllipseForm n (z₁ - z₂) < 1 then 1 else 0)) =
        ∑ w₂ ∈ W, ((analyticOrderAt F z₁).toNat : ℤ) *
          ((analyticOrderAt _root_.RHTower.xi w₂).toNat : ℤ) *
          (if w₁.im = w₂.im ∧ w₂.re < w₁.re then 1 else 0) := by
      intro z₁ hz₁
      rw [Finset.sum_biUnion hdisj]
      refine Finset.sum_congr rfl fun w₂ hw₂ => ?_
      have hcond : ∀ z₂ ∈ slice w₂,
          (if zhukovskyEllipseForm n (z₁ - z₂) < 1 then (1 : ℤ) else 0) =
            if w₁.im = w₂.im ∧ w₂.re < w₁.re then 1 else 0 := by
        intro z₂ hz₂
        have hcl := hpair_class w₁ hw₁ w₂ hw₂ z₁ hz₁ z₂ hz₂
        by_cases h : w₁.im = w₂.im ∧ w₂.re < w₁.re
        · rw [if_pos h, if_pos (hcl.1 h)]
        · rw [if_neg h, if_neg (not_lt.mpr (hcl.2 h).le)]
      have hfactor : (∑ z₂ ∈ slice w₂,
            ((analyticOrderAt F z₁).toNat : ℤ) * ((analyticOrderAt F z₂).toNat : ℤ) *
              (if zhukovskyEllipseForm n (z₁ - z₂) < 1 then 1 else 0)) =
          ((analyticOrderAt F z₁).toNat : ℤ) *
            (∑ z₂ ∈ slice w₂, ((analyticOrderAt F z₂).toNat : ℤ)) *
            (if w₁.im = w₂.im ∧ w₂.re < w₁.re then 1 else 0) := by
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun z₂ hz₂ => ?_
        rw [hcond z₂ hz₂]
      rw [hfactor, ← Nat.cast_sum, hdisc_mult w₂ hw₂]
    rw [Finset.sum_congr rfl hinner, Finset.sum_comm]
    refine Finset.sum_congr rfl fun w₂ hw₂ => ?_
    have hfactor₁ : (∑ z₁ ∈ slice w₁,
          ((analyticOrderAt F z₁).toNat : ℤ) *
            ((analyticOrderAt _root_.RHTower.xi w₂).toNat : ℤ) *
            (if w₁.im = w₂.im ∧ w₂.re < w₁.re then 1 else 0)) =
        (∑ z₁ ∈ slice w₁, ((analyticOrderAt F z₁).toNat : ℤ)) *
          (((analyticOrderAt _root_.RHTower.xi w₂).toNat : ℤ) *
            (if w₁.im = w₂.im ∧ w₂.re < w₁.re then 1 else 0)) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun z₁ _ => by ring
    rw [hfactor₁, ← Nat.cast_sum, hdisc_mult w₁ hw₁, mul_assoc]
  rw [hsum_collapse]
  exact two_mul_ordered_collision_sum_eq_charge T

/-- Stabilization predicate at `(T, n)`: from prefix `N₀` onward, `finiteThetaAmplitude N` avoids
`∂R_{T,n}`, has exact window degree `xiStripWindowTotalOrder T`, has nonvanishing Zhukovsky loop,
and has Fredholm index equal to `(xiHorizontalCollisionCharge T : ℤ)`. -/
def IsArtifactFreeFrom (T : ℝ) (n N₀ : ℕ) : Prop :=
  ∀ N ≥ N₀,
    (∀ t : ℝ, _root_.RHTower.finiteThetaAmplitude N
      (_root_.RHTower.rectangleBoundaryPath
        (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t) ≠ 0) ∧
    integerThetaWindowDegree T n N = _root_.RHTower.xiStripWindowTotalOrder T ∧
    (∀ u : HTGeometry.UnitCircle, integerThetaLaurentLoop T n N u ≠ 0) ∧
    HTGeometry.fredholmIndex (integerThetaCollisionOperator T n N) =
      (_root_.RHTower.xiHorizontalCollisionCharge T : ℤ)

/-- Exact first prefix cutoff from which all finite-prefix artifacts have permanently stabilized on
`(T, n)`. -/
def firstArtifactFreePrefix (T : ℝ) (n : ℕ) : ℕ :=
  sInf {N₀ : ℕ | IsArtifactFreeFrom T n N₀}

theorem isArtifactFreeFrom_annihilationPrefix {T : ℝ} {n : ℕ}
    (hn : thetaAnnihilationScale T ≤ n) :
    IsArtifactFreeFrom T n (thetaArtifactAnnihilationPrefix T n) := by
  intro N hN
  obtain ⟨hperf, _, hdeg, hloop, hind⟩ :=
    integerThetaCollisionOperator_rouche_annihilation T hn hN
  exact ⟨fun t => hperf _ (rectangleBoundaryPath_mem_perforatedWindowSet hn t), hdeg, hloop, hind⟩

theorem isArtifactFreeFrom_firstArtifactFreePrefix {T : ℝ} {n : ℕ}
    (hn : thetaAnnihilationScale T ≤ n) :
    IsArtifactFreeFrom T n (firstArtifactFreePrefix T n) ∧
      firstArtifactFreePrefix T n ≤ thetaArtifactAnnihilationPrefix T n := by
  have hmem : thetaArtifactAnnihilationPrefix T n ∈ {N₀ : ℕ | IsArtifactFreeFrom T n N₀} :=
    isArtifactFreeFrom_annihilationPrefix hn
  exact ⟨Nat.sInf_mem ⟨_, hmem⟩, Nat.sInf_le hmem⟩

/-- On every low window `T ≤ 3` and every stage `n : ℕ`, `firstArtifactFreePrefix T n = 0`:
not even `N = 0` exhibits any finite-prefix artifact. -/
theorem firstArtifactFreePrefix_eq_zero_of_le_three {T : ℝ} (hT : T ≤ 3) (n : ℕ) :
    firstArtifactFreePrefix T n = 0 := by
  have h0 : (0 : ℕ) ∈ {N₀ : ℕ | IsArtifactFreeFrom T n N₀} := by
    intro N _
    obtain ⟨_, hdeg0, _, hloop1, hind0, hcharge0⟩ :=
      integerThetaCollisionOperator_trivial_of_le_three hT n N
    have hbdry : ∀ t : ℝ, _root_.RHTower.finiteThetaAmplitude N
        (_root_.RHTower.rectangleBoundaryPath
          (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t) ≠ 0 := by
      intro t hzero
      set z := _root_.RHTower.rectangleBoundaryPath
        (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t
      have hmem := _root_.RHTower.rectangleBoundaryPath_mem_reProdIm
        (thetaWindowLowerLeft n) (thetaWindowUpperRight T n)
        (thetaWindow_re_le T n) (thetaWindow_im_le T n) t
      rw [uIcc_of_le (thetaWindow_re_le T n), uIcc_of_le (thetaWindow_im_le T n),
        Complex.mem_reProdIm, thetaWindowLowerLeft_re, thetaWindowUpperRight_re,
        thetaWindowLowerLeft_im, thetaWindowUpperRight_im] at hmem
      have hhalf_le : 1 / (2 * (zhukovskyStage n : ℝ)) ≤ 1 / 12 :=
        one_div_le_one_div_of_le (by norm_num) (by linarith [six_le_zhukovskyStage_real n])
      have hhalf_pos : 0 < 1 / (2 * (zhukovskyStage n : ℝ)) := by positivity
      have hmax3 : max 0 T ≤ 3 := max_le (by norm_num) hT
      have hre : |z.re - 1 / 2| ≤ 9 / 8 :=
        abs_le.mpr ⟨by linarith [hmem.1.1], by linarith [hmem.1.2]⟩
      have him : |z.im| ≤ 61 / 20 :=
        abs_le.mpr ⟨by linarith [hmem.2.1], by linarith [hmem.2.2]⟩
      have hpos : 0 < (finiteThetaShellPencil N 0 z).re :=
        lt_of_lt_of_le (by positivity)
          (finiteThetaShellPencil_re_ge_lowWindow N ⟨le_rfl, zero_le_one⟩ hre him)
      rw [finiteThetaShellPencil_zero, hzero, Complex.zero_re] at hpos
      exact lt_irrefl 0 hpos
    have hxi0 : _root_.RHTower.xiStripWindowTotalOrder T = 0 := by
      unfold _root_.RHTower.xiStripWindowTotalOrder
      refine Finset.sum_eq_zero fun w hw => ?_
      exfalso
      have hw_mem := (_root_.RHTower.stripZeros_finite T).mem_toFinset.mp hw
      have hre : |w.re - 1 / 2| ≤ 9 / 8 :=
        abs_le.mpr ⟨by linarith [hw_mem.1.1], by linarith [hw_mem.1.2.1]⟩
      have him : |w.im| ≤ 61 / 20 :=
        abs_le.mpr ⟨by linarith [hw_mem.1.2.2.1], by linarith [hw_mem.1.2.2.2, hT]⟩
      have hpos : 0 < (_root_.RHTower.xi w).re :=
        lt_of_lt_of_le (by positivity) (xi_re_ge_lowWindow hre him)
      rw [hw_mem.2, Complex.zero_re] at hpos
      exact lt_irrefl 0 hpos
    refine ⟨hbdry, by rw [hdeg0, hxi0], ?_, by rw [hind0, hcharge0]; rfl⟩
    intro u
    rw [hloop1]
    exact one_ne_zero
  exact Nat.le_zero.mp (Nat.sInf_le h0)

/-- **Unconditional unboundedness of `firstArtifactFreePrefix T n` in height `T`.**
Whenever `xiStripWindowTotalOrder T > prefixGlobalStripZeroBound N₀` and
`n ≥ thetaAnnihilationScale T`, `N₀ < firstArtifactFreePrefix T n`; in particular, for every `N₀ : ℕ`
there exists `T > 0` where `N₀ < firstArtifactFreePrefix T n`, proving no single finite integer
theta prefix can ever be artifact-free uniformly across all heights `T`. -/
theorem lt_firstArtifactFreePrefix_of_gt_globalBound {T : ℝ} {n : ℕ} (N₀ : ℕ)
    (hn : thetaAnnihilationScale T ≤ n)
    (hgt : prefixGlobalStripZeroBound N₀ < _root_.RHTower.xiStripWindowTotalOrder T) :
    N₀ < firstArtifactFreePrefix T n := by
  by_contra hle
  replace hle : firstArtifactFreePrefix T n ≤ N₀ := not_lt.mp hle
  have haf := (isArtifactFreeFrom_firstArtifactFreePrefix hn).1 N₀ hle
  have hle_bound := integerThetaWindowDegree_le_globalStripZeroBound T n N₀ haf.1
  omega

theorem forall_prefix_exists_window_lt_firstArtifactFreePrefix (N₀ : ℕ) :
    ∃ T : ℝ, 0 < T ∧ ∀ n : ℕ, thetaAnnihilationScale T ≤ n →
      N₀ < firstArtifactFreePrefix T n := by
  obtain ⟨T, hT0, hgt⟩ := exists_xiStripWindowTotalOrder_gt (prefixGlobalStripZeroBound N₀)
  exact ⟨T, hT0, fun n hn => lt_firstArtifactFreePrefix_of_gt_globalBound N₀ hn hgt⟩

end GaloisForLFunctions.ConjugateDiagonalGeometry

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.fredholmIndex_integerThetaCollisionOperator_eq_pairSum
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.fredholmIndex_integerThetaCollisionOperator_eq_zero_of_collar
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.fredholmIndex_integerThetaCollisionOperator_eq_zero_of_criticalLine
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.fredholmIndex_integerThetaCollisionOperator_succ_eq
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.exists_pencil_wall_crossing_of_index_ne
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.exists_pencil_boundary_crossing_of_gt_globalBound
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.forall_prefix_exists_window_pencil_boundary_crossing
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.integerThetaCollisionOperator_rouche_annihilation
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.isArtifactFreeFrom_firstArtifactFreePrefix
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.firstArtifactFreePrefix_eq_zero_of_le_three
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.forall_prefix_exists_window_lt_firstArtifactFreePrefix
