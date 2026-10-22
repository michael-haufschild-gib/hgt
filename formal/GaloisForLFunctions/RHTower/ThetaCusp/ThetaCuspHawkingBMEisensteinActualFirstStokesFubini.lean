import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEisensteinActualFirstStokesIntegral
import GaloisForLFunctions.HTGeometry.BlockWindowFubini

/-!
# Compact-cell Fubini for the actual first Stokes defect

Corpus conjecture C-A.9t3d supplies the exact coefficient interface after the literal paired
Green theorem.  It builds joint compact-cell regularity for the actual Poincare fields and then
identifies the coordinate-split divergence integral with the standard hyperbolic first-defect
moment.

RH chain:

`actual defect Fubini -> first moment reduction -> second full-Hessian Green/Stokes -> actual
balanced BM ++- coefficient -> negative BM leg -> conserved left-QNM projection -> HC94 -> RH`.
-/

open Complex Real Filter Set Topology MeasureTheory
open scoped Interval

namespace RHTower
noncomputable section

def d4BMStokesPairCoordinate (w : ℝ × ℝ) : D4BMUpperHalfPlaneCoordinate :=
  d4BMStokesCoordinate w.1 w.2

theorem continuous_d4BMPoincareSeed_stokesPair
    (s : ℂ) (p : D4BMPrimitiveIntegerPair) :
    Continuous (fun w : ℝ × ℝ => d4BMPoincareSeed (d4BMStokesPairCoordinate w) s p) := by
  let b : ℝ × ℝ → ℝ := fun w =>
    (d4BMStokesPairCoordinate w).y /
      d4BMPoincareQuadratic (d4BMStokesPairCoordinate w) p.pair
  have hbpos (w : ℝ × ℝ) : 0 < b w := by
    exact div_pos (d4BMStokesPairCoordinate w).y_pos
      (d4BMPoincareQuadratic_pos (d4BMStokesPairCoordinate w) p.pair p.pair_ne_zero)
  have hb : Continuous b := by
    have hy : Continuous (fun w : ℝ × ℝ => (d4BMStokesPairCoordinate w).y) := by
      unfold d4BMStokesPairCoordinate d4BMStokesCoordinate
      fun_prop
    have hQ : Continuous (fun w : ℝ × ℝ =>
        d4BMPoincareQuadratic (d4BMStokesPairCoordinate w) p.pair) := by
      unfold d4BMPoincareQuadratic d4BMStokesPairCoordinate d4BMStokesCoordinate
      fun_prop
    exact hy.div₀ hQ fun w => ne_of_gt
      (d4BMPoincareQuadratic_pos (d4BMStokesPairCoordinate w) p.pair p.pair_ne_zero)
  rw [continuous_iff_continuousAt]
  intro w
  have hslit : ((b w : ℝ) : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    exact Or.inl (by simpa using hbpos w)
  have hreal : ContinuousAt (fun t : ℝ => (t : ℂ) ^ s) (b w) :=
    (continuousAt_cpow_const hslit).comp Complex.continuous_ofReal.continuousAt
  have hpow := hreal.comp hb.continuousAt
  simpa [d4BMPoincareSeed, b, Function.comp_def] using hpow

theorem continuous_d4BMPoincareQuadratic_stokesPair
    (p : D4BMPrimitiveIntegerPair) :
    Continuous (fun w : ℝ × ℝ =>
      d4BMPoincareQuadratic (d4BMStokesPairCoordinate w) p.pair) := by
  unfold d4BMPoincareQuadratic d4BMStokesPairCoordinate d4BMStokesCoordinate
  fun_prop

theorem continuous_d4BMPoincareHorizontalLinear_stokesPair
    (p : D4BMPrimitiveIntegerPair) :
    Continuous (fun w : ℝ × ℝ =>
      d4BMPoincareHorizontalLinear (d4BMStokesPairCoordinate w) p) := by
  unfold d4BMPoincareHorizontalLinear d4BMStokesPairCoordinate d4BMStokesCoordinate
  fun_prop

theorem continuous_d4BMStokesPairCoordinate_height :
    Continuous (fun w : ℝ × ℝ => (d4BMStokesPairCoordinate w).y) := by
  unfold d4BMStokesPairCoordinate d4BMStokesCoordinate
  fun_prop

private theorem d4BMPoincareQuadratic_stokesPair_ne_zero
    (p : D4BMPrimitiveIntegerPair) (w : ℝ × ℝ) :
    (d4BMPoincareQuadratic (d4BMStokesPairCoordinate w) p.pair : ℂ) ≠ 0 := by
  exact_mod_cast (d4BMPoincareQuadratic_pos
    (d4BMStokesPairCoordinate w) p.pair p.pair_ne_zero).ne'

private theorem d4BMStokesPairCoordinate_height_ne_zero (w : ℝ × ℝ) :
    ((d4BMStokesPairCoordinate w).y : ℂ) ≠ 0 := by
  exact_mod_cast (d4BMStokesPairCoordinate w).y_pos.ne'

theorem continuous_d4BMPoincareSeedHorizontalFirstJet_stokesPair
    (s : ℂ) (p : D4BMPrimitiveIntegerPair) :
    Continuous (fun w : ℝ × ℝ =>
      d4BMPoincareSeedHorizontalFirstJet (d4BMStokesPairCoordinate w) s p) := by
  have hQ : Continuous (fun w : ℝ × ℝ =>
      (d4BMPoincareQuadratic (d4BMStokesPairCoordinate w) p.pair : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_d4BMPoincareQuadratic_stokesPair p)
  have hL : Continuous (fun w : ℝ × ℝ =>
      (d4BMPoincareHorizontalLinear (d4BMStokesPairCoordinate w) p : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_d4BMPoincareHorizontalLinear_stokesPair p)
  have hnum : Continuous (fun w : ℝ × ℝ =>
      -2 * s * (p.pair.1 : ℂ) *
        (d4BMPoincareHorizontalLinear (d4BMStokesPairCoordinate w) p : ℂ)) := by
    fun_prop
  have hquot := hnum.div₀ hQ (d4BMPoincareQuadratic_stokesPair_ne_zero p)
  have hfun :
      (fun w : ℝ × ℝ =>
        d4BMPoincareSeedHorizontalFirstJet (d4BMStokesPairCoordinate w) s p) =
      (fun w =>
        (-2 * s * (p.pair.1 : ℂ) *
          (d4BMPoincareHorizontalLinear (d4BMStokesPairCoordinate w) p : ℂ) /
            (d4BMPoincareQuadratic (d4BMStokesPairCoordinate w) p.pair : ℂ)) *
          d4BMPoincareSeed (d4BMStokesPairCoordinate w) s p) := by
    funext w
    rfl
  rw [hfun]
  exact hquot.mul (continuous_d4BMPoincareSeed_stokesPair s p)

theorem continuous_d4BMPoincareSeedHorizontalSecondJet_stokesPair
    (s : ℂ) (p : D4BMPrimitiveIntegerPair) :
    Continuous (fun w : ℝ × ℝ =>
      d4BMPoincareSeedHorizontalSecondJet (d4BMStokesPairCoordinate w) s p) := by
  have hQ : Continuous (fun w : ℝ × ℝ =>
      (d4BMPoincareQuadratic (d4BMStokesPairCoordinate w) p.pair : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_d4BMPoincareQuadratic_stokesPair p)
  have hL : Continuous (fun w : ℝ × ℝ =>
      (d4BMPoincareHorizontalLinear (d4BMStokesPairCoordinate w) p : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_d4BMPoincareHorizontalLinear_stokesPair p)
  have hterm1 : Continuous (fun w : ℝ × ℝ =>
      -2 * s * (p.pair.1 : ℂ) ^ 2 /
        (d4BMPoincareQuadratic (d4BMStokesPairCoordinate w) p.pair : ℂ)) := by
    exact continuous_const.div₀ hQ (d4BMPoincareQuadratic_stokesPair_ne_zero p)
  have hnum2 : Continuous (fun w : ℝ × ℝ =>
      4 * s * (s + 1) * (p.pair.1 : ℂ) ^ 2 *
        (d4BMPoincareHorizontalLinear (d4BMStokesPairCoordinate w) p : ℂ) ^ 2) := by
    fun_prop
  have hterm2 : Continuous (fun w : ℝ × ℝ =>
      4 * s * (s + 1) * (p.pair.1 : ℂ) ^ 2 *
          (d4BMPoincareHorizontalLinear (d4BMStokesPairCoordinate w) p : ℂ) ^ 2 /
        (d4BMPoincareQuadratic (d4BMStokesPairCoordinate w) p.pair : ℂ) ^ 2) := by
    exact hnum2.div₀ (hQ.pow 2) fun w =>
      pow_ne_zero 2 (d4BMPoincareQuadratic_stokesPair_ne_zero p w)
  have hfun :
      (fun w : ℝ × ℝ =>
        d4BMPoincareSeedHorizontalSecondJet (d4BMStokesPairCoordinate w) s p) =
      (fun w =>
        (-2 * s * (p.pair.1 : ℂ) ^ 2 /
              (d4BMPoincareQuadratic (d4BMStokesPairCoordinate w) p.pair : ℂ) +
            4 * s * (s + 1) * (p.pair.1 : ℂ) ^ 2 *
              (d4BMPoincareHorizontalLinear (d4BMStokesPairCoordinate w) p : ℂ) ^ 2 /
                (d4BMPoincareQuadratic (d4BMStokesPairCoordinate w) p.pair : ℂ) ^ 2) *
          d4BMPoincareSeed (d4BMStokesPairCoordinate w) s p) := by
    funext w
    rfl
  rw [hfun]
  exact (hterm1.add hterm2).mul (continuous_d4BMPoincareSeed_stokesPair s p)

theorem continuous_d4BMPoincareSeedVerticalFirstJet_stokesPair
    (s : ℂ) (p : D4BMPrimitiveIntegerPair) :
    Continuous (fun w : ℝ × ℝ =>
      d4BMPoincareSeedVerticalFirstJet (d4BMStokesPairCoordinate w) s p) := by
  have hQ : Continuous (fun w : ℝ × ℝ =>
      (d4BMPoincareQuadratic (d4BMStokesPairCoordinate w) p.pair : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_d4BMPoincareQuadratic_stokesPair p)
  have hy : Continuous (fun w : ℝ × ℝ =>
      ((d4BMStokesPairCoordinate w).y : ℂ)) :=
    Complex.continuous_ofReal.comp continuous_d4BMStokesPairCoordinate_height
  have hterm1 : Continuous (fun w : ℝ × ℝ =>
      s / ((d4BMStokesPairCoordinate w).y : ℂ)) :=
    continuous_const.div₀ hy d4BMStokesPairCoordinate_height_ne_zero
  have hnum2 : Continuous (fun w : ℝ × ℝ =>
      2 * s * (p.pair.1 : ℂ) ^ 2 * ((d4BMStokesPairCoordinate w).y : ℂ)) := by
    fun_prop
  have hterm2 := hnum2.div₀ hQ (d4BMPoincareQuadratic_stokesPair_ne_zero p)
  have hfun :
      (fun w : ℝ × ℝ =>
        d4BMPoincareSeedVerticalFirstJet (d4BMStokesPairCoordinate w) s p) =
      (fun w =>
        (s / ((d4BMStokesPairCoordinate w).y : ℂ) -
            2 * s * (p.pair.1 : ℂ) ^ 2 * ((d4BMStokesPairCoordinate w).y : ℂ) /
              (d4BMPoincareQuadratic (d4BMStokesPairCoordinate w) p.pair : ℂ)) *
          d4BMPoincareSeed (d4BMStokesPairCoordinate w) s p) := by
    funext w
    rfl
  rw [hfun]
  exact (hterm1.sub hterm2).mul (continuous_d4BMPoincareSeed_stokesPair s p)

theorem continuous_d4BMPoincareSeedVerticalSecondJet_stokesPair
    (s : ℂ) (p : D4BMPrimitiveIntegerPair) :
    Continuous (fun w : ℝ × ℝ =>
      d4BMPoincareSeedVerticalSecondJet (d4BMStokesPairCoordinate w) s p) := by
  have hQ : Continuous (fun w : ℝ × ℝ =>
      (d4BMPoincareQuadratic (d4BMStokesPairCoordinate w) p.pair : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_d4BMPoincareQuadratic_stokesPair p)
  have hy : Continuous (fun w : ℝ × ℝ =>
      ((d4BMStokesPairCoordinate w).y : ℂ)) :=
    Complex.continuous_ofReal.comp continuous_d4BMStokesPairCoordinate_height
  have hterm1 : Continuous (fun w : ℝ × ℝ =>
      s * (s - 1) / ((d4BMStokesPairCoordinate w).y : ℂ) ^ 2) := by
    exact continuous_const.div₀ (hy.pow 2) fun w =>
      pow_ne_zero 2 (d4BMStokesPairCoordinate_height_ne_zero w)
  have hterm2 : Continuous (fun w : ℝ × ℝ =>
      2 * s * (1 + 2 * s) * (p.pair.1 : ℂ) ^ 2 /
        (d4BMPoincareQuadratic (d4BMStokesPairCoordinate w) p.pair : ℂ)) := by
    exact continuous_const.div₀ hQ (d4BMPoincareQuadratic_stokesPair_ne_zero p)
  have hnum3 : Continuous (fun w : ℝ × ℝ =>
      4 * s * (s + 1) * (p.pair.1 : ℂ) ^ 4 *
        ((d4BMStokesPairCoordinate w).y : ℂ) ^ 2) := by
    fun_prop
  have hterm3 : Continuous (fun w : ℝ × ℝ =>
      4 * s * (s + 1) * (p.pair.1 : ℂ) ^ 4 *
          ((d4BMStokesPairCoordinate w).y : ℂ) ^ 2 /
        (d4BMPoincareQuadratic (d4BMStokesPairCoordinate w) p.pair : ℂ) ^ 2) := by
    exact hnum3.div₀ (hQ.pow 2) fun w =>
      pow_ne_zero 2 (d4BMPoincareQuadratic_stokesPair_ne_zero p w)
  have hfun :
      (fun w : ℝ × ℝ =>
        d4BMPoincareSeedVerticalSecondJet (d4BMStokesPairCoordinate w) s p) =
      (fun w =>
        (s * (s - 1) / ((d4BMStokesPairCoordinate w).y : ℂ) ^ 2 -
            2 * s * (1 + 2 * s) * (p.pair.1 : ℂ) ^ 2 /
              (d4BMPoincareQuadratic (d4BMStokesPairCoordinate w) p.pair : ℂ) +
            4 * s * (s + 1) * (p.pair.1 : ℂ) ^ 4 *
              ((d4BMStokesPairCoordinate w).y : ℂ) ^ 2 /
                (d4BMPoincareQuadratic (d4BMStokesPairCoordinate w) p.pair : ℂ) ^ 2) *
          d4BMPoincareSeed (d4BMStokesPairCoordinate w) s p) := by
    funext w
    rfl
  rw [hfun]
  exact ((hterm1.sub hterm2).add hterm3).mul
    (continuous_d4BMPoincareSeed_stokesPair s p)

def d4BMStokesBaseCoordinate : D4BMUpperHalfPlaneCoordinate :=
  d4BMStokesCoordinate 0 1

/-- One fixed primitive-pair summand at `i` dominates the same summand throughout every
truncated modular cell, up to a scalar depending only on the top height.  The geometric input is
the uniform comparison `c² + d² ≤ 6 (c²y² + (cx+d)²)` on `|x| ≤ 1/2`, `y ≥ 1/2`. -/
theorem d4BM_stokesBase_quadratic_le_six_mul
    (p : D4BMPrimitiveIntegerPair) (w : ℝ × ℝ)
    (hx : w.1 ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2))
    (hy : (1 / 2 : ℝ) ≤ w.2) :
    d4BMPoincareQuadratic d4BMStokesBaseCoordinate p.pair ≤
      6 * d4BMPoincareQuadratic (d4BMStokesPairCoordinate w) p.pair := by
  let c : ℝ := p.pair.1
  let d : ℝ := p.pair.2
  let x : ℝ := w.1
  let y : ℝ := w.2
  let u : ℝ := c * x + d
  have hxSq : x ^ 2 ≤ 1 / 4 := by
    dsimp only [x] at *
    nlinarith [hx.1, hx.2, sq_nonneg (w.1 + 1 / 2), sq_nonneg (1 / 2 - w.1)]
  have hySq : 1 / 4 ≤ y ^ 2 := by
    dsimp only [y] at *
    nlinarith [sq_nonneg (w.2 - 1 / 2)]
  have hcxSq : (c * x) ^ 2 ≤ c ^ 2 / 4 := by
    nlinarith [sq_nonneg c]
  have hdSq : d ^ 2 ≤ 2 * u ^ 2 + 2 * (c * x) ^ 2 := by
    dsimp only [u]
    nlinarith [sq_nonneg (c * x + d + c * x)]
  have hcY : c ^ 2 ≤ 4 * (c * y) ^ 2 := by
    nlinarith [sq_nonneg c]
  unfold d4BMStokesBaseCoordinate d4BMStokesPairCoordinate
    d4BMPoincareQuadratic d4BMStokesCoordinate
  simp only [max_eq_left hy, max_eq_left (by norm_num : (1 / 2 : ℝ) ≤ 1)]
  dsimp only [c, d, x, y, u] at *
  norm_num at *
  nlinarith

theorem norm_d4BMPoincareSeed_stokesPair_le
    (P : D4BMEisensteinAbsoluteConvergenceParameter)
    (p : D4BMPrimitiveIntegerPair) (w : ℝ × ℝ) {Y : ℝ}
    (hx : w.1 ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2))
    (hy : (1 / 2 : ℝ) ≤ w.2) (hwY : w.2 ≤ Y) :
    ‖d4BMPoincareSeed (d4BMStokesPairCoordinate w) P.s p‖ ≤
      (Y ^ P.s.re * 6 ^ P.s.re) *
        ‖d4BMPoincareSeed d4BMStokesBaseCoordinate P.s p‖ := by
  have hy0 : 0 < w.2 := lt_of_lt_of_le (by norm_num) hy
  have hY0 : 0 < Y := hy0.trans_le hwY
  have hsigma : 0 ≤ P.s.re := by linarith [P.re_gt_one]
  have hQbase : 0 < d4BMPoincareQuadratic d4BMStokesBaseCoordinate p.pair :=
    d4BMPoincareQuadratic_pos d4BMStokesBaseCoordinate p.pair p.pair_ne_zero
  have hQ : 0 < d4BMPoincareQuadratic (d4BMStokesPairCoordinate w) p.pair :=
    d4BMPoincareQuadratic_pos (d4BMStokesPairCoordinate w) p.pair p.pair_ne_zero
  have hrpow := d4BM_rpow_neg_le_of_le_mul hQbase hQ
    (by norm_num : (0 : ℝ) < 6) hsigma
    (d4BM_stokesBase_quadratic_le_six_mul p w hx hy)
  have hyrpow : w.2 ^ P.s.re ≤ Y ^ P.s.re :=
    Real.rpow_le_rpow hy0.le hwY hsigma
  rw [norm_d4BMPoincareSeed, norm_d4BMPoincareSeed]
  have hycoord : (d4BMStokesPairCoordinate w).y = w.2 := by
    change max w.2 (1 / 2 : ℝ) = w.2
    exact max_eq_left hy
  have hybase : d4BMStokesBaseCoordinate.y = 1 := by
    change max (1 : ℝ) (1 / 2) = 1
    exact max_eq_left (by norm_num)
  rw [hycoord, hybase]
  change
    w.2 ^ P.s.re *
        d4BMPoincareQuadratic (d4BMStokesPairCoordinate w) p.pair ^ (-P.s.re) ≤
      (Y ^ P.s.re * 6 ^ P.s.re) *
        (1 ^ P.s.re *
          d4BMPoincareQuadratic d4BMStokesBaseCoordinate p.pair ^ (-P.s.re))
  rw [one_rpow]
  simp only [one_mul]
  calc
    w.2 ^ P.s.re *
        d4BMPoincareQuadratic (d4BMStokesPairCoordinate w) p.pair ^ (-P.s.re) ≤
        Y ^ P.s.re *
          (6 ^ P.s.re *
            d4BMPoincareQuadratic d4BMStokesBaseCoordinate p.pair ^ (-P.s.re)) :=
      mul_le_mul hyrpow hrpow (Real.rpow_nonneg hQ.le _)
        (Real.rpow_nonneg hY0.le _)
    _ = (Y ^ P.s.re * 6 ^ P.s.re) *
        d4BMPoincareQuadratic d4BMStokesBaseCoordinate p.pair ^ (-P.s.re) := by
      ring

def d4BMStokesCompactCell (Y : ℝ) : Set (ℝ × ℝ) :=
  Set.Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Set.Icc (1 / 2 : ℝ) Y

def d4BMStokesValueMajorant
    (P : D4BMEisensteinAbsoluteConvergenceParameter) (Y : ℝ)
    (p : D4BMPrimitiveIntegerPair) : ℝ :=
  (Y ^ P.s.re * 6 ^ P.s.re) *
    ‖d4BMPoincareSeed d4BMStokesBaseCoordinate P.s p‖

theorem summable_d4BMStokesValueMajorant
    (P : D4BMEisensteinAbsoluteConvergenceParameter) (Y : ℝ) :
    Summable (d4BMStokesValueMajorant P Y) := by
  exact (summable_d4BMPoincareSeed d4BMStokesBaseCoordinate P).norm.mul_left _

theorem continuousOn_tsum_d4BMPoincareSeed_stokesCompactCell
    (P : D4BMEisensteinAbsoluteConvergenceParameter) {Y : ℝ} :
    ContinuousOn
      (fun w : ℝ × ℝ => ∑' p : D4BMPrimitiveIntegerPair,
        d4BMPoincareSeed (d4BMStokesPairCoordinate w) P.s p)
      (d4BMStokesCompactCell Y) := by
  apply continuousOn_tsum
  · intro p
    exact (continuous_d4BMPoincareSeed_stokesPair P.s p).continuousOn
  · exact summable_d4BMStokesValueMajorant P Y
  · intro p w hw
    exact norm_d4BMPoincareSeed_stokesPair_le P p w hw.1 hw.2.1 hw.2.2

theorem continuousOn_d4BMCompletedEisensteinPoincareSeries_stokesCompactCell
    (P : D4BMEisensteinAbsoluteConvergenceParameter) {Y : ℝ} :
    ContinuousOn
      (fun w : ℝ × ℝ =>
        d4BMCompletedEisensteinPoincareSeries (d4BMStokesPairCoordinate w) P)
      (d4BMStokesCompactCell Y) := by
  have hsum := continuousOn_tsum_d4BMPoincareSeed_stokesCompactCell P (Y := Y)
  have hraw : ContinuousOn
      (fun w : ℝ × ℝ => (1 / 2 : ℂ) *
        ∑' p : D4BMPrimitiveIntegerPair,
          d4BMPoincareSeed (d4BMStokesPairCoordinate w) P.s p)
      (d4BMStokesCompactCell Y) := continuousOn_const.mul hsum
  have hcompleted : ContinuousOn
      (fun w : ℝ × ℝ => reflectedCompletedLambda (2 * P.s) *
        ((1 / 2 : ℂ) * ∑' p : D4BMPrimitiveIntegerPair,
          d4BMPoincareSeed (d4BMStokesPairCoordinate w) P.s p))
      (d4BMStokesCompactCell Y) := continuousOn_const.mul hraw
  simpa [d4BMCompletedEisensteinPoincareSeries,
    d4BMRawEisensteinPoincareSeries] using hcompleted

def d4BMStokesJetMajorant
    (K : ℝ) (P : D4BMEisensteinAbsoluteConvergenceParameter) (Y : ℝ)
    (p : D4BMPrimitiveIntegerPair) : ℝ :=
  K * d4BMStokesValueMajorant P Y p

theorem summable_d4BMStokesJetMajorant
    (K : ℝ) (P : D4BMEisensteinAbsoluteConvergenceParameter) (Y : ℝ) :
    Summable (d4BMStokesJetMajorant K P Y) :=
  (summable_d4BMStokesValueMajorant P Y).mul_left K

private theorem continuousOn_d4BMCompletedTsum_stokesCompactCell
    {f : D4BMPrimitiveIntegerPair → (ℝ × ℝ) → ℂ}
    (P : D4BMEisensteinAbsoluteConvergenceParameter) {Y : ℝ}
    (h : ContinuousOn (fun w => ∑' p, f p w) (d4BMStokesCompactCell Y)) :
    ContinuousOn
      (fun w => reflectedCompletedLambda (2 * P.s) *
        ((1 / 2 : ℂ) * ∑' p, f p w))
      (d4BMStokesCompactCell Y) := by
  exact continuousOn_const.mul (continuousOn_const.mul h)

theorem continuousOn_tsum_d4BMPoincareSeedHorizontalFirstJet_stokesCompactCell
    (P : D4BMEisensteinAbsoluteConvergenceParameter) {Y : ℝ} :
    ContinuousOn
      (fun w : ℝ × ℝ => ∑' p : D4BMPrimitiveIntegerPair,
        d4BMPoincareSeedHorizontalFirstJet (d4BMStokesPairCoordinate w) P.s p)
      (d4BMStokesCompactCell Y) := by
  let K : ℝ := 4 * ‖P.s‖
  apply continuousOn_tsum
  · intro p
    exact (continuous_d4BMPoincareSeedHorizontalFirstJet_stokesPair P.s p).continuousOn
  · exact summable_d4BMStokesJetMajorant K P Y
  · intro p w hw
    change w.1 ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) ∧
      w.2 ∈ Set.Icc (1 / 2 : ℝ) Y at hw
    have hy0 : 0 < w.2 := lt_of_lt_of_le (by norm_num) hw.2.1
    have hK : 0 ≤ K := by positivity
    have hfactor : 2 * ‖P.s‖ / w.2 ≤ K := by
      apply (div_le_iff₀ hy0).2
      dsimp only [K]
      nlinarith [hw.2.1, norm_nonneg P.s]
    calc
      ‖d4BMPoincareSeedHorizontalFirstJet (d4BMStokesPairCoordinate w) P.s p‖ ≤
          (2 * ‖P.s‖ / w.2) *
            ‖d4BMPoincareSeed (d4BMStokesPairCoordinate w) P.s p‖ := by
        have h := norm_d4BMPoincareSeedHorizontalFirstJet_le
          (d4BMStokesPairCoordinate w) P.s p
        have hycoord : (d4BMStokesPairCoordinate w).y = w.2 := by
          change max w.2 (1 / 2 : ℝ) = w.2
          exact max_eq_left hw.2.1
        rw [hycoord] at h
        exact h
      _ ≤ K * ‖d4BMPoincareSeed (d4BMStokesPairCoordinate w) P.s p‖ :=
        mul_le_mul_of_nonneg_right hfactor (norm_nonneg _)
      _ ≤ K * d4BMStokesValueMajorant P Y p :=
        mul_le_mul_of_nonneg_left
          (norm_d4BMPoincareSeed_stokesPair_le P p w hw.1 hw.2.1 hw.2.2) hK
      _ = d4BMStokesJetMajorant K P Y p := rfl

theorem continuousOn_d4BMCompletedPoincareHorizontalFirstJet_stokesCompactCell
    (P : D4BMEisensteinAbsoluteConvergenceParameter) {Y : ℝ} :
    ContinuousOn
      (fun w : ℝ × ℝ =>
        d4BMCompletedPoincareHorizontalFirstJet (d4BMStokesPairCoordinate w) P)
      (d4BMStokesCompactCell Y) := by
  have h := continuousOn_d4BMCompletedTsum_stokesCompactCell P
    (continuousOn_tsum_d4BMPoincareSeedHorizontalFirstJet_stokesCompactCell P (Y := Y))
  simpa [d4BMCompletedPoincareHorizontalFirstJet,
    d4BMRawPoincareHorizontalFirstJet] using h

theorem continuousOn_tsum_d4BMPoincareSeedVerticalFirstJet_stokesCompactCell
    (P : D4BMEisensteinAbsoluteConvergenceParameter) {Y : ℝ} :
    ContinuousOn
      (fun w : ℝ × ℝ => ∑' p : D4BMPrimitiveIntegerPair,
        d4BMPoincareSeedVerticalFirstJet (d4BMStokesPairCoordinate w) P.s p)
      (d4BMStokesCompactCell Y) := by
  let K : ℝ := 6 * ‖P.s‖
  apply continuousOn_tsum
  · intro p
    exact (continuous_d4BMPoincareSeedVerticalFirstJet_stokesPair P.s p).continuousOn
  · exact summable_d4BMStokesJetMajorant K P Y
  · intro p w hw
    change w.1 ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) ∧
      w.2 ∈ Set.Icc (1 / 2 : ℝ) Y at hw
    have hy0 : 0 < w.2 := lt_of_lt_of_le (by norm_num) hw.2.1
    have hK : 0 ≤ K := by positivity
    have hfactor : 3 * ‖P.s‖ / w.2 ≤ K := by
      apply (div_le_iff₀ hy0).2
      dsimp only [K]
      nlinarith [hw.2.1, norm_nonneg P.s]
    calc
      ‖d4BMPoincareSeedVerticalFirstJet (d4BMStokesPairCoordinate w) P.s p‖ ≤
          (3 * ‖P.s‖ / w.2) *
            ‖d4BMPoincareSeed (d4BMStokesPairCoordinate w) P.s p‖ := by
        have h := norm_d4BMPoincareSeedVerticalFirstJet_le
          (d4BMStokesPairCoordinate w) P.s p
        have hycoord : (d4BMStokesPairCoordinate w).y = w.2 := by
          change max w.2 (1 / 2 : ℝ) = w.2
          exact max_eq_left hw.2.1
        rw [hycoord] at h
        exact h
      _ ≤ K * ‖d4BMPoincareSeed (d4BMStokesPairCoordinate w) P.s p‖ :=
        mul_le_mul_of_nonneg_right hfactor (norm_nonneg _)
      _ ≤ K * d4BMStokesValueMajorant P Y p :=
        mul_le_mul_of_nonneg_left
          (norm_d4BMPoincareSeed_stokesPair_le P p w hw.1 hw.2.1 hw.2.2) hK
      _ = d4BMStokesJetMajorant K P Y p := rfl

theorem continuousOn_d4BMCompletedPoincareVerticalFirstJet_stokesCompactCell
    (P : D4BMEisensteinAbsoluteConvergenceParameter) {Y : ℝ} :
    ContinuousOn
      (fun w : ℝ × ℝ =>
        d4BMCompletedPoincareVerticalFirstJet (d4BMStokesPairCoordinate w) P)
      (d4BMStokesCompactCell Y) := by
  have h := continuousOn_d4BMCompletedTsum_stokesCompactCell P
    (continuousOn_tsum_d4BMPoincareSeedVerticalFirstJet_stokesCompactCell P (Y := Y))
  simpa [d4BMCompletedPoincareVerticalFirstJet,
    d4BMRawPoincareVerticalFirstJet] using h

theorem continuousOn_tsum_d4BMPoincareSeedHorizontalSecondJet_stokesCompactCell
    (P : D4BMEisensteinAbsoluteConvergenceParameter) {Y : ℝ} :
    ContinuousOn
      (fun w : ℝ × ℝ => ∑' p : D4BMPrimitiveIntegerPair,
        d4BMPoincareSeedHorizontalSecondJet (d4BMStokesPairCoordinate w) P.s p)
      (d4BMStokesCompactCell Y) := by
  let C : ℝ := 2 * ‖P.s‖ + 4 * ‖P.s‖ * ‖P.s + 1‖
  let K : ℝ := 4 * C
  apply continuousOn_tsum
  · intro p
    exact (continuous_d4BMPoincareSeedHorizontalSecondJet_stokesPair P.s p).continuousOn
  · exact summable_d4BMStokesJetMajorant K P Y
  · intro p w hw
    change w.1 ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) ∧
      w.2 ∈ Set.Icc (1 / 2 : ℝ) Y at hw
    have hy0 : 0 < w.2 := lt_of_lt_of_le (by norm_num) hw.2.1
    have hySq : 1 / 4 ≤ w.2 ^ 2 := by
      nlinarith [hw.2.1, sq_nonneg (w.2 - 1 / 2)]
    have hC : 0 ≤ C := by dsimp only [C]; positivity
    have hK : 0 ≤ K := by dsimp only [K]; positivity
    have hfactor : C / w.2 ^ 2 ≤ K := by
      apply (div_le_iff₀ (sq_pos_of_pos hy0)).2
      dsimp only [K]
      nlinarith
    calc
      ‖d4BMPoincareSeedHorizontalSecondJet (d4BMStokesPairCoordinate w) P.s p‖ ≤
          (C / w.2 ^ 2) *
            ‖d4BMPoincareSeed (d4BMStokesPairCoordinate w) P.s p‖ := by
        have h := norm_d4BMPoincareSeedHorizontalSecondJet_le
          (d4BMStokesPairCoordinate w) P.s p
        have hycoord : (d4BMStokesPairCoordinate w).y = w.2 := by
          change max w.2 (1 / 2 : ℝ) = w.2
          exact max_eq_left hw.2.1
        rw [hycoord] at h
        simpa only [C] using h
      _ ≤ K * ‖d4BMPoincareSeed (d4BMStokesPairCoordinate w) P.s p‖ :=
        mul_le_mul_of_nonneg_right hfactor (norm_nonneg _)
      _ ≤ K * d4BMStokesValueMajorant P Y p :=
        mul_le_mul_of_nonneg_left
          (norm_d4BMPoincareSeed_stokesPair_le P p w hw.1 hw.2.1 hw.2.2) hK
      _ = d4BMStokesJetMajorant K P Y p := rfl

theorem continuousOn_d4BMCompletedPoincareHorizontalSecondJet_stokesCompactCell
    (P : D4BMEisensteinAbsoluteConvergenceParameter) {Y : ℝ} :
    ContinuousOn
      (fun w : ℝ × ℝ =>
        d4BMCompletedPoincareHorizontalSecondJet (d4BMStokesPairCoordinate w) P)
      (d4BMStokesCompactCell Y) := by
  have h := continuousOn_d4BMCompletedTsum_stokesCompactCell P
    (continuousOn_tsum_d4BMPoincareSeedHorizontalSecondJet_stokesCompactCell P (Y := Y))
  simpa [d4BMCompletedPoincareHorizontalSecondJet,
    d4BMRawPoincareHorizontalSecondJet] using h

theorem continuousOn_tsum_d4BMPoincareSeedVerticalSecondJet_stokesCompactCell
    (P : D4BMEisensteinAbsoluteConvergenceParameter) {Y : ℝ} :
    ContinuousOn
      (fun w : ℝ × ℝ => ∑' p : D4BMPrimitiveIntegerPair,
        d4BMPoincareSeedVerticalSecondJet (d4BMStokesPairCoordinate w) P.s p)
      (d4BMStokesCompactCell Y) := by
  let C : ℝ := ‖P.s‖ * ‖P.s - 1‖ + 2 * ‖P.s‖ * ‖1 + 2 * P.s‖ +
    4 * ‖P.s‖ * ‖P.s + 1‖
  let K : ℝ := 4 * C
  apply continuousOn_tsum
  · intro p
    exact (continuous_d4BMPoincareSeedVerticalSecondJet_stokesPair P.s p).continuousOn
  · exact summable_d4BMStokesJetMajorant K P Y
  · intro p w hw
    change w.1 ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) ∧
      w.2 ∈ Set.Icc (1 / 2 : ℝ) Y at hw
    have hy0 : 0 < w.2 := lt_of_lt_of_le (by norm_num) hw.2.1
    have hySq : 1 / 4 ≤ w.2 ^ 2 := by
      nlinarith [hw.2.1, sq_nonneg (w.2 - 1 / 2)]
    have hC : 0 ≤ C := by dsimp only [C]; positivity
    have hK : 0 ≤ K := by dsimp only [K]; positivity
    have hfactor : C / w.2 ^ 2 ≤ K := by
      apply (div_le_iff₀ (sq_pos_of_pos hy0)).2
      dsimp only [K]
      nlinarith
    calc
      ‖d4BMPoincareSeedVerticalSecondJet (d4BMStokesPairCoordinate w) P.s p‖ ≤
          (C / w.2 ^ 2) *
            ‖d4BMPoincareSeed (d4BMStokesPairCoordinate w) P.s p‖ := by
        have h := norm_d4BMPoincareSeedVerticalSecondJet_le
          (d4BMStokesPairCoordinate w) P.s p
        have hycoord : (d4BMStokesPairCoordinate w).y = w.2 := by
          change max w.2 (1 / 2 : ℝ) = w.2
          exact max_eq_left hw.2.1
        rw [hycoord] at h
        simpa only [C] using h
      _ ≤ K * ‖d4BMPoincareSeed (d4BMStokesPairCoordinate w) P.s p‖ :=
        mul_le_mul_of_nonneg_right hfactor (norm_nonneg _)
      _ ≤ K * d4BMStokesValueMajorant P Y p :=
        mul_le_mul_of_nonneg_left
          (norm_d4BMPoincareSeed_stokesPair_le P p w hw.1 hw.2.1 hw.2.2) hK
      _ = d4BMStokesJetMajorant K P Y p := rfl

theorem continuousOn_d4BMCompletedPoincareVerticalSecondJet_stokesCompactCell
    (P : D4BMEisensteinAbsoluteConvergenceParameter) {Y : ℝ} :
    ContinuousOn
      (fun w : ℝ × ℝ =>
        d4BMCompletedPoincareVerticalSecondJet (d4BMStokesPairCoordinate w) P)
      (d4BMStokesCompactCell Y) := by
  have h := continuousOn_d4BMCompletedTsum_stokesCompactCell P
    (continuousOn_tsum_d4BMPoincareSeedVerticalSecondJet_stokesCompactCell P (Y := Y))
  simpa [d4BMCompletedPoincareVerticalSecondJet,
    d4BMRawPoincareVerticalSecondJet] using h

theorem continuousOn_d4BMActualFirstStokesHorizontalDivergence_stokesCompactCell
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) {Y : ℝ} :
    ContinuousOn
      (fun w : ℝ × ℝ =>
        d4BMActualFirstStokesHorizontalDivergenceAt P Q w.1 w.2)
      (d4BMStokesCompactCell Y) := by
  have hF := continuousOn_d4BMCompletedEisensteinPoincareSeries_stokesCompactCell
    P (Y := Y)
  have hG := continuousOn_d4BMCompletedEisensteinPoincareSeries_stokesCompactCell
    Q (Y := Y)
  have hFx := continuousOn_d4BMCompletedPoincareHorizontalFirstJet_stokesCompactCell
    P (Y := Y)
  have hFxx := continuousOn_d4BMCompletedPoincareHorizontalSecondJet_stokesCompactCell
    P (Y := Y)
  have hGxx := continuousOn_d4BMCompletedPoincareHorizontalSecondJet_stokesCompactCell
    Q (Y := Y)
  unfold d4BMActualFirstStokesHorizontalDivergenceAt
    d4BMActualFirstStokesHorizontalDivergence
  change ContinuousOn
    (fun w : ℝ × ℝ =>
      2 * d4BMCompletedEisensteinPoincareSeries (d4BMStokesPairCoordinate w) Q *
          d4BMCompletedPoincareHorizontalFirstJet (d4BMStokesPairCoordinate w) P ^ 2 +
        2 * d4BMCompletedEisensteinPoincareSeries (d4BMStokesPairCoordinate w) P *
          d4BMCompletedEisensteinPoincareSeries (d4BMStokesPairCoordinate w) Q *
          d4BMCompletedPoincareHorizontalSecondJet (d4BMStokesPairCoordinate w) P -
        d4BMCompletedEisensteinPoincareSeries (d4BMStokesPairCoordinate w) P ^ 2 *
          d4BMCompletedPoincareHorizontalSecondJet (d4BMStokesPairCoordinate w) Q)
      (d4BMStokesCompactCell Y)
  fun_prop

theorem continuousOn_d4BMActualFirstStokesVerticalDivergence_stokesCompactCell
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) {Y : ℝ} :
    ContinuousOn
      (fun w : ℝ × ℝ =>
        d4BMActualFirstStokesVerticalDivergenceAt P Q w.1 w.2)
      (d4BMStokesCompactCell Y) := by
  have hF := continuousOn_d4BMCompletedEisensteinPoincareSeries_stokesCompactCell
    P (Y := Y)
  have hG := continuousOn_d4BMCompletedEisensteinPoincareSeries_stokesCompactCell
    Q (Y := Y)
  have hFy := continuousOn_d4BMCompletedPoincareVerticalFirstJet_stokesCompactCell
    P (Y := Y)
  have hFyy := continuousOn_d4BMCompletedPoincareVerticalSecondJet_stokesCompactCell
    P (Y := Y)
  have hGyy := continuousOn_d4BMCompletedPoincareVerticalSecondJet_stokesCompactCell
    Q (Y := Y)
  unfold d4BMActualFirstStokesVerticalDivergenceAt
    d4BMActualFirstStokesVerticalDivergence
  change ContinuousOn
    (fun w : ℝ × ℝ =>
      2 * d4BMCompletedEisensteinPoincareSeries (d4BMStokesPairCoordinate w) Q *
          d4BMCompletedPoincareVerticalFirstJet (d4BMStokesPairCoordinate w) P ^ 2 +
        2 * d4BMCompletedEisensteinPoincareSeries (d4BMStokesPairCoordinate w) P *
          d4BMCompletedEisensteinPoincareSeries (d4BMStokesPairCoordinate w) Q *
          d4BMCompletedPoincareVerticalSecondJet (d4BMStokesPairCoordinate w) P -
        d4BMCompletedEisensteinPoincareSeries (d4BMStokesPairCoordinate w) P ^ 2 *
          d4BMCompletedPoincareVerticalSecondJet (d4BMStokesPairCoordinate w) Q)
      (d4BMStokesCompactCell Y)
  fun_prop

def d4BMActualFirstStokesTotalDivergenceAt
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) (w : ℝ × ℝ) : ℂ :=
  d4BMActualFirstStokesHorizontalDivergenceAt P Q w.1 w.2 +
    d4BMActualFirstStokesVerticalDivergenceAt P Q w.1 w.2

theorem continuousOn_d4BMActualFirstStokesTotalDivergence_stokesCompactCell
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) {Y : ℝ} :
    ContinuousOn (d4BMActualFirstStokesTotalDivergenceAt P Q)
      (d4BMStokesCompactCell Y) := by
  exact
    (continuousOn_d4BMActualFirstStokesHorizontalDivergence_stokesCompactCell
      P Q (Y := Y)).add
    (continuousOn_d4BMActualFirstStokesVerticalDivergence_stokesCompactCell
      P Q (Y := Y))

def d4BMTruncatedModularDomain (Y : ℝ) : Set (ℝ × ℝ) :=
  d4BMStokesCompactCell Y ∩
    {w : ℝ × ℝ | d4BMModularArcHeight w.1 ≤ w.2}

theorem isCompact_d4BMTruncatedModularDomain (Y : ℝ) :
    IsCompact (d4BMTruncatedModularDomain Y) := by
  unfold d4BMTruncatedModularDomain d4BMStokesCompactCell
  apply (isCompact_Icc.prod isCompact_Icc).inter_right
  exact isClosed_le
    (continuous_d4BMModularArcHeight.comp continuous_fst) continuous_snd

theorem d4BMTruncatedModularDomain_subset_stokesCompactCell (Y : ℝ) :
    d4BMTruncatedModularDomain Y ⊆ d4BMStokesCompactCell Y := by
  intro w hw
  exact hw.1

theorem integrableOn_d4BMActualFirstStokesTotalDivergence_truncatedDomain
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) (Y : ℝ) :
    IntegrableOn (d4BMActualFirstStokesTotalDivergenceAt P Q)
      (d4BMTruncatedModularDomain Y) := by
  apply ContinuousOn.integrableOn_compact (isCompact_d4BMTruncatedModularDomain Y)
  exact (continuousOn_d4BMActualFirstStokesTotalDivergence_stokesCompactCell
    P Q (Y := Y)).mono (d4BMTruncatedModularDomain_subset_stokesCompactCell Y)

def d4BMActualFirstStokesTruncatedDefectMoment
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) (Y : ℝ) : ℂ :=
  ∫ w in d4BMTruncatedModularDomain Y,
    (2 * d4BMActualFirstStokesDefectDensity (d4BMStokesPairCoordinate w) P Q) /
      (w.2 : ℂ) ^ 2

/-- The standard hyperbolic first-defect moment is the integral of the actual Euclidean
divergence on the genuine truncated modular domain. -/
theorem d4BM_actualFirstStokesTruncatedDefectMoment_eq_totalDivergence
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter)
    {Y : ℝ} (_hY : 1 ≤ Y) :
    d4BMActualFirstStokesTruncatedDefectMoment P Q Y =
      ∫ w in d4BMTruncatedModularDomain Y,
        d4BMActualFirstStokesTotalDivergenceAt P Q w := by
  unfold d4BMActualFirstStokesTruncatedDefectMoment
  apply MeasureTheory.setIntegral_congr_fun
    (isCompact_d4BMTruncatedModularDomain Y).measurableSet
  intro w hw
  have hwcell := (d4BMTruncatedModularDomain_subset_stokesCompactCell Y) hw
  have hy : (1 / 2 : ℝ) ≤ w.2 := hwcell.2.1
  exact d4BM_actualFirstStokesDefectDensity_div_heightSq_eq_divergenceAt
    P Q w.1 w.2 hy

def d4BMTruncatedVerticalSetSlice
    (f : ℝ × ℝ → ℂ) (Y x : ℝ) : ℂ :=
  ∫ y in Set.Icc (d4BMModularArcHeight x) Y, f (x, y)

private theorem integral_indicator_d4BMTruncatedModularDomain_verticalSlice
    (f : ℝ × ℝ → ℂ) (Y x : ℝ) :
    (∫ y, (d4BMTruncatedModularDomain Y).indicator f (x, y)) =
      (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator
        (d4BMTruncatedVerticalSetSlice f Y) x := by
  by_cases hx : x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2)
  · rw [Set.indicator_of_mem hx]
    have hfun :
        (fun y : ℝ => (d4BMTruncatedModularDomain Y).indicator f (x, y)) =
          (Set.Icc (d4BMModularArcHeight x) Y).indicator (fun y => f (x, y)) := by
      funext y
      by_cases hy : y ∈ Set.Icc (d4BMModularArcHeight x) Y
      · have hyhalf : (1 / 2 : ℝ) ≤ y :=
          (d4BMModularArcHeight_half_le hx).trans hy.1
        have hmem : (x, y) ∈ d4BMTruncatedModularDomain Y := by
          exact ⟨⟨hx, ⟨hyhalf, hy.2⟩⟩, hy.1⟩
        rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hy]
      · have hnotmem : (x, y) ∉ d4BMTruncatedModularDomain Y := by
          intro hw
          apply hy
          exact ⟨hw.2, hw.1.2.2⟩
        rw [Set.indicator_of_notMem hnotmem, Set.indicator_of_notMem hy]
    rw [hfun, MeasureTheory.integral_indicator measurableSet_Icc]
    rfl
  · rw [Set.indicator_of_notMem hx]
    have hzero :
        (fun y : ℝ => (d4BMTruncatedModularDomain Y).indicator f (x, y)) = 0 := by
      funext y
      have hnotmem : (x, y) ∉ d4BMTruncatedModularDomain Y := by
        intro hw
        exact hx hw.1.1
      rw [Set.indicator_of_notMem hnotmem]
      rfl
    rw [hzero]
    simp

private theorem setIntegral_d4BMTruncatedModularDomain_eq_indicator_prod
    (f : ℝ × ℝ → ℂ) (Y : ℝ) :
    (∫ w in d4BMTruncatedModularDomain Y, f w) =
      ∫ w, (d4BMTruncatedModularDomain Y).indicator f w
        ∂(volume.prod volume) := by
  calc
    (∫ w in d4BMTruncatedModularDomain Y, f w) =
        ∫ w in d4BMTruncatedModularDomain Y, f w ∂(volume.prod volume) := by
      rw [← MeasureTheory.Measure.volume_eq_prod]
    _ = ∫ w, (d4BMTruncatedModularDomain Y).indicator f w
          ∂(volume.prod volume) := by
      rw [MeasureTheory.integral_indicator
        (isCompact_d4BMTruncatedModularDomain Y).measurableSet]

private theorem integral_indicator_d4BMTruncatedModularDomain_eq_iterated
    {f : ℝ × ℝ → ℂ} {Y : ℝ}
    (hf : IntegrableOn f (d4BMTruncatedModularDomain Y)) :
    (∫ w, (d4BMTruncatedModularDomain Y).indicator f w
        ∂(volume.prod volume)) =
      ∫ x, ∫ y, (d4BMTruncatedModularDomain Y).indicator f (x, y) := by
  have hfprod : IntegrableOn f (d4BMTruncatedModularDomain Y)
      (volume.prod volume) := by
    simpa only [← MeasureTheory.Measure.volume_eq_prod] using hf
  have hind := hfprod.integrable_indicator
    (isCompact_d4BMTruncatedModularDomain Y).measurableSet
  exact MeasureTheory.integral_prod
    ((d4BMTruncatedModularDomain Y).indicator f) hind

set_option maxHeartbeats 800000 in
private theorem iterated_indicator_d4BMTruncatedModularDomain_eq_outerIndicator
    (f : ℝ × ℝ → ℂ) (Y : ℝ) :
    (∫ x, ∫ y, (d4BMTruncatedModularDomain Y).indicator f (x, y)) =
      ∫ x, (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator
        (d4BMTruncatedVerticalSetSlice f Y) x := by
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall
    (integral_indicator_d4BMTruncatedModularDomain_verticalSlice f Y)

private theorem integral_outerIndicator_d4BMTruncatedModularDomain_eq_setSlices
    (f : ℝ × ℝ → ℂ) (Y : ℝ) :
    (∫ x, (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator
        (d4BMTruncatedVerticalSetSlice f Y) x) =
      ∫ x in Set.Icc (-(1 / 2 : ℝ)) (1 / 2),
        d4BMTruncatedVerticalSetSlice f Y x := by
  rw [MeasureTheory.integral_indicator measurableSet_Icc]

private theorem setIntegral_d4BMTruncatedModularDomain_eq_verticalSetSlices
    {f : ℝ × ℝ → ℂ} {Y : ℝ}
    (hf : IntegrableOn f (d4BMTruncatedModularDomain Y)) :
    (∫ w in d4BMTruncatedModularDomain Y, f w) =
      ∫ x in Set.Icc (-(1 / 2 : ℝ)) (1 / 2),
        d4BMTruncatedVerticalSetSlice f Y x := by
  rw [setIntegral_d4BMTruncatedModularDomain_eq_indicator_prod f Y,
    integral_indicator_d4BMTruncatedModularDomain_eq_iterated hf,
    iterated_indicator_d4BMTruncatedModularDomain_eq_outerIndicator f Y,
    integral_outerIndicator_d4BMTruncatedModularDomain_eq_setSlices f Y]

private theorem verticalSetSlices_eq_intervalSlices
    (f : ℝ × ℝ → ℂ) {Y : ℝ} (hY : 1 ≤ Y) :
    (∫ x in Set.Icc (-(1 / 2 : ℝ)) (1 / 2),
        d4BMTruncatedVerticalSetSlice f Y x) =
      ∫ x in (-(1 / 2 : ℝ))..(1 / 2),
        ∫ y in d4BMModularArcHeight x..Y, f (x, y) := by
  rw [intervalIntegral.integral_of_le (by norm_num),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
  intro x hx
  have harcleY : d4BMModularArcHeight x ≤ Y :=
    (d4BMModularArcHeight_le_one hx).trans hY
  change (∫ y in Set.Icc (d4BMModularArcHeight x) Y, f (x, y)) =
    ∫ y in d4BMModularArcHeight x..Y, f (x, y)
  rw [intervalIntegral.integral_of_le harcleY,
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]

/-- Product-measure Fubini on the genuine curved truncated modular domain, in vertical-fibre
coordinates.  This is not a formal iterated-integral definition: the left side is the standard
two-dimensional set integral. -/
theorem d4BM_setIntegral_truncatedDomain_eq_verticalSlices
    {f : ℝ × ℝ → ℂ} {Y : ℝ} (hY : 1 ≤ Y)
    (hf : IntegrableOn f (d4BMTruncatedModularDomain Y)) :
    (∫ w in d4BMTruncatedModularDomain Y, f w) =
      ∫ x in (-(1 / 2 : ℝ))..(1 / 2),
        ∫ y in d4BMModularArcHeight x..Y, f (x, y) := by
  rw [setIntegral_d4BMTruncatedModularDomain_eq_verticalSetSlices hf,
    verticalSetSlices_eq_intervalSlices f hY]

def d4BMTruncatedHorizontalSlice (Y y : ℝ) : Set ℝ :=
  {x : ℝ | (x, y) ∈ d4BMTruncatedModularDomain Y}

def d4BMTruncatedHorizontalSetSlice
    (f : ℝ × ℝ → ℂ) (Y y : ℝ) : ℂ :=
  ∫ x in d4BMTruncatedHorizontalSlice Y y, f (x, y)

private theorem integral_indicator_d4BMTruncatedModularDomain_horizontalSlice
    (f : ℝ × ℝ → ℂ) (Y y : ℝ) :
    (∫ x, (d4BMTruncatedModularDomain Y).indicator f (x, y)) =
      d4BMTruncatedHorizontalSetSlice f Y y := by
  have hfun :
      (fun x : ℝ => (d4BMTruncatedModularDomain Y).indicator f (x, y)) =
        (d4BMTruncatedHorizontalSlice Y y).indicator (fun x => f (x, y)) := by
    funext x
    by_cases hx : (x, y) ∈ d4BMTruncatedModularDomain Y
    · have hxslice : x ∈ d4BMTruncatedHorizontalSlice Y y := hx
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hxslice]
    · have hxslice : x ∉ d4BMTruncatedHorizontalSlice Y y := hx
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hxslice]
  have hmeas : MeasurableSet (d4BMTruncatedHorizontalSlice Y y) :=
    (isCompact_d4BMTruncatedModularDomain Y).measurableSet.preimage
      (measurable_id.prodMk measurable_const)
  rw [hfun, MeasureTheory.integral_indicator hmeas]
  rfl

private theorem iterated_indicator_d4BMTruncatedModularDomain_swap
    {f : ℝ × ℝ → ℂ} {Y : ℝ}
    (hf : IntegrableOn f (d4BMTruncatedModularDomain Y)) :
    (∫ x, ∫ y, (d4BMTruncatedModularDomain Y).indicator f (x, y)) =
      ∫ y, ∫ x, (d4BMTruncatedModularDomain Y).indicator f (x, y) := by
  have hfprod : IntegrableOn f (d4BMTruncatedModularDomain Y)
      (volume.prod volume) := by
    simpa only [← MeasureTheory.Measure.volume_eq_prod] using hf
  have hind := hfprod.integrable_indicator
    (isCompact_d4BMTruncatedModularDomain Y).measurableSet
  exact MeasureTheory.integral_integral_swap hind

private theorem horizontal_iterated_indicator_eq_setSlices
    (f : ℝ × ℝ → ℂ) (Y : ℝ) :
    (∫ y, ∫ x, (d4BMTruncatedModularDomain Y).indicator f (x, y)) =
      ∫ y, d4BMTruncatedHorizontalSetSlice f Y y := by
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall
    (integral_indicator_d4BMTruncatedModularDomain_horizontalSlice f Y)

/-- Product-measure Fubini on the genuine curved truncated modular domain, now in horizontal-slice
coordinates.  Together with the vertical theorem this supplies both orders from one standard
two-dimensional integral. -/
theorem d4BM_setIntegral_truncatedDomain_eq_horizontalSetSlices
    {f : ℝ × ℝ → ℂ} {Y : ℝ}
    (hf : IntegrableOn f (d4BMTruncatedModularDomain Y)) :
    (∫ w in d4BMTruncatedModularDomain Y, f w) =
      ∫ y, d4BMTruncatedHorizontalSetSlice f Y y := by
  rw [setIntegral_d4BMTruncatedModularDomain_eq_indicator_prod f Y,
    integral_indicator_d4BMTruncatedModularDomain_eq_iterated hf,
    iterated_indicator_d4BMTruncatedModularDomain_swap hf,
    horizontal_iterated_indicator_eq_setSlices f Y]

theorem d4BMModularArcFloor_sq :
    d4BMModularArcFloor ^ 2 = (3 / 4 : ℝ) := by
  have h := d4BMModularArcHeight_sq
    (x := (1 / 2 : ℝ)) (by constructor <;> norm_num)
  change d4BMModularArcHeight (1 / 2 : ℝ) ^ 2 = 3 / 4
  convert h using 1 <;> norm_num

theorem d4BMModularArcFloor_le_arcHeight
    {x : ℝ} (hx : x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) :
    d4BMModularArcFloor ≤ d4BMModularArcHeight x := by
  have harcSq := d4BMModularArcHeight_sq hx
  have hxSq : x ^ 2 ≤ (1 / 4 : ℝ) := by
    nlinarith [hx.1, hx.2, sq_nonneg (x + 1 / 2), sq_nonneg (1 / 2 - x)]
  apply (sq_le_sq₀ (le_of_lt d4BMModularArcFloor_pos)
    (Real.sqrt_nonneg _)).1
  calc
    d4BMModularArcFloor ^ 2 = 3 / 4 := d4BMModularArcFloor_sq
    _ ≤ 1 - x ^ 2 := by nlinarith
    _ = d4BMModularArcHeight x ^ 2 := harcSq.symm

theorem d4BMModularSideRadius_sq_of_lowerHeight
    {y : ℝ} (hy : y ∈ Set.Icc d4BMModularArcFloor 1) :
    d4BMModularSideRadius y ^ 2 = 1 - y ^ 2 := by
  unfold d4BMModularSideRadius
  apply Real.sq_sqrt
  have hy0 : 0 ≤ y := (le_of_lt d4BMModularArcFloor_pos).trans hy.1
  nlinarith [hy.2]

theorem d4BMModularSideRadius_le_half
    {y : ℝ} (hy : y ∈ Set.Icc d4BMModularArcFloor 1) :
    d4BMModularSideRadius y ≤ (1 / 2 : ℝ) := by
  have hfloor0 : 0 ≤ d4BMModularArcFloor := le_of_lt d4BMModularArcFloor_pos
  have hy0 : 0 ≤ y := hfloor0.trans hy.1
  have hfloorYsq : d4BMModularArcFloor ^ 2 ≤ y ^ 2 :=
    (sq_le_sq₀ hfloor0 hy0).2 hy.1
  have hrSq := d4BMModularSideRadius_sq_of_lowerHeight hy
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 2)).1
  calc
    d4BMModularSideRadius y ^ 2 = 1 - y ^ 2 := hrSq
    _ ≤ (1 / 2 : ℝ) ^ 2 := by
      rw [d4BMModularArcFloor_sq] at hfloorYsq
      nlinarith

/-- Exact horizontal-slice geometry below height one: the circular exclusion is equivalent to
lying in one of the two side slivers. -/
theorem d4BMModularArcHeight_le_iff_side
    {x y : ℝ} (hx : x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2))
    (hy : y ∈ Set.Icc d4BMModularArcFloor 1) :
    d4BMModularArcHeight x ≤ y ↔
      x ≤ -d4BMModularSideRadius y ∨ d4BMModularSideRadius y ≤ x := by
  have harc0 : 0 ≤ d4BMModularArcHeight x := Real.sqrt_nonneg _
  have hy0 : 0 ≤ y := (le_of_lt d4BMModularArcFloor_pos).trans hy.1
  have hr0 : 0 ≤ d4BMModularSideRadius y := Real.sqrt_nonneg _
  have harcSq := d4BMModularArcHeight_sq hx
  have hrSq := d4BMModularSideRadius_sq_of_lowerHeight hy
  constructor
  · intro h
    have hsquare : d4BMModularArcHeight x ^ 2 ≤ y ^ 2 :=
      (sq_le_sq₀ harc0 hy0).2 h
    have hrx : d4BMModularSideRadius y ^ 2 ≤ x ^ 2 := by
      calc
        d4BMModularSideRadius y ^ 2 = 1 - y ^ 2 := hrSq
        _ ≤ x ^ 2 := by rw [harcSq] at hsquare; nlinarith
    have habs0 : |d4BMModularSideRadius y| ≤ |x| := (sq_le_sq).1 hrx
    have habs : d4BMModularSideRadius y ≤ |x| := by
      simpa [abs_of_nonneg hr0] using habs0
    by_cases hx0 : 0 ≤ x
    · exact Or.inr (by simpa [abs_of_nonneg hx0] using habs)
    · have hxnonpos : x ≤ 0 := le_of_not_ge hx0
      exact Or.inl (by rw [abs_of_nonpos hxnonpos] at habs; linarith)
  · intro h
    have habs : d4BMModularSideRadius y ≤ |x| := by
      rcases h with hleft | hright
      · have hxnonpos : x ≤ 0 := by linarith [hr0]
        rw [abs_of_nonpos hxnonpos]
        linarith
      · have hx0 : 0 ≤ x := hr0.trans hright
        simpa [abs_of_nonneg hx0] using hright
    have hrx : d4BMModularSideRadius y ^ 2 ≤ x ^ 2 := by
      apply (sq_le_sq).2
      simpa [abs_of_nonneg hr0] using habs
    have hsquare : d4BMModularArcHeight x ^ 2 ≤ y ^ 2 := by
      calc
        d4BMModularArcHeight x ^ 2 = 1 - x ^ 2 := harcSq
        _ ≤ y ^ 2 := by rw [hrSq] at hrx; nlinarith
    exact (sq_le_sq₀ harc0 hy0).1 hsquare

theorem d4BMTruncatedHorizontalSlice_eq_full
    {Y y : ℝ} (hy : y ∈ Set.Icc 1 Y) :
    d4BMTruncatedHorizontalSlice Y y =
      Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := by
  ext x
  constructor
  · intro hx
    exact hx.1.1
  · intro hx
    have hyhalf : (1 / 2 : ℝ) ≤ y := by linarith [hy.1]
    have harcle : d4BMModularArcHeight x ≤ y :=
      (d4BMModularArcHeight_le_one hx).trans hy.1
    exact ⟨⟨hx, ⟨hyhalf, hy.2⟩⟩, harcle⟩

theorem d4BMTruncatedHorizontalSlice_eq_sideSlivers
    {Y y : ℝ} (hY : 1 ≤ Y)
    (hy : y ∈ Set.Icc d4BMModularArcFloor 1) :
    d4BMTruncatedHorizontalSlice Y y =
      Set.Icc (-(1 / 2 : ℝ)) (-d4BMModularSideRadius y) ∪
        Set.Icc (d4BMModularSideRadius y) (1 / 2) := by
  ext x
  constructor
  · intro hx
    have hxstrip : x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := hx.1.1
    rcases (d4BMModularArcHeight_le_iff_side hxstrip hy).1 hx.2 with hleft | hright
    · exact Or.inl ⟨hxstrip.1, hleft⟩
    · exact Or.inr ⟨hright, hxstrip.2⟩
  · intro hx
    rcases hx with hxleft | hxright
    · have hxstrip : x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := by
        constructor
        · exact hxleft.1
        · have hr0 : 0 ≤ d4BMModularSideRadius y := Real.sqrt_nonneg _
          linarith [hxleft.2]
      have hyhalf : (1 / 2 : ℝ) ≤ y :=
        (le_of_lt d4BMModularArcFloor_gt_half).trans hy.1
      have hyY : y ≤ Y := hy.2.trans hY
      exact ⟨⟨hxstrip, ⟨hyhalf, hyY⟩⟩,
        (d4BMModularArcHeight_le_iff_side hxstrip hy).2 (Or.inl hxleft.2)⟩
    · have hxstrip : x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := by
        constructor
        · have hr0 : 0 ≤ d4BMModularSideRadius y := Real.sqrt_nonneg _
          linarith [hxright.1]
        · exact hxright.2
      have hyhalf : (1 / 2 : ℝ) ≤ y :=
        (le_of_lt d4BMModularArcFloor_gt_half).trans hy.1
      have hyY : y ≤ Y := hy.2.trans hY
      exact ⟨⟨hxstrip, ⟨hyhalf, hyY⟩⟩,
        (d4BMModularArcHeight_le_iff_side hxstrip hy).2 (Or.inr hxright.1)⟩

theorem continuous_d4BMActualFirstStokesHorizontalDivergenceAt_fixedHeight
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) (y : ℝ) :
    Continuous (fun x : ℝ =>
      d4BMActualFirstStokesHorizontalDivergenceAt P Q x y) := by
  have h := continuous_d4BMActualFirstStokesHorizontalDivergence_horizontal
    (d4BMStokesCoordinate 0 y) P Q
  simpa [d4BMActualFirstStokesHorizontalDivergenceAt,
    d4BMHorizontalCoordinate, d4BMStokesCoordinate] using h

theorem d4BMActualFirstStokesHorizontalSetSlice_eq_fullInterval
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter)
    {Y y : ℝ} (hy : y ∈ Set.Icc 1 Y) :
    d4BMTruncatedHorizontalSetSlice
        (fun w => d4BMActualFirstStokesHorizontalDivergenceAt P Q w.1 w.2) Y y =
      ∫ x in (-(1 / 2 : ℝ))..(1 / 2),
        d4BMActualFirstStokesHorizontalDivergenceAt P Q x y := by
  unfold d4BMTruncatedHorizontalSetSlice
  rw [d4BMTruncatedHorizontalSlice_eq_full hy,
    intervalIntegral.integral_of_le (by norm_num),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]

theorem d4BMActualFirstStokesHorizontalSetSlice_eq_sideIntervals
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter)
    {Y y : ℝ} (hY : 1 ≤ Y)
    (hy : y ∈ Set.Icc d4BMModularArcFloor 1) :
    d4BMTruncatedHorizontalSetSlice
        (fun w => d4BMActualFirstStokesHorizontalDivergenceAt P Q w.1 w.2) Y y =
      (∫ x in (-(1 / 2 : ℝ))..(-d4BMModularSideRadius y),
        d4BMActualFirstStokesHorizontalDivergenceAt P Q x y) +
      ∫ x in d4BMModularSideRadius y..(1 / 2),
        d4BMActualFirstStokesHorizontalDivergenceAt P Q x y := by
  let L : Set ℝ := Set.Icc (-(1 / 2 : ℝ)) (-d4BMModularSideRadius y)
  let R : Set ℝ := Set.Icc (d4BMModularSideRadius y) (1 / 2)
  let f : ℝ → ℂ := fun x =>
    d4BMActualFirstStokesHorizontalDivergenceAt P Q x y
  have hcont : Continuous f := by
    exact continuous_d4BMActualFirstStokesHorizontalDivergenceAt_fixedHeight P Q y
  have hLint : IntegrableOn f L :=
    hcont.continuousOn.integrableOn_compact isCompact_Icc
  have hRint : IntegrableOn f R :=
    hcont.continuousOn.integrableOn_compact isCompact_Icc
  have haedis : AEDisjoint volume L R := by
    unfold AEDisjoint
    apply MeasureTheory.measure_mono_null (t := ({0} : Set ℝ))
    · intro x hx
      have hr0 : 0 ≤ d4BMModularSideRadius y := Real.sqrt_nonneg _
      change x ∈ Set.Icc (-(1 / 2 : ℝ)) (-d4BMModularSideRadius y) ∧
        x ∈ Set.Icc (d4BMModularSideRadius y) (1 / 2) at hx
      simp only [Set.mem_singleton_iff]
      linarith [hx.1.2, hx.2.1]
    · exact MeasureTheory.measure_singleton 0
  have hrhalf := d4BMModularSideRadius_le_half hy
  unfold d4BMTruncatedHorizontalSetSlice
  rw [d4BMTruncatedHorizontalSlice_eq_sideSlivers hY hy]
  change (∫ x in L ∪ R, f x) = _
  rw [MeasureTheory.integral_union_ae haedis measurableSet_Icc.nullMeasurableSet
      hLint hRint,
    intervalIntegral.integral_of_le (by linarith : (-(1 / 2 : ℝ)) ≤
      -d4BMModularSideRadius y),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hrhalf,
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]

theorem d4BMTruncatedHorizontalSlice_eq_empty_of_not_mem
    {Y y : ℝ} (hy : y ∉ Set.Icc d4BMModularArcFloor Y) :
    d4BMTruncatedHorizontalSlice Y y = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  apply hy
  have hxstrip : x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := hx.1.1
  exact ⟨(d4BMModularArcFloor_le_arcHeight hxstrip).trans hx.2, hx.1.2.2⟩

theorem d4BMTruncatedHorizontalSetSlice_eq_zero_of_not_mem
    (f : ℝ × ℝ → ℂ) {Y y : ℝ}
    (hy : y ∉ Set.Icc d4BMModularArcFloor Y) :
    d4BMTruncatedHorizontalSetSlice f Y y = 0 := by
  unfold d4BMTruncatedHorizontalSetSlice
  rw [d4BMTruncatedHorizontalSlice_eq_empty_of_not_mem hy]
  simp

theorem integrable_d4BMTruncatedHorizontalSetSlice
    {f : ℝ × ℝ → ℂ} {Y : ℝ}
    (hf : IntegrableOn f (d4BMTruncatedModularDomain Y)) :
    Integrable (fun y => d4BMTruncatedHorizontalSetSlice f Y y) := by
  have hfprod : IntegrableOn f (d4BMTruncatedModularDomain Y)
      (volume.prod volume) := by
    simpa only [← MeasureTheory.Measure.volume_eq_prod] using hf
  have hind := hfprod.integrable_indicator
    (isCompact_d4BMTruncatedModularDomain Y).measurableSet
  have hright := hind.integral_prod_right
  exact hright.congr (Filter.Eventually.of_forall fun y =>
    integral_indicator_d4BMTruncatedModularDomain_horizontalSlice f Y y)

theorem integral_d4BMTruncatedHorizontalSetSlice_eq_interval
    (f : ℝ × ℝ → ℂ) {Y : ℝ} (hY : 1 ≤ Y) :
    (∫ y, d4BMTruncatedHorizontalSetSlice f Y y) =
      ∫ y in d4BMModularArcFloor..Y,
        d4BMTruncatedHorizontalSetSlice f Y y := by
  have hfloorOne : d4BMModularArcFloor ≤ 1 :=
    d4BMModularArcHeight_le_one (by constructor <;> norm_num)
  have hfloorY : d4BMModularArcFloor ≤ Y := hfloorOne.trans hY
  have hfun :
      (fun y => d4BMTruncatedHorizontalSetSlice f Y y) =
        (Set.Icc d4BMModularArcFloor Y).indicator
          (fun y => d4BMTruncatedHorizontalSetSlice f Y y) := by
    funext y
    by_cases hy : y ∈ Set.Icc d4BMModularArcFloor Y
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy,
        d4BMTruncatedHorizontalSetSlice_eq_zero_of_not_mem f hy]
  calc
    (∫ y, d4BMTruncatedHorizontalSetSlice f Y y) =
        ∫ y, (Set.Icc d4BMModularArcFloor Y).indicator
          (fun q => d4BMTruncatedHorizontalSetSlice f Y q) y := by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall fun y => congrFun hfun y
    _ = ∫ y in Set.Icc d4BMModularArcFloor Y,
          d4BMTruncatedHorizontalSetSlice f Y y := by
      rw [MeasureTheory.integral_indicator measurableSet_Icc]
    _ = ∫ y in d4BMModularArcFloor..Y,
          d4BMTruncatedHorizontalSetSlice f Y y := by
      rw [intervalIntegral.integral_of_le hfloorY,
        ← MeasureTheory.integral_Icc_eq_integral_Ioc]

theorem integrableOn_d4BMActualFirstStokesHorizontalDivergence_truncatedDomain
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) (Y : ℝ) :
    IntegrableOn
      (fun w : ℝ × ℝ =>
        d4BMActualFirstStokesHorizontalDivergenceAt P Q w.1 w.2)
      (d4BMTruncatedModularDomain Y) := by
  apply ContinuousOn.integrableOn_compact (isCompact_d4BMTruncatedModularDomain Y)
  exact (continuousOn_d4BMActualFirstStokesHorizontalDivergence_stokesCompactCell
    P Q (Y := Y)).mono (d4BMTruncatedModularDomain_subset_stokesCompactCell Y)

theorem integrableOn_d4BMActualFirstStokesVerticalDivergence_truncatedDomain
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) (Y : ℝ) :
    IntegrableOn
      (fun w : ℝ × ℝ =>
        d4BMActualFirstStokesVerticalDivergenceAt P Q w.1 w.2)
      (d4BMTruncatedModularDomain Y) := by
  apply ContinuousOn.integrableOn_compact (isCompact_d4BMTruncatedModularDomain Y)
  exact (continuousOn_d4BMActualFirstStokesVerticalDivergence_stokesCompactCell
    P Q (Y := Y)).mono (d4BMTruncatedModularDomain_subset_stokesCompactCell Y)

/-- Horizontal Fubini identification: the standard two-dimensional integral of the horizontal
actual divergence is exactly the lower-side-sliver plus upper-strip bulk already used by the
literal Green theorem. -/
theorem d4BM_setIntegral_horizontalDivergence_eq_horizontalBulk
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter)
    {Y : ℝ} (hY : 1 ≤ Y) :
    (∫ w in d4BMTruncatedModularDomain Y,
        d4BMActualFirstStokesHorizontalDivergenceAt P Q w.1 w.2) =
      d4BMActualFirstStokesHorizontalBulk P Q Y := by
  let f : ℝ × ℝ → ℂ := fun w =>
    d4BMActualFirstStokesHorizontalDivergenceAt P Q w.1 w.2
  let S : ℝ → ℂ := fun y => d4BMTruncatedHorizontalSetSlice f Y y
  have hf := integrableOn_d4BMActualFirstStokesHorizontalDivergence_truncatedDomain P Q Y
  have hSint : Integrable S := by
    exact integrable_d4BMTruncatedHorizontalSetSlice hf
  have hfloorOne : d4BMModularArcFloor ≤ 1 :=
    d4BMModularArcHeight_le_one (by constructor <;> norm_num)
  have hsplit :
      (∫ y in d4BMModularArcFloor..Y, S y) =
        (∫ y in d4BMModularArcFloor..1, S y) + ∫ y in 1..Y, S y := by
    exact (intervalIntegral.integral_add_adjacent_intervals
      hSint.intervalIntegrable hSint.intervalIntegrable).symm
  calc
    (∫ w in d4BMTruncatedModularDomain Y,
        d4BMActualFirstStokesHorizontalDivergenceAt P Q w.1 w.2) =
        ∫ y, S y := by
      exact d4BM_setIntegral_truncatedDomain_eq_horizontalSetSlices hf
    _ = ∫ y in d4BMModularArcFloor..Y, S y :=
      integral_d4BMTruncatedHorizontalSetSlice_eq_interval f hY
    _ = (∫ y in d4BMModularArcFloor..1, S y) + ∫ y in 1..Y, S y := hsplit
    _ = d4BMActualFirstStokesHorizontalLowerBulk P Q +
        d4BMActualFirstStokesHorizontalUpperBulk P Q Y := by
      congr 1
      · unfold d4BMActualFirstStokesHorizontalLowerBulk
        apply intervalIntegral.integral_congr
        intro y hy
        have hyI : y ∈ Set.Icc d4BMModularArcFloor 1 := by
          simpa [uIcc_of_le hfloorOne] using hy
        exact d4BMActualFirstStokesHorizontalSetSlice_eq_sideIntervals P Q hY hyI
      · unfold d4BMActualFirstStokesHorizontalUpperBulk
        apply intervalIntegral.integral_congr
        intro y hy
        have hyI : y ∈ Set.Icc 1 Y := by
          simpa [uIcc_of_le hY] using hy
        exact d4BMActualFirstStokesHorizontalSetSlice_eq_fullInterval P Q hyI
    _ = d4BMActualFirstStokesHorizontalBulk P Q Y := rfl

theorem d4BM_setIntegral_verticalDivergence_eq_verticalBulk
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter)
    {Y : ℝ} (hY : 1 ≤ Y) :
    (∫ w in d4BMTruncatedModularDomain Y,
        d4BMActualFirstStokesVerticalDivergenceAt P Q w.1 w.2) =
      d4BMActualFirstStokesVerticalBulk P Q Y := by
  unfold d4BMActualFirstStokesVerticalBulk
  exact d4BM_setIntegral_truncatedDomain_eq_verticalSlices hY
    (integrableOn_d4BMActualFirstStokesVerticalDivergence_truncatedDomain P Q Y)

theorem d4BM_setIntegral_totalDivergence_eq_horizontalBulk_add_verticalBulk
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter)
    {Y : ℝ} (hY : 1 ≤ Y) :
    (∫ w in d4BMTruncatedModularDomain Y,
        d4BMActualFirstStokesTotalDivergenceAt P Q w) =
      d4BMActualFirstStokesHorizontalBulk P Q Y +
        d4BMActualFirstStokesVerticalBulk P Q Y := by
  have hH := integrableOn_d4BMActualFirstStokesHorizontalDivergence_truncatedDomain P Q Y
  have hV := integrableOn_d4BMActualFirstStokesVerticalDivergence_truncatedDomain P Q Y
  unfold d4BMActualFirstStokesTotalDivergenceAt
  rw [MeasureTheory.integral_add hH hV,
    d4BM_setIntegral_horizontalDivergence_eq_horizontalBulk P Q hY,
    d4BM_setIntegral_verticalDivergence_eq_verticalBulk P Q hY]

/-- The standard hyperbolic actual first-defect moment is exactly the coordinate-split literal
Green bulk.  This is the Fubini bridge absent from the prior boundary proof. -/
theorem d4BM_actualFirstStokesTruncatedDefectMoment_eq_horizontalBulk_add_verticalBulk
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter)
    {Y : ℝ} (hY : 1 ≤ Y) :
    d4BMActualFirstStokesTruncatedDefectMoment P Q Y =
      d4BMActualFirstStokesHorizontalBulk P Q Y +
        d4BMActualFirstStokesVerticalBulk P Q Y := by
  rw [d4BM_actualFirstStokesTruncatedDefectMoment_eq_totalDivergence P Q hY,
    d4BM_setIntegral_totalDivergence_eq_horizontalBulk_add_verticalBulk P Q hY]

theorem continuousOn_d4BMActualFirstStokesHorizontalCurrent_stokesCompactCell
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) {Y : ℝ} :
    ContinuousOn
      (fun w : ℝ × ℝ => d4BMActualFirstStokesHorizontalCurrentAt P Q w.1 w.2)
      (d4BMStokesCompactCell Y) := by
  have hF := continuousOn_d4BMCompletedEisensteinPoincareSeries_stokesCompactCell
    P (Y := Y)
  have hG := continuousOn_d4BMCompletedEisensteinPoincareSeries_stokesCompactCell
    Q (Y := Y)
  have hFx := continuousOn_d4BMCompletedPoincareHorizontalFirstJet_stokesCompactCell
    P (Y := Y)
  have hGx := continuousOn_d4BMCompletedPoincareHorizontalFirstJet_stokesCompactCell
    Q (Y := Y)
  unfold d4BMActualFirstStokesHorizontalCurrentAt d4BMActualFirstStokesHorizontalCurrent
  change ContinuousOn
    (fun w : ℝ × ℝ =>
      2 * d4BMCompletedEisensteinPoincareSeries (d4BMStokesPairCoordinate w) P *
          d4BMCompletedEisensteinPoincareSeries (d4BMStokesPairCoordinate w) Q *
          d4BMCompletedPoincareHorizontalFirstJet (d4BMStokesPairCoordinate w) P -
        d4BMCompletedEisensteinPoincareSeries (d4BMStokesPairCoordinate w) P ^ 2 *
          d4BMCompletedPoincareHorizontalFirstJet (d4BMStokesPairCoordinate w) Q)
      (d4BMStokesCompactCell Y)
  fun_prop

theorem continuousOn_d4BMActualFirstStokesVerticalCurrent_stokesCompactCell
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) {Y : ℝ} :
    ContinuousOn
      (fun w : ℝ × ℝ => d4BMActualFirstStokesVerticalCurrentAt P Q w.1 w.2)
      (d4BMStokesCompactCell Y) := by
  have hF := continuousOn_d4BMCompletedEisensteinPoincareSeries_stokesCompactCell
    P (Y := Y)
  have hG := continuousOn_d4BMCompletedEisensteinPoincareSeries_stokesCompactCell
    Q (Y := Y)
  have hFy := continuousOn_d4BMCompletedPoincareVerticalFirstJet_stokesCompactCell
    P (Y := Y)
  have hGy := continuousOn_d4BMCompletedPoincareVerticalFirstJet_stokesCompactCell
    Q (Y := Y)
  unfold d4BMActualFirstStokesVerticalCurrentAt d4BMActualFirstStokesVerticalCurrent
  change ContinuousOn
    (fun w : ℝ × ℝ =>
      2 * d4BMCompletedEisensteinPoincareSeries (d4BMStokesPairCoordinate w) P *
          d4BMCompletedEisensteinPoincareSeries (d4BMStokesPairCoordinate w) Q *
          d4BMCompletedPoincareVerticalFirstJet (d4BMStokesPairCoordinate w) P -
        d4BMCompletedEisensteinPoincareSeries (d4BMStokesPairCoordinate w) P ^ 2 *
          d4BMCompletedPoincareVerticalFirstJet (d4BMStokesPairCoordinate w) Q)
      (d4BMStokesCompactCell Y)
  fun_prop

def d4BMActualFirstStokesVerticalBoundaryIntegrand
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) (Y x : ℝ) : ℂ :=
  d4BMActualFirstStokesVerticalCurrentAt P Q x Y -
    d4BMActualFirstStokesVerticalCurrentAt P Q x (d4BMModularArcHeight x)

theorem continuousOn_d4BMActualFirstStokesVerticalBoundaryIntegrand
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter)
    {Y : ℝ} (hY : 1 ≤ Y) :
    ContinuousOn (d4BMActualFirstStokesVerticalBoundaryIntegrand P Q Y)
      (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) := by
  let I : Set ℝ := Set.Icc (-(1 / 2 : ℝ)) (1 / 2)
  have hcurrent := continuousOn_d4BMActualFirstStokesVerticalCurrent_stokesCompactCell
    P Q (Y := Y)
  have htopMap : ContinuousOn (fun x : ℝ => (x, Y)) I :=
    (continuous_id.prodMk continuous_const).continuousOn
  have htopTo : MapsTo (fun x : ℝ => (x, Y)) I (d4BMStokesCompactCell Y) := by
    intro x hx
    exact ⟨hx, ⟨by linarith, le_rfl⟩⟩
  have htop := hcurrent.comp htopMap htopTo
  have harcMap : ContinuousOn (fun x : ℝ => (x, d4BMModularArcHeight x)) I :=
    (continuous_id.prodMk continuous_d4BMModularArcHeight).continuousOn
  have harcTo : MapsTo (fun x : ℝ => (x, d4BMModularArcHeight x)) I
      (d4BMStokesCompactCell Y) := by
    intro x hx
    exact ⟨hx, ⟨d4BMModularArcHeight_half_le hx,
      (d4BMModularArcHeight_le_one hx).trans hY⟩⟩
  have harc := hcurrent.comp harcMap harcTo
  unfold d4BMActualFirstStokesVerticalBoundaryIntegrand
  exact htop.sub harc

theorem intervalIntegral_d4BMActualFirstStokesVerticalBoundaryIntegrand_fold
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter)
    {Y : ℝ} (hY : 1 ≤ Y) :
    (∫ x in (-(1 / 2 : ℝ))..(1 / 2),
        d4BMActualFirstStokesVerticalBoundaryIntegrand P Q Y x) =
      ∫ x in 0..(1 / 2),
        (d4BMActualFirstStokesVerticalBoundaryIntegrand P Q Y (-x) +
          d4BMActualFirstStokesVerticalBoundaryIntegrand P Q Y x) := by
  let B := d4BMActualFirstStokesVerticalBoundaryIntegrand P Q Y
  have hB := continuousOn_d4BMActualFirstStokesVerticalBoundaryIntegrand P Q hY
  have hleft : IntervalIntegrable B volume (-(1 / 2 : ℝ)) 0 :=
    (hB.mono (by
      intro x hx
      have hxI : x ∈ Set.Icc (-(1 / 2 : ℝ)) 0 := by
        simpa [uIcc_of_le (by norm_num : (-(1 / 2 : ℝ)) ≤ 0)] using hx
      exact ⟨hxI.1, hxI.2.trans (by norm_num)⟩)).intervalIntegrable
  have hright : IntervalIntegrable B volume 0 (1 / 2) :=
    (hB.mono (by
      intro x hx
      have hxI : x ∈ Set.Icc 0 (1 / 2 : ℝ) := by
        simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] using hx
      exact ⟨(by linarith [hxI.1]), hxI.2⟩)).intervalIntegrable
  have hnegCont : ContinuousOn (fun x : ℝ => B (-x)) (Set.Icc 0 (1 / 2)) := by
    exact hB.comp (continuous_neg.comp continuous_id).continuousOn (by
      intro x hx
      constructor <;> linarith [hx.1, hx.2])
  have hneg : IntervalIntegrable (fun x : ℝ => B (-x)) volume 0 (1 / 2) :=
    (by
      have h : ContinuousOn (fun x : ℝ => B (-x)) (uIcc 0 (1 / 2)) := by
        simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] using hnegCont
      exact h.intervalIntegrable)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hleft hright
  have hreflect := intervalIntegral.integral_comp_neg
    (a := (0 : ℝ)) (b := (1 / 2 : ℝ)) B
  change (∫ x in (-(1 / 2 : ℝ))..(1 / 2), B x) = _
  calc
    (∫ x in (-(1 / 2 : ℝ))..(1 / 2), B x) =
        (∫ x in (-(1 / 2 : ℝ))..0, B x) + ∫ x in 0..(1 / 2), B x := hsplit.symm
    _ = (∫ x in 0..(1 / 2), B (-x)) + ∫ x in 0..(1 / 2), B x := by
      rw [hreflect]
      norm_num
    _ = ∫ x in 0..(1 / 2), (B (-x) + B x) := by
      rw [intervalIntegral.integral_add hneg hright]

theorem d4BMModularArcHeight_neg (x : ℝ) :
    d4BMModularArcHeight (-x) = d4BMModularArcHeight x := by
  simp [d4BMModularArcHeight]

theorem continuousOn_d4BMActualFirstStokesHorizontalArcParameterFlux
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) :
    ContinuousOn (d4BMActualFirstStokesHorizontalArcParameterFlux P Q)
      (Set.Icc (0 : ℝ) (1 / 2)) := by
  let I : Set ℝ := Set.Icc (0 : ℝ) (1 / 2)
  have hcurrent := continuousOn_d4BMActualFirstStokesHorizontalCurrent_stokesCompactCell
    P Q (Y := (1 : ℝ))
  have harcC : ContinuousOn d4BMModularArcHeight I :=
    continuous_d4BMModularArcHeight.continuousOn
  have hratio : ContinuousOn (fun x : ℝ => x / d4BMModularArcHeight x) I := by
    exact continuous_id.continuousOn.div₀ harcC fun x hx =>
      (d4BMModularArcHeight_pos_of_mem
        ⟨by linarith [hx.1], hx.2⟩).ne'
  have hposMap : ContinuousOn (fun x : ℝ => (x, d4BMModularArcHeight x)) I :=
    (continuous_id.prodMk continuous_d4BMModularArcHeight).continuousOn
  have hposTo : MapsTo (fun x : ℝ => (x, d4BMModularArcHeight x)) I
      (d4BMStokesCompactCell 1) := by
    intro x hx
    have hxfull : x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) :=
      ⟨by linarith [hx.1], hx.2⟩
    exact ⟨hxfull, ⟨d4BMModularArcHeight_half_le hxfull,
      d4BMModularArcHeight_le_one hxfull⟩⟩
  have hpos := hcurrent.comp hposMap hposTo
  have hnegMap : ContinuousOn (fun x : ℝ => (-x, d4BMModularArcHeight x)) I :=
    (continuous_neg.comp continuous_id).prodMk continuous_d4BMModularArcHeight |>.continuousOn
  have hnegTo : MapsTo (fun x : ℝ => (-x, d4BMModularArcHeight x)) I
      (d4BMStokesCompactCell 1) := by
    intro x hx
    have hxfull : -x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) :=
      ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have hxposfull : x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) :=
      ⟨by linarith [hx.1], hx.2⟩
    exact ⟨hxfull, ⟨d4BMModularArcHeight_half_le hxposfull,
      d4BMModularArcHeight_le_one hxposfull⟩⟩
  have hneg := hcurrent.comp hnegMap hnegTo
  unfold d4BMActualFirstStokesHorizontalArcParameterFlux
  exact hratio.smul (hneg.sub hpos)

/-- Closed compact-cell Green theorem for the standard horizontal-plus-vertical bulk: arc
inversion cancels the full circular boundary after Fubini, leaving exactly the paired cusp top. -/
theorem d4BM_actualFirstStokesHorizontalBulk_add_verticalBulk_eq_pairedCuspTop
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter)
    {Y : ℝ} (hY : 1 ≤ Y) :
    d4BMActualFirstStokesHorizontalBulk P Q Y +
        d4BMActualFirstStokesVerticalBulk P Q Y =
      d4BMActualFirstStokesPairedCuspTop P Q Y := by
  let H : ℝ → ℂ := d4BMActualFirstStokesHorizontalArcParameterFlux P Q
  let B : ℝ → ℂ := d4BMActualFirstStokesVerticalBoundaryIntegrand P Q Y
  let T : ℝ → ℂ := fun x =>
    d4BMActualFirstStokesVerticalCurrentAt P Q (-x) Y +
      d4BMActualFirstStokesVerticalCurrentAt P Q x Y
  have hHbulk : d4BMActualFirstStokesHorizontalBulk P Q Y =
      ∫ x in 0..(1 / 2), H x := by
    calc
      d4BMActualFirstStokesHorizontalBulk P Q Y =
          ∫ y in d4BMModularArcFloor..1,
            d4BMActualFirstStokesHorizontalArcHeightFlux P Q y :=
        d4BM_actualFirstStokesHorizontalBulk_eq_arc P Q hY
      _ = ∫ x in 0..(1 / 2), H x := by
        exact d4BM_actualFirstStokesHorizontalArc_changeOfVariables P Q
  have hVbulk : d4BMActualFirstStokesVerticalBulk P Q Y =
      ∫ x in 0..(1 / 2), (B (-x) + B x) := by
    rw [d4BM_actualFirstStokesVerticalBulk_eq_boundary P Q hY]
    change (∫ x in (-(1 / 2 : ℝ))..(1 / 2), B x) = _
    exact intervalIntegral_d4BMActualFirstStokesVerticalBoundaryIntegrand_fold P Q hY
  have hHcont := continuousOn_d4BMActualFirstStokesHorizontalArcParameterFlux P Q
  have hHint : IntervalIntegrable H volume 0 (1 / 2) := by
    have h : ContinuousOn H (uIcc 0 (1 / 2)) := by
      simpa [H, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] using hHcont
    exact h.intervalIntegrable
  have hBcont := continuousOn_d4BMActualFirstStokesVerticalBoundaryIntegrand P Q hY
  have hBpairCont : ContinuousOn (fun x : ℝ => B (-x) + B x)
      (Set.Icc 0 (1 / 2)) := by
    have hnegTo : MapsTo (fun x : ℝ => -x) (Set.Icc 0 (1 / 2))
        (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) := by
      intro x hx
      constructor <;> linarith [hx.1, hx.2]
    have hneg := hBcont.comp
      (continuous_neg.comp continuous_id).continuousOn hnegTo
    have hpos := hBcont.mono (by
      intro (x : ℝ) (hx : x ∈ Set.Icc 0 (1 / 2))
      constructor <;> linarith [hx.1, hx.2])
    exact hneg.add hpos
  have hBpairInt : IntervalIntegrable (fun x : ℝ => B (-x) + B x)
      volume 0 (1 / 2) := by
    have h : ContinuousOn (fun x : ℝ => B (-x) + B x) (uIcc 0 (1 / 2)) := by
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] using hBpairCont
    exact h.intervalIntegrable
  have hadd := intervalIntegral.integral_add hHint hBpairInt
  calc
    d4BMActualFirstStokesHorizontalBulk P Q Y +
        d4BMActualFirstStokesVerticalBulk P Q Y =
        (∫ x in 0..(1 / 2), H x) +
          ∫ x in 0..(1 / 2), (B (-x) + B x) := by rw [hHbulk, hVbulk]
    _ = ∫ x in 0..(1 / 2), (H x + (B (-x) + B x)) := hadd.symm
    _ = ∫ x in 0..(1 / 2), T x := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hxI : x ∈ Set.Icc (0 : ℝ) (1 / 2) := by
        simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] using hx
      have hflux := d4BM_actualFirstStokesCircularBoundaryFlux_eq_zero P Q hxI
      dsimp only [H, B, T, d4BMActualFirstStokesVerticalBoundaryIntegrand]
      rw [d4BMModularArcHeight_neg]
      unfold d4BMActualFirstStokesCircularBoundaryFlux at hflux
      unfold d4BMActualFirstStokesHorizontalArcParameterFlux
      linear_combination hflux
    _ = d4BMActualFirstStokesPairedCuspTop P Q Y := rfl

/-- **C-A.9t3d: standard truncated first-moment reduction.**  The actual hyperbolic defect,
integrated with the standard two-dimensional Lebesgue measure on the truncated modular domain,
equals the genuine paired cusp-top Green current. -/
theorem d4BM_actualFirstStokesTruncatedDefectMoment_eq_pairedCuspTop
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter)
    {Y : ℝ} (hY : 1 ≤ Y) :
    d4BMActualFirstStokesTruncatedDefectMoment P Q Y =
      d4BMActualFirstStokesPairedCuspTop P Q Y := by
  rw [d4BM_actualFirstStokesTruncatedDefectMoment_eq_horizontalBulk_add_verticalBulk
      P Q hY,
    d4BM_actualFirstStokesHorizontalBulk_add_verticalBulk_eq_pairedCuspTop P Q hY]

/-- The standard two-dimensional defect moment and the earlier literal paired-coordinate Green
bulk are exactly the same object.  This closes the analytic Fubini/regularization gap rather than
introducing a second notion of truncated moment. -/
theorem d4BM_actualFirstStokesTruncatedDefectMoment_eq_pairedTruncatedBulk
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter)
    {Y : ℝ} (hY : 1 ≤ Y) :
    d4BMActualFirstStokesTruncatedDefectMoment P Q Y =
      d4BMActualFirstStokesPairedTruncatedBulk P Q Y := by
  rw [d4BM_actualFirstStokesTruncatedDefectMoment_eq_pairedCuspTop P Q hY,
    d4BM_actualFirstStokesPairedTruncatedBulk_eq_cuspTop P Q hY]

end
end RHTower
