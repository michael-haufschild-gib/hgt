import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinActualFirstStokesIntegral
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

private theorem integral_indicator_d4BMTruncatedModularDomain_verticalSlice
    (f : ℝ × ℝ → ℂ) (Y x : ℝ) :
    (∫ y, (d4BMTruncatedModularDomain Y).indicator f (x, y)) =
      (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator
        (fun _ => ∫ y in Set.Icc (d4BMModularArcHeight x) Y, f (x, y)) x := by
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

private theorem setIntegral_d4BMTruncatedModularDomain_eq_verticalSetSlices
    {f : ℝ × ℝ → ℂ} {Y : ℝ}
    (hf : IntegrableOn f (d4BMTruncatedModularDomain Y)) :
    (∫ w in d4BMTruncatedModularDomain Y, f w) =
      ∫ x in Set.Icc (-(1 / 2 : ℝ)) (1 / 2),
        ∫ y in Set.Icc (d4BMModularArcHeight x) Y, f (x, y) := by
  let D : Set (ℝ × ℝ) := d4BMTruncatedModularDomain Y
  have hD : MeasurableSet D := (isCompact_d4BMTruncatedModularDomain Y).measurableSet
  have hfprod : IntegrableOn f D (volume.prod volume) := by
    simpa only [D, ← MeasureTheory.Measure.volume_eq_prod] using hf
  have hind : Integrable (D.indicator f) (volume.prod volume) :=
    hfprod.integrable_indicator hD
  have hslice (x : ℝ) :
      (∫ y, D.indicator f (x, y)) =
        (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator
          (fun _ => ∫ y in Set.Icc (d4BMModularArcHeight x) Y, f (x, y)) x := by
    exact integral_indicator_d4BMTruncatedModularDomain_verticalSlice f Y x
  calc
    (∫ w in d4BMTruncatedModularDomain Y, f w) =
        ∫ w in D, f w ∂(volume.prod volume) := by
      rw [← MeasureTheory.Measure.volume_eq_prod]
    _ = ∫ w, D.indicator f w ∂(volume.prod volume) := by
      rw [MeasureTheory.integral_indicator hD]
    _ = ∫ x, ∫ y, D.indicator f (x, y) :=
      MeasureTheory.integral_prod (D.indicator f) hind
    _ = ∫ x, (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator
          (fun q => ∫ y in Set.Icc (d4BMModularArcHeight q) Y, f (q, y)) x := by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall hslice
    _ = ∫ x in Set.Icc (-(1 / 2 : ℝ)) (1 / 2),
          ∫ y in Set.Icc (d4BMModularArcHeight x) Y, f (x, y) := by
      rw [MeasureTheory.integral_indicator measurableSet_Icc]

private theorem verticalSetSlices_eq_intervalSlices
    (f : ℝ × ℝ → ℂ) {Y : ℝ} (hY : 1 ≤ Y) :
    (∫ x in Set.Icc (-(1 / 2 : ℝ)) (1 / 2),
        ∫ y in Set.Icc (d4BMModularArcHeight x) Y, f (x, y)) =
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

end
end RHTower
