import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEisensteinActualFirstStokesFubini
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEisensteinActualSecondStokesBoundaryCancellation

open Complex Real Filter Set Topology MeasureTheory
open scoped Interval

/-!
# Literal modular Green--Stokes theorem for the actual second defect

Corpus conjecture C-A.9t4d closes exact standard-measure integration premise left by the
pointwise Bochner current and boundary cancellation. Genuine mixed and third Poincare jets are
jointly continuous by compact-cell normal convergence; Fubini and one-dimensional FTC then turn
the standard truncated hyperbolic defect moment into the actual cusp boundary current.

RH chain:

`literal second Green/Stokes + standard-measure Fubini -> actual balanced BM ++- coefficient ->
negative BM leg -> conserved left-QNM projection -> HC94 -> RH`.
-/

namespace RHTower
noncomputable section

theorem continuous_d4BMPoincareSeedHorizontalThirdJet_stokesPair
    (s : ℂ) (p : D4BMPrimitiveIntegerPair) :
    Continuous (fun w : ℝ × ℝ =>
      d4BMPoincareSeedHorizontalThirdJet (d4BMStokesPairCoordinate w) s p) := by
  have hQ : Continuous (fun w : ℝ × ℝ =>
      (d4BMPoincareQuadratic (d4BMStokesPairCoordinate w) p.pair : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_d4BMPoincareQuadratic_stokesPair p)
  have hL : Continuous (fun w : ℝ × ℝ =>
      (d4BMPoincareHorizontalLinear (d4BMStokesPairCoordinate w) p : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_d4BMPoincareHorizontalLinear_stokesPair p)
  have hQne (w : ℝ × ℝ) :
      (d4BMPoincareQuadratic (d4BMStokesPairCoordinate w) p.pair : ℂ) ≠ 0 := by
    exact_mod_cast (d4BMPoincareQuadratic_pos
      (d4BMStokesPairCoordinate w) p.pair p.pair_ne_zero).ne'
  have hA1 : Continuous (fun w : ℝ × ℝ =>
      4 * s * (p.pair.1 : ℂ) ^ (3 : ℕ) *
        (d4BMPoincareHorizontalLinear (d4BMStokesPairCoordinate w) p : ℂ) /
        (d4BMPoincareQuadratic (d4BMStokesPairCoordinate w) p.pair : ℂ) ^ (2 : ℕ)) := by
    exact (hL.const_mul (4 * s * (p.pair.1 : ℂ) ^ (3 : ℕ))).div₀
      (hQ.pow 2) fun w => pow_ne_zero 2 (hQne w)
  have hA2 : Continuous (fun w : ℝ × ℝ =>
      8 * s * (s + 1) * (p.pair.1 : ℂ) ^ (3 : ℕ) *
        (d4BMPoincareHorizontalLinear (d4BMStokesPairCoordinate w) p : ℂ) /
        (d4BMPoincareQuadratic (d4BMStokesPairCoordinate w) p.pair : ℂ) ^ (2 : ℕ)) := by
    exact (hL.const_mul (8 * s * (s + 1) * (p.pair.1 : ℂ) ^ (3 : ℕ))).div₀
      (hQ.pow 2) fun w => pow_ne_zero 2 (hQne w)
  have hA3 : Continuous (fun w : ℝ × ℝ =>
      16 * s * (s + 1) * (p.pair.1 : ℂ) ^ (3 : ℕ) *
        (d4BMPoincareHorizontalLinear (d4BMStokesPairCoordinate w) p : ℂ) ^ (3 : ℕ) /
        (d4BMPoincareQuadratic (d4BMStokesPairCoordinate w) p.pair : ℂ) ^ (3 : ℕ)) := by
    exact ((hL.pow 3).const_mul (16 * s * (s + 1) * (p.pair.1 : ℂ) ^ (3 : ℕ))).div₀
      (hQ.pow 3) fun w => pow_ne_zero 3 (hQne w)
  have hB : Continuous (fun w : ℝ × ℝ =>
      -2 * s * (p.pair.1 : ℂ) *
        (d4BMPoincareHorizontalLinear (d4BMStokesPairCoordinate w) p : ℂ) /
        (d4BMPoincareQuadratic (d4BMStokesPairCoordinate w) p.pair : ℂ)) := by
    exact (hL.const_mul (-2 * s * (p.pair.1 : ℂ))).div₀ hQ hQne
  have hseed := continuous_d4BMPoincareSeed_stokesPair s p
  have hsecond := continuous_d4BMPoincareSeedHorizontalSecondJet_stokesPair s p
  change Continuous (fun w : ℝ × ℝ =>
    (4 * s * (p.pair.1 : ℂ) ^ (3 : ℕ) *
          (d4BMPoincareHorizontalLinear (d4BMStokesPairCoordinate w) p : ℂ) /
          (d4BMPoincareQuadratic (d4BMStokesPairCoordinate w) p.pair : ℂ) ^ (2 : ℕ) +
        8 * s * (s + 1) * (p.pair.1 : ℂ) ^ (3 : ℕ) *
          (d4BMPoincareHorizontalLinear (d4BMStokesPairCoordinate w) p : ℂ) /
          (d4BMPoincareQuadratic (d4BMStokesPairCoordinate w) p.pair : ℂ) ^ (2 : ℕ) -
        16 * s * (s + 1) * (p.pair.1 : ℂ) ^ (3 : ℕ) *
          (d4BMPoincareHorizontalLinear (d4BMStokesPairCoordinate w) p : ℂ) ^ (3 : ℕ) /
          (d4BMPoincareQuadratic (d4BMStokesPairCoordinate w) p.pair : ℂ) ^ (3 : ℕ)) *
        d4BMPoincareSeed (d4BMStokesPairCoordinate w) s p +
      (-2 * s * (p.pair.1 : ℂ) *
          (d4BMPoincareHorizontalLinear (d4BMStokesPairCoordinate w) p : ℂ) /
          (d4BMPoincareQuadratic (d4BMStokesPairCoordinate w) p.pair : ℂ)) *
        d4BMPoincareSeedHorizontalSecondJet (d4BMStokesPairCoordinate w) s p)
  exact ((hA1.add hA2).sub hA3).mul hseed |>.add (hB.mul hsecond)

theorem continuous_d4BMPoincareSeedHorizontalHorizontalVerticalThirdJet_stokesPair
    (s : ℂ) (p : D4BMPrimitiveIntegerPair) :
    Continuous (fun w : ℝ × ℝ =>
      d4BMPoincareSeedHorizontalHorizontalVerticalThirdJet
        (d4BMStokesPairCoordinate w) s p) := by
  have hQ : Continuous (fun w : ℝ × ℝ =>
      (d4BMPoincareQuadratic (d4BMStokesPairCoordinate w) p.pair : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_d4BMPoincareQuadratic_stokesPair p)
  have hL : Continuous (fun w : ℝ × ℝ =>
      (d4BMPoincareHorizontalLinear (d4BMStokesPairCoordinate w) p : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_d4BMPoincareHorizontalLinear_stokesPair p)
  have hy : Continuous (fun w : ℝ × ℝ =>
      ((d4BMStokesPairCoordinate w).y : ℂ)) :=
    Complex.continuous_ofReal.comp continuous_d4BMStokesPairCoordinate_height
  have hQne (w : ℝ × ℝ) :
      (d4BMPoincareQuadratic (d4BMStokesPairCoordinate w) p.pair : ℂ) ≠ 0 := by
    exact_mod_cast (d4BMPoincareQuadratic_pos
      (d4BMStokesPairCoordinate w) p.pair p.pair_ne_zero).ne'
  have hyne (w : ℝ × ℝ) : ((d4BMStokesPairCoordinate w).y : ℂ) ≠ 0 := by
    exact_mod_cast (d4BMStokesPairCoordinate w).y_pos.ne'
  have hA1 : Continuous (fun w : ℝ × ℝ =>
      4 * s * (p.pair.1 : ℂ) ^ (4 : ℕ) * ((d4BMStokesPairCoordinate w).y : ℂ) /
        (d4BMPoincareQuadratic (d4BMStokesPairCoordinate w) p.pair : ℂ) ^ (2 : ℕ)) := by
    exact (hy.const_mul (4 * s * (p.pair.1 : ℂ) ^ (4 : ℕ))).div₀
      (hQ.pow 2) fun w => pow_ne_zero 2 (hQne w)
  have hA2 : Continuous (fun w : ℝ × ℝ =>
      16 * s * (s + 1) * (p.pair.1 : ℂ) ^ (4 : ℕ) *
        (d4BMPoincareHorizontalLinear (d4BMStokesPairCoordinate w) p : ℂ) ^ (2 : ℕ) *
        ((d4BMStokesPairCoordinate w).y : ℂ) /
        (d4BMPoincareQuadratic (d4BMStokesPairCoordinate w) p.pair : ℂ) ^ (3 : ℕ)) := by
    exact (((hL.pow 2).const_mul
      (16 * s * (s + 1) * (p.pair.1 : ℂ) ^ (4 : ℕ))).mul hy).div₀
      (hQ.pow 3) fun w => pow_ne_zero 3 (hQne w)
  have hB1 : Continuous (fun w : ℝ × ℝ =>
      s / ((d4BMStokesPairCoordinate w).y : ℂ)) := by
    exact continuous_const.div₀ hy hyne
  have hB2 : Continuous (fun w : ℝ × ℝ =>
      2 * s * (p.pair.1 : ℂ) ^ (2 : ℕ) * ((d4BMStokesPairCoordinate w).y : ℂ) /
        (d4BMPoincareQuadratic (d4BMStokesPairCoordinate w) p.pair : ℂ)) := by
    exact (hy.const_mul (2 * s * (p.pair.1 : ℂ) ^ (2 : ℕ))).div₀ hQ hQne
  have hseed := continuous_d4BMPoincareSeed_stokesPair s p
  have hsecond := continuous_d4BMPoincareSeedHorizontalSecondJet_stokesPair s p
  change Continuous (fun w : ℝ × ℝ =>
    (4 * s * (p.pair.1 : ℂ) ^ (4 : ℕ) * ((d4BMStokesPairCoordinate w).y : ℂ) /
          (d4BMPoincareQuadratic (d4BMStokesPairCoordinate w) p.pair : ℂ) ^ (2 : ℕ) -
        16 * s * (s + 1) * (p.pair.1 : ℂ) ^ (4 : ℕ) *
          (d4BMPoincareHorizontalLinear (d4BMStokesPairCoordinate w) p : ℂ) ^ (2 : ℕ) *
          ((d4BMStokesPairCoordinate w).y : ℂ) /
          (d4BMPoincareQuadratic (d4BMStokesPairCoordinate w) p.pair : ℂ) ^ (3 : ℕ)) *
        d4BMPoincareSeed (d4BMStokesPairCoordinate w) s p +
      (s / ((d4BMStokesPairCoordinate w).y : ℂ) -
          2 * s * (p.pair.1 : ℂ) ^ (2 : ℕ) * ((d4BMStokesPairCoordinate w).y : ℂ) /
            (d4BMPoincareQuadratic (d4BMStokesPairCoordinate w) p.pair : ℂ)) *
        d4BMPoincareSeedHorizontalSecondJet (d4BMStokesPairCoordinate w) s p)
  exact (hA1.sub hA2).mul hseed |>.add ((hB1.sub hB2).mul hsecond)

theorem continuous_d4BMPoincareSeedHorizontalVerticalVerticalThirdJet_stokesPair
    (s : ℂ) (p : D4BMPrimitiveIntegerPair) :
    Continuous (fun w : ℝ × ℝ =>
      d4BMPoincareSeedHorizontalVerticalVerticalThirdJet
        (d4BMStokesPairCoordinate w) s p) := by
  have hy : Continuous (fun w : ℝ × ℝ =>
      ((d4BMStokesPairCoordinate w).y : ℂ)) :=
    Complex.continuous_ofReal.comp continuous_d4BMStokesPairCoordinate_height
  have hyne (w : ℝ × ℝ) : ((d4BMStokesPairCoordinate w).y : ℂ) ≠ 0 := by
    exact_mod_cast (d4BMStokesPairCoordinate w).y_pos.ne'
  have hcoef : Continuous (fun w : ℝ × ℝ =>
      s * (s - 1) / ((d4BMStokesPairCoordinate w).y : ℂ) ^ (2 : ℕ)) := by
    exact continuous_const.div₀ (hy.pow 2) fun w => pow_ne_zero 2 (hyne w)
  change Continuous (fun w : ℝ × ℝ =>
    s * (s - 1) / ((d4BMStokesPairCoordinate w).y : ℂ) ^ (2 : ℕ) *
        d4BMPoincareSeedHorizontalFirstJet (d4BMStokesPairCoordinate w) s p -
      d4BMPoincareSeedHorizontalThirdJet (d4BMStokesPairCoordinate w) s p)
  exact hcoef.mul (continuous_d4BMPoincareSeedHorizontalFirstJet_stokesPair s p) |>.sub
    (continuous_d4BMPoincareSeedHorizontalThirdJet_stokesPair s p)

private theorem continuousOn_tsum_d4BMPoincareSeedThirdJet_stokesCompactCell
    (P : D4BMEisensteinAbsoluteConvergenceParameter) {Y C : ℝ}
    (f : D4BMPrimitiveIntegerPair → D4BMUpperHalfPlaneCoordinate → ℂ)
    (hC : 0 ≤ C)
    (hcont : ∀ p, Continuous (fun w : ℝ × ℝ => f p (d4BMStokesPairCoordinate w)))
    (hbound : ∀ z p, ‖f p z‖ ≤
      (C / z.y ^ (3 : ℕ)) * ‖d4BMPoincareSeed z P.s p‖) :
    ContinuousOn
      (fun w : ℝ × ℝ => ∑' p : D4BMPrimitiveIntegerPair,
        f p (d4BMStokesPairCoordinate w))
      (d4BMStokesCompactCell Y) := by
  let K : ℝ := 8 * C
  apply continuousOn_tsum
  · intro p
    exact (hcont p).continuousOn
  · exact summable_d4BMStokesJetMajorant K P Y
  · intro p w hw
    change w.1 ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) ∧
      w.2 ∈ Set.Icc (1 / 2 : ℝ) Y at hw
    have hy0 : 0 < w.2 := lt_of_lt_of_le (by norm_num) hw.2.1
    have hySq : (1 / 4 : ℝ) ≤ w.2 ^ (2 : ℕ) := by
      have hs := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hy0.le).2 hw.2.1
      norm_num at hs ⊢
      exact hs
    have hyCube : (1 / 8 : ℝ) ≤ w.2 ^ (3 : ℕ) := by
      have hm := mul_le_mul hw.2.1 hySq (by norm_num : (0 : ℝ) ≤ 1 / 4) hy0.le
      nlinarith
    have hK : 0 ≤ K := by dsimp only [K]; positivity
    have hfactor : C / w.2 ^ (3 : ℕ) ≤ K := by
      apply (div_le_iff₀ (pow_pos hy0 3)).2
      dsimp only [K]
      nlinarith
    have hycoord : (d4BMStokesPairCoordinate w).y = w.2 := by
      change max w.2 (1 / 2 : ℝ) = w.2
      exact max_eq_left hw.2.1
    calc
      ‖f p (d4BMStokesPairCoordinate w)‖ ≤
          (C / w.2 ^ (3 : ℕ)) *
            ‖d4BMPoincareSeed (d4BMStokesPairCoordinate w) P.s p‖ := by
        rw [← hycoord]
        exact hbound (d4BMStokesPairCoordinate w) p
      _ ≤ K * ‖d4BMPoincareSeed (d4BMStokesPairCoordinate w) P.s p‖ :=
        mul_le_mul_of_nonneg_right hfactor (norm_nonneg _)
      _ ≤ K * d4BMStokesValueMajorant P Y p :=
        mul_le_mul_of_nonneg_left
          (norm_d4BMPoincareSeed_stokesPair_le P p w hw.1 hw.2.1 hw.2.2) hK
      _ = d4BMStokesJetMajorant K P Y p := rfl

theorem continuousOn_tsum_d4BMPoincareSeedHorizontalThirdJet_stokesCompactCell
    (P : D4BMEisensteinAbsoluteConvergenceParameter) {Y : ℝ} :
    ContinuousOn
      (fun w : ℝ × ℝ => ∑' p : D4BMPrimitiveIntegerPair,
        d4BMPoincareSeedHorizontalThirdJet (d4BMStokesPairCoordinate w) P.s p)
      (d4BMStokesCompactCell Y) := by
  exact continuousOn_tsum_d4BMPoincareSeedThirdJet_stokesCompactCell P
    (f := fun p z => d4BMPoincareSeedHorizontalThirdJet z P.s p)
    (d4BMHorizontalThirdJetNormConstant_nonneg P.s)
    (fun p => continuous_d4BMPoincareSeedHorizontalThirdJet_stokesPair P.s p)
    (fun z p => norm_d4BMPoincareSeedHorizontalThirdJet_le z P.s p)

theorem continuousOn_tsum_d4BMPoincareSeedHorizontalHorizontalVerticalThirdJet_stokesCompactCell
    (P : D4BMEisensteinAbsoluteConvergenceParameter) {Y : ℝ} :
    ContinuousOn
      (fun w : ℝ × ℝ => ∑' p : D4BMPrimitiveIntegerPair,
        d4BMPoincareSeedHorizontalHorizontalVerticalThirdJet
          (d4BMStokesPairCoordinate w) P.s p)
      (d4BMStokesCompactCell Y) := by
  exact continuousOn_tsum_d4BMPoincareSeedThirdJet_stokesCompactCell P
    (f := fun p z => d4BMPoincareSeedHorizontalHorizontalVerticalThirdJet z P.s p)
    (d4BMHorizontalHorizontalVerticalThirdJetNormConstant_nonneg P.s)
    (fun p => continuous_d4BMPoincareSeedHorizontalHorizontalVerticalThirdJet_stokesPair P.s p)
    (fun z p => norm_d4BMPoincareSeedHorizontalHorizontalVerticalThirdJet_le z P.s p)

theorem continuousOn_tsum_d4BMPoincareSeedHorizontalVerticalVerticalThirdJet_stokesCompactCell
    (P : D4BMEisensteinAbsoluteConvergenceParameter) {Y : ℝ} :
    ContinuousOn
      (fun w : ℝ × ℝ => ∑' p : D4BMPrimitiveIntegerPair,
        d4BMPoincareSeedHorizontalVerticalVerticalThirdJet
          (d4BMStokesPairCoordinate w) P.s p)
      (d4BMStokesCompactCell Y) := by
  exact continuousOn_tsum_d4BMPoincareSeedThirdJet_stokesCompactCell P
    (f := fun p z => d4BMPoincareSeedHorizontalVerticalVerticalThirdJet z P.s p)
    (d4BMHorizontalVerticalVerticalThirdJetNormConstant_nonneg P.s)
    (fun p => continuous_d4BMPoincareSeedHorizontalVerticalVerticalThirdJet_stokesPair P.s p)
    (fun z p => norm_d4BMPoincareSeedHorizontalVerticalVerticalThirdJet_le z P.s p)

theorem continuousOn_d4BMCompletedPoincareHorizontalThirdJet_stokesCompactCell
    (P : D4BMEisensteinAbsoluteConvergenceParameter) {Y : ℝ} :
    ContinuousOn
      (fun w : ℝ × ℝ =>
        d4BMCompletedPoincareHorizontalThirdJet (d4BMStokesPairCoordinate w) P)
      (d4BMStokesCompactCell Y) := by
  have hraw : ContinuousOn (fun w : ℝ × ℝ => (1 / 2 : ℂ) *
      ∑' p : D4BMPrimitiveIntegerPair,
        d4BMPoincareSeedHorizontalThirdJet (d4BMStokesPairCoordinate w) P.s p)
      (d4BMStokesCompactCell Y) :=
    continuousOn_const.mul (continuousOn_tsum_d4BMPoincareSeedHorizontalThirdJet_stokesCompactCell P (Y := Y))
  have h : ContinuousOn (fun w : ℝ × ℝ => reflectedCompletedLambda (2 * P.s) *
      ((1 / 2 : ℂ) * ∑' p : D4BMPrimitiveIntegerPair,
        d4BMPoincareSeedHorizontalThirdJet (d4BMStokesPairCoordinate w) P.s p))
      (d4BMStokesCompactCell Y) := continuousOn_const.mul hraw
  simpa [d4BMCompletedPoincareHorizontalThirdJet,
    d4BMRawPoincareHorizontalThirdJet] using h

theorem continuousOn_d4BMCompletedPoincareHorizontalHorizontalVerticalThirdJet_stokesCompactCell
    (P : D4BMEisensteinAbsoluteConvergenceParameter) {Y : ℝ} :
    ContinuousOn
      (fun w : ℝ × ℝ =>
        d4BMCompletedPoincareHorizontalHorizontalVerticalThirdJet
          (d4BMStokesPairCoordinate w) P)
      (d4BMStokesCompactCell Y) := by
  have hraw : ContinuousOn (fun w : ℝ × ℝ => (1 / 2 : ℂ) *
      ∑' p : D4BMPrimitiveIntegerPair,
        d4BMPoincareSeedHorizontalHorizontalVerticalThirdJet
          (d4BMStokesPairCoordinate w) P.s p)
      (d4BMStokesCompactCell Y) :=
    continuousOn_const.mul (continuousOn_tsum_d4BMPoincareSeedHorizontalHorizontalVerticalThirdJet_stokesCompactCell P (Y := Y))
  have h : ContinuousOn (fun w : ℝ × ℝ => reflectedCompletedLambda (2 * P.s) *
      ((1 / 2 : ℂ) * ∑' p : D4BMPrimitiveIntegerPair,
        d4BMPoincareSeedHorizontalHorizontalVerticalThirdJet
          (d4BMStokesPairCoordinate w) P.s p))
      (d4BMStokesCompactCell Y) := continuousOn_const.mul hraw
  simpa [d4BMCompletedPoincareHorizontalHorizontalVerticalThirdJet,
    d4BMRawPoincareHorizontalHorizontalVerticalThirdJet] using h

theorem continuousOn_d4BMCompletedPoincareHorizontalVerticalVerticalThirdJet_stokesCompactCell
    (P : D4BMEisensteinAbsoluteConvergenceParameter) {Y : ℝ} :
    ContinuousOn
      (fun w : ℝ × ℝ =>
        d4BMCompletedPoincareHorizontalVerticalVerticalThirdJet
          (d4BMStokesPairCoordinate w) P)
      (d4BMStokesCompactCell Y) := by
  have hraw : ContinuousOn (fun w : ℝ × ℝ => (1 / 2 : ℂ) *
      ∑' p : D4BMPrimitiveIntegerPair,
        d4BMPoincareSeedHorizontalVerticalVerticalThirdJet
          (d4BMStokesPairCoordinate w) P.s p)
      (d4BMStokesCompactCell Y) :=
    continuousOn_const.mul (continuousOn_tsum_d4BMPoincareSeedHorizontalVerticalVerticalThirdJet_stokesCompactCell P (Y := Y))
  have h : ContinuousOn (fun w : ℝ × ℝ => reflectedCompletedLambda (2 * P.s) *
      ((1 / 2 : ℂ) * ∑' p : D4BMPrimitiveIntegerPair,
        d4BMPoincareSeedHorizontalVerticalVerticalThirdJet
          (d4BMStokesPairCoordinate w) P.s p))
      (d4BMStokesCompactCell Y) := continuousOn_const.mul hraw
  simpa [d4BMCompletedPoincareHorizontalVerticalVerticalThirdJet,
    d4BMRawPoincareHorizontalVerticalVerticalThirdJet] using h

theorem continuousOn_d4BMCompletedPoincareVerticalThirdJet_stokesCompactCell
    (P : D4BMEisensteinAbsoluteConvergenceParameter) {Y : ℝ} :
    ContinuousOn
      (fun w : ℝ × ℝ =>
        d4BMCompletedPoincareVerticalThirdJet (d4BMStokesPairCoordinate w) P)
      (d4BMStokesCompactCell Y) := by
  have hy : Continuous (fun w : ℝ × ℝ =>
      ((d4BMStokesPairCoordinate w).y : ℂ)) :=
    Complex.continuous_ofReal.comp continuous_d4BMStokesPairCoordinate_height
  have hyne (w : ℝ × ℝ) : ((d4BMStokesPairCoordinate w).y : ℂ) ≠ 0 := by
    exact_mod_cast (d4BMStokesPairCoordinate w).y_pos.ne'
  have hcoef3 : Continuous (fun w : ℝ × ℝ =>
      -2 * P.s * (P.s - 1) / ((d4BMStokesPairCoordinate w).y : ℂ) ^ (3 : ℕ)) := by
    exact continuous_const.div₀ (hy.pow 3) fun w => pow_ne_zero 3 (hyne w)
  have hcoef2 : Continuous (fun w : ℝ × ℝ =>
      P.s * (P.s - 1) / ((d4BMStokesPairCoordinate w).y : ℂ) ^ (2 : ℕ)) := by
    exact continuous_const.div₀ (hy.pow 2) fun w => pow_ne_zero 2 (hyne w)
  have hF := continuousOn_d4BMCompletedEisensteinPoincareSeries_stokesCompactCell
    P (Y := Y)
  have hFy := continuousOn_d4BMCompletedPoincareVerticalFirstJet_stokesCompactCell
    P (Y := Y)
  have hxxy := continuousOn_d4BMCompletedPoincareHorizontalHorizontalVerticalThirdJet_stokesCompactCell P (Y := Y)
  unfold d4BMCompletedPoincareVerticalThirdJet
  exact (hcoef3.continuousOn.mul hF).add (hcoef2.continuousOn.mul hFy) |>.sub hxxy

theorem continuous_d4BMPoincareSeedMixedSecondJet_stokesPair
    (s : ℂ) (p : D4BMPrimitiveIntegerPair) :
    Continuous (fun w : ℝ × ℝ =>
      d4BMPoincareSeedMixedSecondJet (d4BMStokesPairCoordinate w) s p) := by
  have hQ : Continuous (fun w : ℝ × ℝ =>
      (d4BMPoincareQuadratic (d4BMStokesPairCoordinate w) p.pair : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_d4BMPoincareQuadratic_stokesPair p)
  have hL : Continuous (fun w : ℝ × ℝ =>
      (d4BMPoincareHorizontalLinear (d4BMStokesPairCoordinate w) p : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_d4BMPoincareHorizontalLinear_stokesPair p)
  have hy : Continuous (fun w : ℝ × ℝ =>
      ((d4BMStokesPairCoordinate w).y : ℂ)) :=
    Complex.continuous_ofReal.comp continuous_d4BMStokesPairCoordinate_height
  have hQne (w : ℝ × ℝ) :
      (d4BMPoincareQuadratic (d4BMStokesPairCoordinate w) p.pair : ℂ) ≠ 0 := by
    exact_mod_cast (d4BMPoincareQuadratic_pos
      (d4BMStokesPairCoordinate w) p.pair p.pair_ne_zero).ne'
  have hyne (w : ℝ × ℝ) : ((d4BMStokesPairCoordinate w).y : ℂ) ≠ 0 := by
    exact_mod_cast (d4BMStokesPairCoordinate w).y_pos.ne'
  have hA : Continuous (fun w : ℝ × ℝ =>
      4 * s * (p.pair.1 : ℂ) ^ (3 : ℕ) * ((d4BMStokesPairCoordinate w).y : ℂ) *
        (d4BMPoincareHorizontalLinear (d4BMStokesPairCoordinate w) p : ℂ) /
        (d4BMPoincareQuadratic (d4BMStokesPairCoordinate w) p.pair : ℂ) ^ (2 : ℕ)) := by
    exact ((hy.const_mul (4 * s * (p.pair.1 : ℂ) ^ (3 : ℕ))).mul hL).div₀
      (hQ.pow 2) fun w => pow_ne_zero 2 (hQne w)
  have hB1 : Continuous (fun w : ℝ × ℝ =>
      s / ((d4BMStokesPairCoordinate w).y : ℂ)) :=
    continuous_const.div₀ hy hyne
  have hB2 : Continuous (fun w : ℝ × ℝ =>
      2 * s * (p.pair.1 : ℂ) ^ (2 : ℕ) * ((d4BMStokesPairCoordinate w).y : ℂ) /
        (d4BMPoincareQuadratic (d4BMStokesPairCoordinate w) p.pair : ℂ)) := by
    exact (hy.const_mul (2 * s * (p.pair.1 : ℂ) ^ (2 : ℕ))).div₀ hQ hQne
  have hH : Continuous (fun w : ℝ × ℝ =>
      -2 * s * (p.pair.1 : ℂ) *
        (d4BMPoincareHorizontalLinear (d4BMStokesPairCoordinate w) p : ℂ) /
        (d4BMPoincareQuadratic (d4BMStokesPairCoordinate w) p.pair : ℂ)) := by
    exact (hL.const_mul (-2 * s * (p.pair.1 : ℂ))).div₀ hQ hQne
  unfold d4BMPoincareSeedMixedSecondJet
  exact (hA.add ((hB1.sub hB2).mul hH)).mul
    (continuous_d4BMPoincareSeed_stokesPair s p)

theorem continuousOn_tsum_d4BMPoincareSeedMixedSecondJet_stokesCompactCell
    (P : D4BMEisensteinAbsoluteConvergenceParameter) {Y : ℝ} :
    ContinuousOn
      (fun w : ℝ × ℝ => ∑' p : D4BMPrimitiveIntegerPair,
        d4BMPoincareSeedMixedSecondJet (d4BMStokesPairCoordinate w) P.s p)
      (d4BMStokesCompactCell Y) := by
  let C : ℝ := 4 * ‖P.s‖ + 6 * ‖P.s‖ ^ (2 : ℕ)
  let K : ℝ := 4 * C
  apply continuousOn_tsum
  · intro p
    exact (continuous_d4BMPoincareSeedMixedSecondJet_stokesPair P.s p).continuousOn
  · exact summable_d4BMStokesJetMajorant K P Y
  · intro p w hw
    change w.1 ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) ∧
      w.2 ∈ Set.Icc (1 / 2 : ℝ) Y at hw
    have hy0 : 0 < w.2 := lt_of_lt_of_le (by norm_num) hw.2.1
    have hySq : (1 / 4 : ℝ) ≤ w.2 ^ (2 : ℕ) := by
      have hs := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hy0.le).2 hw.2.1
      norm_num at hs ⊢
      exact hs
    have hC : 0 ≤ C := by dsimp only [C]; positivity
    have hK : 0 ≤ K := by dsimp only [K]; positivity
    have hfactor : C / w.2 ^ (2 : ℕ) ≤ K := by
      apply (div_le_iff₀ (sq_pos_of_pos hy0)).2
      dsimp only [K]
      nlinarith
    have hycoord : (d4BMStokesPairCoordinate w).y = w.2 := by
      change max w.2 (1 / 2 : ℝ) = w.2
      exact max_eq_left hw.2.1
    calc
      ‖d4BMPoincareSeedMixedSecondJet (d4BMStokesPairCoordinate w) P.s p‖ ≤
          (C / w.2 ^ (2 : ℕ)) *
            ‖d4BMPoincareSeed (d4BMStokesPairCoordinate w) P.s p‖ := by
        have h := norm_d4BMPoincareSeedMixedSecondJet_le
          (d4BMStokesPairCoordinate w) P.s p
        rw [hycoord] at h
        simpa only [C] using h
      _ ≤ K * ‖d4BMPoincareSeed (d4BMStokesPairCoordinate w) P.s p‖ :=
        mul_le_mul_of_nonneg_right hfactor (norm_nonneg _)
      _ ≤ K * d4BMStokesValueMajorant P Y p :=
        mul_le_mul_of_nonneg_left
          (norm_d4BMPoincareSeed_stokesPair_le P p w hw.1 hw.2.1 hw.2.2) hK
      _ = d4BMStokesJetMajorant K P Y p := rfl

theorem continuousOn_d4BMCompletedPoincareMixedSecondJet_stokesCompactCell
    (P : D4BMEisensteinAbsoluteConvergenceParameter) {Y : ℝ} :
    ContinuousOn
      (fun w : ℝ × ℝ =>
        d4BMCompletedPoincareMixedSecondJet (d4BMStokesPairCoordinate w) P)
      (d4BMStokesCompactCell Y) := by
  have hraw : ContinuousOn (fun w : ℝ × ℝ => (1 / 2 : ℂ) *
      ∑' p : D4BMPrimitiveIntegerPair,
        d4BMPoincareSeedMixedSecondJet (d4BMStokesPairCoordinate w) P.s p)
      (d4BMStokesCompactCell Y) :=
    continuousOn_const.mul (continuousOn_tsum_d4BMPoincareSeedMixedSecondJet_stokesCompactCell P (Y := Y))
  have h : ContinuousOn (fun w : ℝ × ℝ => reflectedCompletedLambda (2 * P.s) *
      ((1 / 2 : ℂ) * ∑' p : D4BMPrimitiveIntegerPair,
        d4BMPoincareSeedMixedSecondJet (d4BMStokesPairCoordinate w) P.s p))
      (d4BMStokesCompactCell Y) := continuousOn_const.mul hraw
  simpa [d4BMCompletedPoincareMixedSecondJet,
    d4BMRawPoincareMixedSecondJet] using h

def d4BMActualSecondStokesHorizontalCurrentAt
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) (x y : ℝ) : ℂ :=
  d4BMActualSecondStokesHorizontalCurrent (d4BMStokesCoordinate x y) P Q

def d4BMActualSecondStokesVerticalCurrentAt
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) (x y : ℝ) : ℂ :=
  d4BMActualSecondStokesVerticalCurrent (d4BMStokesCoordinate x y) P Q

def d4BMActualSecondStokesHorizontalDivergenceAt
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) (x y : ℝ) : ℂ :=
  d4BMActualSecondStokesHorizontalDivergence (d4BMStokesCoordinate x y) P Q

def d4BMActualSecondStokesVerticalDivergenceAt
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) (x y : ℝ) : ℂ :=
  d4BMActualSecondStokesVerticalDivergence (d4BMStokesCoordinate x y) P Q

theorem continuousOn_d4BMActualSecondStokesHorizontalDivergence_stokesCompactCell
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) {Y : ℝ} :
    ContinuousOn (fun w : ℝ × ℝ => d4BMActualSecondStokesHorizontalDivergenceAt P Q w.1 w.2)
      (d4BMStokesCompactCell Y) := by
  have hG := continuousOn_d4BMCompletedEisensteinPoincareSeries_stokesCompactCell Q (Y := Y)
  have hFx := continuousOn_d4BMCompletedPoincareHorizontalFirstJet_stokesCompactCell P (Y := Y)
  have hFy := continuousOn_d4BMCompletedPoincareVerticalFirstJet_stokesCompactCell P (Y := Y)
  have hFxx := continuousOn_d4BMCompletedPoincareHorizontalSecondJet_stokesCompactCell P (Y := Y)
  have hFxy := continuousOn_d4BMCompletedPoincareMixedSecondJet_stokesCompactCell P (Y := Y)
  have hFxxx := continuousOn_d4BMCompletedPoincareHorizontalThirdJet_stokesCompactCell P (Y := Y)
  have hFxxy := continuousOn_d4BMCompletedPoincareHorizontalHorizontalVerticalThirdJet_stokesCompactCell P (Y := Y)
  have hGxx := continuousOn_d4BMCompletedPoincareHorizontalSecondJet_stokesCompactCell Q (Y := Y)
  have hE : ContinuousOn
      (fun w : ℝ × ℝ => d4BMActualSecondStokesEnergy (d4BMStokesPairCoordinate w) P)
      (d4BMStokesCompactCell Y) := by
    unfold d4BMActualSecondStokesEnergy
    fun_prop
  have hExx : ContinuousOn
      (fun w : ℝ × ℝ =>
        d4BMActualSecondStokesEnergyHorizontalSecondJet (d4BMStokesPairCoordinate w) P)
      (d4BMStokesCompactCell Y) := by
    unfold d4BMActualSecondStokesEnergyHorizontalSecondJet
    fun_prop
  unfold d4BMActualSecondStokesHorizontalDivergenceAt d4BMActualSecondStokesHorizontalDivergence
  change ContinuousOn (fun w : ℝ × ℝ =>
    d4BMCompletedEisensteinPoincareSeries (d4BMStokesPairCoordinate w) Q *
        d4BMActualSecondStokesEnergyHorizontalSecondJet (d4BMStokesPairCoordinate w) P -
      d4BMActualSecondStokesEnergy (d4BMStokesPairCoordinate w) P *
        d4BMCompletedPoincareHorizontalSecondJet (d4BMStokesPairCoordinate w) Q)
    (d4BMStokesCompactCell Y)
  exact hG.mul hExx |>.sub (hE.mul hGxx)

theorem continuousOn_d4BMActualSecondStokesVerticalDivergence_stokesCompactCell
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) {Y : ℝ} :
    ContinuousOn (fun w : ℝ × ℝ => d4BMActualSecondStokesVerticalDivergenceAt P Q w.1 w.2)
      (d4BMStokesCompactCell Y) := by
  have hG := continuousOn_d4BMCompletedEisensteinPoincareSeries_stokesCompactCell Q (Y := Y)
  have hFx := continuousOn_d4BMCompletedPoincareHorizontalFirstJet_stokesCompactCell P (Y := Y)
  have hFy := continuousOn_d4BMCompletedPoincareVerticalFirstJet_stokesCompactCell P (Y := Y)
  have hFxy := continuousOn_d4BMCompletedPoincareMixedSecondJet_stokesCompactCell P (Y := Y)
  have hFyy := continuousOn_d4BMCompletedPoincareVerticalSecondJet_stokesCompactCell P (Y := Y)
  have hFxyy := continuousOn_d4BMCompletedPoincareHorizontalVerticalVerticalThirdJet_stokesCompactCell P (Y := Y)
  have hFyyy := continuousOn_d4BMCompletedPoincareVerticalThirdJet_stokesCompactCell P (Y := Y)
  have hGyy := continuousOn_d4BMCompletedPoincareVerticalSecondJet_stokesCompactCell Q (Y := Y)
  have hE : ContinuousOn
      (fun w : ℝ × ℝ => d4BMActualSecondStokesEnergy (d4BMStokesPairCoordinate w) P)
      (d4BMStokesCompactCell Y) := by
    unfold d4BMActualSecondStokesEnergy
    fun_prop
  have hEyy : ContinuousOn
      (fun w : ℝ × ℝ =>
        d4BMActualSecondStokesEnergyVerticalSecondJet (d4BMStokesPairCoordinate w) P)
      (d4BMStokesCompactCell Y) := by
    unfold d4BMActualSecondStokesEnergyVerticalSecondJet
    fun_prop
  unfold d4BMActualSecondStokesVerticalDivergenceAt d4BMActualSecondStokesVerticalDivergence
  change ContinuousOn (fun w : ℝ × ℝ =>
    d4BMCompletedEisensteinPoincareSeries (d4BMStokesPairCoordinate w) Q *
        d4BMActualSecondStokesEnergyVerticalSecondJet (d4BMStokesPairCoordinate w) P -
      d4BMActualSecondStokesEnergy (d4BMStokesPairCoordinate w) P *
        d4BMCompletedPoincareVerticalSecondJet (d4BMStokesPairCoordinate w) Q)
    (d4BMStokesCompactCell Y)
  exact hG.mul hEyy |>.sub (hE.mul hGyy)

def d4BMActualSecondStokesVerticalDivergenceSlice
    (z : D4BMUpperHalfPlaneCoordinate)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) (y : ℝ) : ℂ :=
  d4BMActualSecondStokesVerticalDivergence (d4BMStokesCoordinate z.x y) P Q

theorem hasDerivAt_d4BMActualSecondStokesVerticalCurrentSlice_at_positive
    (z : D4BMUpperHalfPlaneCoordinate)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter)
    {y : ℝ} (hy : (1 / 2 : ℝ) ≤ y) :
    HasDerivAt (d4BMActualSecondStokesVerticalCurrentSlice z P Q)
      (d4BMActualSecondStokesVerticalDivergenceSlice z P Q y) y := by
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy
  let zy : D4BMUpperHalfPlaneCoordinate := ⟨z.x, y, hy0⟩
  have h := hasDerivAt_d4BMActualSecondStokesVerticalCurrentSlice zy P Q
  have hfun : d4BMActualSecondStokesVerticalCurrentSlice zy P Q =
      d4BMActualSecondStokesVerticalCurrentSlice z P Q := by
    funext v
    rfl
  rw [hfun] at h
  have hcoord : d4BMStokesCoordinate z.x y = zy :=
    d4BMStokesCoordinate_eq_of_half_le z.x y hy
  change HasDerivAt (d4BMActualSecondStokesVerticalCurrentSlice z P Q)
    (d4BMActualSecondStokesVerticalDivergence (d4BMStokesCoordinate z.x y) P Q) y
  rw [hcoord]
  exact h

/-- One-dimensional vertical FTC for the literal actual second-Stokes current. -/
theorem intervalIntegral_d4BMActualSecondStokesVerticalDivergenceSlice_eq_sub
    (z : D4BMUpperHalfPlaneCoordinate)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter)
    {a b : ℝ} (hx : z.x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2))
    (ha : (1 / 2 : ℝ) ≤ a) (hb : (1 / 2 : ℝ) ≤ b) :
    (∫ y in a..b, d4BMActualSecondStokesVerticalDivergenceSlice z P Q y) =
      d4BMActualSecondStokesVerticalCurrentSlice z P Q b -
        d4BMActualSecondStokesVerticalCurrentSlice z P Q a := by
  have hsub : uIcc a b ⊆ Set.Icc (1 / 2 : ℝ) (max a b) := by
    intro y hy
    rcases mem_uIcc.mp hy with hab | hba
    · exact ⟨ha.trans hab.1, hab.2.trans (le_max_right _ _)⟩
    · exact ⟨hb.trans hba.1, hba.2.trans (le_max_left _ _)⟩
  have hmap : MapsTo (fun y : ℝ => (z.x, y)) (uIcc a b)
      (d4BMStokesCompactCell (max a b)) := by
    intro y hy
    exact ⟨hx, hsub hy⟩
  have hcont : ContinuousOn
      (d4BMActualSecondStokesVerticalDivergenceSlice z P Q) (uIcc a b) := by
    have h := (continuousOn_d4BMActualSecondStokesVerticalDivergence_stokesCompactCell
      P Q (Y := max a b)).comp
        (continuous_const.prodMk continuous_id).continuousOn hmap
    change ContinuousOn
      (fun y : ℝ => d4BMActualSecondStokesVerticalDivergence
        (d4BMStokesCoordinate z.x y) P Q) (uIcc a b)
    simpa [Function.comp_def, d4BMActualSecondStokesVerticalDivergenceSlice,
      d4BMActualSecondStokesVerticalDivergenceAt, d4BMStokesPairCoordinate] using h
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro y hy
    exact hasDerivAt_d4BMActualSecondStokesVerticalCurrentSlice_at_positive
      z P Q (hsub hy).1
  · exact hcont.intervalIntegrable

theorem hasDerivAt_d4BMActualSecondStokesHorizontalCurrent_at
    (z : D4BMUpperHalfPlaneCoordinate)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) (x : ℝ) :
    HasDerivAt
      (fun q : ℝ => d4BMActualSecondStokesHorizontalCurrent
        (d4BMHorizontalCoordinate z q) P Q)
      (d4BMActualSecondStokesHorizontalDivergence
        (d4BMHorizontalCoordinate z x) P Q) x := by
  simpa [d4BMHorizontalCoordinate] using
    hasDerivAt_d4BMActualSecondStokesHorizontalCurrent
      (d4BMHorizontalCoordinate z x) P Q

/-! ## Literal modular-domain geometry -/

/-- Height of the circular boundary of the standard modular domain above horizontal coordinate
`x`.  Outside the geometric interval this total function is used only as an integration
parameter. -/
def d4BMActualSecondStokesRadialCurrentAt
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) (x y : ℝ) : ℂ :=
  d4BMActualSecondStokesRadialCurrent (d4BMStokesCoordinate x y) P Q

theorem d4BM_actualSecondStokesRadialCurrentAt_arc_pair_eq_zero
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    d4BMActualSecondStokesRadialCurrentAt P Q (-x) (d4BMModularArcHeight x) +
        d4BMActualSecondStokesRadialCurrentAt P Q x (d4BMModularArcHeight x) = 0 := by
  have hxfull : x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := ⟨by linarith [hx.1], hx.2⟩
  let z : D4BMUnitSemicircleCoordinate :=
    ⟨d4BMStokesCoordinate x (d4BMModularArcHeight x),
      d4BMStokesCoordinate_arc_unitCircle hxfull⟩
  have hinv := d4BM_actualSecondStokesRadialCurrent_invert_unitCircle z P Q
  rw [d4BMStokesCoordinate_arc_invert hxfull] at hinv
  change d4BMActualSecondStokesRadialCurrent
      (d4BMStokesCoordinate (-x) (d4BMModularArcHeight x)) P Q +
    d4BMActualSecondStokesRadialCurrent
      (d4BMStokesCoordinate x (d4BMModularArcHeight x)) P Q = 0
  rw [hinv]
  ring

theorem d4BMActualSecondStokesVerticalDivergenceSlice_eq_at
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter)
    (x y : ℝ) (_hy : (1 / 2 : ℝ) ≤ y) :
    d4BMActualSecondStokesVerticalDivergenceSlice
        (d4BMStokesCoordinate x 1) P Q y =
      d4BMActualSecondStokesVerticalDivergenceAt P Q x y := by
  rfl

theorem d4BMActualSecondStokesVerticalCurrentSlice_eq_at
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter)
    (x y : ℝ) (hy : (1 / 2 : ℝ) ≤ y) :
    d4BMActualSecondStokesVerticalCurrentSlice
        (d4BMStokesCoordinate x 1) P Q y =
      d4BMActualSecondStokesVerticalCurrentAt P Q x y := by
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy
  let zy : D4BMUpperHalfPlaneCoordinate := ⟨x, y, hy0⟩
  have hcoord : d4BMStokesCoordinate x y = zy := by
    exact d4BMStokesCoordinate_eq_of_half_le x y hy
  unfold d4BMActualSecondStokesVerticalCurrentAt
  rw [hcoord]
  rfl

/-- Literal vertical part of the Euclidean divergence integral over the truncated modular
fundamental domain. -/
def d4BMActualSecondStokesVerticalBulk
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) (Y : ℝ) : ℂ :=
  ∫ x in (-(1 / 2 : ℝ))..(1 / 2),
    ∫ y in d4BMModularArcHeight x..Y,
      d4BMActualSecondStokesVerticalDivergenceAt P Q x y

/-- Vertical FTC on every genuine modular-domain fibre. -/
theorem d4BM_actualSecondStokesVerticalBulk_eq_boundary
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter)
    {Y : ℝ} (hY : 1 ≤ Y) :
    d4BMActualSecondStokesVerticalBulk P Q Y =
      ∫ x in (-(1 / 2 : ℝ))..(1 / 2),
        (d4BMActualSecondStokesVerticalCurrentAt P Q x Y -
          d4BMActualSecondStokesVerticalCurrentAt P Q x
            (d4BMModularArcHeight x)) := by
  unfold d4BMActualSecondStokesVerticalBulk
  apply intervalIntegral.integral_congr
  intro x hx
  have hxI : x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := by
    simpa [uIcc_of_le (by norm_num : (-(1 / 2 : ℝ)) ≤ 1 / 2)] using hx
  have harcpos := d4BMModularArcHeight_pos_of_mem hxI
  have hYpos : 0 < Y := lt_of_lt_of_le (by norm_num) hY
  have harcleY : d4BMModularArcHeight x ≤ Y :=
    (d4BMModularArcHeight_le_one hxI).trans hY
  change
    (∫ y in d4BMModularArcHeight x..Y,
      d4BMActualSecondStokesVerticalDivergenceAt P Q x y) = _
  calc
    (∫ y in d4BMModularArcHeight x..Y,
        d4BMActualSecondStokesVerticalDivergenceAt P Q x y) =
        ∫ y in d4BMModularArcHeight x..Y,
          d4BMActualSecondStokesVerticalDivergenceSlice
            (d4BMStokesCoordinate x 1) P Q y := by
      apply intervalIntegral.integral_congr
      intro y hy
      have hyI : y ∈ Set.Icc (d4BMModularArcHeight x) Y := by
        simpa [uIcc_of_le harcleY] using hy
      have hyhalf : (1 / 2 : ℝ) ≤ y :=
        (d4BMModularArcHeight_half_le hxI).trans hyI.1
      exact (d4BMActualSecondStokesVerticalDivergenceSlice_eq_at
        P Q x y hyhalf).symm
    _ = d4BMActualSecondStokesVerticalCurrentSlice
          (d4BMStokesCoordinate x 1) P Q Y -
        d4BMActualSecondStokesVerticalCurrentSlice
          (d4BMStokesCoordinate x 1) P Q (d4BMModularArcHeight x) :=
      intervalIntegral_d4BMActualSecondStokesVerticalDivergenceSlice_eq_sub
        (d4BMStokesCoordinate x 1) P Q hxI
          (d4BMModularArcHeight_half_le hxI) (by linarith)
    _ = d4BMActualSecondStokesVerticalCurrentAt P Q x Y -
        d4BMActualSecondStokesVerticalCurrentAt P Q x
          (d4BMModularArcHeight x) := by
      rw [d4BMActualSecondStokesVerticalCurrentSlice_eq_at P Q x Y
          (by linarith),
        d4BMActualSecondStokesVerticalCurrentSlice_eq_at P Q x
          (d4BMModularArcHeight x) (d4BMModularArcHeight_half_le hxI)]

/-- Horizontal radius of the circular boundary at height `y`. -/
theorem d4BM_actualSecondStokesHorizontalCurrentAt_verticalSides
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) (y : ℝ) :
    d4BMActualSecondStokesHorizontalCurrentAt P Q (1 / 2) y =
      d4BMActualSecondStokesHorizontalCurrentAt P Q (-(1 / 2)) y := by
  unfold d4BMActualSecondStokesHorizontalCurrentAt
  rw [d4BMStokesCoordinate_right_eq_translate_left,
    d4BM_actualSecondStokesHorizontalCurrent_translate]

theorem intervalIntegral_d4BMActualSecondStokesHorizontalDivergenceAt_eq_sub
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter)
    (y a b : ℝ) (hy : (1 / 2 : ℝ) ≤ y)
    (ha : a ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2))
    (hb : b ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) :
    (∫ x in a..b, d4BMActualSecondStokesHorizontalDivergenceAt P Q x y) =
      d4BMActualSecondStokesHorizontalCurrentAt P Q b y -
        d4BMActualSecondStokesHorizontalCurrentAt P Q a y := by
  have hab : Set.uIcc a b ⊆ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := by
    intro x hx
    rcases Set.mem_uIcc.mp hx with hx | hx
    · exact ⟨ha.1.trans hx.1, hx.2.trans hb.2⟩
    · exact ⟨hb.1.trans hx.1, hx.2.trans ha.2⟩
  have hmap : MapsTo (fun x : ℝ => (x, y)) (Set.uIcc a b)
      (d4BMStokesCompactCell y) := by
    intro x hx
    exact ⟨hab hx, hy, le_rfl⟩
  have hbase :=
    continuousOn_d4BMActualSecondStokesHorizontalDivergence_stokesCompactCell
      P Q (Y := y)
  have hcomp := hbase.comp
    (continuous_id.prodMk continuous_const).continuousOn hmap
  have hcont : ContinuousOn
      (fun x : ℝ => d4BMActualSecondStokesHorizontalDivergenceAt P Q x y)
      (Set.uIcc a b) := by
    simpa [Function.comp_def, d4BMActualSecondStokesHorizontalDivergenceAt,
      d4BMStokesPairCoordinate] using hcomp
  let z := d4BMStokesCoordinate 0 y
  have hcoord (x : ℝ) : d4BMHorizontalCoordinate z x = d4BMStokesCoordinate x y := by
    apply d4BMUpperHalfPlaneCoordinate_eq_of_xy <;> rfl
  have hfun : (fun x : ℝ => d4BMActualSecondStokesHorizontalCurrentAt P Q x y) =
      (fun x : ℝ => d4BMActualSecondStokesHorizontalCurrent
        (d4BMHorizontalCoordinate z x) P Q) := by
    funext x
    unfold d4BMActualSecondStokesHorizontalCurrentAt
    rw [hcoord]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x _hx
    rw [hfun]
    have h := hasDerivAt_d4BMActualSecondStokesHorizontalCurrent_at z P Q x
    have hvalue : d4BMActualSecondStokesHorizontalDivergenceAt P Q x y =
        d4BMActualSecondStokesHorizontalDivergence
          (d4BMHorizontalCoordinate z x) P Q := by
      unfold d4BMActualSecondStokesHorizontalDivergenceAt
      rw [hcoord]
    rw [hvalue]
    exact h
  · exact hcont.intervalIntegrable

/-- Horizontal divergence over the two side slivers below height one.  The central interval is
excluded because the standard modular domain satisfies `x^(2 : ℕ) + y^(2 : ℕ) ≥ 1`. -/
def d4BMActualSecondStokesHorizontalLowerBulk
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  ∫ y in d4BMModularArcFloor..1,
    ((∫ x in (-(1 / 2 : ℝ))..(-d4BMModularSideRadius y),
        d4BMActualSecondStokesHorizontalDivergenceAt P Q x y) +
      ∫ x in d4BMModularSideRadius y..(1 / 2),
        d4BMActualSecondStokesHorizontalDivergenceAt P Q x y)

/-- Horizontal divergence over the full strip above height one. -/
def d4BMActualSecondStokesHorizontalUpperBulk
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) (Y : ℝ) : ℂ :=
  ∫ y in 1..Y,
    ∫ x in (-(1 / 2 : ℝ))..(1 / 2),
      d4BMActualSecondStokesHorizontalDivergenceAt P Q x y

def d4BMActualSecondStokesHorizontalBulk
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) (Y : ℝ) : ℂ :=
  d4BMActualSecondStokesHorizontalLowerBulk P Q +
    d4BMActualSecondStokesHorizontalUpperBulk P Q Y

theorem d4BM_actualSecondStokesHorizontalLowerBulk_eq_arc
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMActualSecondStokesHorizontalLowerBulk P Q =
      ∫ y in d4BMModularArcFloor..1,
        (d4BMActualSecondStokesHorizontalCurrentAt P Q
            (-d4BMModularSideRadius y) y -
          d4BMActualSecondStokesHorizontalCurrentAt P Q
            (d4BMModularSideRadius y) y) := by
  unfold d4BMActualSecondStokesHorizontalLowerBulk
  apply intervalIntegral.integral_congr
  intro y hy
  have hfloorHalf : (1 / 2 : ℝ) ≤ d4BMModularArcFloor :=
    le_of_lt d4BMModularArcFloor_gt_half
  have hfloorOne : d4BMModularArcFloor ≤ 1 := by
    exact d4BMModularArcHeight_le_one (by constructor <;> norm_num)
  have hyI : y ∈ Set.Icc d4BMModularArcFloor 1 := by
    simpa [uIcc_of_le hfloorOne] using hy
  have hyhalf : (1 / 2 : ℝ) ≤ y := hfloorHalf.trans hyI.1
  change
    (∫ x in (-(1 / 2 : ℝ))..(-d4BMModularSideRadius y),
        d4BMActualSecondStokesHorizontalDivergenceAt P Q x y) +
      (∫ x in d4BMModularSideRadius y..(1 / 2),
        d4BMActualSecondStokesHorizontalDivergenceAt P Q x y) = _
  rw [intervalIntegral_d4BMActualSecondStokesHorizontalDivergenceAt_eq_sub
      P Q y (-(1 / 2)) (-d4BMModularSideRadius y) hyhalf
        (by constructor <;> norm_num)
        (by
          have hr0 : 0 ≤ d4BMModularSideRadius y := Real.sqrt_nonneg _
          have hrh := d4BMModularSideRadius_le_half hyI
          constructor <;> linarith),
    intervalIntegral_d4BMActualSecondStokesHorizontalDivergenceAt_eq_sub
      P Q y (d4BMModularSideRadius y) (1 / 2) hyhalf
        (by
          have hr0 : 0 ≤ d4BMModularSideRadius y := Real.sqrt_nonneg _
          have hrh := d4BMModularSideRadius_le_half hyI
          constructor <;> linarith)
        (by constructor <;> norm_num),
    d4BM_actualSecondStokesHorizontalCurrentAt_verticalSides P Q y]
  ring

theorem d4BM_actualSecondStokesHorizontalUpperBulk_eq_zero
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter)
    {Y : ℝ} (hY : 1 ≤ Y) :
    d4BMActualSecondStokesHorizontalUpperBulk P Q Y = 0 := by
  unfold d4BMActualSecondStokesHorizontalUpperBulk
  calc
    (∫ y in 1..Y,
        ∫ x in (-(1 / 2 : ℝ))..(1 / 2),
          d4BMActualSecondStokesHorizontalDivergenceAt P Q x y) =
        ∫ _y in 1..Y, (0 : ℂ) := by
      apply intervalIntegral.integral_congr
      intro y hy
      have hyI : y ∈ Set.Icc (1 : ℝ) Y := by
        simpa [uIcc_of_le hY] using hy
      change
        (∫ x in (-(1 / 2 : ℝ))..(1 / 2),
          d4BMActualSecondStokesHorizontalDivergenceAt P Q x y) = 0
      rw [intervalIntegral_d4BMActualSecondStokesHorizontalDivergenceAt_eq_sub
          P Q y (-(1 / 2)) (1 / 2) (by linarith [hyI.1])
            (by constructor <;> norm_num) (by constructor <;> norm_num),
        d4BM_actualSecondStokesHorizontalCurrentAt_verticalSides]
      ring
    _ = 0 := by simp

theorem d4BM_actualSecondStokesHorizontalBulk_eq_arc
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter)
    {Y : ℝ} (hY : 1 ≤ Y) :
    d4BMActualSecondStokesHorizontalBulk P Q Y =
      ∫ y in d4BMModularArcFloor..1,
        (d4BMActualSecondStokesHorizontalCurrentAt P Q
            (-d4BMModularSideRadius y) y -
          d4BMActualSecondStokesHorizontalCurrentAt P Q
            (d4BMModularSideRadius y) y) := by
  unfold d4BMActualSecondStokesHorizontalBulk
  rw [d4BM_actualSecondStokesHorizontalLowerBulk_eq_arc,
    d4BM_actualSecondStokesHorizontalUpperBulk_eq_zero P Q hY, add_zero]

def d4BMActualSecondStokesHorizontalArcHeightFlux
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) (y : ℝ) : ℂ :=
  d4BMActualSecondStokesHorizontalCurrentAt P Q (-d4BMModularSideRadius y) y -
    d4BMActualSecondStokesHorizontalCurrentAt P Q (d4BMModularSideRadius y) y

def d4BMActualSecondStokesHorizontalArcParameterFlux
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) (x : ℝ) : ℂ :=
  (x / d4BMModularArcHeight x) •
    (d4BMActualSecondStokesHorizontalCurrentAt P Q (-x) (d4BMModularArcHeight x) -
      d4BMActualSecondStokesHorizontalCurrentAt P Q x (d4BMModularArcHeight x))

/-- Exact change of variables from horizontal height slices to the right-half circular arc.
This is the orientation-sensitive step absent from the previous pointwise boundary pairing. -/
theorem d4BM_actualSecondStokesHorizontalArc_changeOfVariables
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) :
    (∫ y in d4BMModularArcFloor..1,
        d4BMActualSecondStokesHorizontalArcHeightFlux P Q y) =
      ∫ x in 0..(1 / 2),
        d4BMActualSecondStokesHorizontalArcParameterFlux P Q x := by
  let g : ℝ → ℂ := d4BMActualSecondStokesHorizontalArcHeightFlux P Q
  have hsubst := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonpos
    (g := g) (a := (0 : ℝ)) (b := (1 / 2 : ℝ))
    (f := d4BMModularArcHeight)
    (f' := fun x => -x / d4BMModularArcHeight x)
    continuous_d4BMModularArcHeight.continuousOn
    (by
      intro x hx
      have hx' : x ∈ Set.Ioo (0 : ℝ) (1 / 2) := by simpa using hx
      exact hasDerivAt_d4BMModularArcHeight hx')
    (by
      intro x hx
      have hx' : x ∈ Set.Ioo (0 : ℝ) (1 / 2) := by simpa using hx
      have harcpos : 0 < d4BMModularArcHeight x := by
        apply d4BMModularArcHeight_pos_of_mem
        constructor <;> linarith [hx'.1, hx'.2]
      exact div_nonpos_of_nonpos_of_nonneg (by linarith [hx'.1]) harcpos.le)
  have hsubst' :
      (∫ x in 0..(1 / 2),
          (-x / d4BMModularArcHeight x) • (g ∘ d4BMModularArcHeight) x) =
        ∫ y in 1..d4BMModularArcFloor, g y := by
    rw [d4BMModularArcHeight_zero, d4BMModularArcHeight_half] at hsubst
    exact hsubst
  have hleft :
      (∫ x in 0..(1 / 2),
          (-x / d4BMModularArcHeight x) • (g ∘ d4BMModularArcHeight) x) =
        -(∫ x in 0..(1 / 2),
          d4BMActualSecondStokesHorizontalArcParameterFlux P Q x) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro x hx
    have hxI : x ∈ Set.Icc (0 : ℝ) (1 / 2) := by
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] using hx
    have hradius := d4BMModularSideRadius_arcHeight hxI
    unfold g d4BMActualSecondStokesHorizontalArcHeightFlux
      d4BMActualSecondStokesHorizontalArcParameterFlux
    simp only [Function.comp_apply, hradius]
    rw [show -x / d4BMModularArcHeight x =
        -(x / d4BMModularArcHeight x) by ring, neg_smul]
  have hright :
      (∫ y in 1..d4BMModularArcFloor, g y) =
        -(∫ y in d4BMModularArcFloor..1, g y) :=
    intervalIntegral.integral_symm d4BMModularArcFloor 1
  have hneg :
      -(∫ x in 0..(1 / 2),
          d4BMActualSecondStokesHorizontalArcParameterFlux P Q x) =
        -(∫ y in d4BMModularArcFloor..1,
          d4BMActualSecondStokesHorizontalArcHeightFlux P Q y) := by
    calc
      _ = ∫ x in 0..(1 / 2),
          (-x / d4BMModularArcHeight x) • (g ∘ d4BMModularArcHeight) x := hleft.symm
      _ = ∫ y in 1..d4BMModularArcFloor, g y := hsubst'
      _ = -(∫ y in d4BMModularArcFloor..1, g y) := hright
      _ = -(∫ y in d4BMModularArcFloor..1,
          d4BMActualSecondStokesHorizontalArcHeightFlux P Q y) := rfl
  exact (neg_inj.mp hneg).symm

theorem d4BM_actualSecondStokesRadialCurrent_eq_components
    (z : D4BMUpperHalfPlaneCoordinate)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMActualSecondStokesRadialCurrent z P Q =
      (z.x : ℂ) * d4BMActualSecondStokesHorizontalCurrent z P Q +
        (z.y : ℂ) * d4BMActualSecondStokesVerticalCurrent z P Q := by
  unfold d4BMActualSecondStokesRadialCurrent
    d4BMActualSecondStokesEnergyRadialFirstJet
    d4BMActualSecondStokesHorizontalCurrent d4BMActualSecondStokesVerticalCurrent
  rw [
    d4BM_completedPoincareRadialFirstJet_eq_gradientContraction z Q]
  ring

def d4BMActualSecondStokesCircularBoundaryFlux
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) (x : ℝ) : ℂ :=
  (x / d4BMModularArcHeight x) •
      (d4BMActualSecondStokesHorizontalCurrentAt P Q (-x) (d4BMModularArcHeight x) -
        d4BMActualSecondStokesHorizontalCurrentAt P Q x (d4BMModularArcHeight x)) -
    d4BMActualSecondStokesVerticalCurrentAt P Q (-x) (d4BMModularArcHeight x) -
    d4BMActualSecondStokesVerticalCurrentAt P Q x (d4BMModularArcHeight x)

/-- The exact oriented circular flux vanishes pointwise after both half-arcs are paired.  This is
the radial inversion law with the Jacobian and outward-normal signs made literal. -/
theorem d4BM_actualSecondStokesCircularBoundaryFlux_eq_zero
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    d4BMActualSecondStokesCircularBoundaryFlux P Q x = 0 := by
  have hxfull : x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := ⟨by linarith [hx.1], hx.2⟩
  have hxneg : -x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have harcpos := d4BMModularArcHeight_pos_of_mem hxfull
  have harchalf := d4BMModularArcHeight_half_le hxfull
  have hpair := d4BM_actualSecondStokesRadialCurrentAt_arc_pair_eq_zero P Q hx
  have hneg := d4BM_actualSecondStokesRadialCurrent_eq_components
    (d4BMStokesCoordinate (-x) (d4BMModularArcHeight x)) P Q
  have hpos := d4BM_actualSecondStokesRadialCurrent_eq_components
    (d4BMStokesCoordinate x (d4BMModularArcHeight x)) P Q
  change
    d4BMActualSecondStokesRadialCurrentAt P Q (-x) (d4BMModularArcHeight x) = _
      at hneg
  change
    d4BMActualSecondStokesRadialCurrentAt P Q x (d4BMModularArcHeight x) = _
      at hpos
  simp only [d4BMStokesCoordinate, max_eq_left harchalf] at hneg hpos
  rw [hneg, hpos] at hpair
  unfold d4BMActualSecondStokesCircularBoundaryFlux
  rw [Complex.real_smul, Complex.ofReal_div]
  unfold d4BMActualSecondStokesHorizontalCurrentAt
    d4BMActualSecondStokesVerticalCurrentAt
  simp only [d4BMStokesCoordinate, max_eq_left harchalf]
  have harcC : (d4BMModularArcHeight x : ℂ) ≠ 0 := by
    exact_mod_cast harcpos.ne'
  push_cast at hpair ⊢
  field_simp [harcC]
  linear_combination -hpair

theorem intervalIntegral_d4BMActualSecondStokesVerticalDivergenceAt_eq_sub
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter)
    (x a b : ℝ) (hx : x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2))
    (ha : (1 / 2 : ℝ) ≤ a) (hb : (1 / 2 : ℝ) ≤ b) :
    (∫ y in a..b, d4BMActualSecondStokesVerticalDivergenceAt P Q x y) =
      d4BMActualSecondStokesVerticalCurrentAt P Q x b -
        d4BMActualSecondStokesVerticalCurrentAt P Q x a := by
  calc
    (∫ y in a..b, d4BMActualSecondStokesVerticalDivergenceAt P Q x y) =
        ∫ y in a..b,
          d4BMActualSecondStokesVerticalDivergenceSlice
            (d4BMStokesCoordinate x 1) P Q y := by
      apply intervalIntegral.integral_congr
      intro y hy
      have hyhalf : (1 / 2 : ℝ) ≤ y := by
        rcases mem_uIcc.mp hy with hab | hba
        · exact ha.trans hab.1
        · exact hb.trans hba.1
      exact (d4BMActualSecondStokesVerticalDivergenceSlice_eq_at
        P Q x y hyhalf).symm
    _ = d4BMActualSecondStokesVerticalCurrentSlice
          (d4BMStokesCoordinate x 1) P Q b -
        d4BMActualSecondStokesVerticalCurrentSlice
          (d4BMStokesCoordinate x 1) P Q a :=
      intervalIntegral_d4BMActualSecondStokesVerticalDivergenceSlice_eq_sub
        (d4BMStokesCoordinate x 1) P Q hx ha hb
    _ = d4BMActualSecondStokesVerticalCurrentAt P Q x b -
        d4BMActualSecondStokesVerticalCurrentAt P Q x a := by
      rw [d4BMActualSecondStokesVerticalCurrentSlice_eq_at P Q x b hb,
        d4BMActualSecondStokesVerticalCurrentSlice_eq_at P Q x a ha]

/-- Literal paired-coordinate integral of the vertical divergence on both halves of the truncated
modular domain and the horizontal divergence on both lower side slivers.  The omitted upper-strip
horizontal integral is identically zero by
`d4BM_actualSecondStokesHorizontalUpperBulk_eq_zero`. -/
def d4BMActualSecondStokesPairedTruncatedBulk
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) (Y : ℝ) : ℂ :=
  ∫ x in 0..(1 / 2),
    ((∫ y in d4BMModularArcHeight x..Y,
        d4BMActualSecondStokesVerticalDivergenceAt P Q (-x) y) +
      (∫ y in d4BMModularArcHeight x..Y,
        d4BMActualSecondStokesVerticalDivergenceAt P Q x y) +
      (x / d4BMModularArcHeight x) •
        ((∫ q in (-(1 / 2 : ℝ))..(-x),
            d4BMActualSecondStokesHorizontalDivergenceAt P Q q
              (d4BMModularArcHeight x)) +
          ∫ q in x..(1 / 2),
            d4BMActualSecondStokesHorizontalDivergenceAt P Q q
              (d4BMModularArcHeight x)))

def d4BMActualSecondStokesPairedCuspTop
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) (Y : ℝ) : ℂ :=
  ∫ x in 0..(1 / 2),
    (d4BMActualSecondStokesVerticalCurrentAt P Q (-x) Y +
      d4BMActualSecondStokesVerticalCurrentAt P Q x Y)

/-- Literal two-dimensional Green theorem on the truncated standard modular domain.  Every
vertical fibre and both curved side slivers are actual iterated interval integrals; FTC, translation,
the arc Jacobian, and inversion leave exactly the paired cusp-top current. -/
theorem d4BM_actualSecondStokesPairedTruncatedBulk_eq_cuspTop
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter)
    {Y : ℝ} (hY : 1 ≤ Y) :
    d4BMActualSecondStokesPairedTruncatedBulk P Q Y =
      d4BMActualSecondStokesPairedCuspTop P Q Y := by
  unfold d4BMActualSecondStokesPairedTruncatedBulk
    d4BMActualSecondStokesPairedCuspTop
  apply intervalIntegral.integral_congr
  intro x hx
  have hxI : x ∈ Set.Icc (0 : ℝ) (1 / 2) := by
    simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] using hx
  have hxfull : x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := ⟨by linarith [hxI.1], hxI.2⟩
  have harchalf := d4BMModularArcHeight_half_le hxfull
  have hYhalf : (1 / 2 : ℝ) ≤ Y := by linarith
  change
    (∫ y in d4BMModularArcHeight x..Y,
        d4BMActualSecondStokesVerticalDivergenceAt P Q (-x) y) +
      (∫ y in d4BMModularArcHeight x..Y,
        d4BMActualSecondStokesVerticalDivergenceAt P Q x y) +
      (x / d4BMModularArcHeight x) •
        ((∫ q in (-(1 / 2 : ℝ))..(-x),
            d4BMActualSecondStokesHorizontalDivergenceAt P Q q
              (d4BMModularArcHeight x)) +
          ∫ q in x..(1 / 2),
            d4BMActualSecondStokesHorizontalDivergenceAt P Q q
              (d4BMModularArcHeight x)) = _
  rw [intervalIntegral_d4BMActualSecondStokesVerticalDivergenceAt_eq_sub
      P Q (-x) (d4BMModularArcHeight x) Y
        (by constructor <;> linarith [hxI.1, hxI.2]) harchalf hYhalf,
    intervalIntegral_d4BMActualSecondStokesVerticalDivergenceAt_eq_sub
      P Q x (d4BMModularArcHeight x) Y hxfull harchalf hYhalf,
    intervalIntegral_d4BMActualSecondStokesHorizontalDivergenceAt_eq_sub
      P Q (d4BMModularArcHeight x) (-(1 / 2)) (-x) harchalf
        (by constructor <;> norm_num)
        (by constructor <;> linarith [hxI.1, hxI.2]),
    intervalIntegral_d4BMActualSecondStokesHorizontalDivergenceAt_eq_sub
      P Q (d4BMModularArcHeight x) x (1 / 2) harchalf hxfull
        (by constructor <;> norm_num),
    d4BM_actualSecondStokesHorizontalCurrentAt_verticalSides P Q
      (d4BMModularArcHeight x)]
  have hflux := d4BM_actualSecondStokesCircularBoundaryFlux_eq_zero P Q hxI
  unfold d4BMActualSecondStokesCircularBoundaryFlux at hflux
  rw [Complex.real_smul] at hflux ⊢
  linear_combination hflux

/-- Pointwise hyperbolic-measure form of the actual second defect on every literal integration
coordinate.  This is the exact density bridge needed before any Fubini interchange. -/
theorem d4BM_actualSecondStokesDefectDensity_div_heightSq_eq_divergenceAt
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter)
    (x y : ℝ) (hy : (1 / 2 : ℝ) ≤ y) :
    (2 * d4BMActualSecondStokesDefectDensity (d4BMStokesCoordinate x y) P Q) /
        (y : ℂ) ^ (2 : ℕ) =
      d4BMActualSecondStokesHorizontalDivergenceAt P Q x y +
        d4BMActualSecondStokesVerticalDivergenceAt P Q x y := by
  have h := d4BM_actualSecondStokesDefectDensity_eq_divergence
    (d4BMStokesCoordinate x y) P Q
  have hy0 : (y : ℂ) ≠ 0 := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num) hy).ne'
  unfold d4BMActualSecondStokesHorizontalDivergenceAt
    d4BMActualSecondStokesVerticalDivergenceAt
  simp only [d4BMStokesCoordinate, max_eq_left hy] at h ⊢
  rw [h]
  field_simp

def d4BMActualSecondStokesTotalDivergenceAt
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) (w : ℝ × ℝ) : ℂ :=
  d4BMActualSecondStokesHorizontalDivergenceAt P Q w.1 w.2 +
    d4BMActualSecondStokesVerticalDivergenceAt P Q w.1 w.2

theorem continuousOn_d4BMActualSecondStokesTotalDivergence_stokesCompactCell
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) {Y : ℝ} :
    ContinuousOn (d4BMActualSecondStokesTotalDivergenceAt P Q)
      (d4BMStokesCompactCell Y) := by
  exact
    (continuousOn_d4BMActualSecondStokesHorizontalDivergence_stokesCompactCell
      P Q (Y := Y)).add
    (continuousOn_d4BMActualSecondStokesVerticalDivergence_stokesCompactCell
      P Q (Y := Y))

theorem integrableOn_d4BMActualSecondStokesTotalDivergence_truncatedDomain
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) (Y : ℝ) :
    IntegrableOn (d4BMActualSecondStokesTotalDivergenceAt P Q)
      (d4BMTruncatedModularDomain Y) := by
  apply ContinuousOn.integrableOn_compact (isCompact_d4BMTruncatedModularDomain Y)
  exact (continuousOn_d4BMActualSecondStokesTotalDivergence_stokesCompactCell
    P Q (Y := Y)).mono (d4BMTruncatedModularDomain_subset_stokesCompactCell Y)

def d4BMActualSecondStokesTruncatedDefectMoment
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) (Y : ℝ) : ℂ :=
  ∫ w in d4BMTruncatedModularDomain Y,
    (2 * d4BMActualSecondStokesDefectDensity (d4BMStokesPairCoordinate w) P Q) /
      (w.2 : ℂ) ^ (2 : ℕ)

/-- The standard hyperbolic first-defect moment is the integral of the actual Euclidean
divergence on the genuine truncated modular domain. -/
theorem d4BM_actualSecondStokesTruncatedDefectMoment_eq_totalDivergence
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter)
    {Y : ℝ} (_hY : 1 ≤ Y) :
    d4BMActualSecondStokesTruncatedDefectMoment P Q Y =
      ∫ w in d4BMTruncatedModularDomain Y,
        d4BMActualSecondStokesTotalDivergenceAt P Q w := by
  unfold d4BMActualSecondStokesTruncatedDefectMoment
  apply MeasureTheory.setIntegral_congr_fun
    (isCompact_d4BMTruncatedModularDomain Y).measurableSet
  intro w hw
  have hwcell := (d4BMTruncatedModularDomain_subset_stokesCompactCell Y) hw
  have hy : (1 / 2 : ℝ) ≤ w.2 := hwcell.2.1
  exact d4BM_actualSecondStokesDefectDensity_div_heightSq_eq_divergenceAt
    P Q w.1 w.2 hy

theorem continuous_d4BMActualSecondStokesHorizontalDivergenceAt_fixedHeight
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) {y : ℝ}
    (hy : (1 / 2 : ℝ) ≤ y) :
    ContinuousOn (fun x : ℝ =>
      d4BMActualSecondStokesHorizontalDivergenceAt P Q x y)
      (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) := by
  have hmap : MapsTo (fun x : ℝ => (x, y))
      (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) (d4BMStokesCompactCell y) := by
    intro x hx
    exact ⟨hx, hy, le_rfl⟩
  have h :=
    (continuousOn_d4BMActualSecondStokesHorizontalDivergence_stokesCompactCell
      P Q (Y := y)).comp (continuous_id.prodMk continuous_const).continuousOn hmap
  simpa [Function.comp_def, d4BMActualSecondStokesHorizontalDivergenceAt,
    d4BMStokesPairCoordinate] using h

theorem d4BMActualSecondStokesHorizontalSetSlice_eq_fullInterval
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter)
    {Y y : ℝ} (hy : y ∈ Set.Icc 1 Y) :
    d4BMTruncatedHorizontalSetSlice
        (fun w => d4BMActualSecondStokesHorizontalDivergenceAt P Q w.1 w.2) Y y =
      ∫ x in (-(1 / 2 : ℝ))..(1 / 2),
        d4BMActualSecondStokesHorizontalDivergenceAt P Q x y := by
  unfold d4BMTruncatedHorizontalSetSlice
  rw [d4BMTruncatedHorizontalSlice_eq_full hy,
    intervalIntegral.integral_of_le (by norm_num),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]

theorem d4BMActualSecondStokesHorizontalSetSlice_eq_sideIntervals
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter)
    {Y y : ℝ} (hY : 1 ≤ Y)
    (hy : y ∈ Set.Icc d4BMModularArcFloor 1) :
    d4BMTruncatedHorizontalSetSlice
        (fun w => d4BMActualSecondStokesHorizontalDivergenceAt P Q w.1 w.2) Y y =
      (∫ x in (-(1 / 2 : ℝ))..(-d4BMModularSideRadius y),
        d4BMActualSecondStokesHorizontalDivergenceAt P Q x y) +
      ∫ x in d4BMModularSideRadius y..(1 / 2),
        d4BMActualSecondStokesHorizontalDivergenceAt P Q x y := by
  let L : Set ℝ := Set.Icc (-(1 / 2 : ℝ)) (-d4BMModularSideRadius y)
  let R : Set ℝ := Set.Icc (d4BMModularSideRadius y) (1 / 2)
  let f : ℝ → ℂ := fun x =>
    d4BMActualSecondStokesHorizontalDivergenceAt P Q x y
  have hr0 : 0 ≤ d4BMModularSideRadius y := Real.sqrt_nonneg _
  have hrhalf := d4BMModularSideRadius_le_half hy
  have hyhalf : (1 / 2 : ℝ) ≤ y :=
    (le_of_lt d4BMModularArcFloor_gt_half).trans hy.1
  have hcont : ContinuousOn f (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) := by
    exact continuous_d4BMActualSecondStokesHorizontalDivergenceAt_fixedHeight P Q hyhalf
  have hLsub : L ⊆ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := by
    intro x hx
    exact ⟨hx.1, hx.2.trans (by linarith)⟩
  have hRsub : R ⊆ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := by
    intro x hx
    exact ⟨(by linarith [hx.1]), hx.2⟩
  have hLint : IntegrableOn f L :=
    (hcont.mono hLsub).integrableOn_compact isCompact_Icc
  have hRint : IntegrableOn f R :=
    (hcont.mono hRsub).integrableOn_compact isCompact_Icc
  have haedis : AEDisjoint volume L R := by
    unfold AEDisjoint
    apply MeasureTheory.measure_mono_null (t := ({0} : Set ℝ))
    · intro x hx
      change x ∈ Set.Icc (-(1 / 2 : ℝ)) (-d4BMModularSideRadius y) ∧
        x ∈ Set.Icc (d4BMModularSideRadius y) (1 / 2) at hx
      simp only [Set.mem_singleton_iff]
      linarith [hx.1.2, hx.2.1]
    · exact MeasureTheory.measure_singleton 0
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

theorem integrableOn_d4BMActualSecondStokesHorizontalDivergence_truncatedDomain
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) (Y : ℝ) :
    IntegrableOn
      (fun w : ℝ × ℝ =>
        d4BMActualSecondStokesHorizontalDivergenceAt P Q w.1 w.2)
      (d4BMTruncatedModularDomain Y) := by
  apply ContinuousOn.integrableOn_compact (isCompact_d4BMTruncatedModularDomain Y)
  exact (continuousOn_d4BMActualSecondStokesHorizontalDivergence_stokesCompactCell
    P Q (Y := Y)).mono (d4BMTruncatedModularDomain_subset_stokesCompactCell Y)

theorem integrableOn_d4BMActualSecondStokesVerticalDivergence_truncatedDomain
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) (Y : ℝ) :
    IntegrableOn
      (fun w : ℝ × ℝ =>
        d4BMActualSecondStokesVerticalDivergenceAt P Q w.1 w.2)
      (d4BMTruncatedModularDomain Y) := by
  apply ContinuousOn.integrableOn_compact (isCompact_d4BMTruncatedModularDomain Y)
  exact (continuousOn_d4BMActualSecondStokesVerticalDivergence_stokesCompactCell
    P Q (Y := Y)).mono (d4BMTruncatedModularDomain_subset_stokesCompactCell Y)

/-- Horizontal Fubini identification: the standard two-dimensional integral of the horizontal
actual divergence is exactly the lower-side-sliver plus upper-strip bulk already used by the
literal Green theorem. -/
theorem d4BM_setIntegral_actualSecondStokesHorizontalDivergence_eq_horizontalBulk
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter)
    {Y : ℝ} (hY : 1 ≤ Y) :
    (∫ w in d4BMTruncatedModularDomain Y,
        d4BMActualSecondStokesHorizontalDivergenceAt P Q w.1 w.2) =
      d4BMActualSecondStokesHorizontalBulk P Q Y := by
  let f : ℝ × ℝ → ℂ := fun w =>
    d4BMActualSecondStokesHorizontalDivergenceAt P Q w.1 w.2
  let S : ℝ → ℂ := fun y => d4BMTruncatedHorizontalSetSlice f Y y
  have hf := integrableOn_d4BMActualSecondStokesHorizontalDivergence_truncatedDomain P Q Y
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
        d4BMActualSecondStokesHorizontalDivergenceAt P Q w.1 w.2) =
        ∫ y, S y := by
      exact d4BM_setIntegral_truncatedDomain_eq_horizontalSetSlices hf
    _ = ∫ y in d4BMModularArcFloor..Y, S y :=
      integral_d4BMTruncatedHorizontalSetSlice_eq_interval f hY
    _ = (∫ y in d4BMModularArcFloor..1, S y) + ∫ y in 1..Y, S y := hsplit
    _ = d4BMActualSecondStokesHorizontalLowerBulk P Q +
        d4BMActualSecondStokesHorizontalUpperBulk P Q Y := by
      congr 1
      · unfold d4BMActualSecondStokesHorizontalLowerBulk
        apply intervalIntegral.integral_congr
        intro y hy
        have hyI : y ∈ Set.Icc d4BMModularArcFloor 1 := by
          simpa [uIcc_of_le hfloorOne] using hy
        exact d4BMActualSecondStokesHorizontalSetSlice_eq_sideIntervals P Q hY hyI
      · unfold d4BMActualSecondStokesHorizontalUpperBulk
        apply intervalIntegral.integral_congr
        intro y hy
        have hyI : y ∈ Set.Icc 1 Y := by
          simpa [uIcc_of_le hY] using hy
        exact d4BMActualSecondStokesHorizontalSetSlice_eq_fullInterval P Q hyI
    _ = d4BMActualSecondStokesHorizontalBulk P Q Y := rfl

theorem d4BM_setIntegral_actualSecondStokesVerticalDivergence_eq_verticalBulk
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter)
    {Y : ℝ} (hY : 1 ≤ Y) :
    (∫ w in d4BMTruncatedModularDomain Y,
        d4BMActualSecondStokesVerticalDivergenceAt P Q w.1 w.2) =
      d4BMActualSecondStokesVerticalBulk P Q Y := by
  unfold d4BMActualSecondStokesVerticalBulk
  exact d4BM_setIntegral_truncatedDomain_eq_verticalSlices hY
    (integrableOn_d4BMActualSecondStokesVerticalDivergence_truncatedDomain P Q Y)

theorem d4BM_setIntegral_actualSecondStokesTotalDivergence_eq_horizontalBulk_add_verticalBulk
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter)
    {Y : ℝ} (hY : 1 ≤ Y) :
    (∫ w in d4BMTruncatedModularDomain Y,
        d4BMActualSecondStokesTotalDivergenceAt P Q w) =
      d4BMActualSecondStokesHorizontalBulk P Q Y +
        d4BMActualSecondStokesVerticalBulk P Q Y := by
  have hH := integrableOn_d4BMActualSecondStokesHorizontalDivergence_truncatedDomain P Q Y
  have hV := integrableOn_d4BMActualSecondStokesVerticalDivergence_truncatedDomain P Q Y
  unfold d4BMActualSecondStokesTotalDivergenceAt
  rw [MeasureTheory.integral_add hH hV,
    d4BM_setIntegral_actualSecondStokesHorizontalDivergence_eq_horizontalBulk P Q hY,
    d4BM_setIntegral_actualSecondStokesVerticalDivergence_eq_verticalBulk P Q hY]

/-- The standard hyperbolic actual second-defect moment is exactly the coordinate-split literal
Green bulk.  This is the Fubini bridge absent from the prior boundary proof. -/
theorem d4BM_actualSecondStokesTruncatedDefectMoment_eq_horizontalBulk_add_verticalBulk
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter)
    {Y : ℝ} (hY : 1 ≤ Y) :
    d4BMActualSecondStokesTruncatedDefectMoment P Q Y =
      d4BMActualSecondStokesHorizontalBulk P Q Y +
        d4BMActualSecondStokesVerticalBulk P Q Y := by
  rw [d4BM_actualSecondStokesTruncatedDefectMoment_eq_totalDivergence P Q hY,
    d4BM_setIntegral_actualSecondStokesTotalDivergence_eq_horizontalBulk_add_verticalBulk P Q hY]


theorem continuousOn_d4BMActualSecondStokesHorizontalCurrent_stokesCompactCell
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) {Y : ℝ} :
    ContinuousOn
      (fun w : ℝ × ℝ => d4BMActualSecondStokesHorizontalCurrentAt P Q w.1 w.2)
      (d4BMStokesCompactCell Y) := by
  have hG := continuousOn_d4BMCompletedEisensteinPoincareSeries_stokesCompactCell
    Q (Y := Y)
  have hFx := continuousOn_d4BMCompletedPoincareHorizontalFirstJet_stokesCompactCell
    P (Y := Y)
  have hFy := continuousOn_d4BMCompletedPoincareVerticalFirstJet_stokesCompactCell
    P (Y := Y)
  have hFxx := continuousOn_d4BMCompletedPoincareHorizontalSecondJet_stokesCompactCell
    P (Y := Y)
  have hFxy := continuousOn_d4BMCompletedPoincareMixedSecondJet_stokesCompactCell
    P (Y := Y)
  have hGx := continuousOn_d4BMCompletedPoincareHorizontalFirstJet_stokesCompactCell
    Q (Y := Y)
  have hE : ContinuousOn
      (fun w : ℝ × ℝ => d4BMActualSecondStokesEnergy (d4BMStokesPairCoordinate w) P)
      (d4BMStokesCompactCell Y) := by
    unfold d4BMActualSecondStokesEnergy
    fun_prop
  have hEx : ContinuousOn
      (fun w : ℝ × ℝ =>
        d4BMActualSecondStokesEnergyHorizontalFirstJet (d4BMStokesPairCoordinate w) P)
      (d4BMStokesCompactCell Y) := by
    unfold d4BMActualSecondStokesEnergyHorizontalFirstJet
    fun_prop
  unfold d4BMActualSecondStokesHorizontalCurrentAt d4BMActualSecondStokesHorizontalCurrent
  change ContinuousOn
    (fun w : ℝ × ℝ =>
      d4BMCompletedEisensteinPoincareSeries (d4BMStokesPairCoordinate w) Q *
          d4BMActualSecondStokesEnergyHorizontalFirstJet (d4BMStokesPairCoordinate w) P -
        d4BMActualSecondStokesEnergy (d4BMStokesPairCoordinate w) P *
          d4BMCompletedPoincareHorizontalFirstJet (d4BMStokesPairCoordinate w) Q)
      (d4BMStokesCompactCell Y)
  exact hG.mul hEx |>.sub (hE.mul hGx)

theorem continuousOn_d4BMActualSecondStokesVerticalCurrent_stokesCompactCell
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) {Y : ℝ} :
    ContinuousOn
      (fun w : ℝ × ℝ => d4BMActualSecondStokesVerticalCurrentAt P Q w.1 w.2)
      (d4BMStokesCompactCell Y) := by
  have hG := continuousOn_d4BMCompletedEisensteinPoincareSeries_stokesCompactCell
    Q (Y := Y)
  have hFx := continuousOn_d4BMCompletedPoincareHorizontalFirstJet_stokesCompactCell
    P (Y := Y)
  have hFy := continuousOn_d4BMCompletedPoincareVerticalFirstJet_stokesCompactCell
    P (Y := Y)
  have hFxy := continuousOn_d4BMCompletedPoincareMixedSecondJet_stokesCompactCell
    P (Y := Y)
  have hFyy := continuousOn_d4BMCompletedPoincareVerticalSecondJet_stokesCompactCell
    P (Y := Y)
  have hGy := continuousOn_d4BMCompletedPoincareVerticalFirstJet_stokesCompactCell
    Q (Y := Y)
  have hE : ContinuousOn
      (fun w : ℝ × ℝ => d4BMActualSecondStokesEnergy (d4BMStokesPairCoordinate w) P)
      (d4BMStokesCompactCell Y) := by
    unfold d4BMActualSecondStokesEnergy
    fun_prop
  have hEy : ContinuousOn
      (fun w : ℝ × ℝ =>
        d4BMActualSecondStokesEnergyVerticalFirstJet (d4BMStokesPairCoordinate w) P)
      (d4BMStokesCompactCell Y) := by
    unfold d4BMActualSecondStokesEnergyVerticalFirstJet
    fun_prop
  unfold d4BMActualSecondStokesVerticalCurrentAt d4BMActualSecondStokesVerticalCurrent
  change ContinuousOn
    (fun w : ℝ × ℝ =>
      d4BMCompletedEisensteinPoincareSeries (d4BMStokesPairCoordinate w) Q *
          d4BMActualSecondStokesEnergyVerticalFirstJet (d4BMStokesPairCoordinate w) P -
        d4BMActualSecondStokesEnergy (d4BMStokesPairCoordinate w) P *
          d4BMCompletedPoincareVerticalFirstJet (d4BMStokesPairCoordinate w) Q)
      (d4BMStokesCompactCell Y)
  exact hG.mul hEy |>.sub (hE.mul hGy)

def d4BMActualSecondStokesVerticalBoundaryIntegrand
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) (Y x : ℝ) : ℂ :=
  d4BMActualSecondStokesVerticalCurrentAt P Q x Y -
    d4BMActualSecondStokesVerticalCurrentAt P Q x (d4BMModularArcHeight x)

theorem continuousOn_d4BMActualSecondStokesVerticalBoundaryIntegrand
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter)
    {Y : ℝ} (hY : 1 ≤ Y) :
    ContinuousOn (d4BMActualSecondStokesVerticalBoundaryIntegrand P Q Y)
      (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) := by
  let I : Set ℝ := Set.Icc (-(1 / 2 : ℝ)) (1 / 2)
  have hcurrent := continuousOn_d4BMActualSecondStokesVerticalCurrent_stokesCompactCell
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
  unfold d4BMActualSecondStokesVerticalBoundaryIntegrand
  exact htop.sub harc

theorem intervalIntegral_d4BMActualSecondStokesVerticalBoundaryIntegrand_fold
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter)
    {Y : ℝ} (hY : 1 ≤ Y) :
    (∫ x in (-(1 / 2 : ℝ))..(1 / 2),
        d4BMActualSecondStokesVerticalBoundaryIntegrand P Q Y x) =
      ∫ x in 0..(1 / 2),
        (d4BMActualSecondStokesVerticalBoundaryIntegrand P Q Y (-x) +
          d4BMActualSecondStokesVerticalBoundaryIntegrand P Q Y x) := by
  let B := d4BMActualSecondStokesVerticalBoundaryIntegrand P Q Y
  have hB := continuousOn_d4BMActualSecondStokesVerticalBoundaryIntegrand P Q hY
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

theorem continuousOn_d4BMActualSecondStokesHorizontalArcParameterFlux
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) :
    ContinuousOn (d4BMActualSecondStokesHorizontalArcParameterFlux P Q)
      (Set.Icc (0 : ℝ) (1 / 2)) := by
  let I : Set ℝ := Set.Icc (0 : ℝ) (1 / 2)
  have hcurrent := continuousOn_d4BMActualSecondStokesHorizontalCurrent_stokesCompactCell
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
  unfold d4BMActualSecondStokesHorizontalArcParameterFlux
  exact hratio.smul (hneg.sub hpos)

/-- Closed compact-cell Green theorem for the standard horizontal-plus-vertical bulk: arc
inversion cancels the full circular boundary after Fubini, leaving exactly the paired cusp top. -/
theorem d4BM_actualSecondStokesHorizontalBulk_add_verticalBulk_eq_pairedCuspTop
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter)
    {Y : ℝ} (hY : 1 ≤ Y) :
    d4BMActualSecondStokesHorizontalBulk P Q Y +
        d4BMActualSecondStokesVerticalBulk P Q Y =
      d4BMActualSecondStokesPairedCuspTop P Q Y := by
  let H : ℝ → ℂ := d4BMActualSecondStokesHorizontalArcParameterFlux P Q
  let B : ℝ → ℂ := d4BMActualSecondStokesVerticalBoundaryIntegrand P Q Y
  let T : ℝ → ℂ := fun x =>
    d4BMActualSecondStokesVerticalCurrentAt P Q (-x) Y +
      d4BMActualSecondStokesVerticalCurrentAt P Q x Y
  have hHbulk : d4BMActualSecondStokesHorizontalBulk P Q Y =
      ∫ x in 0..(1 / 2), H x := by
    calc
      d4BMActualSecondStokesHorizontalBulk P Q Y =
          ∫ y in d4BMModularArcFloor..1,
            d4BMActualSecondStokesHorizontalArcHeightFlux P Q y :=
        d4BM_actualSecondStokesHorizontalBulk_eq_arc P Q hY
      _ = ∫ x in 0..(1 / 2), H x := by
        exact d4BM_actualSecondStokesHorizontalArc_changeOfVariables P Q
  have hVbulk : d4BMActualSecondStokesVerticalBulk P Q Y =
      ∫ x in 0..(1 / 2), (B (-x) + B x) := by
    rw [d4BM_actualSecondStokesVerticalBulk_eq_boundary P Q hY]
    change (∫ x in (-(1 / 2 : ℝ))..(1 / 2), B x) = _
    exact intervalIntegral_d4BMActualSecondStokesVerticalBoundaryIntegrand_fold P Q hY
  have hHcont := continuousOn_d4BMActualSecondStokesHorizontalArcParameterFlux P Q
  have hHint : IntervalIntegrable H volume 0 (1 / 2) := by
    have h : ContinuousOn H (uIcc 0 (1 / 2)) := by
      simpa [H, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] using hHcont
    exact h.intervalIntegrable
  have hBcont := continuousOn_d4BMActualSecondStokesVerticalBoundaryIntegrand P Q hY
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
    d4BMActualSecondStokesHorizontalBulk P Q Y +
        d4BMActualSecondStokesVerticalBulk P Q Y =
        (∫ x in 0..(1 / 2), H x) +
          ∫ x in 0..(1 / 2), (B (-x) + B x) := by rw [hHbulk, hVbulk]
    _ = ∫ x in 0..(1 / 2), (H x + (B (-x) + B x)) := hadd.symm
    _ = ∫ x in 0..(1 / 2), T x := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hxI : x ∈ Set.Icc (0 : ℝ) (1 / 2) := by
        simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] using hx
      have hflux := d4BM_actualSecondStokesCircularBoundaryFlux_eq_zero P Q hxI
      dsimp only [H, B, T, d4BMActualSecondStokesVerticalBoundaryIntegrand]
      rw [d4BMModularArcHeight_neg]
      unfold d4BMActualSecondStokesCircularBoundaryFlux at hflux
      unfold d4BMActualSecondStokesHorizontalArcParameterFlux
      linear_combination hflux
    _ = d4BMActualSecondStokesPairedCuspTop P Q Y := rfl

/-- **C-A.9t4d: standard truncated second-moment reduction.** The actual hyperbolic defect,
integrated with the standard two-dimensional Lebesgue measure on the truncated modular domain,
equals the genuine paired cusp-top Green current. -/
theorem d4BM_actualSecondStokesTruncatedDefectMoment_eq_pairedCuspTop
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter)
    {Y : ℝ} (hY : 1 ≤ Y) :
    d4BMActualSecondStokesTruncatedDefectMoment P Q Y =
      d4BMActualSecondStokesPairedCuspTop P Q Y := by
  rw [d4BM_actualSecondStokesTruncatedDefectMoment_eq_horizontalBulk_add_verticalBulk
      P Q hY,
    d4BM_actualSecondStokesHorizontalBulk_add_verticalBulk_eq_pairedCuspTop P Q hY]

/-- **C-A.9t4d.** Standard-measure Fubini and the literal paired-coordinate Green bulk are
the same actual second-defect moment. No boundary, regularization, or integrability premise is
assumed. -/
theorem d4BM_actualSecondStokesTruncatedDefectMoment_eq_pairedTruncatedBulk
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter)
    {Y : ℝ} (hY : 1 ≤ Y) :
    d4BMActualSecondStokesTruncatedDefectMoment P Q Y =
      d4BMActualSecondStokesPairedTruncatedBulk P Q Y := by
  calc
    d4BMActualSecondStokesTruncatedDefectMoment P Q Y =
        d4BMActualSecondStokesPairedCuspTop P Q Y :=
      d4BM_actualSecondStokesTruncatedDefectMoment_eq_pairedCuspTop P Q hY
    _ = d4BMActualSecondStokesPairedTruncatedBulk P Q Y :=
      (d4BM_actualSecondStokesPairedTruncatedBulk_eq_cuspTop P Q hY).symm

end
end RHTower
