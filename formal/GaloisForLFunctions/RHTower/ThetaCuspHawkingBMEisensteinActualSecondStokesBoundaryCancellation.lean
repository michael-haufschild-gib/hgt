import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinActualSecondStokesCurrent

/-!
# Exact non-cusp cancellation for the actual second Bochner--Stokes current

Corpus conjecture C-A.9t4c asks for the modular-boundary and cusp closure of the literal second
Stokes current.  This module closes its complete non-cusp half.  The proof is source-level: it
derives the full inversion covariance of the actual completed Poincare gradient and of its
radial Hessian contraction by reindexing the primitive-pair series.  Consequently the
hyperbolic energy is inversion invariant, its radial derivative is anti-invariant, and the
radial second-Stokes current cancels on the paired unit semicircle.  Translation cancels the
vertical sides.

The RH chain is

`actual second-current non-cusp cancellation -> second modular Green/Stokes + cusp finite part ->
actual balanced BM ++- coefficient -> negative BM leg -> conserved left-QNM projection -> HC94 ->
RH`.

`[BRIDGE] [PAPER-PROVED] [LEAN-PROVED] [HC94] [SECOND STOKES NON-CUSP CLOSURE]`
-/

open Complex Real Filter Set Topology
open scoped BigOperators

namespace RHTower
noncomputable section

set_option maxHeartbeats 800000

theorem d4BM_completedPoincareMixedSecondJet_translate
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMCompletedPoincareMixedSecondJet
        (d4BMEisensteinTranslateCoordinate z) P =
      d4BMCompletedPoincareMixedSecondJet z P := by
  let f₁ : ℝ → ℂ := fun x =>
    d4BMCompletedPoincareVerticalFirstJet (d4BMHorizontalCoordinate z x) P
  let f₂ : ℝ → ℂ := fun x =>
    d4BMCompletedPoincareMixedSecondJet (d4BMHorizontalCoordinate z x) P
  have hper₁ : Function.Periodic f₁ 1 := by
    intro x
    dsimp only [f₁]
    simpa [d4BMHorizontalCoordinate, d4BMEisensteinTranslateCoordinate] using
      d4BM_completedPoincareVerticalFirstJet_translate
        (d4BMHorizontalCoordinate z x) P
  have hright : HasDerivAt f₁ (f₂ z.x) z.x := by
    simpa [f₁, f₂, d4BMHorizontalCoordinate] using
      hasDerivAt_d4BMCompletedPoincareVerticalFirstJet_horizontal z P
  have hleftBase : HasDerivAt f₁ (f₂ (z.x + 1)) (z.x + 1) := by
    simpa [f₁, f₂, d4BMHorizontalCoordinate] using
      hasDerivAt_d4BMCompletedPoincareVerticalFirstJet_horizontal
        (d4BMHorizontalCoordinate z (z.x + 1)) P
  have hshift : HasDerivAt (fun x : ℝ => x + 1) 1 z.x := by
    simpa using (hasDerivAt_id z.x).add_const 1
  have hleft := hleftBase.scomp z.x hshift
  have hfun : (fun x : ℝ => f₁ (x + 1)) = f₁ := funext hper₁
  have hleft' : HasDerivAt f₁ (f₂ (z.x + 1)) z.x := by
    rw [← hfun]
    simpa [Function.comp_def] using hleft
  have hvalue : f₂ (z.x + 1) = f₂ z.x := hleft'.unique hright
  simpa [f₂, d4BMHorizontalCoordinate, d4BMEisensteinTranslateCoordinate] using hvalue

theorem d4BM_poincareSeedGradient_invert_horizontal
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) :
    d4BMPoincareSeedHorizontalFirstJet (d4BMEisensteinInvertCoordinate z) s p =
      (((z.x : ℂ) ^ 2 - (z.y : ℂ) ^ 2) *
          d4BMPoincareSeedHorizontalFirstJet z s
            (d4BMEisensteinRotatePrimitivePair p) +
        2 * (z.x : ℂ) * (z.y : ℂ) *
          d4BMPoincareSeedVerticalFirstJet z s
            (d4BMEisensteinRotatePrimitivePair p)) := by
  let q := d4BMEisensteinRotatePrimitivePair p
  have hR : z.x ^ 2 + z.y ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg z.x, sq_pos_of_pos z.y_pos]
  have hRC : (z.x : ℂ) ^ 2 + (z.y : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hR
  have hy : (z.y : ℂ) ≠ 0 := by exact_mod_cast z.y_pos.ne'
  have hQ : d4BMPoincareQuadratic z q.pair ≠ 0 :=
    ne_of_gt (d4BMPoincareQuadratic_pos z q.pair q.pair_ne_zero)
  have hQC : (d4BMPoincareQuadratic z q.pair : ℂ) ≠ 0 := by exact_mod_cast hQ
  have hQformula : (d4BMPoincareQuadratic z q.pair : ℂ) =
      ((p.pair.2 : ℂ) * (z.y : ℂ)) ^ 2 +
        ((p.pair.2 : ℂ) * (z.x : ℂ) - (p.pair.1 : ℂ)) ^ 2 := by
    dsimp only [q]
    unfold d4BMPoincareQuadratic d4BMEisensteinRotatePrimitivePair
    push_cast
    ring
  have hquad :
      d4BMPoincareQuadratic (d4BMEisensteinInvertCoordinate z) p.pair =
        d4BMPoincareQuadratic z q.pair / (z.x ^ 2 + z.y ^ 2) := by
    dsimp only [q]
    unfold d4BMEisensteinInvertCoordinate d4BMPoincareQuadratic
      d4BMEisensteinRotatePrimitivePair
    field_simp [hR]
    push_cast
    ring
  have hseed := d4BM_poincareSeed_invert z s p
  unfold d4BMPoincareSeedHorizontalFirstJet d4BMPoincareSeedVerticalFirstJet
    d4BMPoincareHorizontalLinear
  rw [hseed, hquad]
  dsimp only [q] at hQ hQC hQformula ⊢
  change d4BMPoincareQuadratic z (p.pair.2, -p.pair.1) ≠ 0 at hQ
  change (d4BMPoincareQuadratic z (p.pair.2, -p.pair.1) : ℂ) ≠ 0 at hQC
  change (d4BMPoincareQuadratic z (p.pair.2, -p.pair.1) : ℂ) =
    ((p.pair.2 : ℂ) * (z.y : ℂ)) ^ 2 +
      ((p.pair.2 : ℂ) * (z.x : ℂ) - (p.pair.1 : ℂ)) ^ 2 at hQformula
  unfold d4BMEisensteinInvertCoordinate d4BMEisensteinRotatePrimitivePair
  push_cast
  field_simp [hRC, hQC, hy]
  rw [hQformula]
  ring

theorem d4BM_poincareSeedGradient_invert_vertical
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) :
    d4BMPoincareSeedVerticalFirstJet (d4BMEisensteinInvertCoordinate z) s p =
      (-2 * (z.x : ℂ) * (z.y : ℂ) *
          d4BMPoincareSeedHorizontalFirstJet z s
            (d4BMEisensteinRotatePrimitivePair p) +
        ((z.x : ℂ) ^ 2 - (z.y : ℂ) ^ 2) *
          d4BMPoincareSeedVerticalFirstJet z s
            (d4BMEisensteinRotatePrimitivePair p)) := by
  let q := d4BMEisensteinRotatePrimitivePair p
  have hR : z.x ^ 2 + z.y ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg z.x, sq_pos_of_pos z.y_pos]
  have hRC : (z.x : ℂ) ^ 2 + (z.y : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hR
  have hy : (z.y : ℂ) ≠ 0 := by exact_mod_cast z.y_pos.ne'
  have hQ : d4BMPoincareQuadratic z q.pair ≠ 0 :=
    ne_of_gt (d4BMPoincareQuadratic_pos z q.pair q.pair_ne_zero)
  have hQC : (d4BMPoincareQuadratic z q.pair : ℂ) ≠ 0 := by exact_mod_cast hQ
  have hQformula : (d4BMPoincareQuadratic z q.pair : ℂ) =
      ((p.pair.2 : ℂ) * (z.y : ℂ)) ^ 2 +
        ((p.pair.2 : ℂ) * (z.x : ℂ) - (p.pair.1 : ℂ)) ^ 2 := by
    dsimp only [q]
    unfold d4BMPoincareQuadratic d4BMEisensteinRotatePrimitivePair
    push_cast
    ring
  have hquad :
      d4BMPoincareQuadratic (d4BMEisensteinInvertCoordinate z) p.pair =
        d4BMPoincareQuadratic z q.pair / (z.x ^ 2 + z.y ^ 2) := by
    dsimp only [q]
    unfold d4BMEisensteinInvertCoordinate d4BMPoincareQuadratic
      d4BMEisensteinRotatePrimitivePair
    field_simp [hR]
    push_cast
    ring
  have hseed := d4BM_poincareSeed_invert z s p
  unfold d4BMPoincareSeedHorizontalFirstJet d4BMPoincareSeedVerticalFirstJet
    d4BMPoincareHorizontalLinear
  rw [hseed, hquad]
  dsimp only [q] at hQ hQC hQformula ⊢
  change d4BMPoincareQuadratic z (p.pair.2, -p.pair.1) ≠ 0 at hQ
  change (d4BMPoincareQuadratic z (p.pair.2, -p.pair.1) : ℂ) ≠ 0 at hQC
  change (d4BMPoincareQuadratic z (p.pair.2, -p.pair.1) : ℂ) =
    ((p.pair.2 : ℂ) * (z.y : ℂ)) ^ 2 +
      ((p.pair.2 : ℂ) * (z.x : ℂ) - (p.pair.1 : ℂ)) ^ 2 at hQformula
  unfold d4BMEisensteinInvertCoordinate d4BMEisensteinRotatePrimitivePair
  push_cast
  field_simp [hRC, hQC, hy]
  rw [hQformula]
  ring

theorem d4BM_completedPoincareGradient_invert_horizontal
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMCompletedPoincareHorizontalFirstJet
        (d4BMEisensteinInvertCoordinate z) P =
      (((z.x : ℂ) ^ 2 - (z.y : ℂ) ^ 2) *
          d4BMCompletedPoincareHorizontalFirstJet z P +
        2 * (z.x : ℂ) * (z.y : ℂ) *
          d4BMCompletedPoincareVerticalFirstJet z P) := by
  let e := d4BMEisensteinRotatePrimitivePairEquiv
  let a : ℂ := (z.x : ℂ) ^ 2 - (z.y : ℂ) ^ 2
  let b : ℂ := 2 * (z.x : ℂ) * (z.y : ℂ)
  have hX : Summable (fun p : D4BMPrimitiveIntegerPair =>
      d4BMPoincareSeedHorizontalFirstJet z P.s p) :=
    summable_d4BMPoincareSeedHorizontalFirstJet z P
  have hY : Summable (fun p : D4BMPrimitiveIntegerPair =>
      d4BMPoincareSeedVerticalFirstJet z P.s p) :=
    summable_d4BMPoincareSeedVerticalFirstJet z P
  have hXe : Summable (fun p : D4BMPrimitiveIntegerPair =>
      d4BMPoincareSeedHorizontalFirstJet z P.s (e p)) := (e.summable_iff).2 hX
  have hYe : Summable (fun p : D4BMPrimitiveIntegerPair =>
      d4BMPoincareSeedVerticalFirstJet z P.s (e p)) := (e.summable_iff).2 hY
  unfold d4BMCompletedPoincareHorizontalFirstJet
    d4BMCompletedPoincareVerticalFirstJet d4BMRawPoincareHorizontalFirstJet
    d4BMRawPoincareVerticalFirstJet
  rw [show (fun p : D4BMPrimitiveIntegerPair =>
      d4BMPoincareSeedHorizontalFirstJet
        (d4BMEisensteinInvertCoordinate z) P.s p) =
      fun p => a * d4BMPoincareSeedHorizontalFirstJet z P.s (e p) +
        b * d4BMPoincareSeedVerticalFirstJet z P.s (e p) by
    funext p
    exact d4BM_poincareSeedGradient_invert_horizontal z P.s p]
  rw [(hXe.mul_left a).tsum_add (hYe.mul_left b), tsum_mul_left, tsum_mul_left,
    e.tsum_eq, e.tsum_eq]
  dsimp only [a, b]
  ring

theorem d4BM_completedPoincareGradient_invert_vertical
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMCompletedPoincareVerticalFirstJet
        (d4BMEisensteinInvertCoordinate z) P =
      (-2 * (z.x : ℂ) * (z.y : ℂ) *
          d4BMCompletedPoincareHorizontalFirstJet z P +
        ((z.x : ℂ) ^ 2 - (z.y : ℂ) ^ 2) *
          d4BMCompletedPoincareVerticalFirstJet z P) := by
  let e := d4BMEisensteinRotatePrimitivePairEquiv
  let a : ℂ := -2 * (z.x : ℂ) * (z.y : ℂ)
  let b : ℂ := (z.x : ℂ) ^ 2 - (z.y : ℂ) ^ 2
  have hX : Summable (fun p : D4BMPrimitiveIntegerPair =>
      d4BMPoincareSeedHorizontalFirstJet z P.s p) :=
    summable_d4BMPoincareSeedHorizontalFirstJet z P
  have hY : Summable (fun p : D4BMPrimitiveIntegerPair =>
      d4BMPoincareSeedVerticalFirstJet z P.s p) :=
    summable_d4BMPoincareSeedVerticalFirstJet z P
  have hXe : Summable (fun p : D4BMPrimitiveIntegerPair =>
      d4BMPoincareSeedHorizontalFirstJet z P.s (e p)) := (e.summable_iff).2 hX
  have hYe : Summable (fun p : D4BMPrimitiveIntegerPair =>
      d4BMPoincareSeedVerticalFirstJet z P.s (e p)) := (e.summable_iff).2 hY
  unfold d4BMCompletedPoincareHorizontalFirstJet
    d4BMCompletedPoincareVerticalFirstJet d4BMRawPoincareHorizontalFirstJet
    d4BMRawPoincareVerticalFirstJet
  rw [show (fun p : D4BMPrimitiveIntegerPair =>
      d4BMPoincareSeedVerticalFirstJet
        (d4BMEisensteinInvertCoordinate z) P.s p) =
      fun p => a * d4BMPoincareSeedHorizontalFirstJet z P.s (e p) +
        b * d4BMPoincareSeedVerticalFirstJet z P.s (e p) by
    funext p
    exact d4BM_poincareSeedGradient_invert_vertical z P.s p]
  rw [(hXe.mul_left a).tsum_add (hYe.mul_left b), tsum_mul_left, tsum_mul_left,
    e.tsum_eq, e.tsum_eq]
  dsimp only [a, b]
  ring

theorem d4BM_actualSecondStokesEnergy_invert
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMActualSecondStokesEnergy (d4BMEisensteinInvertCoordinate z) P =
      d4BMActualSecondStokesEnergy z P := by
  have hR : (z.x : ℂ) ^ 2 + (z.y : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast (show z.x ^ 2 + z.y ^ 2 ≠ 0 by
      nlinarith [sq_nonneg z.x, sq_pos_of_pos z.y_pos])
  unfold d4BMActualSecondStokesEnergy
  rw [d4BM_completedPoincareGradient_invert_horizontal,
    d4BM_completedPoincareGradient_invert_vertical]
  unfold d4BMEisensteinInvertCoordinate
  push_cast
  field_simp [hR]
  ring

/-- Radial contraction of the horizontal row of one seed Hessian. -/
def d4BMPoincareSeedHorizontalGradientRadialJet
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) : ℂ :=
  (z.x : ℂ) * d4BMPoincareSeedHorizontalSecondJet z s p +
    (z.y : ℂ) * d4BMPoincareSeedMixedSecondJet z s p

/-- Radial contraction of the vertical row of one seed Hessian. -/
def d4BMPoincareSeedVerticalGradientRadialJet
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) : ℂ :=
  (z.x : ℂ) * d4BMPoincareSeedMixedSecondJet z s p +
    (z.y : ℂ) * d4BMPoincareSeedVerticalSecondJet z s p

theorem d4BM_poincareSeedHorizontalGradientRadialJet_invert
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) :
    d4BMPoincareSeedHorizontalGradientRadialJet
        (d4BMEisensteinInvertCoordinate z) s p =
      -(((z.x : ℂ) ^ 2 - (z.y : ℂ) ^ 2) *
          (2 * d4BMPoincareSeedHorizontalFirstJet z s
              (d4BMEisensteinRotatePrimitivePair p) +
            d4BMPoincareSeedHorizontalGradientRadialJet z s
              (d4BMEisensteinRotatePrimitivePair p)) +
        2 * (z.x : ℂ) * (z.y : ℂ) *
          (2 * d4BMPoincareSeedVerticalFirstJet z s
              (d4BMEisensteinRotatePrimitivePair p) +
            d4BMPoincareSeedVerticalGradientRadialJet z s
              (d4BMEisensteinRotatePrimitivePair p))) := by
  let q := d4BMEisensteinRotatePrimitivePair p
  have hR : z.x ^ 2 + z.y ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg z.x, sq_pos_of_pos z.y_pos]
  have hRC : (z.x : ℂ) ^ 2 + (z.y : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hR
  have hy : (z.y : ℂ) ≠ 0 := by exact_mod_cast z.y_pos.ne'
  have hQ : d4BMPoincareQuadratic z q.pair ≠ 0 :=
    ne_of_gt (d4BMPoincareQuadratic_pos z q.pair q.pair_ne_zero)
  have hQC : (d4BMPoincareQuadratic z q.pair : ℂ) ≠ 0 := by exact_mod_cast hQ
  have hQformula : (d4BMPoincareQuadratic z q.pair : ℂ) =
      ((p.pair.2 : ℂ) * (z.y : ℂ)) ^ 2 +
        ((p.pair.2 : ℂ) * (z.x : ℂ) - (p.pair.1 : ℂ)) ^ 2 := by
    dsimp only [q]
    unfold d4BMPoincareQuadratic d4BMEisensteinRotatePrimitivePair
    push_cast
    ring
  have hquad :
      d4BMPoincareQuadratic (d4BMEisensteinInvertCoordinate z) p.pair =
        d4BMPoincareQuadratic z q.pair / (z.x ^ 2 + z.y ^ 2) := by
    dsimp only [q]
    unfold d4BMEisensteinInvertCoordinate d4BMPoincareQuadratic
      d4BMEisensteinRotatePrimitivePair
    field_simp [hR]
    push_cast
    ring
  have hseed := d4BM_poincareSeed_invert z s p
  unfold d4BMPoincareSeedHorizontalGradientRadialJet
    d4BMPoincareSeedVerticalGradientRadialJet
    d4BMPoincareSeedHorizontalFirstJet d4BMPoincareSeedVerticalFirstJet
    d4BMPoincareSeedHorizontalSecondJet d4BMPoincareSeedMixedSecondJet
    d4BMPoincareSeedVerticalSecondJet d4BMPoincareHorizontalLinear
  rw [hseed, hquad]
  dsimp only [q] at hQ hQC hQformula ⊢
  change d4BMPoincareQuadratic z (p.pair.2, -p.pair.1) ≠ 0 at hQ
  change (d4BMPoincareQuadratic z (p.pair.2, -p.pair.1) : ℂ) ≠ 0 at hQC
  change (d4BMPoincareQuadratic z (p.pair.2, -p.pair.1) : ℂ) =
    ((p.pair.2 : ℂ) * (z.y : ℂ)) ^ 2 +
      ((p.pair.2 : ℂ) * (z.x : ℂ) - (p.pair.1 : ℂ)) ^ 2 at hQformula
  unfold d4BMEisensteinInvertCoordinate d4BMEisensteinRotatePrimitivePair
  push_cast
  field_simp [hRC, hQC, hy]
  rw [hQformula]
  ring

theorem d4BM_poincareSeedVerticalGradientRadialJet_invert
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) :
    d4BMPoincareSeedVerticalGradientRadialJet
        (d4BMEisensteinInvertCoordinate z) s p =
      -(-2 * (z.x : ℂ) * (z.y : ℂ) *
          (2 * d4BMPoincareSeedHorizontalFirstJet z s
              (d4BMEisensteinRotatePrimitivePair p) +
            d4BMPoincareSeedHorizontalGradientRadialJet z s
              (d4BMEisensteinRotatePrimitivePair p)) +
        ((z.x : ℂ) ^ 2 - (z.y : ℂ) ^ 2) *
          (2 * d4BMPoincareSeedVerticalFirstJet z s
              (d4BMEisensteinRotatePrimitivePair p) +
            d4BMPoincareSeedVerticalGradientRadialJet z s
              (d4BMEisensteinRotatePrimitivePair p))) := by
  let q := d4BMEisensteinRotatePrimitivePair p
  have hR : z.x ^ 2 + z.y ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg z.x, sq_pos_of_pos z.y_pos]
  have hRC : (z.x : ℂ) ^ 2 + (z.y : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hR
  have hy : (z.y : ℂ) ≠ 0 := by exact_mod_cast z.y_pos.ne'
  have hQ : d4BMPoincareQuadratic z q.pair ≠ 0 :=
    ne_of_gt (d4BMPoincareQuadratic_pos z q.pair q.pair_ne_zero)
  have hQC : (d4BMPoincareQuadratic z q.pair : ℂ) ≠ 0 := by exact_mod_cast hQ
  have hQformula : (d4BMPoincareQuadratic z q.pair : ℂ) =
      ((p.pair.2 : ℂ) * (z.y : ℂ)) ^ 2 +
        ((p.pair.2 : ℂ) * (z.x : ℂ) - (p.pair.1 : ℂ)) ^ 2 := by
    dsimp only [q]
    unfold d4BMPoincareQuadratic d4BMEisensteinRotatePrimitivePair
    push_cast
    ring
  have hquad :
      d4BMPoincareQuadratic (d4BMEisensteinInvertCoordinate z) p.pair =
        d4BMPoincareQuadratic z q.pair / (z.x ^ 2 + z.y ^ 2) := by
    dsimp only [q]
    unfold d4BMEisensteinInvertCoordinate d4BMPoincareQuadratic
      d4BMEisensteinRotatePrimitivePair
    field_simp [hR]
    push_cast
    ring
  have hseed := d4BM_poincareSeed_invert z s p
  unfold d4BMPoincareSeedHorizontalGradientRadialJet
    d4BMPoincareSeedVerticalGradientRadialJet
    d4BMPoincareSeedHorizontalFirstJet d4BMPoincareSeedVerticalFirstJet
    d4BMPoincareSeedHorizontalSecondJet d4BMPoincareSeedMixedSecondJet
    d4BMPoincareSeedVerticalSecondJet d4BMPoincareHorizontalLinear
  rw [hseed, hquad]
  dsimp only [q] at hQ hQC hQformula ⊢
  change d4BMPoincareQuadratic z (p.pair.2, -p.pair.1) ≠ 0 at hQ
  change (d4BMPoincareQuadratic z (p.pair.2, -p.pair.1) : ℂ) ≠ 0 at hQC
  change (d4BMPoincareQuadratic z (p.pair.2, -p.pair.1) : ℂ) =
    ((p.pair.2 : ℂ) * (z.y : ℂ)) ^ 2 +
      ((p.pair.2 : ℂ) * (z.x : ℂ) - (p.pair.1 : ℂ)) ^ 2 at hQformula
  unfold d4BMEisensteinInvertCoordinate d4BMEisensteinRotatePrimitivePair
  push_cast
  field_simp [hRC, hQC, hy]
  rw [hQformula]
  ring

theorem summable_d4BMPoincareSeedHorizontalGradientRadialJet
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    Summable (fun p : D4BMPrimitiveIntegerPair =>
      d4BMPoincareSeedHorizontalGradientRadialJet z P.s p) := by
  exact (summable_d4BMPoincareSeedHorizontalSecondJet z P).mul_left (z.x : ℂ) |>.add
    ((summable_d4BMPoincareSeedMixedSecondJet z P).mul_left (z.y : ℂ))

theorem summable_d4BMPoincareSeedVerticalGradientRadialJet
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    Summable (fun p : D4BMPrimitiveIntegerPair =>
      d4BMPoincareSeedVerticalGradientRadialJet z P.s p) := by
  exact (summable_d4BMPoincareSeedMixedSecondJet z P).mul_left (z.x : ℂ) |>.add
    ((summable_d4BMPoincareSeedVerticalSecondJet z P).mul_left (z.y : ℂ))

def d4BMCompletedPoincareHorizontalGradientRadialJet
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  reflectedCompletedLambda (2 * P.s) * (1 / 2 : ℂ) *
    ∑' p : D4BMPrimitiveIntegerPair,
      d4BMPoincareSeedHorizontalGradientRadialJet z P.s p

def d4BMCompletedPoincareVerticalGradientRadialJet
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  reflectedCompletedLambda (2 * P.s) * (1 / 2 : ℂ) *
    ∑' p : D4BMPrimitiveIntegerPair,
      d4BMPoincareSeedVerticalGradientRadialJet z P.s p

theorem d4BM_completedPoincareHorizontalGradientRadialJet_eq
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMCompletedPoincareHorizontalGradientRadialJet z P =
      (z.x : ℂ) * d4BMCompletedPoincareHorizontalSecondJet z P +
        (z.y : ℂ) * d4BMCompletedPoincareMixedSecondJet z P := by
  have hXX := summable_d4BMPoincareSeedHorizontalSecondJet z P
  have hXY := summable_d4BMPoincareSeedMixedSecondJet z P
  unfold d4BMCompletedPoincareHorizontalGradientRadialJet
    d4BMPoincareSeedHorizontalGradientRadialJet
    d4BMCompletedPoincareHorizontalSecondJet d4BMRawPoincareHorizontalSecondJet
    d4BMCompletedPoincareMixedSecondJet d4BMRawPoincareMixedSecondJet
  rw [(hXX.mul_left (z.x : ℂ)).tsum_add (hXY.mul_left (z.y : ℂ)),
    tsum_mul_left, tsum_mul_left]
  ring

theorem d4BM_completedPoincareVerticalGradientRadialJet_eq
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMCompletedPoincareVerticalGradientRadialJet z P =
      (z.x : ℂ) * d4BMCompletedPoincareMixedSecondJet z P +
        (z.y : ℂ) * d4BMCompletedPoincareVerticalSecondJet z P := by
  have hXY := summable_d4BMPoincareSeedMixedSecondJet z P
  have hYY := summable_d4BMPoincareSeedVerticalSecondJet z P
  unfold d4BMCompletedPoincareVerticalGradientRadialJet
    d4BMPoincareSeedVerticalGradientRadialJet
    d4BMCompletedPoincareMixedSecondJet d4BMRawPoincareMixedSecondJet
    d4BMCompletedPoincareVerticalSecondJet d4BMRawPoincareVerticalSecondJet
  rw [(hXY.mul_left (z.x : ℂ)).tsum_add (hYY.mul_left (z.y : ℂ)),
    tsum_mul_left, tsum_mul_left]
  ring

theorem d4BM_completedPoincareHorizontalGradientRadialJet_invert
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMCompletedPoincareHorizontalGradientRadialJet
        (d4BMEisensteinInvertCoordinate z) P =
      -(((z.x : ℂ) ^ 2 - (z.y : ℂ) ^ 2) *
          (2 * d4BMCompletedPoincareHorizontalFirstJet z P +
            d4BMCompletedPoincareHorizontalGradientRadialJet z P) +
        2 * (z.x : ℂ) * (z.y : ℂ) *
          (2 * d4BMCompletedPoincareVerticalFirstJet z P +
            d4BMCompletedPoincareVerticalGradientRadialJet z P)) := by
  let e := d4BMEisensteinRotatePrimitivePairEquiv
  let a : ℂ := (z.x : ℂ) ^ 2 - (z.y : ℂ) ^ 2
  let b : ℂ := 2 * (z.x : ℂ) * (z.y : ℂ)
  let X : D4BMPrimitiveIntegerPair → ℂ := fun p =>
    d4BMPoincareSeedHorizontalFirstJet z P.s (e p)
  let Y : D4BMPrimitiveIntegerPair → ℂ := fun p =>
    d4BMPoincareSeedVerticalFirstJet z P.s (e p)
  let RX : D4BMPrimitiveIntegerPair → ℂ := fun p =>
    d4BMPoincareSeedHorizontalGradientRadialJet z P.s (e p)
  let RY : D4BMPrimitiveIntegerPair → ℂ := fun p =>
    d4BMPoincareSeedVerticalGradientRadialJet z P.s (e p)
  have hX : Summable X := (e.summable_iff).2
    (summable_d4BMPoincareSeedHorizontalFirstJet z P)
  have hY : Summable Y := (e.summable_iff).2
    (summable_d4BMPoincareSeedVerticalFirstJet z P)
  have hRX : Summable RX := (e.summable_iff).2
    (summable_d4BMPoincareSeedHorizontalGradientRadialJet z P)
  have hRY : Summable RY := (e.summable_iff).2
    (summable_d4BMPoincareSeedVerticalGradientRadialJet z P)
  unfold d4BMCompletedPoincareHorizontalGradientRadialJet
  rw [show (fun p : D4BMPrimitiveIntegerPair =>
      d4BMPoincareSeedHorizontalGradientRadialJet
        (d4BMEisensteinInvertCoordinate z) P.s p) =
      fun p => -(a * (2 * X p + RX p) + b * (2 * Y p + RY p)) by
    funext p
    exact d4BM_poincareSeedHorizontalGradientRadialJet_invert z P.s p]
  have hAX : Summable (fun p => a * (2 * X p + RX p)) :=
    (hX.mul_left 2 |>.add hRX).mul_left a
  have hBY : Summable (fun p => b * (2 * Y p + RY p)) :=
    (hY.mul_left 2 |>.add hRY).mul_left b
  rw [tsum_neg, hAX.tsum_add hBY, tsum_mul_left, tsum_mul_left,
    (hX.mul_left 2).tsum_add hRX, (hY.mul_left 2).tsum_add hRY,
    tsum_mul_left, tsum_mul_left, e.tsum_eq, e.tsum_eq, e.tsum_eq, e.tsum_eq]
  unfold d4BMCompletedPoincareHorizontalFirstJet d4BMRawPoincareHorizontalFirstJet
    d4BMCompletedPoincareVerticalFirstJet d4BMRawPoincareVerticalFirstJet
    d4BMCompletedPoincareVerticalGradientRadialJet
  dsimp only [a, b]
  ring

theorem d4BM_completedPoincareVerticalGradientRadialJet_invert
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMCompletedPoincareVerticalGradientRadialJet
        (d4BMEisensteinInvertCoordinate z) P =
      -(-2 * (z.x : ℂ) * (z.y : ℂ) *
          (2 * d4BMCompletedPoincareHorizontalFirstJet z P +
            d4BMCompletedPoincareHorizontalGradientRadialJet z P) +
        ((z.x : ℂ) ^ 2 - (z.y : ℂ) ^ 2) *
          (2 * d4BMCompletedPoincareVerticalFirstJet z P +
            d4BMCompletedPoincareVerticalGradientRadialJet z P)) := by
  let e := d4BMEisensteinRotatePrimitivePairEquiv
  let a : ℂ := -2 * (z.x : ℂ) * (z.y : ℂ)
  let b : ℂ := (z.x : ℂ) ^ 2 - (z.y : ℂ) ^ 2
  let X : D4BMPrimitiveIntegerPair → ℂ := fun p =>
    d4BMPoincareSeedHorizontalFirstJet z P.s (e p)
  let Y : D4BMPrimitiveIntegerPair → ℂ := fun p =>
    d4BMPoincareSeedVerticalFirstJet z P.s (e p)
  let RX : D4BMPrimitiveIntegerPair → ℂ := fun p =>
    d4BMPoincareSeedHorizontalGradientRadialJet z P.s (e p)
  let RY : D4BMPrimitiveIntegerPair → ℂ := fun p =>
    d4BMPoincareSeedVerticalGradientRadialJet z P.s (e p)
  have hX : Summable X := (e.summable_iff).2
    (summable_d4BMPoincareSeedHorizontalFirstJet z P)
  have hY : Summable Y := (e.summable_iff).2
    (summable_d4BMPoincareSeedVerticalFirstJet z P)
  have hRX : Summable RX := (e.summable_iff).2
    (summable_d4BMPoincareSeedHorizontalGradientRadialJet z P)
  have hRY : Summable RY := (e.summable_iff).2
    (summable_d4BMPoincareSeedVerticalGradientRadialJet z P)
  unfold d4BMCompletedPoincareVerticalGradientRadialJet
  rw [show (fun p : D4BMPrimitiveIntegerPair =>
      d4BMPoincareSeedVerticalGradientRadialJet
        (d4BMEisensteinInvertCoordinate z) P.s p) =
      fun p => -(a * (2 * X p + RX p) + b * (2 * Y p + RY p)) by
    funext p
    exact d4BM_poincareSeedVerticalGradientRadialJet_invert z P.s p]
  have hAX : Summable (fun p => a * (2 * X p + RX p)) :=
    (hX.mul_left 2 |>.add hRX).mul_left a
  have hBY : Summable (fun p => b * (2 * Y p + RY p)) :=
    (hY.mul_left 2 |>.add hRY).mul_left b
  rw [tsum_neg, hAX.tsum_add hBY, tsum_mul_left, tsum_mul_left,
    (hX.mul_left 2).tsum_add hRX, (hY.mul_left 2).tsum_add hRY,
    tsum_mul_left, tsum_mul_left, e.tsum_eq, e.tsum_eq, e.tsum_eq, e.tsum_eq]
  unfold d4BMCompletedPoincareHorizontalFirstJet d4BMRawPoincareHorizontalFirstJet
    d4BMCompletedPoincareVerticalFirstJet d4BMRawPoincareVerticalFirstJet
    d4BMCompletedPoincareHorizontalGradientRadialJet
  dsimp only [a, b]
  ring

theorem d4BM_completedPoincareRadialFirstJet_invert
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMCompletedPoincareRadialFirstJet
        (d4BMEisensteinInvertCoordinate z) P =
      -d4BMCompletedPoincareRadialFirstJet z P := by
  have hR : (z.x : ℂ) ^ 2 + (z.y : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast (show z.x ^ 2 + z.y ^ 2 ≠ 0 by
      nlinarith [sq_nonneg z.x, sq_pos_of_pos z.y_pos])
  rw [d4BM_completedPoincareRadialFirstJet_eq_gradientContraction,
    d4BM_completedPoincareRadialFirstJet_eq_gradientContraction,
    d4BM_completedPoincareGradient_invert_horizontal,
    d4BM_completedPoincareGradient_invert_vertical]
  unfold d4BMEisensteinInvertCoordinate
  push_cast
  field_simp [hR]
  ring

/-- Radial derivative of the actual hyperbolic gradient energy. -/
def d4BMActualSecondStokesEnergyRadialFirstJet
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  (z.x : ℂ) * d4BMActualSecondStokesEnergyHorizontalFirstJet z P +
    (z.y : ℂ) * d4BMActualSecondStokesEnergyVerticalFirstJet z P

theorem d4BM_actualSecondStokesEnergyRadialFirstJet_expansion
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMActualSecondStokesEnergyRadialFirstJet z P =
      2 * d4BMActualSecondStokesEnergy z P +
        2 * (z.y : ℂ) ^ 2 *
          (d4BMCompletedPoincareHorizontalFirstJet z P *
              d4BMCompletedPoincareHorizontalGradientRadialJet z P +
            d4BMCompletedPoincareVerticalFirstJet z P *
              d4BMCompletedPoincareVerticalGradientRadialJet z P) := by
  rw [d4BM_completedPoincareHorizontalGradientRadialJet_eq,
    d4BM_completedPoincareVerticalGradientRadialJet_eq]
  unfold d4BMActualSecondStokesEnergyRadialFirstJet
    d4BMActualSecondStokesEnergyHorizontalFirstJet
    d4BMActualSecondStokesEnergyVerticalFirstJet
    d4BMActualSecondStokesEnergy
  ring

theorem d4BM_actualSecondStokesEnergyRadialFirstJet_invert
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMActualSecondStokesEnergyRadialFirstJet
        (d4BMEisensteinInvertCoordinate z) P =
      -d4BMActualSecondStokesEnergyRadialFirstJet z P := by
  have hR : (z.x : ℂ) ^ 2 + (z.y : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast (show z.x ^ 2 + z.y ^ 2 ≠ 0 by
      nlinarith [sq_nonneg z.x, sq_pos_of_pos z.y_pos])
  rw [d4BM_actualSecondStokesEnergyRadialFirstJet_expansion,
    d4BM_actualSecondStokesEnergyRadialFirstJet_expansion,
    d4BM_actualSecondStokesEnergy_invert,
    d4BM_completedPoincareGradient_invert_horizontal,
    d4BM_completedPoincareGradient_invert_vertical,
    d4BM_completedPoincareHorizontalGradientRadialJet_invert,
    d4BM_completedPoincareVerticalGradientRadialJet_invert]
  unfold d4BMEisensteinInvertCoordinate d4BMActualSecondStokesEnergy
  push_cast
  field_simp [hR]
  ring

theorem d4BM_actualSecondStokesEnergy_translate
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMActualSecondStokesEnergy (d4BMEisensteinTranslateCoordinate z) P =
      d4BMActualSecondStokesEnergy z P := by
  unfold d4BMActualSecondStokesEnergy
  rw [d4BM_completedPoincareHorizontalFirstJet_translate,
    d4BM_completedPoincareVerticalFirstJet_translate]
  rfl

theorem d4BM_actualSecondStokesEnergyHorizontalFirstJet_translate
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMActualSecondStokesEnergyHorizontalFirstJet
        (d4BMEisensteinTranslateCoordinate z) P =
      d4BMActualSecondStokesEnergyHorizontalFirstJet z P := by
  unfold d4BMActualSecondStokesEnergyHorizontalFirstJet
  rw [d4BM_completedPoincareHorizontalFirstJet_translate,
    d4BM_completedPoincareHorizontalSecondJet_translate,
    d4BM_completedPoincareVerticalFirstJet_translate,
    d4BM_completedPoincareMixedSecondJet_translate]
  rfl

theorem d4BM_actualSecondStokesHorizontalCurrent_translate
    (z : D4BMUpperHalfPlaneCoordinate)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMActualSecondStokesHorizontalCurrent
        (d4BMEisensteinTranslateCoordinate z) P Q =
      d4BMActualSecondStokesHorizontalCurrent z P Q := by
  unfold d4BMActualSecondStokesHorizontalCurrent
  rw [d4BM_completedEisensteinPoincareSeries_translate,
    d4BM_actualSecondStokesEnergyHorizontalFirstJet_translate,
    d4BM_actualSecondStokesEnergy_translate,
    d4BM_completedPoincareHorizontalFirstJet_translate]

/-- Radial component of the literal second Bochner--Stokes current. -/
def d4BMActualSecondStokesRadialCurrent
    (z : D4BMUpperHalfPlaneCoordinate)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  d4BMCompletedEisensteinPoincareSeries z Q *
      d4BMActualSecondStokesEnergyRadialFirstJet z P -
    d4BMActualSecondStokesEnergy z P *
      d4BMCompletedPoincareRadialFirstJet z Q

theorem d4BM_actualSecondStokesRadialCurrent_invert_unitCircle
    (z : D4BMUnitSemicircleCoordinate)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMActualSecondStokesRadialCurrent
        (d4BMEisensteinInvertCoordinate z.point) P Q =
      -d4BMActualSecondStokesRadialCurrent z.point P Q := by
  unfold d4BMActualSecondStokesRadialCurrent
  rw [d4BM_completedEisensteinPoincareSeries_invert,
    d4BM_actualSecondStokesEnergyRadialFirstJet_invert,
    d4BM_actualSecondStokesEnergy_invert,
    d4BM_completedPoincareRadialFirstJet_invert]
  ring

def d4BMActualSecondStokesNonCuspPairedDefect
    (B : D4BMTruncatedModularBoundaryPair)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  (d4BMActualSecondStokesHorizontalCurrent
      (d4BMEisensteinTranslateCoordinate B.verticalSide) P Q -
    d4BMActualSecondStokesHorizontalCurrent B.verticalSide P Q) +
  (d4BMActualSecondStokesRadialCurrent
      (d4BMEisensteinInvertCoordinate B.circularArc.point) P Q +
    d4BMActualSecondStokesRadialCurrent B.circularArc.point P Q)

def d4BMActualSecondStokesPairedBoundaryCurrent
    (B : D4BMTruncatedModularBoundaryPair)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  d4BMActualSecondStokesVerticalCurrent B.cuspTop P Q +
    d4BMActualSecondStokesNonCuspPairedDefect B P Q

/-- Every non-cusp boundary contribution of the actual second Bochner current cancels. -/
theorem d4BM_actualSecondStokes_nonCuspPairedDefect_eq_zero
    (B : D4BMTruncatedModularBoundaryPair)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMActualSecondStokesNonCuspPairedDefect B P Q = 0 := by
  unfold d4BMActualSecondStokesNonCuspPairedDefect
  rw [d4BM_actualSecondStokesHorizontalCurrent_translate,
    d4BM_actualSecondStokesRadialCurrent_invert_unitCircle]
  ring

theorem d4BM_actualSecondStokes_pairedBoundaryCurrent_eq_cuspCurrent
    (B : D4BMTruncatedModularBoundaryPair)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMActualSecondStokesPairedBoundaryCurrent B P Q =
      d4BMActualSecondStokesVerticalCurrent B.cuspTop P Q := by
  rw [d4BMActualSecondStokesPairedBoundaryCurrent,
    d4BM_actualSecondStokes_nonCuspPairedDefect_eq_zero]
  simp

end
end RHTower
