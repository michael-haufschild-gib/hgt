import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinActualSecondStokesCurrent
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinActualFirstStokesDefect

/-!
# Exact boundary and cusp closure for the actual second Bochner--Stokes current

Corpus conjecture C-A.9t4c asks for the modular-boundary and cusp closure of the literal second
Stokes current.  This module closes both halves.  Source-level primitive-pair reindexing proves
translation and inversion cancellation of every non-cusp boundary.  At the cusp, an exact Maass
factorization reduces the nonconstant second-current remainder to scalar, first-jet, and two-step
raise/lower cusp tails, proving rapid decay.  The literal zero-frequency current is exactly a
diagonal affine spectral family, so its analytic-family finite part vanishes.

The RH chain is

`actual second-current complete boundary/cusp closure -> second modular Green/Stokes ->
actual balanced BM ++- coefficient -> negative BM leg -> conserved left-QNM projection -> HC94 ->
RH`.

`[BRIDGE] [PAPER-PROVED] [LEAN-PROVED] [HC94] [SECOND STOKES BOUNDARY CLOSURE]`
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

/-! ## Full cusp closure of the actual second Stokes current

The vertical derivative of the hyperbolic energy admits an exact Maass factorization:
its only nonconstant factors are the scalar, horizontal/vertical first-jet, and two-step
raise/lower cusp legs already controlled by the corpus.  This makes the mixed sector rapidly
decaying.  The zero-frequency current is simultaneously identified with a diagonal affine
spectral family, whose analytic-family finite part vanishes coefficient-independently.
-/


def d4BMCanonicalSecondStokesEnergy (Y : ℝ) (J : D4BMFullSecondJet) : ℂ :=
  (Y : ℂ) ^ 2 * (J.first.horizonX ^ 2 + J.first.sigma ^ 2)

def d4BMCanonicalSecondStokesEnergyVerticalFirstJet
    (Y : ℝ) (J : D4BMFullSecondJet) : ℂ :=
  2 * (Y : ℂ) * (J.first.horizonX ^ 2 + J.first.sigma ^ 2) +
    2 * (Y : ℂ) ^ 2 *
      (J.first.horizonX * J.horizonXSigma + J.first.sigma * J.sigmaSigma)

def d4BMCanonicalSecondStokesVerticalCurrent
    (u v : ℂ) (x : ℝ) (Y : {y : ℝ // 1 ≤ y}) : ℂ :=
  let Ju := d4BMCompletedEisensteinCanonicalCuspFullSecondJet u x Y
  let Jv := d4BMCompletedEisensteinCanonicalCuspFullSecondJet v x Y
  Jv.first.value * d4BMCanonicalSecondStokesEnergyVerticalFirstJet Y Ju -
    d4BMCanonicalSecondStokesEnergy Y Ju * Jv.first.sigma

theorem d4BM_actualSecondStokesVerticalCurrent_eq_canonical
    (Z : D4BMExteriorCuspCoordinate)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMActualSecondStokesVerticalCurrent Z.1 P Q =
      d4BMCanonicalSecondStokesVerticalCurrent
        (P.s - 1 / 2) (Q.s - 1 / 2) Z.1.x (d4BMExteriorCuspHeight Z) := by
  have hP :=
    d4BM_actualCompletedPoincareFullSecondJet_eq_canonicalCuspFullSecondJet Z P
  have hQ :=
    d4BM_actualCompletedPoincareFullSecondJet_eq_canonicalCuspFullSecondJet Z Q
  unfold d4BMActualSecondStokesVerticalCurrent
    d4BMActualSecondStokesEnergy d4BMActualSecondStokesEnergyVerticalFirstJet
    d4BMCanonicalSecondStokesVerticalCurrent
  simpa [d4BMCanonicalSecondStokesEnergy,
    d4BMCanonicalSecondStokesEnergyVerticalFirstJet,
    d4BMExteriorCuspHeight,
    d4BMActualCompletedPoincareFullSecondJet,
    d4BMActualCompletedPoincareFullFirstJet] using
      congrArg₂ (fun a b : D4BMFullSecondJet =>
        b.first.value *
            (2 * (Z.1.y : ℂ) *
                (a.first.horizonX ^ 2 + a.first.sigma ^ 2) +
              2 * (Z.1.y : ℂ) ^ 2 *
                (a.first.horizonX * a.horizonXSigma +
                  a.first.sigma * a.sigmaSigma)) -
          (Z.1.y : ℂ) ^ 2 *
              (a.first.horizonX ^ 2 + a.first.sigma ^ 2) *
            b.first.sigma) hP hQ

theorem d4BM_canonicalSecondStokesEnergyVerticalFirstJet_maassFactorization
    (u : ℂ) (x : ℝ) (Y : {y : ℝ // 1 ≤ y}) :
    let J := d4BMCompletedEisensteinCanonicalCuspFullSecondJet u x Y
    d4BMCanonicalSecondStokesEnergyVerticalFirstJet Y J =
      (u ^ 2 - 1 / 4) * J.first.value * J.first.sigma +
        (1 / (2 * (Y : ℂ))) *
          (d4BMMaassLowerZeroOnFullSecondJet (Y : ℂ) J *
              d4BMMaassRaiseTwoRaiseZeroOnFullSecondJet (Y : ℂ) J +
            d4BMMaassRaiseZeroOnFullSecondJet (Y : ℂ) J *
              d4BMMaassLowerNegTwoLowerZeroOnFullSecondJet (Y : ℂ) J) := by
  dsimp only
  let J := d4BMCompletedEisensteinCanonicalCuspFullSecondJet u x Y
  have heigen := d4BM_canonicalCuspFullSecondJet_eigenEquation u x Y
  have hY : (Y : ℂ) ≠ 0 := by
    exact_mod_cast (show (Y : ℝ) ≠ 0 by linarith [Y.2])
  rw [← heigen]
  unfold d4BMCanonicalSecondStokesEnergyVerticalFirstJet
    d4BMMaassLowerZeroOnFullSecondJet d4BMMaassRaiseZeroOnFullSecondJet
    d4BMMaassRaiseTwoRaiseZeroOnFullSecondJet
    d4BMMaassLowerNegTwoLowerZeroOnFullSecondJet
  field_simp [hY]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem d4BM_canonicalSecondStokesEnergy_maassFactorization
    (Y : ℂ) (J : D4BMFullSecondJet) :
    Y ^ 2 * (J.first.horizonX ^ 2 + J.first.sigma ^ 2) =
      d4BMMaassRaiseZeroOnFullSecondJet Y J *
        d4BMMaassLowerZeroOnFullSecondJet Y J := by
  unfold d4BMMaassRaiseZeroOnFullSecondJet d4BMMaassLowerZeroOnFullSecondJet
  ring_nf
  rw [Complex.I_sq]
  ring

theorem d4BM_completedEisensteinSignedSqrtWhittakerHorizontalFirstJetTail_decomposition
    (u nu : ℂ) (negative : Bool) (x Y : ℝ) :
    d4BMCompletedEisensteinSignedSqrtWhittakerHorizontalFirstJetTail
        u nu negative x Y =
      (d4BMFourierSign negative : ℂ) * (2 * Real.pi : ℂ) * Complex.I *
        d4BMCompletedEisensteinSignedSqrtWhittakerTail
          u nu negative x 1 0 Y := by
  unfold d4BMCompletedEisensteinSignedSqrtWhittakerHorizontalFirstJetTail
    d4BMCompletedEisensteinSignedSqrtWhittakerTail
  rw [← tsum_mul_left]
  apply tsum_congr
  intro N
  unfold d4BMCompletedEisensteinWeightedSignedWhittakerHorizontalFirstJet
    d4BMSignedWhittakerModeHorizontalFirstJet d4BMSignedFourierRate
    d4BMSignedWhittakerMode d4BMWhittakerP0 d4BMPositiveFourierScale
  simp only [pow_one, pow_zero, mul_one]
  push_cast
  ring

def d4BMCompletedEisensteinCuspHorizontalFirstJetTail (u : ℂ) (x Y : ℝ) : ℂ :=
  2 *
    (d4BMCompletedEisensteinSignedSqrtWhittakerHorizontalFirstJetTail
        u u false x Y +
      d4BMCompletedEisensteinSignedSqrtWhittakerHorizontalFirstJetTail
        u u true x Y)

theorem d4BMCuspRapidDecay_horizontalFirstJetTail (u : ℂ) (x : ℝ) :
    D4BMCuspRapidDecay (d4BMCompletedEisensteinCuspHorizontalFirstJetTail u x) := by
  intro w
  have hp :=
    (tendsto_d4BMCompletedEisensteinComplexPowerSignedSqrtWhittakerTail_atTop_zero
      u u w false x 1 0).const_mul
        ((d4BMFourierSign false : ℂ) * (2 * Real.pi : ℂ) * Complex.I)
  have hn :=
    (tendsto_d4BMCompletedEisensteinComplexPowerSignedSqrtWhittakerTail_atTop_zero
      u u w true x 1 0).const_mul
        ((d4BMFourierSign true : ℂ) * (2 * Real.pi : ℂ) * Complex.I)
  have h := (hp.add hn).const_mul (2 : ℂ)
  simp only [mul_zero, add_zero] at h
  apply h.congr'
  exact Filter.Eventually.of_forall fun Y => by
    unfold d4BMCompletedEisensteinCuspHorizontalFirstJetTail
    simp only
    rw [d4BM_completedEisensteinSignedSqrtWhittakerHorizontalFirstJetTail_decomposition,
      d4BM_completedEisensteinSignedSqrtWhittakerHorizontalFirstJetTail_decomposition]
    unfold d4BMCompletedEisensteinComplexPowerSignedSqrtWhittakerTail
    ring

def d4BMCanonicalCuspRaiseZeroFirstJet (u : ℂ) (x Y : ℝ) : ℂ :=
  (Y : ℂ) *
    ((d4BMCanonicalCuspConstantVerticalFirstJet u Y +
        d4BMCompletedEisensteinCuspVerticalFirstJetTail u x Y) +
      Complex.I * d4BMCompletedEisensteinCuspHorizontalFirstJetTail u x Y)

def d4BMCanonicalCuspLowerZeroFirstJet (u : ℂ) (x Y : ℝ) : ℂ :=
  (Y : ℂ) *
    ((d4BMCanonicalCuspConstantVerticalFirstJet u Y +
        d4BMCompletedEisensteinCuspVerticalFirstJetTail u x Y) -
      Complex.I * d4BMCompletedEisensteinCuspHorizontalFirstJetTail u x Y)

def d4BMCanonicalSecondStokesVerticalMaassCurrent
    (u v : ℂ) (x Y : ℝ) : ℂ :=
  d4BMCompletedEisensteinCuspLeg .scalar v x Y *
      ((u ^ 2 - 1 / 4) *
          d4BMCompletedEisensteinCuspLeg .scalar u x Y *
          (d4BMCanonicalCuspConstantVerticalFirstJet u Y +
            d4BMCompletedEisensteinCuspVerticalFirstJetTail u x Y) +
        (1 / (2 * (Y : ℂ))) *
          (d4BMCanonicalCuspLowerZeroFirstJet u x Y *
              d4BMCompletedEisensteinCuspLeg .raise u x Y +
            d4BMCanonicalCuspRaiseZeroFirstJet u x Y *
              d4BMCompletedEisensteinCuspLeg .lower u x Y)) -
    d4BMCanonicalCuspRaiseZeroFirstJet u x Y *
        d4BMCanonicalCuspLowerZeroFirstJet u x Y *
      (d4BMCanonicalCuspConstantVerticalFirstJet v Y +
        d4BMCompletedEisensteinCuspVerticalFirstJetTail v x Y)

def d4BMCanonicalSecondStokesConstantVerticalCurrent
    (u v : ℂ) (Y : ℝ) : ℂ :=
  let Ju := d4BMCompletedEisensteinCuspConstantFullSecondJet u Y
  let Jv := d4BMCompletedEisensteinCuspConstantFullSecondJet v Y
  Jv.first.value * d4BMCanonicalSecondStokesEnergyVerticalFirstJet Y Ju -
    d4BMCanonicalSecondStokesEnergy Y Ju * Jv.first.sigma

theorem d4BM_canonicalSecondStokesVerticalCurrent_eq_maass
    (u v : ℂ) (x : ℝ) (Y : {y : ℝ // 1 ≤ y}) :
    d4BMCanonicalSecondStokesVerticalCurrent u v x Y =
      d4BMCanonicalSecondStokesVerticalMaassCurrent u v x Y := by
  let Ju := d4BMCompletedEisensteinCanonicalCuspFullSecondJet u x Y
  let Jv := d4BMCompletedEisensteinCanonicalCuspFullSecondJet v x Y
  have hEy := d4BM_canonicalSecondStokesEnergyVerticalFirstJet_maassFactorization u x Y
  have hE := d4BM_canonicalSecondStokesEnergy_maassFactorization (Y : ℂ) Ju
  have hvValue := d4BM_canonicalCuspFullSecondJet_value_eq_cuspLeg v x Y
  have huValue := d4BM_canonicalCuspFullSecondJet_value_eq_cuspLeg u x Y
  have huSigma := d4BM_canonicalCuspFullSecondJet_sigma_eq_constant_add_tail u x Y
  have hvSigma := d4BM_canonicalCuspFullSecondJet_sigma_eq_constant_add_tail v x Y
  have huRaise := d4BM_maassRaise_canonicalCuspFullSecondJet_eq_cuspLeg u x Y
  have huLower := d4BM_maassLower_canonicalCuspFullSecondJet_eq_cuspLeg u x Y
  have huX : Ju.first.horizonX = d4BMCompletedEisensteinCuspHorizontalFirstJetTail u x Y := by
    unfold Ju d4BMCompletedEisensteinCuspHorizontalFirstJetTail
      d4BMCompletedEisensteinCanonicalCuspFullSecondJet
      d4BMCompletedEisensteinFullSignedTailFullSecondJet
      d4BMCompletedEisensteinSignedTailFullSecondJet
    rfl
  have huR0 : d4BMMaassRaiseZeroOnFullSecondJet (Y : ℂ) Ju =
      d4BMCanonicalCuspRaiseZeroFirstJet u x Y := by
    unfold d4BMMaassRaiseZeroOnFullSecondJet
      d4BMCanonicalCuspRaiseZeroFirstJet
    rw [huSigma, huX]
  have huL0 : d4BMMaassLowerZeroOnFullSecondJet (Y : ℂ) Ju =
      d4BMCanonicalCuspLowerZeroFirstJet u x Y := by
    unfold d4BMMaassLowerZeroOnFullSecondJet
      d4BMCanonicalCuspLowerZeroFirstJet
    rw [huSigma, huX]
  unfold d4BMCanonicalSecondStokesVerticalCurrent
    d4BMCanonicalSecondStokesVerticalMaassCurrent d4BMCanonicalSecondStokesEnergy
  dsimp only [Ju, Jv] at hEy hE hvValue huValue huSigma hvSigma huRaise huLower huR0 huL0 ⊢
  rw [hEy, hE, hvValue, huValue, hvSigma, huSigma,
    huRaise, huLower, huR0, huL0]

def d4BMCanonicalSecondStokesConstantVerticalMaassCurrent
    (u v : ℂ) (Y : ℝ) : ℂ :=
  let Du := d4BMCanonicalCuspConstantVerticalFirstJet u Y
  let Dv := d4BMCanonicalCuspConstantVerticalFirstJet v Y
  let R0u := (Y : ℂ) * Du
  d4BMCompletedEisensteinCuspConstantPart .scalar v Y *
      ((u ^ 2 - 1 / 4) *
          d4BMCompletedEisensteinCuspConstantPart .scalar u Y * Du +
        (1 / (2 * (Y : ℂ))) *
          (R0u * d4BMCompletedEisensteinCuspConstantPart .raise u Y +
            R0u * d4BMCompletedEisensteinCuspConstantPart .lower u Y)) -
    R0u * R0u * Dv

def D4BMCuspModerateGrowth (f : ℝ → ℂ) : Prop :=
  ∀ (r : ℝ → ℂ), D4BMCuspRapidDecay r →
    D4BMCuspRapidDecay (fun Y => r Y * f Y)

theorem d4BMCuspRapidDecay_mul_cpow {f : ℝ → ℂ}
    (hf : D4BMCuspRapidDecay f) (a : ℂ) :
    D4BMCuspRapidDecay (fun Y => f Y * (Y : ℂ) ^ a) := by
  intro w
  have h := hf (w + a)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with Y hY
  have hYC : (Y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hY.ne'
  rw [Complex.cpow_add w a hYC]
  ring

theorem d4BMCuspModerateGrowth_of_rapid {f : ℝ → ℂ}
    (hf : D4BMCuspRapidDecay f) : D4BMCuspModerateGrowth f := by
  intro r hr
  exact d4BMCuspRapidDecay_mul hr hf

theorem d4BMCuspModerateGrowth_cpow (a : ℂ) :
    D4BMCuspModerateGrowth (fun Y : ℝ => (Y : ℂ) ^ a) := by
  intro r hr
  exact d4BMCuspRapidDecay_mul_cpow hr a

theorem d4BMCuspModerateGrowth_add {f g : ℝ → ℂ}
    (hf : D4BMCuspModerateGrowth f)
    (hg : D4BMCuspModerateGrowth g) :
    D4BMCuspModerateGrowth (fun Y => f Y + g Y) := by
  intro r hr
  apply d4BMCuspRapidDecay_congr (d4BMCuspRapidDecay_add (hf r hr) (hg r hr))
  intro Y
  ring

theorem d4BMCuspModerateGrowth_sub {f g : ℝ → ℂ}
    (hf : D4BMCuspModerateGrowth f)
    (hg : D4BMCuspModerateGrowth g) :
    D4BMCuspModerateGrowth (fun Y => f Y - g Y) := by
  intro r hr
  apply d4BMCuspRapidDecay_congr (d4BMCuspRapidDecay_sub (hf r hr) (hg r hr))
  intro Y
  ring

theorem d4BMCuspModerateGrowth_const_mul {f : ℝ → ℂ}
    (hf : D4BMCuspModerateGrowth f) (c : ℂ) :
    D4BMCuspModerateGrowth (fun Y => c * f Y) := by
  intro r hr
  apply d4BMCuspRapidDecay_congr (d4BMCuspRapidDecay_const_mul (hf r hr) c)
  intro Y
  ring

theorem d4BMCuspModerateGrowth_mul {f g : ℝ → ℂ}
    (hf : D4BMCuspModerateGrowth f)
    (hg : D4BMCuspModerateGrowth g) :
    D4BMCuspModerateGrowth (fun Y => f Y * g Y) := by
  intro r hr
  have hrf := hf r hr
  have h := hg (fun Y => r Y * f Y) hrf
  apply d4BMCuspRapidDecay_congr h
  intro Y
  ring

theorem d4BMCuspModerateGrowth_constantPart
    (kind : D4BMCompletedEisensteinCuspLegKind) (u : ℂ) :
    D4BMCuspModerateGrowth
      (d4BMCompletedEisensteinCuspConstantPart kind u) := by
  intro r hr
  exact d4BMCuspRapidDecay_mul_constantPart hr kind u

theorem d4BMCuspModerateGrowth_cuspLeg
    (kind : D4BMCompletedEisensteinCuspLegKind) (u : ℂ) (x : ℝ) :
    D4BMCuspModerateGrowth (d4BMCompletedEisensteinCuspLeg kind u x) := by
  intro r hr
  exact d4BMCuspRapidDecay_mul_cuspLeg hr kind u x

theorem d4BMCuspModerateGrowth_constantVerticalFirstJet (u : ℂ) :
    D4BMCuspModerateGrowth
      (d4BMCanonicalCuspConstantVerticalFirstJet u) := by
  intro r hr
  exact d4BMCuspRapidDecay_mul_constantVerticalFirstJet hr u

theorem d4BMCuspRapidDecay_product_sub_product {f F g G : ℝ → ℂ}
    (hf : D4BMCuspRapidDecay (fun Y => f Y - F Y))
    (hg : D4BMCuspRapidDecay (fun Y => g Y - G Y))
    (mg : D4BMCuspModerateGrowth g)
    (mF : D4BMCuspModerateGrowth F) :
    D4BMCuspRapidDecay (fun Y => f Y * g Y - F Y * G Y) := by
  have hleft := mg (fun Y => f Y - F Y) hf
  have hrightRaw := mF (fun Y => g Y - G Y) hg
  have hright : D4BMCuspRapidDecay (fun Y => F Y * (g Y - G Y)) := by
    apply d4BMCuspRapidDecay_congr hrightRaw
    intro Y
    ring
  apply d4BMCuspRapidDecay_congr (d4BMCuspRapidDecay_add hleft hright)
  intro Y
  ring

theorem d4BMCuspRapidDecay_product3_sub_product3
    {f F g G h H : ℝ → ℂ}
    (hf : D4BMCuspRapidDecay (fun Y => f Y - F Y))
    (hg : D4BMCuspRapidDecay (fun Y => g Y - G Y))
    (hh : D4BMCuspRapidDecay (fun Y => h Y - H Y))
    (mf : D4BMCuspModerateGrowth f)
    (mF : D4BMCuspModerateGrowth F)
    (mg : D4BMCuspModerateGrowth g)
    (mG : D4BMCuspModerateGrowth G)
    (mh : D4BMCuspModerateGrowth h) :
    D4BMCuspRapidDecay
      (fun Y => f Y * g Y * h Y - F Y * G Y * H Y) := by
  have hfg := d4BMCuspRapidDecay_product_sub_product hf hg mg mF
  have mfg := d4BMCuspModerateGrowth_mul mf mg
  have mFG := d4BMCuspModerateGrowth_mul mF mG
  exact d4BMCuspRapidDecay_product_sub_product hfg hh mh mFG

theorem d4BMCuspRapidDecay_invHeight_mul {f : ℝ → ℂ}
    (hf : D4BMCuspRapidDecay f) :
    D4BMCuspRapidDecay (fun Y => (1 / (2 * (Y : ℂ))) * f Y) := by
  have hpow := d4BMCuspRapidDecay_mul_cpow hf (-1)
  have hc := d4BMCuspRapidDecay_const_mul hpow (1 / 2 : ℂ)
  apply d4BMCuspRapidDecay_congr hc
  intro Y
  by_cases hY : Y = 0
  · subst Y
    simp
  · have hYC : (Y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hY
    rw [Complex.cpow_neg_one]
    field_simp [hYC]

theorem d4BMCuspRapidDecay_fullVerticalFirstJet_sub_constant (u : ℂ) (x : ℝ) :
    D4BMCuspRapidDecay (fun Y =>
      (d4BMCanonicalCuspConstantVerticalFirstJet u Y +
          d4BMCompletedEisensteinCuspVerticalFirstJetTail u x Y) -
        d4BMCanonicalCuspConstantVerticalFirstJet u Y) := by
  apply d4BMCuspRapidDecay_congr
    (d4BMCuspRapidDecay_verticalFirstJetTail u x)
  intro Y
  ring

theorem d4BMCuspModerateGrowth_fullVerticalFirstJet (u : ℂ) (x : ℝ) :
    D4BMCuspModerateGrowth (fun Y =>
      d4BMCanonicalCuspConstantVerticalFirstJet u Y +
        d4BMCompletedEisensteinCuspVerticalFirstJetTail u x Y) :=
  d4BMCuspModerateGrowth_add (d4BMCuspModerateGrowth_constantVerticalFirstJet u)
    (d4BMCuspModerateGrowth_of_rapid (d4BMCuspRapidDecay_verticalFirstJetTail u x))

theorem d4BMCuspRapidDecay_raiseZero_sub_constant (u : ℂ) (x : ℝ) :
    D4BMCuspRapidDecay (fun Y =>
      d4BMCanonicalCuspRaiseZeroFirstJet u x Y -
        (Y : ℂ) * d4BMCanonicalCuspConstantVerticalFirstJet u Y) := by
  have hinside := d4BMCuspRapidDecay_add
    (d4BMCuspRapidDecay_verticalFirstJetTail u x)
    (d4BMCuspRapidDecay_const_mul (d4BMCuspRapidDecay_horizontalFirstJetTail u x) Complex.I)
  have hheight := d4BMCuspRapidDecay_mul_cpow hinside 1
  apply d4BMCuspRapidDecay_congr hheight
  intro Y
  unfold d4BMCanonicalCuspRaiseZeroFirstJet
  simp only [Complex.cpow_one]
  ring

theorem d4BMCuspRapidDecay_lowerZero_sub_constant (u : ℂ) (x : ℝ) :
    D4BMCuspRapidDecay (fun Y =>
      d4BMCanonicalCuspLowerZeroFirstJet u x Y -
        (Y : ℂ) * d4BMCanonicalCuspConstantVerticalFirstJet u Y) := by
  have hinside := d4BMCuspRapidDecay_sub
    (d4BMCuspRapidDecay_verticalFirstJetTail u x)
    (d4BMCuspRapidDecay_const_mul (d4BMCuspRapidDecay_horizontalFirstJetTail u x) Complex.I)
  have hheight := d4BMCuspRapidDecay_mul_cpow hinside 1
  apply d4BMCuspRapidDecay_congr hheight
  intro Y
  unfold d4BMCanonicalCuspLowerZeroFirstJet
  simp only [Complex.cpow_one]
  ring

theorem d4BMCuspModerateGrowth_constantRaiseZero (u : ℂ) :
    D4BMCuspModerateGrowth (fun Y =>
      (Y : ℂ) * d4BMCanonicalCuspConstantVerticalFirstJet u Y) := by
  have h := d4BMCuspModerateGrowth_mul (d4BMCuspModerateGrowth_cpow 1)
    (d4BMCuspModerateGrowth_constantVerticalFirstJet u)
  intro r hr
  apply d4BMCuspRapidDecay_congr (h r hr)
  intro Y
  simp

theorem d4BMCuspModerateGrowth_raiseZero (u : ℂ) (x : ℝ) :
    D4BMCuspModerateGrowth (d4BMCanonicalCuspRaiseZeroFirstJet u x) := by
  have hdiff := d4BMCuspRapidDecay_raiseZero_sub_constant u x
  have hsum := d4BMCuspModerateGrowth_add (d4BMCuspModerateGrowth_constantRaiseZero u)
    (d4BMCuspModerateGrowth_of_rapid hdiff)
  apply fun r hr => d4BMCuspRapidDecay_congr (hsum r hr) (fun Y => by
    unfold d4BMCanonicalCuspRaiseZeroFirstJet
    ring)

theorem d4BMCuspModerateGrowth_lowerZero (u : ℂ) (x : ℝ) :
    D4BMCuspModerateGrowth (d4BMCanonicalCuspLowerZeroFirstJet u x) := by
  have hdiff := d4BMCuspRapidDecay_lowerZero_sub_constant u x
  have hsum := d4BMCuspModerateGrowth_add (d4BMCuspModerateGrowth_constantRaiseZero u)
    (d4BMCuspModerateGrowth_of_rapid hdiff)
  apply fun r hr => d4BMCuspRapidDecay_congr (hsum r hr) (fun Y => by
    unfold d4BMCanonicalCuspLowerZeroFirstJet
    ring)

def d4BMCanonicalSecondStokesVerticalMixedRemainder
    (u v : ℂ) (x Y : ℝ) : ℂ :=
  d4BMCanonicalSecondStokesVerticalMaassCurrent u v x Y -
    d4BMCanonicalSecondStokesConstantVerticalMaassCurrent u v Y

theorem d4BMCuspRapidDecay_canonicalSecondStokesVerticalMixedRemainder
    (u v : ℂ) (x : ℝ) :
    D4BMCuspRapidDecay
      (d4BMCanonicalSecondStokesVerticalMixedRemainder u v x) := by
  let Fu := d4BMCompletedEisensteinCuspLeg .scalar u x
  let Fv := d4BMCompletedEisensteinCuspLeg .scalar v x
  let Cu := d4BMCompletedEisensteinCuspConstantPart .scalar u
  let Cv := d4BMCompletedEisensteinCuspConstantPart .scalar v
  let Du : ℝ → ℂ := d4BMCanonicalCuspConstantVerticalFirstJet u
  let Dv : ℝ → ℂ := d4BMCanonicalCuspConstantVerticalFirstJet v
  let Eu : ℝ → ℂ := fun Y => Du Y +
    d4BMCompletedEisensteinCuspVerticalFirstJetTail u x Y
  let Ev : ℝ → ℂ := fun Y => Dv Y +
    d4BMCompletedEisensteinCuspVerticalFirstJetTail v x Y
  let Ru := d4BMCanonicalCuspRaiseZeroFirstJet u x
  let Lu := d4BMCanonicalCuspLowerZeroFirstJet u x
  let Rcu : ℝ → ℂ := fun Y => (Y : ℂ) * Du Y
  let ARu := d4BMCompletedEisensteinCuspLeg .raise u x
  let ALu := d4BMCompletedEisensteinCuspLeg .lower u x
  let ARcu := d4BMCompletedEisensteinCuspConstantPart .raise u
  let ALcu := d4BMCompletedEisensteinCuspConstantPart .lower u
  have hFu : D4BMCuspRapidDecay (fun Y => Fu Y - Cu Y) := by
    apply d4BMCuspRapidDecay_congr (d4BMCuspRapidDecay_cuspTailPart .scalar u x)
    intro Y
    simp [Fu, Cu, d4BMCompletedEisensteinCuspLeg]
  have hFv : D4BMCuspRapidDecay (fun Y => Fv Y - Cv Y) := by
    apply d4BMCuspRapidDecay_congr (d4BMCuspRapidDecay_cuspTailPart .scalar v x)
    intro Y
    simp [Fv, Cv, d4BMCompletedEisensteinCuspLeg]
  have hEu : D4BMCuspRapidDecay (fun Y => Eu Y - Du Y) := by
    exact d4BMCuspRapidDecay_fullVerticalFirstJet_sub_constant u x
  have hEv : D4BMCuspRapidDecay (fun Y => Ev Y - Dv Y) := by
    exact d4BMCuspRapidDecay_fullVerticalFirstJet_sub_constant v x
  have hRu : D4BMCuspRapidDecay (fun Y => Ru Y - Rcu Y) :=
    d4BMCuspRapidDecay_raiseZero_sub_constant u x
  have hLu : D4BMCuspRapidDecay (fun Y => Lu Y - Rcu Y) :=
    d4BMCuspRapidDecay_lowerZero_sub_constant u x
  have hAR : D4BMCuspRapidDecay (fun Y => ARu Y - ARcu Y) := by
    apply d4BMCuspRapidDecay_congr (d4BMCuspRapidDecay_cuspTailPart .raise u x)
    intro Y
    simp [ARu, ARcu, d4BMCompletedEisensteinCuspLeg]
  have hAL : D4BMCuspRapidDecay (fun Y => ALu Y - ALcu Y) := by
    apply d4BMCuspRapidDecay_congr (d4BMCuspRapidDecay_cuspTailPart .lower u x)
    intro Y
    simp [ALu, ALcu, d4BMCompletedEisensteinCuspLeg]
  have mFu := d4BMCuspModerateGrowth_cuspLeg .scalar u x
  have mFv := d4BMCuspModerateGrowth_cuspLeg .scalar v x
  have mCu := d4BMCuspModerateGrowth_constantPart .scalar u
  have mCv := d4BMCuspModerateGrowth_constantPart .scalar v
  have mEu := d4BMCuspModerateGrowth_fullVerticalFirstJet u x
  have mEv := d4BMCuspModerateGrowth_fullVerticalFirstJet v x
  have mDu := d4BMCuspModerateGrowth_constantVerticalFirstJet u
  have mDv := d4BMCuspModerateGrowth_constantVerticalFirstJet v
  have mRu := d4BMCuspModerateGrowth_raiseZero u x
  have mLu := d4BMCuspModerateGrowth_lowerZero u x
  have mRcu := d4BMCuspModerateGrowth_constantRaiseZero u
  have mARu := d4BMCuspModerateGrowth_cuspLeg .raise u x
  have mALu := d4BMCuspModerateGrowth_cuspLeg .lower u x
  have mARcu := d4BMCuspModerateGrowth_constantPart .raise u
  have mALcu := d4BMCuspModerateGrowth_constantPart .lower u
  have hAraw := d4BMCuspRapidDecay_product3_sub_product3 hFv hFu hEu
    mFv mCv mFu mCu mEu
  have hA := d4BMCuspRapidDecay_const_mul hAraw (u ^ 2 - 1 / 4)
  have hBraw := d4BMCuspRapidDecay_product3_sub_product3 hFv hLu hAR
    mFv mCv mLu mRcu mARu
  have hB := d4BMCuspRapidDecay_invHeight_mul hBraw
  have hCraw := d4BMCuspRapidDecay_product3_sub_product3 hFv hRu hAL
    mFv mCv mRu mRcu mALu
  have hC := d4BMCuspRapidDecay_invHeight_mul hCraw
  have hDraw := d4BMCuspRapidDecay_product3_sub_product3 hRu hLu hEv
    mRu mRcu mLu mRcu mEv
  have htotal := d4BMCuspRapidDecay_sub
    (d4BMCuspRapidDecay_add hA (d4BMCuspRapidDecay_add hB hC)) hDraw
  apply d4BMCuspRapidDecay_congr htotal
  intro Y
  unfold d4BMCanonicalSecondStokesVerticalMixedRemainder
    d4BMCanonicalSecondStokesVerticalMaassCurrent
    d4BMCanonicalSecondStokesConstantVerticalMaassCurrent
  dsimp only [Fu, Fv, Cu, Cv, Du, Dv, Eu, Ev, Ru, Lu, Rcu,
    ARu, ALu, ARcu, ALcu]
  ring

theorem d4BM_canonicalSecondStokesConstantEnergyVerticalFirstJet_maassFactorization
    (u : ℂ) (Y : {y : ℝ // 1 ≤ y}) :
    let J := d4BMCompletedEisensteinCuspConstantFullSecondJet u Y
    d4BMCanonicalSecondStokesEnergyVerticalFirstJet Y J =
      (u ^ 2 - 1 / 4) * J.first.value * J.first.sigma +
        (1 / (2 * (Y : ℂ))) *
          (d4BMMaassLowerZeroOnFullSecondJet (Y : ℂ) J *
              d4BMMaassRaiseTwoRaiseZeroOnFullSecondJet (Y : ℂ) J +
            d4BMMaassRaiseZeroOnFullSecondJet (Y : ℂ) J *
              d4BMMaassLowerNegTwoLowerZeroOnFullSecondJet (Y : ℂ) J) := by
  dsimp only
  let J := d4BMCompletedEisensteinCuspConstantFullSecondJet u Y
  have heigen := d4BM_cuspConstantFullSecondJet_eigenEquation
    u (zero_lt_one.trans_le Y.2)
  have hY : (Y : ℂ) ≠ 0 := by
    exact_mod_cast (show (Y : ℝ) ≠ 0 by linarith [Y.2])
  rw [← heigen]
  unfold d4BMCanonicalSecondStokesEnergyVerticalFirstJet
    d4BMMaassLowerZeroOnFullSecondJet d4BMMaassRaiseZeroOnFullSecondJet
    d4BMMaassRaiseTwoRaiseZeroOnFullSecondJet
    d4BMMaassLowerNegTwoLowerZeroOnFullSecondJet
  simp only [d4BMCompletedEisensteinCuspConstantFullSecondJet, sub_zero]
  field_simp [hY]
  ring_nf

theorem d4BM_canonicalSecondStokesConstantVerticalCurrent_eq_maass
    (u v : ℂ) (Y : {y : ℝ // 1 ≤ y}) :
    d4BMCanonicalSecondStokesConstantVerticalCurrent u v Y =
      d4BMCanonicalSecondStokesConstantVerticalMaassCurrent u v Y := by
  let Ju := d4BMCompletedEisensteinCuspConstantFullSecondJet u Y
  let Jv := d4BMCompletedEisensteinCuspConstantFullSecondJet v Y
  have hEy := d4BM_canonicalSecondStokesConstantEnergyVerticalFirstJet_maassFactorization u Y
  have hE := d4BM_canonicalSecondStokesEnergy_maassFactorization (Y : ℂ) Ju
  have huSigma := d4BM_canonicalCuspConstantVerticalFirstJet_eq_fullSecondJet_sigma
    u (zero_lt_one.trans_le Y.2)
  have hvSigma := d4BM_canonicalCuspConstantVerticalFirstJet_eq_fullSecondJet_sigma
    v (zero_lt_one.trans_le Y.2)
  have huRaise := d4BM_maassRaise_cuspConstantFullSecondJet_eq_constantPart
    u (zero_lt_one.trans_le Y.2)
  have huLower := d4BM_maassLower_cuspConstantFullSecondJet_eq_constantPart
    u (zero_lt_one.trans_le Y.2)
  have huR0 : d4BMMaassRaiseZeroOnFullSecondJet (Y : ℂ) Ju =
      (Y : ℂ) * d4BMCanonicalCuspConstantVerticalFirstJet u Y := by
    unfold d4BMMaassRaiseZeroOnFullSecondJet Ju
    rw [← huSigma]
    simp [d4BMCompletedEisensteinCuspConstantFullSecondJet]
  have huL0 : d4BMMaassLowerZeroOnFullSecondJet (Y : ℂ) Ju =
      (Y : ℂ) * d4BMCanonicalCuspConstantVerticalFirstJet u Y := by
    unfold d4BMMaassLowerZeroOnFullSecondJet Ju
    rw [← huSigma]
    simp [d4BMCompletedEisensteinCuspConstantFullSecondJet]
  unfold d4BMCanonicalSecondStokesConstantVerticalCurrent
    d4BMCanonicalSecondStokesConstantVerticalMaassCurrent
    d4BMCanonicalSecondStokesEnergy
  dsimp only [Ju, Jv] at hEy hE huSigma hvSigma huRaise huLower huR0 huL0 ⊢
  rw [hEy, hE, ← huSigma, ← hvSigma, huRaise, huLower, huR0, huL0]
  rfl

def d4BMCanonicalSecondStokesConstantBoundaryCoefficient
    (u v : ℂ) (e₁ e₂ e₃ : Bool) : ℂ :=
  let c₁ := d4BMCompletedEisensteinCuspConstantCoefficient u e₁
  let c₂ := d4BMCompletedEisensteinCuspConstantCoefficient u e₂
  let c₃ := d4BMCompletedEisensteinCuspConstantCoefficient v e₃
  let w₁ := d4BMCompletedEisensteinCuspWeylExponent u e₁
  let w₂ := d4BMCompletedEisensteinCuspWeylExponent u e₂
  let w₃ := d4BMCompletedEisensteinCuspWeylExponent v e₃
  2 * c₃ * c₁ * w₁ * c₂ * w₂ +
    2 * c₃ * c₁ * w₁ * c₂ * w₂ * (w₂ - 1) -
    c₁ * w₁ * c₂ * w₂ * c₃ * w₃

def d4BMCanonicalSecondStokesConstantBoundaryFamily (u v : ℂ) :
    D4BMDiagonalEisensteinCuspAffineExponent →₀ ℂ :=
  d4BMDiagonalEisensteinCuspBoundaryFamily
    (d4BMCanonicalSecondStokesConstantBoundaryCoefficient u v)

/-- The literal zero-frequency second-Stokes vertical current is exactly evaluation of its
diagonal affine-exponent family. -/
theorem d4BM_canonicalSecondStokesConstantVerticalCurrent_eq_familyEvaluation
    (u v : ℂ) {Y : ℝ} (hY : 0 < Y) :
    d4BMCanonicalSecondStokesConstantVerticalCurrent u v Y =
      d4BMEvaluateCuspAffineBoundaryFamily u v Y
        (d4BMCanonicalSecondStokesConstantBoundaryFamily u v) := by
  have hYC : (Y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hY.ne'
  have hpower (a b c : ℂ) :
      (Y : ℂ) ^ (-1 + a + b + c) =
        (Y : ℂ) ^ (-1 : ℂ) * (Y : ℂ) ^ a *
          (Y : ℂ) ^ b * (Y : ℂ) ^ c := by
    rw [show -1 + a + b + c = ((-1 : ℂ) + a) + b + c by ring,
      Complex.cpow_add (((-1 : ℂ) + a) + b) c hYC,
      Complex.cpow_add ((-1 : ℂ) + a) b hYC,
      Complex.cpow_add (-1 : ℂ) a hYC]
  have hfirst (w : ℂ) :
      (Y : ℂ) ^ (w - 1) =
        (Y : ℂ) ^ (-1 : ℂ) * (Y : ℂ) ^ w := by
    rw [← Complex.cpow_add (-1 : ℂ) w hYC]
    congr 1
    ring
  have hsecond (w : ℂ) :
      (Y : ℂ) ^ (w - 2) =
        (Y : ℂ) ^ (-2 : ℂ) * (Y : ℂ) ^ w := by
    rw [← Complex.cpow_add (-2 : ℂ) w hYC]
    congr 1
    ring
  unfold d4BMCanonicalSecondStokesConstantBoundaryFamily
  rw [d4BM_evaluateDiagonalCuspBoundaryFamily_eq_boolSum]
  simp only [Fintype.sum_bool]
  simp_rw [hpower]
  unfold d4BMCanonicalSecondStokesConstantVerticalCurrent
    d4BMCanonicalSecondStokesEnergyVerticalFirstJet
    d4BMCanonicalSecondStokesEnergy
    d4BMCanonicalSecondStokesConstantBoundaryCoefficient
    d4BMCompletedEisensteinCuspConstantFullSecondJet
    d4BMCompletedEisensteinCuspConstantFirstJetTerm
    d4BMCompletedEisensteinCuspConstantSecondJetTerm
    d4BMCompletedEisensteinCuspConstantPart
    d4BMCompletedEisensteinCuspConstantTerm
    d4BMCompletedEisensteinCuspConstantMaassFactor
  simp only [zero_add, mul_zero]
  simp_rw [hfirst, hsecond, Complex.cpow_neg_one,
    Complex.cpow_neg, Complex.cpow_two]
  field_simp [hYC]
  ring

/-- Every monomial of the zero-frequency second-Stokes current has nonzero affine spectral
exponent, so its analytic-family finite part vanishes. -/
theorem d4BM_canonicalSecondStokesConstantBoundary_finitePart_zero (u v : ℂ) :
    d4BMCuspAnalyticFamilyFinitePart
        (d4BMCanonicalSecondStokesConstantBoundaryFamily u v) = 0 := by
  exact d4BMCuspAnalyticFamilyFinitePart_diagonalEisensteinBoundary_eq_zero
    (d4BMCanonicalSecondStokesConstantBoundaryCoefficient u v)

/-- Every nonconstant contribution to the canonical second-Stokes cusp current vanishes at the
cusp. -/
theorem tendsto_d4BMCanonicalSecondStokesVerticalMixedRemainder_atTop_zero
    (u v : ℂ) (x : ℝ) :
    Tendsto (d4BMCanonicalSecondStokesVerticalMixedRemainder u v x)
      atTop (𝓝 0) := by
  have h := d4BMCuspRapidDecay_canonicalSecondStokesVerticalMixedRemainder u v x 0
  simpa using h

/-- Full canonical second-Stokes cusp closure: zero constant-sector finite part together with
vanishing nonconstant remainder. -/
theorem d4BM_canonicalSecondStokes_fullCuspCurrentClosure
    (u v : ℂ) (x : ℝ) :
    d4BMCuspAnalyticFamilyFinitePart
        (d4BMCanonicalSecondStokesConstantBoundaryFamily u v) = 0 ∧
      Tendsto (d4BMCanonicalSecondStokesVerticalMixedRemainder u v x)
        atTop (𝓝 0) :=
  ⟨d4BM_canonicalSecondStokesConstantBoundary_finitePart_zero u v,
    tendsto_d4BMCanonicalSecondStokesVerticalMixedRemainder_atTop_zero u v x⟩

/-- Actual-parameter second-Stokes cusp closure, with no asymptotic premise. -/
theorem d4BM_actualSecondStokes_fullCuspBoundaryClosure
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) (x : ℝ) :
    d4BMCuspAnalyticFamilyFinitePart
        (d4BMCanonicalSecondStokesConstantBoundaryFamily
          (P.s - 1 / 2) (Q.s - 1 / 2)) = 0 ∧
      Tendsto
        (d4BMCanonicalSecondStokesVerticalMixedRemainder
          (P.s - 1 / 2) (Q.s - 1 / 2) x)
        atTop (𝓝 0) :=
  d4BM_canonicalSecondStokes_fullCuspCurrentClosure (P.s - 1 / 2) (Q.s - 1 / 2) x

/-- After non-cusp pairing, the actual second-Stokes boundary is the canonical vertical current
throughout the exterior cusp. -/
theorem d4BM_actualSecondStokes_pairedBoundaryCurrent_eq_canonicalCuspCurrent
    (B : D4BMExteriorTruncatedModularBoundaryPair)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMActualSecondStokesPairedBoundaryCurrent B.1 P Q =
      d4BMCanonicalSecondStokesVerticalCurrent
        (P.s - 1 / 2) (Q.s - 1 / 2)
        B.1.cuspTop.x
        (d4BMExteriorCuspHeight
          (⟨B.1.cuspTop, B.2⟩ : D4BMExteriorCuspCoordinate)) := by
  rw [d4BM_actualSecondStokes_pairedBoundaryCurrent_eq_cuspCurrent]
  exact d4BM_actualSecondStokesVerticalCurrent_eq_canonical
    (⟨B.1.cuspTop, B.2⟩ : D4BMExteriorCuspCoordinate) P Q

/-- Exact actual second-boundary decomposition into its affine constant family and a rapidly
decaying mixed remainder. -/
theorem d4BM_actualSecondStokes_pairedBoundaryCurrent_decomposition
    (B : D4BMExteriorTruncatedModularBoundaryPair)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMActualSecondStokesPairedBoundaryCurrent B.1 P Q =
      d4BMCanonicalSecondStokesConstantVerticalCurrent
          (P.s - 1 / 2) (Q.s - 1 / 2) B.1.cuspTop.y +
        d4BMCanonicalSecondStokesVerticalMixedRemainder
          (P.s - 1 / 2) (Q.s - 1 / 2)
          B.1.cuspTop.x B.1.cuspTop.y := by
  have hconstant :=
    d4BM_canonicalSecondStokesConstantVerticalCurrent_eq_maass
      (P.s - 1 / 2) (Q.s - 1 / 2)
      (⟨B.1.cuspTop.y, B.2⟩ : {Y : ℝ // 1 ≤ Y})
  rw [d4BM_actualSecondStokes_pairedBoundaryCurrent_eq_canonicalCuspCurrent,
    d4BM_canonicalSecondStokesVerticalCurrent_eq_maass, hconstant]
  unfold d4BMCanonicalSecondStokesVerticalMixedRemainder
  simp [d4BMExteriorCuspHeight]


end
end RHTower
