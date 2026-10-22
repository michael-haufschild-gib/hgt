import GaloisForLFunctions.RHTower.PrimeArchThetaScoreMomentRecurrence
import GaloisForLFunctions.RHTower.PrimeArchThetaScoreMomentDefect
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspNormalizedShiftedGramStrict

/-!
# Four-moment constraint from score coercivity and shifted Gram positivity

The score recurrence upper-bounds the fifth normalized theta moment. The
strict shifted Gram determinant lower-bounds it. Eliminating that fifth moment
produces a source-specific strict polynomial constraint on the first four
moments, precisely the coordinates of the K-RVM determinant gate.
-/

namespace RHTower
noncomputable section

/-- The fourth and fifth source moments cannot be chosen independently: the
score upper bound and shifted Gram lower bound impose this strict inequality. -/
theorem thetaCusp_fourMoment_scoreSchurConstraint :
    let a := thetaCuspNormalizedEvenMoment 1
    let b := thetaCuspNormalizedEvenMoment 2
    let c := thetaCuspNormalizedEvenMoment 3
    let e := thetaCuspNormalizedEvenMoment 4
    let q := a * c - b ^ (2 : ℕ)
    let p := a * e ^ (2 : ℕ) - 2 * b * c * e + c ^ (3 : ℕ)
    303 * p < 145 * q * e := by
  dsimp only
  let a := thetaCuspNormalizedEvenMoment 1
  let b := thetaCuspNormalizedEvenMoment 2
  let c := thetaCuspNormalizedEvenMoment 3
  let e := thetaCuspNormalizedEvenMoment 4
  let f := thetaCuspNormalizedEvenMoment 5
  let q := a * c - b ^ (2 : ℕ)
  let p := a * e ^ (2 : ℕ) - 2 * b * c * e + c ^ (3 : ℕ)
  have hq := thetaCuspNormalizedEvenMoment_shifted_q_pos
  change 0 < q at hq
  have hΔ := thetaCuspNormalizedEvenMoment_shifted_delta_pos
  change 0 < q * f - p at hΔ
  have hs := thetaCuspNormalizedEvenMoment_succ_le_score 4
  norm_num at hs
  change (303 : ℝ) * f ≤ 145 * e at hs
  have hscaled := mul_le_mul_of_nonneg_left hs hq.le
  change (303 : ℝ) * p < 145 * q * e
  nlinarith

/-- Eliminating the fourth moment as well yields a strict discriminant
constraint in the first three normalized theta moments. -/
theorem thetaCusp_threeMoment_scoreSchurDiscriminant_pos :
    let a := thetaCuspNormalizedEvenMoment 1
    let b := thetaCuspNormalizedEvenMoment 2
    let c := thetaCuspNormalizedEvenMoment 3
    let q := a * c - b ^ (2 : ℕ)
    0 < (606 * b * c + 145 * q) ^ (2 : ℕ) -
      4 * (303 * a) * (303 * c ^ (3 : ℕ)) := by
  dsimp only
  let a := thetaCuspNormalizedEvenMoment 1
  let b := thetaCuspNormalizedEvenMoment 2
  let c := thetaCuspNormalizedEvenMoment 3
  let e := thetaCuspNormalizedEvenMoment 4
  let q := a * c - b ^ (2 : ℕ)
  let A : ℝ := 303 * a
  let B : ℝ := 606 * b * c + 145 * q
  let C : ℝ := 303 * c ^ (3 : ℕ)
  have ha : 0 < a := by
    dsimp only [a, thetaCuspNormalizedEvenMoment]
    exact div_pos (thetaCuspRawEvenMoment_pos 1)
      (thetaCuspRawEvenMoment_pos 0)
  have hA : 0 < A := by dsimp only [A]; positivity
  have hcore := thetaCusp_fourMoment_scoreSchurConstraint
  change 303 * (a * e ^ (2 : ℕ) - 2 * b * c * e + c ^ (3 : ℕ)) <
    145 * q * e at hcore
  have hQ : A * e ^ (2 : ℕ) - B * e + C < 0 := by
    dsimp only [A, B, C]
    nlinarith
  have hproduct : 0 < -4 * A * (A * e ^ (2 : ℕ) - B * e + C) := by
    have hneg : 0 < -(A * e ^ (2 : ℕ) - B * e + C) := neg_pos.mpr hQ
    nlinarith [mul_pos hA hneg]
  change 0 < B ^ (2 : ℕ) - 4 * A * C
  nlinarith [sq_nonneg (B - 2 * A * e), hproduct]

/-- The first atom's square-integral defect survives elimination of the fifth
moment. This is a strict source margin in the four-moment Schur constraint. -/
theorem thetaCusp_fourMoment_scoreSchurConstraint_with_defect :
    let a := thetaCuspNormalizedEvenMoment 1
    let b := thetaCuspNormalizedEvenMoment 2
    let c := thetaCuspNormalizedEvenMoment 3
    let e := thetaCuspNormalizedEvenMoment 4
    let q := a * c - b ^ (2 : ℕ)
    let p := a * e ^ (2 : ℕ) - 2 * b * c * e + c ^ (3 : ℕ)
    let J := 2 * Real.pi *
      (∫ x : ℝ in Set.Ioi 0,
        x ^ (8 : ℕ) * (x - 1) ^ (2 : ℕ) *
          thetaCuspBornWittenAmplitude 1 x ^ (2 : ℕ))
    303 * thetaCuspRawEvenMoment 0 * p + q * J <
      145 * q * thetaCuspRawEvenMoment 4 := by
  dsimp only
  let a := thetaCuspNormalizedEvenMoment 1
  let b := thetaCuspNormalizedEvenMoment 2
  let c := thetaCuspNormalizedEvenMoment 3
  let e := thetaCuspNormalizedEvenMoment 4
  let q := a * c - b ^ (2 : ℕ)
  let p := a * e ^ (2 : ℕ) - 2 * b * c * e + c ^ (3 : ℕ)
  let J : ℝ := 2 * Real.pi *
    (∫ x : ℝ in Set.Ioi 0,
      x ^ (8 : ℕ) * (x - 1) ^ (2 : ℕ) *
        thetaCuspBornWittenAmplitude 1 x ^ (2 : ℕ))
  have hq := thetaCuspNormalizedEvenMoment_shifted_q_pos
  change 0 < q at hq
  have hmass : 0 < thetaCuspRawEvenMoment 0 := thetaCuspRawEvenMoment_pos 0
  have hΔ := thetaCuspNormalizedEvenMoment_shifted_delta_pos
  change 0 < q * (thetaCuspRawEvenMoment 5 / thetaCuspRawEvenMoment 0) - p at hΔ
  have hDdiv : p <
      (q * thetaCuspRawEvenMoment 5) / thetaCuspRawEvenMoment 0 := by
    have heq : q * (thetaCuspRawEvenMoment 5 / thetaCuspRawEvenMoment 0) =
        (q * thetaCuspRawEvenMoment 5) / thetaCuspRawEvenMoment 0 := by ring
    rw [heq] at hΔ
    linarith
  have hcross := (lt_div_iff₀ hmass).mp hDdiv
  have hcross303 := mul_lt_mul_of_pos_left hcross (by norm_num : (0 : ℝ) < 303)
  have hraw := thetaCuspRawEvenMoment_scoreGap_ge_firstAtomSquare 4
  norm_num at hraw
  change J ≤ 145 * thetaCuspRawEvenMoment 4 -
    303 * thetaCuspRawEvenMoment 5 at hraw
  have hscaled := mul_le_mul_of_nonneg_left hraw hq.le
  change 303 * thetaCuspRawEvenMoment 0 * p + q * J <
    145 * q * thetaCuspRawEvenMoment 4
  nlinarith

end
end RHTower
