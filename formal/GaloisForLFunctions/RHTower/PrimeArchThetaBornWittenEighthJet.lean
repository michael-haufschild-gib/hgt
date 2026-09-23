import GaloisForLFunctions.HilbertMetric.ReflectionEighthJet
import GaloisForLFunctions.RHTower.PrimeArchThetaBornWittenSixthJet

/-!
# Seventh and eighth theta Born--Witten jets

The exact Born--Witten readout coordinate has velocity `2q + 3`, so the atomwise logarithmic
jet tower remains rational through order eight.  After clearing the sixteenth power of `q`, the
rank-three reflected-Hankel polynomial is a polynomial with strictly positive coefficients in
`q - 3 / 2`.  This closes the single-atom order-eight source obstruction on the physical
half-line.
-/

open Real

namespace RHTower

noncomputable section

/-- Seventh logarithmic derivative of the theta Born--Witten potential. -/
def thetaCuspBornWittenLogSeventhDerivative (n : ℕ) (x : ℝ) : ℝ :=
  let q := thetaCuspBornWittenWeight n x
  (2 * q + 3) * (64 - 96 / q ^ (2 : ℕ) - 8928 / q ^ (3 : ℕ) -
    116640 / q ^ (4 : ℕ) - 505440 / q ^ (5 : ℕ) - 874800 / q ^ (6 : ℕ) -
    524880 / q ^ (7 : ℕ))

/-- Eighth logarithmic derivative of the theta Born--Witten potential. -/
def thetaCuspBornWittenLogEighthDerivative (n : ℕ) (x : ℝ) : ℝ :=
  let q := thetaCuspBornWittenWeight n x
  (2 * q + 3) * (128 + 192 / q ^ (2 : ℕ) + 36288 / q ^ (3 : ℕ) +
    780192 / q ^ (4 : ℕ) + 5443200 / q ^ (5 : ℕ) + 16329600 / q ^ (6 : ℕ) +
    22044960 / q ^ (7 : ℕ) + 11022480 / q ^ (8 : ℕ))

/-- Differentiating the sixth readout profile produces the literal seventh potential jet. -/
theorem hasDerivAt_thetaCuspBornWittenLogSixthDerivative
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (thetaCuspBornWittenLogSixthDerivative n)
      (thetaCuspBornWittenLogSeventhDerivative n x) x := by
  let q : ℝ → ℝ := thetaCuspBornWittenWeight n
  let r : ℝ → ℝ := fun y => 2 * q y + 3
  have hqpos : 0 < q x := thetaCuspBornWittenWeight_pos hn hx
  have htq : thetaCuspMorseScale n x = q x + 3 / 2 := by
    dsimp only [q]
    rw [thetaCuspBornWittenWeight_eq]
    ring
  have hq : HasDerivAt q (r x) x := by
    convert hasDerivAt_thetaCuspBornWittenWeight n x using 1
    dsimp only [r]
    rw [htq]
    ring
  have hr : HasDerivAt r (2 * r x) x :=
    (hq.const_mul 2).add_const 3
  have hq2 := hq.pow 2
  have hq3 := hq.pow 3
  have hq4 := hq.pow 4
  have hq5 := hq.pow 5
  have hq6 := hq.pow 6
  have hq7 := hq.pow 7
  have hrq2 := hr.div hq2 (pow_ne_zero 2 hqpos.ne')
  have hrq3 := hr.div hq3 (pow_ne_zero 3 hqpos.ne')
  have hrq4 := hr.div hq4 (pow_ne_zero 4 hqpos.ne')
  have hrq5 := hr.div hq5 (pow_ne_zero 5 hqpos.ne')
  have hrq6 := hr.div hq6 (pow_ne_zero 6 hqpos.ne')
  have hrq7 := hr.div hq7 (pow_ne_zero 7 hqpos.ne')
  simp only [Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSubDiff, pow_one] at hrq2 hrq3 hrq4
  simp only [Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSubDiff] at hrq5 hrq6 hrq7
  have hprofile : HasDerivAt
      (fun y : ℝ => 32 * r y + 48 * r y / q y ^ (2 : ℕ) +
        2160 * r y / q y ^ (3 : ℕ) + 16200 * r y / q y ^ (4 : ℕ) +
        38880 * r y / q y ^ (5 : ℕ) + 29160 * r y / q y ^ (6 : ℕ))
      (thetaCuspBornWittenLogSeventhDerivative n x) x := by
    simpa only [Pi.add_apply, Pi.div_apply, Pi.pow_apply, mul_div_assoc] using!
      ((((((hr.const_mul 32).add (hrq2.const_mul 48)).add
        (hrq3.const_mul 2160)).add (hrq4.const_mul 16200)).add
        (hrq5.const_mul 38880)).add (hrq6.const_mul 29160)).congr_deriv (by
        symm
        dsimp only [thetaCuspBornWittenLogSeventhDerivative, r, q]
        simp only [q] at hqpos ⊢
        field_simp [hqpos.ne']
        ring)
  convert hprofile using 1
  funext y
  simp only [thetaCuspBornWittenLogSixthDerivative, r, q]
  ring

/-- Differentiating the seventh readout profile produces the literal eighth potential jet. -/
theorem hasDerivAt_thetaCuspBornWittenLogSeventhDerivative
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (thetaCuspBornWittenLogSeventhDerivative n)
      (thetaCuspBornWittenLogEighthDerivative n x) x := by
  let q : ℝ → ℝ := thetaCuspBornWittenWeight n
  let r : ℝ → ℝ := fun y => 2 * q y + 3
  have hqpos : 0 < q x := thetaCuspBornWittenWeight_pos hn hx
  have htq : thetaCuspMorseScale n x = q x + 3 / 2 := by
    dsimp only [q]
    rw [thetaCuspBornWittenWeight_eq]
    ring
  have hq : HasDerivAt q (r x) x := by
    convert hasDerivAt_thetaCuspBornWittenWeight n x using 1
    dsimp only [r]
    rw [htq]
    ring
  have hr : HasDerivAt r (2 * r x) x :=
    (hq.const_mul 2).add_const 3
  have hq2 := hq.pow 2
  have hq3 := hq.pow 3
  have hq4 := hq.pow 4
  have hq5 := hq.pow 5
  have hq6 := hq.pow 6
  have hq7 := hq.pow 7
  have hq8 := hq.pow 8
  have hrq2 := hr.div hq2 (pow_ne_zero 2 hqpos.ne')
  have hrq3 := hr.div hq3 (pow_ne_zero 3 hqpos.ne')
  have hrq4 := hr.div hq4 (pow_ne_zero 4 hqpos.ne')
  have hrq5 := hr.div hq5 (pow_ne_zero 5 hqpos.ne')
  have hrq6 := hr.div hq6 (pow_ne_zero 6 hqpos.ne')
  have hrq7 := hr.div hq7 (pow_ne_zero 7 hqpos.ne')
  have hrq8 := hr.div hq8 (pow_ne_zero 8 hqpos.ne')
  simp only [Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSubDiff, pow_one] at hrq2 hrq3 hrq4
  simp only [Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSubDiff] at hrq5 hrq6 hrq7 hrq8
  have hprofile : HasDerivAt
      (fun y : ℝ => 64 * r y - 96 * r y / q y ^ (2 : ℕ) -
        8928 * r y / q y ^ (3 : ℕ) - 116640 * r y / q y ^ (4 : ℕ) -
        505440 * r y / q y ^ (5 : ℕ) - 874800 * r y / q y ^ (6 : ℕ) -
        524880 * r y / q y ^ (7 : ℕ))
      (thetaCuspBornWittenLogEighthDerivative n x) x := by
    simpa only [Pi.add_apply, Pi.sub_apply, Pi.div_apply, Pi.pow_apply,
      mul_div_assoc] using!
      (((((((hr.const_mul 64).sub (hrq2.const_mul 96)).sub
        (hrq3.const_mul 8928)).sub (hrq4.const_mul 116640)).sub
        (hrq5.const_mul 505440)).sub (hrq6.const_mul 874800)).sub
        (hrq7.const_mul 524880)).congr_deriv (by
        symm
        dsimp only [thetaCuspBornWittenLogEighthDerivative, r, q]
        simp only [q] at hqpos ⊢
        field_simp [hqpos.ne']
        ring)
  convert hprofile using 1
  funext y
  simp only [thetaCuspBornWittenLogSeventhDerivative, r, q]
  ring

/-- Eighth atomwise potential jet is positive on the physical half-line. -/
theorem thetaCuspBornWittenLogEighthDerivative_pos
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    0 < thetaCuspBornWittenLogEighthDerivative n x := by
  have hq : 0 < thetaCuspBornWittenWeight n x :=
    thetaCuspBornWittenWeight_pos hn hx
  unfold thetaCuspBornWittenLogEighthDerivative
  positivity

/-- Normalized rank-three reflected-Hankel source polynomial for one Born--Witten atom. -/
def thetaCuspBornWittenReflectionEighthHankelCurvature
    (n : ℕ) (x : ℝ) : ℝ :=
  let A := thetaCuspBornWittenLogCurvature n x
  let B := thetaCuspBornWittenLogFourthDerivative n x
  let C := thetaCuspBornWittenLogSixthDerivative n x
  let D := thetaCuspBornWittenLogEighthDerivative n x
  768 * A ^ (6 : ℕ) - 1344 * A ^ (4 : ℕ) * B + 304 * A ^ (2 : ℕ) * B ^ (2 : ℕ) -
    68 * B ^ (3 : ℕ) + 128 * A ^ (3 : ℕ) * C - 4 * A ^ (2 : ℕ) * D + B * D - C ^ (2 : ℕ)

/-- Every positive theta atom has strictly positive rank-three order-eight source curvature. -/
theorem thetaCuspBornWittenReflectionEighthHankelCurvature_pos
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    0 < thetaCuspBornWittenReflectionEighthHankelCurvature n x := by
  let q := thetaCuspBornWittenWeight n x
  have hq0 : 0 < q := thetaCuspBornWittenWeight_pos hn hx
  have hq : (3 / 2 : ℝ) ≤ q :=
    (three_halves_lt_thetaCuspBornWittenWeight hn hx).le
  let y := q - 3 / 2
  have hy : 0 ≤ y := by
    dsimp only [y]
    linarith
  let A := 4 * q + 6 + 6 / q + 9 / q ^ (2 : ℕ)
  let B := (2 * q + 3) *
    (8 + 12 / q ^ (2 : ℕ) + 108 / q ^ (3 : ℕ) + 162 / q ^ (4 : ℕ))
  let C := (2 * q + 3) *
    (32 + 48 / q ^ (2 : ℕ) + 2160 / q ^ (3 : ℕ) + 16200 / q ^ (4 : ℕ) +
      38880 / q ^ (5 : ℕ) + 29160 / q ^ (6 : ℕ))
  let D := (2 * q + 3) *
    (128 + 192 / q ^ (2 : ℕ) + 36288 / q ^ (3 : ℕ) + 780192 / q ^ (4 : ℕ) +
      5443200 / q ^ (5 : ℕ) + 16329600 / q ^ (6 : ℕ) + 22044960 / q ^ (7 : ℕ) +
      11022480 / q ^ (8 : ℕ))
  have hpow : 0 < q ^ (16 : ℕ) := pow_pos hq0 16
  have hcleared : 0 < q ^ (16 : ℕ) *
      thetaCuspBornWittenReflectionEighthHankelCurvature n x := by
    simp only [thetaCuspBornWittenReflectionEighthHankelCurvature]
    rw [thetaCuspBornWittenLogCurvature_eq_readoutProfile hn hx]
    change 0 < q ^ (16 : ℕ) *
      (768 * A ^ (6 : ℕ) - 1344 * A ^ (4 : ℕ) * B + 304 * A ^ (2 : ℕ) * B ^ (2 : ℕ) -
        68 * B ^ (3 : ℕ) + 128 * A ^ (3 : ℕ) * C - 4 * A ^ (2 : ℕ) * D + B * D - C ^ (2 : ℕ))
    dsimp only [A, B, C, D]
    field_simp [hq0.ne']
    rw [show q = 3 / 2 + y by dsimp only [y]; ring]
    ring_nf
    positivity
  nlinarith

/-- Hypothesis-free square-parameter form of single-atom order-eight positivity. -/
theorem thetaCuspBornWittenReflectionEighthHankelCurvature_natSucc_sq_pos
    (n : ℕ) (x : ℝ) :
    0 < thetaCuspBornWittenReflectionEighthHankelCurvature (n + 1) (x ^ (2 : ℕ)) := by
  exact thetaCuspBornWittenReflectionEighthHankelCurvature_pos
    (by omega) (sq_nonneg x)

end

end RHTower
