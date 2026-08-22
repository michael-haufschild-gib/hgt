import GaloisForLFunctions.HilbertMetric.ReflectionSixthJet
import GaloisForLFunctions.RHTower.PrimeArchThetaBornWittenPopescuCorrection

/-!
# Fifth and sixth logarithmic theta Born--Witten jets

The exact Born--Witten readout coordinate closes under differentiation: its velocity is
`2q + 3`.  This module records the next two literal log-density jets.  They are the missing
atomwise analytic layer for a sixth reflected-source Hankel test; no sign conclusion is built in.
-/

open Real

namespace RHTower

noncomputable section

/-- Fifth logarithmic derivative of the theta Born--Witten density in the readout coordinate. -/
def thetaCuspBornWittenLogFifthDerivative (n : ℕ) (x : ℝ) : ℝ :=
  let q := thetaCuspBornWittenWeight n x
  (2 * q + 3) * (16 - 24 / q ^ 2 - 504 / q ^ 3 -
    1944 / q ^ 4 - 1944 / q ^ 5)

/-- Sixth logarithmic derivative of the theta Born--Witten density in the readout coordinate. -/
def thetaCuspBornWittenLogSixthDerivative (n : ℕ) (x : ℝ) : ℝ :=
  let q := thetaCuspBornWittenWeight n x
  (2 * q + 3) * (32 + 48 / q ^ 2 + 2160 / q ^ 3 +
    16200 / q ^ 4 + 38880 / q ^ 5 + 29160 / q ^ 6)

/-- Differentiating the fourth readout profile produces the literal fifth log-density jet. -/
theorem hasDerivAt_thetaCuspBornWittenLogFourthDerivative
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (thetaCuspBornWittenLogFourthDerivative n)
      (thetaCuspBornWittenLogFifthDerivative n x) x := by
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
  have hrq2 := hr.div hq2 (pow_ne_zero 2 hqpos.ne')
  have hrq3 := hr.div hq3 (pow_ne_zero 3 hqpos.ne')
  have hrq4 := hr.div hq4 (pow_ne_zero 4 hqpos.ne')
  have hrq5 := hr.div hq5 (pow_ne_zero 5 hqpos.ne')
  simp only [Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSubDiff, pow_one] at hrq2 hrq3 hrq4 hrq5
  have hprofile : HasDerivAt
      (fun y : ℝ => 8 * r y + 12 * r y / q y ^ 2 + 108 * r y / q y ^ 3 +
        162 * r y / q y ^ 4)
      (thetaCuspBornWittenLogFifthDerivative n x) x := by
    simpa only [Pi.add_apply, Pi.div_apply, Pi.pow_apply, mul_div_assoc] using!
      ((((hr.const_mul 8).add (hrq2.const_mul 12)).add
        (hrq3.const_mul 108)).add (hrq4.const_mul 162)).congr_deriv (by
        symm
        dsimp only [thetaCuspBornWittenLogFifthDerivative, r, q]
        simp only [q] at hqpos ⊢
        field_simp [hqpos.ne']
        ring)
  convert hprofile using 1
  funext y
  simp only [thetaCuspBornWittenLogFourthDerivative, r, q]
  ring

/-- Differentiating the fifth readout profile produces the literal sixth log-density jet. -/
theorem hasDerivAt_thetaCuspBornWittenLogFifthDerivative
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (thetaCuspBornWittenLogFifthDerivative n)
      (thetaCuspBornWittenLogSixthDerivative n x) x := by
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
  have hrq2 := hr.div hq2 (pow_ne_zero 2 hqpos.ne')
  have hrq3 := hr.div hq3 (pow_ne_zero 3 hqpos.ne')
  have hrq4 := hr.div hq4 (pow_ne_zero 4 hqpos.ne')
  have hrq5 := hr.div hq5 (pow_ne_zero 5 hqpos.ne')
  have hrq6 := hr.div hq6 (pow_ne_zero 6 hqpos.ne')
  simp only [Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSubDiff, pow_one] at hrq2 hrq3 hrq4 hrq5 hrq6
  have hprofile : HasDerivAt
      (fun y : ℝ => 16 * r y - 24 * r y / q y ^ 2 - 504 * r y / q y ^ 3 -
        1944 * r y / q y ^ 4 - 1944 * r y / q y ^ 5)
      (thetaCuspBornWittenLogSixthDerivative n x) x := by
    simpa only [Pi.add_apply, Pi.sub_apply, Pi.div_apply, Pi.pow_apply, mul_div_assoc] using!
      (((((hr.const_mul 16).sub (hrq2.const_mul 24)).sub
        (hrq3.const_mul 504)).sub (hrq4.const_mul 1944)).sub
        (hrq5.const_mul 1944)).congr_deriv (by
        symm
        dsimp only [thetaCuspBornWittenLogSixthDerivative, r, q]
        simp only [q] at hqpos ⊢
        field_simp [hqpos.ne']
        ring)
  convert hprofile using 1
  funext y
  simp only [thetaCuspBornWittenLogFifthDerivative, r, q]
  ring

/-- Fifth Born--Witten log jet in the Morse-scale coordinate. -/
theorem thetaCuspBornWittenLogFifthDerivative_eq_scaleProfile
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspBornWittenLogFifthDerivative n x =
      32 * thetaCuspMorseScale n x -
        48 * thetaCuspMorseScale n x /
          (thetaCuspMorseScale n x - 3 / 2) ^ 2 -
        1008 * thetaCuspMorseScale n x /
          (thetaCuspMorseScale n x - 3 / 2) ^ 3 -
        3888 * thetaCuspMorseScale n x /
          (thetaCuspMorseScale n x - 3 / 2) ^ 4 -
        3888 * thetaCuspMorseScale n x /
          (thetaCuspMorseScale n x - 3 / 2) ^ 5 := by
  have hweight := thetaCuspBornWittenWeight_pos hn hx
  rw [thetaCuspBornWittenWeight_eq] at hweight
  unfold thetaCuspBornWittenLogFifthDerivative
  rw [thetaCuspBornWittenWeight_eq]
  field_simp [hweight.ne']
  ring

/-- Sixth Born--Witten log jet in the Morse-scale coordinate. -/
theorem thetaCuspBornWittenLogSixthDerivative_eq_scaleProfile
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspBornWittenLogSixthDerivative n x =
      64 * thetaCuspMorseScale n x +
        96 * thetaCuspMorseScale n x /
          (thetaCuspMorseScale n x - 3 / 2) ^ 2 +
        4320 * thetaCuspMorseScale n x /
          (thetaCuspMorseScale n x - 3 / 2) ^ 3 +
        32400 * thetaCuspMorseScale n x /
          (thetaCuspMorseScale n x - 3 / 2) ^ 4 +
        77760 * thetaCuspMorseScale n x /
          (thetaCuspMorseScale n x - 3 / 2) ^ 5 +
        58320 * thetaCuspMorseScale n x /
          (thetaCuspMorseScale n x - 3 / 2) ^ 6 := by
  have hweight := thetaCuspBornWittenWeight_pos hn hx
  rw [thetaCuspBornWittenWeight_eq] at hweight
  unfold thetaCuspBornWittenLogSixthDerivative
  rw [thetaCuspBornWittenWeight_eq]
  field_simp [hweight.ne']
  ring

/-- The fourth atomwise log-density jet is positive on the physical half-line. -/
theorem thetaCuspBornWittenLogFourthDerivative_pos
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    0 < thetaCuspBornWittenLogFourthDerivative n x := by
  have hq : 0 < thetaCuspBornWittenWeight n x :=
    thetaCuspBornWittenWeight_pos hn hx
  unfold thetaCuspBornWittenLogFourthDerivative
  positivity

/-- The sixth atomwise log-density jet is positive on the physical half-line. -/
theorem thetaCuspBornWittenLogSixthDerivative_pos
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    0 < thetaCuspBornWittenLogSixthDerivative n x := by
  have hq : 0 < thetaCuspBornWittenWeight n x :=
    thetaCuspBornWittenWeight_pos hn hx
  unfold thetaCuspBornWittenLogSixthDerivative
  positivity

/-- The fourth atomwise log-density jet is at most six fifths of curvature squared. -/
theorem thetaCuspBornWittenLogFourthDerivative_le_sixFifths_curvature_sq
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspBornWittenLogFourthDerivative n x ≤
      (6 / 5 : ℝ) * thetaCuspBornWittenLogCurvature n x ^ 2 := by
  let q := thetaCuspBornWittenWeight n x
  have hq : 0 < q := thetaCuspBornWittenWeight_pos hn hx
  have hy : 0 ≤ q - 3 / 2 := by
    dsimp only [q]
    linarith [three_halves_lt_thetaCuspBornWittenWeight hn hx]
  have hpoly : 0 ≤
      96 * (q - 3 / 2) ^ 6 + 1072 * (q - 3 / 2) ^ 5 +
        5184 * (q - 3 / 2) ^ 4 + 14208 * (q - 3 / 2) ^ 3 +
          22446 * (q - 3 / 2) ^ 2 + 16065 * (q - 3 / 2) + 405 := by
    positivity
  rw [thetaCuspBornWittenLogCurvature_eq_readoutProfile hn hx]
  apply sub_nonneg.mp
  change 0 ≤
    (6 / 5 : ℝ) * (4 * q + 6 + 6 / q + 9 / q ^ 2) ^ 2 -
      (2 * q + 3) * (8 + 12 / q ^ 2 + 108 / q ^ 3 + 162 / q ^ 4)
  rw [show
      (6 / 5 : ℝ) * (4 * q + 6 + 6 / q + 9 / q ^ 2) ^ 2 -
        (2 * q + 3) * (8 + 12 / q ^ 2 + 108 / q ^ 3 + 162 / q ^ 4) =
      (96 * (q - 3 / 2) ^ 6 + 1072 * (q - 3 / 2) ^ 5 +
        5184 * (q - 3 / 2) ^ 4 + 14208 * (q - 3 / 2) ^ 3 +
          22446 * (q - 3 / 2) ^ 2 + 16065 * (q - 3 / 2) + 405) /
        (5 * q ^ 4) by
      field_simp [hq.ne']
      ring]
  exact div_nonneg hpoly (by positivity)

/-- The exact sixth reflected-Hankel source polynomial for one theta Born--Witten atom. -/
def thetaCuspBornWittenReflectionSixthCurvature (n : ℕ) (x : ℝ) : ℝ :=
  thetaCuspBornWittenLogCurvature n x * thetaCuspBornWittenLogSixthDerivative n x -
    thetaCuspBornWittenLogFourthDerivative n x ^ 2 -
      18 * thetaCuspBornWittenLogCurvature n x ^ 2 *
        thetaCuspBornWittenLogFourthDerivative n x +
        24 * thetaCuspBornWittenLogCurvature n x ^ 4

/-- Every positive theta atom has strictly positive second--sixth reflected Hankel curvature. -/
theorem thetaCuspBornWittenReflectionSixthCurvature_pos
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    0 < thetaCuspBornWittenReflectionSixthCurvature n x := by
  let A := thetaCuspBornWittenLogCurvature n x
  let B := thetaCuspBornWittenLogFourthDerivative n x
  let C := thetaCuspBornWittenLogSixthDerivative n x
  have hA : 0 < A := by
    dsimp only [A]
    linarith [nineteen_le_thetaCuspBornWittenLogCurvature hn hx]
  have hB : 0 < B := by
    dsimp only [B]
    exact thetaCuspBornWittenLogFourthDerivative_pos hn hx
  have hC : 0 < C := by
    dsimp only [C]
    exact thetaCuspBornWittenLogSixthDerivative_pos hn hx
  have hBbound : B ≤ (6 / 5 : ℝ) * A ^ 2 := by
    dsimp only [A, B]
    exact thetaCuspBornWittenLogFourthDerivative_le_sixFifths_curvature_sq hn hx
  have hBsq : B ^ 2 ≤ (36 / 25 : ℝ) * A ^ 4 := by
    have hbound_sq : B ^ 2 ≤ ((6 / 5 : ℝ) * A ^ 2) ^ 2 := by
      exact (sq_le_sq₀ hB.le (by positivity)).2 hBbound
    nlinarith
  have hBA2 : 18 * A ^ 2 * B ≤ (108 / 5 : ℝ) * A ^ 4 := by
    have hnonneg : 0 ≤ 18 * A ^ 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hBbound hnonneg
    nlinarith
  have hAC : 0 < A * C := mul_pos hA hC
  have hA4 : 0 < A ^ 4 := pow_pos hA 4
  dsimp only [thetaCuspBornWittenReflectionSixthCurvature]
  change 0 < A * C - B ^ 2 - 18 * A ^ 2 * B + 24 * A ^ 4
  nlinarith

end

end RHTower
