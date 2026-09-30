import GaloisForLFunctions.RHTower.PrimeArchThetaBornWittenGroundState
import GaloisForLFunctions.RHTower.PrimeArchThetaGaussianScoreEnvelopeCertificates

/-!
# Strict Gaussian score envelope of the actual first theta atom

The installed Born--Witten amplitude satisfies the explicit Gaussian envelope
with the exact factor 110843/111104 on the complete half-line. The proof keeps
the squared floor observable and the original source normalization.
-/

namespace RHTower
noncomputable section

/-- Exact first-atom density in the installed Born--Witten normalization. -/
theorem thetaCuspFirstAtom_bornWittenAmplitude_sq_eq_exp {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspBornWittenAmplitude 1 x ^ 2 =
      4 * (Real.pi * Real.exp (2 * x) - 3 / 2) *
        Real.exp ((5 / 2 : ℝ) * x - Real.pi * Real.exp (2 * x)) := by
  have he : Real.exp x ^ 2 = Real.exp (2 * x) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [thetaCuspBornWittenAmplitude_sq (by norm_num : 0 < 1) hx,
    thetaCuspBornWittenWeight_eq]
  simp only [thetaCuspMorseScale, thetaCuspMorseGroundState, thetaCuspMorseZeroMode,
    Nat.cast_one, one_mul, he, mul_pow]
  rw [pow_two (Real.exp ((5 / 4 : ℝ) * x)), ← Real.exp_add,
    pow_two (Real.exp (-(Real.pi * Real.exp (2 * x)) / 2)), ← Real.exp_add,
    ← Real.exp_add]
  congr 2
  ring


/-- Actual first-atom envelope on the compact side of the split. -/
theorem thetaCuspFirstAtom_gaussianScoreEnvelope_small
    {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1 / 3) :
    Real.pi * thetaCuspBornWittenAmplitude 1 x ^ 2 * (x - 1) ^ 2 ≤
      (110843 / 111104 : ℝ) * (243 / (100 * Real.sqrt (2 * Real.pi))) *
        Real.exp (-18 * x ^ 2) * (1 + 177 * x ^ 2) := by
  let K : ℝ := 243 / (100 * Real.sqrt (2 * Real.pi))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hq : Real.pi ≤ Real.pi * Real.exp (2 * x) := by
    have he : 1 ≤ Real.exp (2 * x) := Real.one_le_exp (by positivity)
    nlinarith [Real.pi_pos]
  have hd := thetaGaussianScore_firstAtomDecay_le hq
  have hs := thetaGaussianScore_small_scalar_le
  have he := thetaGaussianScore_exp_small_le hx hx1
  have hp := thetaGaussianScore_small_polynomial_le hx hx1
  have hi : Real.pi * thetaCuspBornWittenAmplitude 1 x ^ 2 * (x - 1) ^ 2 =
      (4 * Real.pi) *
        ((Real.pi * Real.exp (2 * x) - 3 / 2) * Real.exp (-(Real.pi * Real.exp (2 * x)))) *
        Real.exp ((5 / 2 : ℝ) * x) * (1 - x) ^ 2 := by
    rw [thetaCuspFirstAtom_bornWittenAmplitude_sq_eq_exp hx,
      sub_eq_add_neg ((5 / 2 : ℝ) * x) (Real.pi * Real.exp (2 * x)), Real.exp_add]
    ring
  have hexp : Real.exp (-18 * x ^ 2) * Real.exp (18 * x ^ 2 + (5 / 2 : ℝ) * x) =
      Real.exp ((5 / 2 : ℝ) * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    Real.pi * thetaCuspBornWittenAmplitude 1 x ^ 2 * (x - 1) ^ 2 =
        (4 * Real.pi) *
          ((Real.pi * Real.exp (2 * x) - 3 / 2) * Real.exp (-(Real.pi * Real.exp (2 * x)))) *
          Real.exp ((5 / 2 : ℝ) * x) * (1 - x) ^ 2 := hi
    _ ≤ (4 * Real.pi) * ((Real.pi - 3 / 2) * Real.exp (-Real.pi)) *
        Real.exp ((5 / 2 : ℝ) * x) * (1 - x) ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hd (by positivity)) (Real.exp_pos _).le)
        (sq_nonneg _)
    _ = (4 * Real.pi * (Real.pi - 3 / 2) * Real.exp (-Real.pi)) *
        Real.exp ((5 / 2 : ℝ) * x) * (1 - x) ^ 2 := by ring
    _ ≤ ((15 / 16 : ℝ) * K) * Real.exp ((5 / 2 : ℝ) * x) * (1 - x) ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hs (Real.exp_pos _).le) (sq_nonneg _)
    _ = K * Real.exp (-18 * x ^ 2) *
        ((15 / 16 : ℝ) * Real.exp (18 * x ^ 2 + (5 / 2 : ℝ) * x) * (1 - x) ^ 2) := by
      rw [show K * Real.exp (-18 * x ^ 2) *
          ((15 / 16 : ℝ) * Real.exp (18 * x ^ 2 + (5 / 2 : ℝ) * x) * (1 - x) ^ 2) =
          ((15 / 16 : ℝ) * K) *
            (Real.exp (-18 * x ^ 2) * Real.exp (18 * x ^ 2 + (5 / 2 : ℝ) * x)) *
            (1 - x) ^ 2 by ring, hexp]
    _ ≤ K * Real.exp (-18 * x ^ 2) *
        ((15 / 16 : ℝ) * (1 + 3 * x + 177 * x ^ 2) * (1 - x) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (by norm_num))
          (sq_nonneg _)) (mul_nonneg hK (Real.exp_pos _).le)
    _ ≤ K * Real.exp (-18 * x ^ 2) *
        ((110843 / 111104 : ℝ) * (1 + 177 * x ^ 2)) :=
      mul_le_mul_of_nonneg_left hp (mul_nonneg hK (Real.exp_pos _).le)
    _ = (110843 / 111104 : ℝ) * (243 / (100 * Real.sqrt (2 * Real.pi))) *
        Real.exp (-18 * x ^ 2) * (1 + 177 * x ^ 2) := by dsimp [K]; ring

/-- Actual first-atom envelope on the tail side of the split. -/
theorem thetaCuspFirstAtom_gaussianScoreEnvelope_large
    {x : ℝ} (hx : (1 / 3 : ℝ) ≤ x) :
    Real.pi * thetaCuspBornWittenAmplitude 1 x ^ 2 * (x - 1) ^ 2 ≤
      (110843 / 111104 : ℝ) * (243 / (100 * Real.sqrt (2 * Real.pi))) *
        Real.exp (-18 * x ^ 2) * (1 + 177 * x ^ 2) := by
  have hx0 : 0 ≤ x := by linarith
  have he := thetaGaussianScore_exponent_nonneg hx0
  have hem : Real.exp ((9 / 2 : ℝ) * x - Real.pi * Real.exp (2 * x)) ≤
      Real.exp (-18 * x ^ 2) := Real.exp_le_exp.mpr (by linarith)
  have hp := thetaGaussianScore_large_polynomial_le hx
  have hs := thetaGaussianScore_large_scalar_le
  have hid : Real.exp (2 * x) *
      Real.exp ((5 / 2 : ℝ) * x - Real.pi * Real.exp (2 * x)) =
      Real.exp ((9 / 2 : ℝ) * x - Real.pi * Real.exp (2 * x)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    Real.pi * thetaCuspBornWittenAmplitude 1 x ^ 2 * (x - 1) ^ 2 =
        Real.pi * (4 * (Real.pi * Real.exp (2 * x) - 3 / 2) *
          Real.exp ((5 / 2 : ℝ) * x - Real.pi * Real.exp (2 * x))) * (x - 1) ^ 2 := by
      rw [thetaCuspFirstAtom_bornWittenAmplitude_sq_eq_exp hx0]
    _ ≤ Real.pi * (4 * (Real.pi * Real.exp (2 * x)) *
        Real.exp ((5 / 2 : ℝ) * x - Real.pi * Real.exp (2 * x))) * (x - 1) ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      nlinarith
    _ = 4 * Real.pi ^ 2 *
        Real.exp ((9 / 2 : ℝ) * x - Real.pi * Real.exp (2 * x)) * (x - 1) ^ 2 := by
      rw [show Real.pi * (4 * (Real.pi * Real.exp (2 * x)) *
          Real.exp ((5 / 2 : ℝ) * x - Real.pi * Real.exp (2 * x))) * (x - 1) ^ 2 =
          4 * Real.pi ^ 2 * (Real.exp (2 * x) *
            Real.exp ((5 / 2 : ℝ) * x - Real.pi * Real.exp (2 * x))) * (x - 1) ^ 2 by ring,
        hid]
    _ ≤ 4 * Real.pi ^ 2 * Real.exp (-18 * x ^ 2) * (x - 1) ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hem (by positivity))
        (sq_nonneg _)
    _ ≤ 4 * Real.pi ^ 2 * Real.exp (-18 * x ^ 2) *
        ((2 / 93 : ℝ) * (1 + 177 * x ^ 2)) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = (4 * Real.pi ^ 2 * (2 / 93 : ℝ)) * Real.exp (-18 * x ^ 2) *
        (1 + 177 * x ^ 2) := by ring
    _ ≤ (110843 / 111104 : ℝ) * (243 / (100 * Real.sqrt (2 * Real.pi))) *
        Real.exp (-18 * x ^ 2) * (1 + 177 * x ^ 2) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hs (Real.exp_pos _).le) (by positivity)

/-- Complete actual first-atom Gaussian score envelope with an exact strict surplus factor. -/
theorem thetaCuspFirstAtom_gaussianScoreEnvelope {x : ℝ} (hx : 0 ≤ x) :
    Real.pi * thetaCuspBornWittenAmplitude 1 x ^ 2 * (x - 1) ^ 2 ≤
      (110843 / 111104 : ℝ) * (243 / (100 * Real.sqrt (2 * Real.pi))) *
        Real.exp (-18 * x ^ 2) * (1 + 177 * x ^ 2) := by
  by_cases hx1 : x ≤ 1 / 3
  · exact thetaCuspFirstAtom_gaussianScoreEnvelope_small hx hx1
  · exact thetaCuspFirstAtom_gaussianScoreEnvelope_large (le_of_not_ge hx1)

end
end RHTower
