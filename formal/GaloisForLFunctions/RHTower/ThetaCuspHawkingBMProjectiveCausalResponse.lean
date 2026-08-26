import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCausalChannelEvaluation

/-!
# Projective Birmingham--Mokhtari causal response

For the four-dimensional Birmingham--Mokhtari master equation, the two AdS connection
coefficients share the horizon factor `Gamma(c)`.  A boundary response is their projective
ratio, so this common normalization cancels.  The pole of `Gamma(c)` at a mixed Hawking--
Matsubara frequency therefore does not make the projective response singular.

Writing `A = c-b` and `B = c-a`, the forbidden and decaying coefficients are

`S = Gamma(c) Gamma(1/2) / (Gamma(A) Gamma(B))`,

`V = Gamma(c) Gamma(-1/2) / (Gamma(A-1/2) Gamma(B-1/2))`.

Their pole-cancelled ratio is

`V/S = -2 Gamma(A) Gamma(B) / (Gamma(A-1/2) Gamma(B-1/2))`.

At the mixed frequency and real horizon momentum, the two Gamma ratios are conjugate.
Consequently the causal projective response is a strictly negative real norm-square.  This
distinguishes the physical response from the reciprocal forbidden coefficient, which is a
normalization-dependent Jost representative.
-/

open Complex Real Set Filter Topology

namespace RHTower

noncomputable section

/-- First hypergeometric parameter, expressed through the plus Jost argument. -/
def d4BMCausalHypergeometricA (omega chi : ℂ) : ℂ :=
  d4BMCausalRadialA omega chi - 1 / 2

/-- Second hypergeometric parameter, expressed through the minus Jost argument. -/
def d4BMCausalHypergeometricB (omega chi : ℂ) : ℂ :=
  d4BMCausalRadialB omega chi - 1 / 2

/-- Coefficient of the decaying AdS boundary branch in the ingoing BM solution. -/
def d4BMCausalDecayingBoundaryCoefficient (omega chi : ℂ) : ℂ :=
  Complex.Gamma (d4BMCausalRadialC omega) * Complex.Gamma (-1 / 2 : ℂ) /
    (Complex.Gamma (d4BMCausalHypergeometricA omega chi) *
      Complex.Gamma (d4BMCausalHypergeometricB omega chi))

/-- Coefficient of the forbidden constant AdS boundary branch in the ingoing BM solution. -/
def d4BMCausalForbiddenBoundaryCoefficient (omega chi : ℂ) : ℂ :=
  Complex.Gamma (d4BMCausalRadialC omega) * Complex.Gamma (1 / 2 : ℂ) /
    (Complex.Gamma (d4BMCausalRadialA omega chi) *
      Complex.Gamma (d4BMCausalRadialB omega chi))

/-- Pole-cancelled response/source ratio of the two BM AdS connection coefficients. -/
def d4BMCausalProjectiveBoundaryResponse (omega chi : ℂ) : ℂ :=
  -2 *
    (Complex.Gamma (d4BMCausalRadialA omega chi) /
      Complex.Gamma (d4BMCausalHypergeometricA omega chi)) *
    (Complex.Gamma (d4BMCausalRadialB omega chi) /
      Complex.Gamma (d4BMCausalHypergeometricB omega chi))

/-- Gamma recurrence at the two boundary exponents. -/
lemma gamma_neg_half_eq_neg_two_mul_gamma_half :
    Complex.Gamma (-1 / 2 : ℂ) = -2 * Complex.Gamma (1 / 2 : ℂ) := by
  have h := Complex.Gamma_add_one (-1 / 2 : ℂ) (by norm_num)
  rw [show (-1 / 2 : ℂ) + 1 = 1 / 2 by ring] at h
  calc
    Complex.Gamma (-1 / 2 : ℂ) =
        -2 * ((-1 / 2 : ℂ) * Complex.Gamma (-1 / 2 : ℂ)) := by ring
    _ = -2 * Complex.Gamma (1 / 2 : ℂ) := by rw [← h]

/-- The decaying coefficient factors as projective response times forbidden coefficient. -/
theorem d4BMCausalDecayingBoundaryCoefficient_eq_projective_mul_forbidden
    (omega chi : ℂ)
    (hA : Complex.Gamma (d4BMCausalRadialA omega chi) ≠ 0)
    (hB : Complex.Gamma (d4BMCausalRadialB omega chi) ≠ 0) :
    d4BMCausalDecayingBoundaryCoefficient omega chi =
      d4BMCausalProjectiveBoundaryResponse omega chi *
        d4BMCausalForbiddenBoundaryCoefficient omega chi := by
  rw [d4BMCausalDecayingBoundaryCoefficient, d4BMCausalProjectiveBoundaryResponse,
    d4BMCausalForbiddenBoundaryCoefficient, gamma_neg_half_eq_neg_two_mul_gamma_half]
  field_simp

/-- First original hypergeometric parameter at the mixed channel. -/
theorem d4BMCausalHypergeometricA_plusMinus (n k : ℕ) (chi : ℂ) :
    d4BMCausalHypergeometricA (d4BMCausalPlusMinusFrequency n k chi) chi =
      -(n : ℂ) - (k : ℂ) - 5 / 4 + Complex.I * chi / 2 := by
  rw [d4BMCausalHypergeometricA, d4BMCausalRadialA_plusMinus]
  ring

/-- Second original hypergeometric parameter at the mixed channel. -/
theorem d4BMCausalHypergeometricB_plusMinus (n k : ℕ) (chi : ℂ) :
    d4BMCausalHypergeometricB (d4BMCausalPlusMinusFrequency n k chi) chi =
      -(n : ℂ) - (k : ℂ) - 5 / 4 - Complex.I * chi / 2 := by
  rw [d4BMCausalHypergeometricB, d4BMCausalRadialB_plusMinus]
  ring

/-- First original hypergeometric parameter at the second harmonic. -/
theorem d4BMCausalHypergeometricA_plusPlus (n : ℕ) (chi : ℂ) :
    d4BMCausalHypergeometricA (d4BMCausalPlusPlusFrequency n chi) chi =
      -2 * (n : ℂ) - 5 / 4 - Complex.I * chi / 2 := by
  rw [d4BMCausalHypergeometricA, d4BMCausalRadialA_plusPlus]
  ring

/-- Second original hypergeometric parameter at the second harmonic. -/
theorem d4BMCausalHypergeometricB_plusPlus (n : ℕ) (chi : ℂ) :
    d4BMCausalHypergeometricB (d4BMCausalPlusPlusFrequency n chi) chi =
      -2 * (n : ℂ) - 5 / 4 - 3 * Complex.I * chi / 2 := by
  rw [d4BMCausalHypergeometricB, d4BMCausalRadialB_plusPlus]
  ring

/-- One chiral Gamma ratio whose norm-square is the physical mixed response. -/
def d4BMMixedProjectiveAmplitude (n k : ℕ) (chi : ℝ) : ℂ :=
  Complex.Gamma (-(n : ℂ) - (k : ℂ) - 3 / 4 + Complex.I * (chi : ℂ) / 2) /
    Complex.Gamma (-(n : ℂ) - (k : ℂ) - 5 / 4 + Complex.I * (chi : ℂ) / 2)

/-- Exact pole-cancelled projective response in the mixed channel. -/
theorem d4BMCausalProjectiveBoundaryResponse_plusMinus
    (n k : ℕ) (chi : ℂ) :
    d4BMCausalProjectiveBoundaryResponse
        (d4BMCausalPlusMinusFrequency n k chi) chi =
      -2 *
        (Complex.Gamma (-(n : ℂ) - (k : ℂ) - 3 / 4 + Complex.I * chi / 2) /
          Complex.Gamma (-(n : ℂ) - (k : ℂ) - 5 / 4 + Complex.I * chi / 2)) *
        (Complex.Gamma (-(n : ℂ) - (k : ℂ) - 3 / 4 - Complex.I * chi / 2) /
          Complex.Gamma (-(n : ℂ) - (k : ℂ) - 5 / 4 - Complex.I * chi / 2)) := by
  rw [d4BMCausalProjectiveBoundaryResponse, d4BMCausalRadialA_plusMinus,
    d4BMCausalRadialB_plusMinus, d4BMCausalHypergeometricA_plusMinus,
    d4BMCausalHypergeometricB_plusMinus]

/-- Exact projective response in the `++` second-harmonic channel. -/
theorem d4BMCausalProjectiveBoundaryResponse_plusPlus
    (n : ℕ) (chi : ℂ) :
    d4BMCausalProjectiveBoundaryResponse
        (d4BMCausalPlusPlusFrequency n chi) chi =
      -2 *
        (Complex.Gamma (-2 * (n : ℂ) - 3 / 4 - Complex.I * chi / 2) /
          Complex.Gamma (-2 * (n : ℂ) - 5 / 4 - Complex.I * chi / 2)) *
        (Complex.Gamma (-2 * (n : ℂ) - 3 / 4 - 3 * Complex.I * chi / 2) /
          Complex.Gamma (-2 * (n : ℂ) - 5 / 4 - 3 * Complex.I * chi / 2)) := by
  rw [d4BMCausalProjectiveBoundaryResponse, d4BMCausalRadialA_plusPlus,
    d4BMCausalRadialB_plusPlus, d4BMCausalHypergeometricA_plusPlus,
    d4BMCausalHypergeometricB_plusPlus]

private lemma d4BMMixedThreeQuarterArg_ne_negNat
    (n k m : ℕ) (chi : ℝ) :
    (-(n : ℂ) - (k : ℂ) - 3 / 4 + Complex.I * (chi : ℂ) / 2) ≠ -(m : ℂ) := by
  intro h
  have hre := congrArg Complex.re h
  norm_num [Complex.div_re, Complex.mul_re] at hre
  have hre4 : (4 : ℝ) * (m : ℝ) = 4 * (n : ℝ) + 4 * (k : ℝ) + 3 := by linarith
  have hnat : 4 * m = 4 * n + 4 * k + 3 := by exact_mod_cast hre4
  omega

private lemma d4BMMixedFiveQuarterArg_ne_negNat
    (n k m : ℕ) (chi : ℝ) :
    (-(n : ℂ) - (k : ℂ) - 5 / 4 + Complex.I * (chi : ℂ) / 2) ≠ -(m : ℂ) := by
  intro h
  have hre := congrArg Complex.re h
  norm_num [Complex.div_re, Complex.mul_re] at hre
  have hre4 : (4 : ℝ) * (m : ℝ) = 4 * (n : ℝ) + 4 * (k : ℝ) + 5 := by linarith
  have hnat : 4 * m = 4 * n + 4 * k + 5 := by exact_mod_cast hre4
  omega

/-- The chiral mixed-channel Gamma ratio never vanishes on the physical momentum line. -/
lemma d4BMMixedProjectiveAmplitude_ne_zero (n k : ℕ) (chi : ℝ) :
    d4BMMixedProjectiveAmplitude n k chi ≠ 0 := by
  apply div_ne_zero
  · apply Complex.Gamma_ne_zero
    intro m
    exact d4BMMixedThreeQuarterArg_ne_negNat n k m chi
  · apply Complex.Gamma_ne_zero
    intro m
    exact d4BMMixedFiveQuarterArg_ne_negNat n k m chi

/-- On the physical momentum line, mixed projective response is minus twice a norm-square. -/
theorem d4BMCausalProjectiveBoundaryResponse_plusMinus_real
    (n k : ℕ) (chi : ℝ) :
    d4BMCausalProjectiveBoundaryResponse
        (d4BMCausalPlusMinusFrequency n k (chi : ℂ)) (chi : ℂ) =
      (-2 : ℂ) * (Complex.normSq (d4BMMixedProjectiveAmplitude n k chi) : ℂ) := by
  rw [d4BMCausalProjectiveBoundaryResponse_plusMinus]
  have hnum :
      Complex.Gamma (-(n : ℂ) - (k : ℂ) - 3 / 4 - Complex.I * (chi : ℂ) / 2) =
        (starRingEnd ℂ)
          (Complex.Gamma (-(n : ℂ) - (k : ℂ) - 3 / 4 + Complex.I * (chi : ℂ) / 2)) := by
    have harg :
        (starRingEnd ℂ)
            (-(n : ℂ) - (k : ℂ) - 3 / 4 + Complex.I * (chi : ℂ) / 2) =
          -(n : ℂ) - (k : ℂ) - 3 / 4 - Complex.I * (chi : ℂ) / 2 := by
      simp only [map_sub, map_neg, map_add, map_mul, map_div₀, map_ofNat,
        Complex.conj_I, Complex.conj_ofReal, Complex.conj_natCast]
      ring
    rw [← harg, Complex.Gamma_conj]
  have hden :
      Complex.Gamma (-(n : ℂ) - (k : ℂ) - 5 / 4 - Complex.I * (chi : ℂ) / 2) =
        (starRingEnd ℂ)
          (Complex.Gamma (-(n : ℂ) - (k : ℂ) - 5 / 4 + Complex.I * (chi : ℂ) / 2)) := by
    have harg :
        (starRingEnd ℂ)
            (-(n : ℂ) - (k : ℂ) - 5 / 4 + Complex.I * (chi : ℂ) / 2) =
          -(n : ℂ) - (k : ℂ) - 5 / 4 - Complex.I * (chi : ℂ) / 2 := by
      simp only [map_sub, map_neg, map_add, map_mul, map_div₀, map_ofNat,
        Complex.conj_I, Complex.conj_ofReal, Complex.conj_natCast]
      ring
    rw [← harg, Complex.Gamma_conj]
  rw [hnum, hden, ← map_div₀]
  unfold d4BMMixedProjectiveAmplitude
  rw [mul_assoc, Complex.mul_conj]

/-- Physical mixed response lies strictly on the negative real ray. -/
theorem d4BMCausalProjectiveBoundaryResponse_plusMinus_re_neg
    (n k : ℕ) (chi : ℝ) :
    (d4BMCausalProjectiveBoundaryResponse
        (d4BMCausalPlusMinusFrequency n k (chi : ℂ)) (chi : ℂ)).re < 0 := by
  rw [d4BMCausalProjectiveBoundaryResponse_plusMinus_real]
  norm_num [Complex.mul_re, Complex.normSq_pos]
  exact d4BMMixedProjectiveAmplitude_ne_zero n k chi

/-- Physical mixed response has no orthogonal phase component. -/
theorem d4BMCausalProjectiveBoundaryResponse_plusMinus_im_eq_zero
    (n k : ℕ) (chi : ℝ) :
    (d4BMCausalProjectiveBoundaryResponse
        (d4BMCausalPlusMinusFrequency n k (chi : ℂ)) (chi : ℂ)).im = 0 := by
  rw [d4BMCausalProjectiveBoundaryResponse_plusMinus_real]
  norm_num [Complex.mul_im]

/-- Hawking--Matsubara resonance does not annihilate the physical mixed response. -/
theorem d4BMCausalProjectiveBoundaryResponse_plusMinus_ne_zero
    (n k : ℕ) (chi : ℝ) :
    d4BMCausalProjectiveBoundaryResponse
        (d4BMCausalPlusMinusFrequency n k (chi : ℂ)) (chi : ℂ) ≠ 0 := by
  intro h
  have hre :
      (d4BMCausalProjectiveBoundaryResponse
        (d4BMCausalPlusMinusFrequency n k (chi : ℂ)) (chi : ℂ)).re = 0 := by
    rw [h]
    rfl
  linarith [d4BMCausalProjectiveBoundaryResponse_plusMinus_re_neg n k chi]

end

end RHTower
