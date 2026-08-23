/-
Reflected reciprocal-Gamma carrier for transverse divisor relocation.

The centered entire carrier
`1 / (Gamma(beta + i z) * Gamma(beta - i z))` has two explicit
critical-axis zero lattices.  It supplies the common Gamma divisor used by
the Cosh-quartet relocation witness.
-/
import GaloisForLFunctions.HTGeometry.MeromorphicGammaNatScale

open Complex
open GaloisForLFunctions

namespace RHTower

noncomputable section

/-- Centered reflected reciprocal-Gamma carrier. -/
def reflectedGammaCarrier (beta : ℝ) (z : ℂ) : ℂ :=
  reciprocalGammaEntire ((beta : ℂ) + I * z) *
    reciprocalGammaEntire ((beta : ℂ) - I * z)

/-- The reflected Gamma carrier is entire. -/
theorem reflectedGammaCarrier_analyticOnNhd (beta : ℝ) :
    AnalyticOnNhd ℂ (reflectedGammaCarrier beta) Set.univ := by
  rw [Complex.analyticOnNhd_univ_iff_differentiable]
  apply Differentiable.mul
  · exact contDiff_reciprocalGammaEntire.differentiable (by simp) |>.comp (by fun_prop)
  · exact contDiff_reciprocalGammaEntire.differentiable (by simp) |>.comp (by fun_prop)

/-- Exact zero lattice of the reflected reciprocal-Gamma carrier. -/
theorem reflectedGammaCarrier_eq_zero_iff {beta : ℝ} {z : ℂ} :
    reflectedGammaCarrier beta z = 0 ↔
      (∃ n : ℕ, z = I * ((n : ℂ) + (beta : ℂ))) ∨
        ∃ n : ℕ, z = -I * ((n : ℂ) + (beta : ℂ)) := by
  unfold reflectedGammaCarrier reciprocalGammaEntire
  rw [mul_eq_zero, inv_eq_zero, inv_eq_zero, Complex.Gamma_eq_zero_iff,
    Complex.Gamma_eq_zero_iff]
  constructor
  · rintro (⟨n, hn⟩ | ⟨n, hn⟩)
    · left
      refine ⟨n, ?_⟩
      have harg : I * z = -(n : ℂ) - (beta : ℂ) := by
        calc
          I * z = ((beta : ℂ) + I * z) - (beta : ℂ) := by ring
          _ = -(n : ℂ) - (beta : ℂ) := by rw [hn]
      calc
        z = -I * (I * z) := by
          rw [neg_mul, ← mul_assoc, Complex.I_mul_I]
          ring
        _ = -I * (-(n : ℂ) - (beta : ℂ)) := by rw [harg]
        _ = I * ((n : ℂ) + (beta : ℂ)) := by ring
    · right
      refine ⟨n, ?_⟩
      have harg : I * z = (beta : ℂ) + (n : ℂ) := by
        calc
          I * z = (beta : ℂ) - ((beta : ℂ) - I * z) := by ring
          _ = (beta : ℂ) - -(n : ℂ) := by rw [hn]
          _ = (beta : ℂ) + (n : ℂ) := by ring
      calc
        z = -I * (I * z) := by
          rw [neg_mul, ← mul_assoc, Complex.I_mul_I]
          ring
        _ = -I * ((beta : ℂ) + (n : ℂ)) := by rw [harg]
        _ = -I * ((n : ℂ) + (beta : ℂ)) := by ring
  · rintro (⟨n, hn⟩ | ⟨n, hn⟩)
    · left
      refine ⟨n, ?_⟩
      rw [hn]
      rw [← mul_assoc, Complex.I_mul_I]
      ring
    · right
      refine ⟨n, ?_⟩
      rw [hn]
      rw [neg_mul, mul_neg, sub_neg_eq_add, ← mul_assoc, Complex.I_mul_I]
      ring

/-- Every zero of the reflected Gamma carrier lies on its central vertical line. -/
theorem reflectedGammaCarrier_zero_re_eq_zero
    {beta : ℝ} {z : ℂ} (hz : reflectedGammaCarrier beta z = 0) :
    z.re = 0 := by
  rcases reflectedGammaCarrier_eq_zero_iff.mp hz with ⟨n, hn⟩ | ⟨n, hn⟩
  · rw [hn]
    simp
  · rw [hn]
    simp

/-- The reflected Gamma carrier is even in the centered coordinate. -/
theorem reflectedGammaCarrier_neg (beta : ℝ) (z : ℂ) :
    reflectedGammaCarrier beta (-z) = reflectedGammaCarrier beta z := by
  unfold reflectedGammaCarrier
  ring

/-- The reflected Gamma carrier is Schwarz-real for real `beta`. -/
theorem reflectedGammaCarrier_conj (beta : ℝ) (z : ℂ) :
    reflectedGammaCarrier beta (starRingEnd ℂ z) =
      starRingEnd ℂ (reflectedGammaCarrier beta z) := by
  unfold reflectedGammaCarrier reciprocalGammaEntire
  rw [map_mul, map_inv₀, map_inv₀]
  have hplus : Complex.Gamma ((beta : ℂ) + I * (starRingEnd ℂ z)) =
      (starRingEnd ℂ) (Complex.Gamma ((beta : ℂ) - I * z)) := by
    rw [← Complex.Gamma_conj]
    congr 1
    simp only [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I, neg_mul]
    ring
  have hminus : Complex.Gamma ((beta : ℂ) - I * (starRingEnd ℂ z)) =
      (starRingEnd ℂ) (Complex.Gamma ((beta : ℂ) + I * z)) := by
    rw [← Complex.Gamma_conj]
    congr 1
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, neg_mul]
    ring
  rw [hplus, hminus]
  ring

end

end RHTower
