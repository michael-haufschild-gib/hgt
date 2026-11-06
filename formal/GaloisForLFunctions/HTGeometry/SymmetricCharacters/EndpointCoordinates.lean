import GaloisForLFunctions.Core

/-!
# Endpoint coordinates and the loss under real projection

The reciprocal endpoint coordinate is real precisely on the real axis or the critical line.
Its real part is positive throughout the open critical strip. Projecting a complex alphabet to
its real parts increases the second power sum by the squared imaginary parts.
-/

noncomputable section
open scoped BigOperators

namespace GaloisForLFunctions.SymmetricCharacters

/-- The reciprocal coordinate associated with the endpoints zero and one. -/
def endpointCoordinate (z : ℂ) : ℂ := (z * (1 - z))⁻¹

theorem endpointCoordinate_im (z : ℂ) :
    (endpointCoordinate z).im =
      (2 * z.re - 1) * z.im / Complex.normSq (z * (1 - z)) := by
  simp only [endpointCoordinate, Complex.inv_im, Complex.mul_im, Complex.sub_im,
    Complex.one_im, Complex.sub_re, Complex.one_re]
  ring

/-- The two real loci of the endpoint map include its singular endpoints. -/
theorem endpointCoordinate_im_eq_zero_iff (z : ℂ) :
    (endpointCoordinate z).im = 0 ↔ z.re = 1 / 2 ∨ z.im = 0 := by
  by_cases hz : z * (1 - z) = 0
  · rcases mul_eq_zero.mp hz with h | h
    · subst z
      simp [endpointCoordinate]
    · have : z = 1 := (sub_eq_zero.mp h).symm
      subst z
      simp [endpointCoordinate]
  · have hd : Complex.normSq (z * (1 - z)) ≠ 0 :=
      (Complex.normSq_pos.mpr hz).ne'
    rw [endpointCoordinate_im, div_eq_zero_iff, or_iff_left hd, mul_eq_zero]
    have hlin : 2 * z.re - 1 = 0 ↔ z.re = 1 / 2 := by
      constructor <;> intro h <;> linarith
    rw [hlin]

/-- Positive real charge does not distinguish the critical line within the open strip. -/
theorem endpointCoordinate_re_pos {z : ℂ} (h0 : 0 < z.re) (h1 : z.re < 1) :
    0 < (endpointCoordinate z).re := by
  have hr : 0 < (z * (1 - z)).re := by
    simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.sub_im,
      Complex.one_im]
    have hp := mul_pos h0 (sub_pos.mpr h1)
    nlinarith only [hp, sq_nonneg z.im]
  have hz : z * (1 - z) ≠ 0 := fun h => by simp [h] at hr
  rw [endpointCoordinate, Complex.inv_re]
  exact div_pos hr (Complex.normSq_pos.mpr hz)

/-- The first nontrivial cycle-value error of real projection. -/
theorem real_projection_secondMoment_gap {I : Type*} [Fintype I] (z : I → ℂ) :
    (∑ i, (z i).re ^ 2) - (∑ i, z i ^ 2).re = ∑ i, (z i).im ^ 2 := by
  rw [Complex.re_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [pow_two, Complex.mul_re]
  ring

/-- Conjugation symmetry makes the error real; it does not make it vanish. -/
theorem conjugatePair_secondMoment_gap (z : ℂ) :
    2 * z.re ^ 2 - (z ^ 2 + (starRingEnd ℂ z) ^ 2).re = 2 * z.im ^ 2 := by
  simp only [Complex.add_re, pow_two, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

end GaloisForLFunctions.SymmetricCharacters
