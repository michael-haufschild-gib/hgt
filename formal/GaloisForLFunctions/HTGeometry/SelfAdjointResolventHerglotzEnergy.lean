import GaloisForLFunctions.HTGeometry.ResolventCompactness

/-!
# Exact Herglotz energy of an unbounded self-adjoint resolvent

For an actual (possibly unbounded) self-adjoint partial linear map, the normalized resolvent
readout has an exact positive imaginary part.  This is an operator-domain identity: it does not
introduce a spectral model, a compactness premise, or a bounded-operator surrogate.
-/

open Complex
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Normalized scalar resolvent readout of a self-adjoint partial linear map. -/
def resolventHerglotzEnergy {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) {z : ℂ}
    (hz : z.im ≠ 0) (v : H) : ℂ :=
  z * inner ℂ v v + (z ^ 2 + 1) * inner ℂ v (resolventLinear hA hz v)

/-- The normalized scalar resolvent readout has exact graph-energy imaginary part. -/
theorem resolventHerglotzEnergy_im_eq_graphEnergy {A : H →ₗ.[ℂ] H}
    (hA : IsSelfAdjoint A) {z : ℂ} (hz : z.im ≠ 0) (v : H) :
    (resolventHerglotzEnergy hA hz v).im =
      z.im *
        (‖A ⟨resolventLinear hA hz v, resolventLinear_mem hA hz v⟩‖ ^ 2 +
          ‖resolventLinear hA hz v‖ ^ 2) := by
  let r : H := resolventLinear hA hz v
  let rd : A.domain := ⟨r, resolventLinear_mem hA hz v⟩
  have hshift : A rd - z • r = v := by
    simp only [r, rd]
    exact shiftedMap_resolventLinear hA hz v
  have hdiag : (inner ℂ (A rd) r).im = 0 :=
    inner_selfAdjoint_self_im hA rd
  have hcross : inner ℂ r (A rd) = inner ℂ (A rd) r := by
    have hconj : (starRingEnd ℂ) (inner ℂ (A rd) r) = inner ℂ (A rd) r :=
      Complex.conj_eq_iff_im.2 hdiag
    rwa [inner_conj_symm] at hconj
  have hselfr : inner ℂ r r = (‖r‖ ^ 2 : ℂ) := by
    simp only [inner_self_eq_norm_sq_to_K]
    rfl
  have hselfA : inner ℂ (A rd) (A rd) = (‖A rd‖ ^ 2 : ℂ) := by
    simp only [inner_self_eq_norm_sq_to_K]
    rfl
  have hnormr_re : ((‖r‖ : ℂ) ^ 2).re = ‖r‖ ^ 2 := by
    rw [pow_two, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hnormr_im : ((‖r‖ : ℂ) ^ 2).im = 0 := by
    rw [pow_two, Complex.mul_im]
    simp
  have hnormA_re : ((‖A rd‖ : ℂ) ^ 2).re = ‖A rd‖ ^ 2 := by
    rw [pow_two, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hnormA_im : ((‖A rd‖ : ℂ) ^ 2).im = 0 := by
    rw [pow_two, Complex.mul_im]
    simp
  have hsq_re : (z ^ 2).re = z.re ^ 2 - z.im ^ 2 := by
    simp [pow_two, Complex.mul_re]
  have hsq_im : (z ^ 2).im = 2 * z.re * z.im := by
    simp [pow_two, Complex.mul_im]
    ring
  change (z * inner ℂ v v + (z ^ 2 + 1) * inner ℂ v r).im =
    z.im * (‖A rd‖ ^ 2 + ‖r‖ ^ 2)
  rw [← hshift]
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    hcross, hselfr, hselfA]
  rw [show (starRingEnd ℂ) z = star z from rfl]
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re,
    Complex.conj_im, Complex.one_re, Complex.one_im]
  rw [hdiag, hnormr_re, hnormr_im, hnormA_re, hnormA_im, hsq_re, hsq_im]
  ring

/-- In the upper half plane, a nonzero source has strictly positive resolvent graph energy. -/
theorem resolventHerglotzEnergy_im_pos {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    {z : ℂ} (hz : 0 < z.im) {v : H} (hv : v ≠ 0) :
    0 < (resolventHerglotzEnergy hA (ne_of_gt hz) v).im := by
  rw [resolventHerglotzEnergy_im_eq_graphEnergy]
  apply mul_pos hz
  have hr : resolventLinear hA (ne_of_gt hz) v ≠ 0 := by
    intro hr
    apply hv
    calc
      v = A ⟨resolventLinear hA (ne_of_gt hz) v,
          resolventLinear_mem hA (ne_of_gt hz) v⟩ -
          z • resolventLinear hA (ne_of_gt hz) v :=
        (shiftedMap_resolventLinear hA (ne_of_gt hz) v).symm
      _ = 0 := by
        simp only [hr, smul_zero, sub_zero]
        change A (0 : A.domain) = 0
        exact A.map_zero
  have hrpos : 0 < ‖resolventLinear hA (ne_of_gt hz) v‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr hr)
  exact add_pos_of_nonneg_of_pos (sq_nonneg _) hrpos

end GaloisForLFunctions.HTGeometry
