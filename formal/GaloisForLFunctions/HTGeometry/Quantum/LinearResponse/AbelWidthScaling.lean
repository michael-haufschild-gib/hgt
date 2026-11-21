import GaloisForLFunctions.HTGeometry.Quantum.LinearResponse.AbelProbeRecovery

/-!
# The scale ambiguity of zero-centered measurements

Changing the width and scaling the Hamiltonian by the same ratio
leaves the entire zero-centered response unchanged. Comparing two
experiments at a common width reduces their ambiguity to an energy shift.
-/

open Matrix Set
open scoped Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Express a Hamiltonian at a new damping width while keeping the
dimensionless Hamiltonian fixed. -/
def abelHamiltonianAtWidth (H : Matrix ι ι ℂ) (ε η : Ioi (0 : ℝ)) : Matrix ι ι ℂ :=
  (((η : ℝ) / (ε : ℝ) : ℝ) : ℂ) • H

omit [Fintype ι] [DecidableEq ι] in
theorem abelHamiltonianAtWidth_isHermitian {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (ε η : Ioi (0 : ℝ)) : (abelHamiltonianAtWidth H ε η).IsHermitian := by
  show (abelHamiltonianAtWidth H ε η)ᴴ = abelHamiltonianAtWidth H ε η
  rw [abelHamiltonianAtWidth, Matrix.conjTranspose_smul, Complex.star_def,
    Complex.conj_ofReal, show Hᴴ = H from hH]

private theorem abelShift_inv_mul_widthRatio (ε η : Ioi (0 : ℝ)) :
    (hamiltonianAbelShift η)⁻¹ * (((η : ℝ) / (ε : ℝ) : ℝ) : ℂ) =
      (hamiltonianAbelShift ε)⁻¹ := by
  let r : ℂ := (((η : ℝ) / (ε : ℝ) : ℝ) : ℂ)
  have hz : r * hamiltonianAbelShift ε = hamiltonianAbelShift η := by
    apply Complex.ext
    · simp only [r, hamiltonianAbelShift, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, zero_mul, sub_self]
    · simp only [r, hamiltonianAbelShift, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero]
      exact div_mul_cancel₀ _ ε.2.ne'
  change (hamiltonianAbelShift η)⁻¹ * r = _
  calc
    _ = (hamiltonianAbelShift η)⁻¹ * ((r * hamiltonianAbelShift ε) * (hamiltonianAbelShift ε)⁻¹) := by
      rw [mul_assoc r, mul_inv_cancel₀ (hamiltonianAbelShift_ne_zero ε), mul_one]
    _ = _ := by rw [hz, ← mul_assoc, inv_mul_cancel₀ (hamiltonianAbelShift_ne_zero η), one_mul]

omit [DecidableEq ι] in
theorem abelInverse_rescale_width (H Y : Matrix ι ι ℂ) (ε η : Ioi (0 : ℝ)) :
    hamiltonianAbelInverse (abelHamiltonianAtWidth H ε η) η Y = hamiltonianAbelInverse H ε Y := by
  simp only [hamiltonianAbelInverse_eq_sub, abelHamiltonianAtWidth, Matrix.smul_mul,
    Matrix.mul_smul, ← smul_sub, smul_smul, abelShift_inv_mul_widthRatio]

/-- The full zero-centered channel has no independent measurement of width. -/
theorem abelResponse_rescale_width {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (ε η : Ioi (0 : ℝ)) :
    hamiltonianDampedGapResponse (abelHamiltonianAtWidth_isHermitian hH ε η) 0 η =
      hamiltonianDampedGapResponse hH 0 ε := by
  let hR := abelHamiltonianAtWidth_isHermitian hH ε η
  funext X
  apply (dampedGapResponse_zero_eq_iff_abelInverse_eq hR η X _).mpr
  rw [abelInverse_rescale_width]
  exact hamiltonianAbelInverse_leftInverse hH ε X

omit [Fintype ι] in
/-- A scalar difference of Hermitian matrices is a real energy shift. -/
theorem hermitian_scalarDifference_iff_real (o : ι) {H K : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hK : K.IsHermitian) :
    (∃ c : ℂ, H - K = c • 1) ↔ ∃ r : ℝ, H - K = (r : ℂ) • 1 := by
  constructor
  · rintro ⟨c, hc⟩
    have he : (c • (1 : Matrix ι ι ℂ))ᴴ = c • 1 := hc ▸ (hH.sub hK)
    have heo := congrArg (fun M : Matrix ι ι ℂ => M o o) he
    simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
      mul_one, Complex.star_def] at heo
    have hi := congrArg Complex.im heo
    rw [Complex.conj_im] at hi
    have him : c.im = 0 := by linarith only [hi]
    have hr : (c.re : ℂ) = c := Complex.ext (Complex.ofReal_re _) (by rw [Complex.ofReal_im, him])
    exact ⟨c.re, by rw [hr]; exact hc⟩
  · rintro ⟨r, hr⟩
    exact ⟨r, hr⟩

/-- Comparing channels with unknown positive widths recovers the
Hamiltonians at a common width up to a real scalar shift. -/
theorem abelResponse_eq_iff_rescale_sub_scalar {d : ℕ} (o : Fin d)
    {H K : Matrix (Fin d) (Fin d) ℂ} (hH : H.IsHermitian) (hK : K.IsHermitian)
    (ε η : Ioi (0 : ℝ)) :
    hamiltonianDampedGapResponse hH 0 ε = hamiltonianDampedGapResponse hK 0 η ↔
      ∃ r : ℝ, H - abelHamiltonianAtWidth K η ε = (r : ℂ) • 1 := by
  rw [← abelResponse_rescale_width hK η ε]
  exact (hamiltonianDampedGapResponse_zero_eq_iff_scalarDifference
    o hH (abelHamiltonianAtWidth_isHermitian hK η ε) ε).trans
    (hermitian_scalarDifference_iff_real o hH (abelHamiltonianAtWidth_isHermitian hK η ε))

#print axioms abelResponse_rescale_width
#print axioms abelResponse_eq_iff_rescale_sub_scalar

end

end GaloisForLFunctions.HTGeometry
