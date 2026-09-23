import GaloisForLFunctions.HTGeometry.Octonion.Coordinate
import GaloisForLFunctions.HTGeometry.Octonion.Sylvester

namespace GaloisForLFunctions.HTGeometry.Octonion.RealOctonion

noncomputable section

/-- The real dimension of the concrete Cayley octonions. -/
theorem finrank_realOctonion : Module.finrank ℝ RealOctonion = 8 := by
  rw [Module.finrank_eq_card_basis standardBasis, Fintype.card_fin]

/-- When both parameters are real, `R_s - L_q` is scalar multiplication by `s - q`. -/
theorem sylvesterDifferenceLinear_scalarEmbed (r t : ℝ) :
    sylvesterDifferenceLinear (scalarEmbed r) (scalarEmbed t) =
      (r - t) • LinearMap.id := by
  apply LinearMap.ext
  intro x
  change x * scalarEmbed r - scalarEmbed t * x = (r - t) • x
  rw [mul_scalarEmbed, scalarEmbed_mul, sub_smul]

/-- The exact determinant specialization of Lemma 8.5 for two real octonions. -/
theorem sylvesterDifferenceLinear_det_scalarEmbed (r t : ℝ) :
    LinearMap.det (sylvesterDifferenceLinear (scalarEmbed r) (scalarEmbed t)) = (r - t) ^ (8 : ℕ) := by
  rw [sylvesterDifferenceLinear_scalarEmbed, LinearMap.det_smul,
    finrank_realOctonion, LinearMap.det_id]
  simp

end
end GaloisForLFunctions.HTGeometry.Octonion.RealOctonion
