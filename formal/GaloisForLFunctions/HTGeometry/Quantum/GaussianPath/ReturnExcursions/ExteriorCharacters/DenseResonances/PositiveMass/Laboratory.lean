import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ExteriorCharacters.ElapsedWindow.Laboratory
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ExteriorCharacters.DenseResonances.PositiveMass.Band

/-! # The physical midpoint phases of a fixed laboratory circuit -/

open Matrix Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters.DenseResonances.PositiveMass
open ElapsedWindow AngularWindings.PhysicalTubes
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
private abbrev Mat (I : Type*) := Matrix I I ℂ

/-- Minor amplitude at a fixed midpoint, with the actual circuit and
the full sum of the selected physical energies. -/
def midpointMinor (H : selfAdjoint (Mat I)) (W : unitary (Mat I)) (t : ℝ) (S : Finset I) : ℂ :=
  circuitMinor H W S*wave (-t*∑ i ∈ S, H.2.isHermitian.eigenvalues i)

omit [Nonempty I] in
theorem midpoint_norm (H : selfAdjoint (Mat I)) (W : unitary (Mat I)) (t : ℝ) (S : Finset I) :
    ‖midpointMinor H W t S‖=‖circuitMinor H W S‖ := by
  rw [midpointMinor,norm_mul,wave,Complex.norm_exp_ofReal_mul_I,mul_one]

/-- A fit at any date forces the same total absolute weight at every
midpoint, irrespective of its displacement from the fitting date. -/
theorem laboratory_weight (H : selfAdjoint (Mat I)) (W : unitary (Mat I)) {v : ℝ}
    (hv : v∈laboratoryDates H W (1/10)) (t : ℝ) (q : ℕ) (hq : q≤Fintype.card I) :
    ((Fintype.card I).choose q:ℝ)*(199/200)^min q (Fintype.card I-q) ≤
      ∑ S ∈ (univ : Finset I).powersetCard q, ‖midpointMinor H W t S‖ := by
  let V := H.2.isHermitian.eigenvectorUnitary
  let p (i : I) := wave (-v*H.2.isHermitian.eigenvalues i)
  have hp (i : I) : ‖p i‖=1 := Complex.norm_exp_ofReal_mul_I _
  have hh := laboratory_fit H W hv (by norm_num) q hq
  change _≤‖subsetCharacter (star (V⁻¹*W*V).val) p q‖ at hh
  rw [show (1:ℝ)-(1/10)^2/2=199/200 by norm_num] at hh
  apply hh.trans (le_trans (norm_sum_le ..) _)
  apply sum_le_sum
  intro S _
  rw [norm_mul,norm_prod]
  simp only [hp,prod_const_one,mul_one,midpoint_norm]
  exact le_rfl

#print axioms laboratory_weight
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters.DenseResonances.PositiveMass
