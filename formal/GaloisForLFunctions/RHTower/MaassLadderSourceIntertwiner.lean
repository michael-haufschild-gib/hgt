import GaloisForLFunctions.RHTower.MaassSourceModelIntertwiner
import GaloisForLFunctions.RHTower.MaassLadderQuotientL2

/-!
# The zero automorphic ladder vector in the completed Maass model

The zero-weight vector of the literal differentiated automorphic ladder is the
same quotient function and quotient-`L²` vector as the original Maass source.
Consequently the completed complementary-model source vector intertwines its
full real `SL(2, ℝ)` orbit with the orbit of that literal zero ladder vector.
This is a real-place identification; it creates neither finite-place factors
nor a global automorphic lift.
-/

open UpperHalfPlane MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.RHTower

open MaassSmooth MaassCircle

noncomputable section

/-- At weight zero, inversion of the literal raised automorphic vector is exactly the
original Maass quotient function. -/
theorem raisedFunction_zero_eq_sourceFunction (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) :
    MaassLadderQuotientL2.raisedFunction N f 0 = MaassQuotientL2.sourceFunction N f := by
  funext q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  simp [MaassLadderQuotientL2.raisedFunction, MaassQuotientL2.sourceFunction,
    MaassSmooth.raisedAutomorphic, automorphicQuotientLift,
    maassInvariantQuotientLift, MaassSmooth.raised, MaassSmooth.ofMaass, weightLift]

/-- The zero raised automorphic ladder vector is the original Maass vector in quotient `L²`. -/
theorem raisedLp_zero_eq_sourceLp (N : ℕ) {lam : ℝ}
    (hlam : 0 < lam)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) :
    MaassLadderQuotientL2.raisedLp N hlam f 0 = MaassQuotientL2.sourceLp N f := by
  apply Lp.ext
  filter_upwards [MaassLadderQuotientL2.raisedLp_ae N hlam f 0,
    MaassQuotientL2.sourceLp_ae N f] with q hraised hsource
  rw [hraised, hsource, raisedFunction_zero_eq_sourceFunction]

/-- The canonical completed-model source vector maps to the zero raised automorphic ladder
vector in quotient `L²`. -/
theorem completedModelIsometry_maassSourceModelVector_eq_raisedLp_zero
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1) :
    MaassModelQuotientL2.completedModelIsometry N lam f (maassSourceModelVector N lam f) =
      MaassLadderQuotientL2.raisedLp N lam.2.1 f 0 := by
  rw [completedModelIsometry_maassSourceModelVector, raisedLp_zero_eq_sourceLp]

/-- The completed complementary representation sends its canonical source vector to the
literal quotient-`L²` orbit of the zero raised automorphic ladder vector. -/
theorem maassSourceModelVector_orbit_intertwines_raisedLp_zero
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (g : SL2R) :
    MaassModelQuotientL2.completedModelIsometry N lam f
      (completedComplementaryModelRepresentation N lam f g
        (maassSourceModelVector N lam f)) =
      integralSubgroupUnitary (CongruenceSubgroup.Gamma (N + 1)) g
        (MaassLadderQuotientL2.raisedLp N lam.2.1 f 0) := by
  rw [maassSourceModelVector_orbit_intertwines, raisedLp_zero_eq_sourceLp]

end

end GaloisForLFunctions.RHTower
