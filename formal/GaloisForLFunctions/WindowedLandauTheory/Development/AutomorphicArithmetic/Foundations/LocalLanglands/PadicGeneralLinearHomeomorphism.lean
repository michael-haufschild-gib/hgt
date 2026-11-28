import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.PadicCongruenceTransport
import Mathlib.Topology.Algebra.Group.OpenMapping

/-! A continuous p-adic chart is open by the additive open
mapping theorem. The induced chart on general linear groups
is a homeomorphism. -/

noncomputable section

open Matrix NumberField IsDedekindDomain

namespace GlobalTheory.GLp

variable {F : Type} [Field F] [NumberField F] {p : ℕ} [Fact p.Prime]
  {n : Type*} [Fintype n] [DecidableEq n]
  (v : HeightOneSpectrum (𝓞 F)) (i : ℚ_[p] ≃+* v.adicCompletion F) (hi : Continuous i)

include hi in
theorem isOpenMap_generalLinear_padicChart :
    IsOpenMap (GeneralLinearGroup.map (n := n) i.toRingHom) := by
  obtain ⟨w, rfl⟩ := (FinitePlace.equivHeightOneSpectrum (K := F)).surjective v
  have ho : IsOpenMap i := AddMonoidHom.isOpenMap_of_sigmaCompact
    i.toAddEquiv.toAddMonoidHom i.surjective hi
  have hi' : Continuous i.symm := (i.toEquiv.toHomeomorphOfContinuousOpen hi ho).symm.continuous
  let j : GL n ℚ_[p] ≃ₜ GL n (w.maximalIdeal.adicCompletion F) :=
    { toFun := GeneralLinearGroup.map i.toRingHom
      invFun := GeneralLinearGroup.map i.symm.toRingHom
      left_inv := fun g => Units.ext (Matrix.ext fun a b => i.symm_apply_apply (g.val a b))
      right_inv := fun g => Units.ext (Matrix.ext fun a b => i.apply_symm_apply (g.val a b))
      continuous_toFun := Units.continuous_map (continuous_id.matrix_map hi)
      continuous_invFun := Units.continuous_map (continuous_id.matrix_map hi') }
  exact j.isOpenMap

end GlobalTheory.GLp

#print axioms GlobalTheory.GLp.isOpenMap_generalLinear_padicChart
