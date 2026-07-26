import GaloisForLFunctions.RHTower.DeningerArithmeticGlobalJetInterpolation
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Compact-open arithmetic cohomology is the full Xi-jet product

The descended all-jets observation is a topological embedding by local quotient openness and is
surjective by constructive global Xi-jet interpolation.  It is therefore a homeomorphism from
compact-open middle cohomology onto the full product of local multiplicity-bounded jets.
-/

open Filter Set Topology

namespace RHTower

noncomputable section

/-- The all-jets observation is a homeomorphism onto the full jet product. -/
theorem isHomeomorph_deningerCompactOpenH1AllJets :
    IsHomeomorph
      (deningerCompactOpenH1AllJets :
        DeningerArithmeticCompactOpenH1 →
          DeningerArithmeticJetProduct) :=
  isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨isEmbedding_deningerCompactOpenH1AllJets,
      deningerCompactOpenH1AllJets_surjective⟩

/-- Canonical topological equivalence between compact-open middle cohomology and all local jets. -/
def deningerCompactOpenH1JetHomeomorph :
    DeningerArithmeticCompactOpenH1 ≃ₜ
      DeningerArithmeticJetProduct :=
  isHomeomorph_deningerCompactOpenH1AllJets.homeomorph
    deningerCompactOpenH1AllJets

@[simp]
theorem deningerCompactOpenH1JetHomeomorph_apply
    (x : DeningerArithmeticCompactOpenH1) :
    deningerCompactOpenH1JetHomeomorph x =
      deningerCompactOpenH1AllJets x :=
  rfl

end

end RHTower
