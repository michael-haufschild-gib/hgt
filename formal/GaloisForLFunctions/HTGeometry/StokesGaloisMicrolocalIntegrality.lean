import GaloisForLFunctions.HTGeometry.StokesCellularMicrolocalSheaf
import GaloisForLFunctions.HTGeometry.StokesPairPuiseuxSourceLaw

/-!
# Galois integrality of microlocal Stokes masses

Every actual cyclic sheet-loss layer is expanded into the directed rank-one microstalks of its
exponential difference.  The full diagonal and mixed sheet masses are therefore literal integer
Morse multiplicities.  Translation invariance and common-kernel cardinalities make their normalized
values integral and recover the diagonal irregularity, mixed Hom coarea, loops, and signed edges.
-/

open scoped BigOperators

namespace GaloisForLFunctions
namespace IrregularStokes

noncomputable section

open CellularMicrolocal

/-- Directed rank-one Morse multiplicity of an ordered exponential difference of degree `k`. -/
def directedRankOneMass (k : ℕ) : ℕ :=
  ∑ wall : Fin k, microRank 1 (decayWall k wall) (activeConormalSide (decayWall k wall))

@[simp] theorem directedRankOneMass_eq (k : ℕ) : directedRankOneMass k = k := by
  simpa [directedRankOneMass] using directedDecayMicroRank_sum k 1

/-- Integer microlocal mass over all ordered pairs of actual sheets of one cyclic orbit. -/
noncomputable def Characteristic.orderedPairMicrolocalMass {R beta : ℕ}
    (c : Characteristic R beta) : ℕ := by
  letI : NeZero R := ⟨Nat.ne_of_gt (Nat.zero_lt_one.trans c.ramification_gt_one)⟩
  exact ∑ a : ZMod R, ∑ b : ZMod R,
    directedRankOneMass (c.canonicalPuiseux.pairDifferenceNumerator a b)

/-- Cellular Morse expansion equals the ordered leading-numerator mass. -/
theorem Characteristic.orderedPairMicrolocalMass_eq_numeratorSum {R beta : ℕ}
    (c : Characteristic R beta) :
    c.orderedPairMicrolocalMass = c.orderedPairDifferenceNumeratorSum := by
  have hR : 0 < R := Nat.zero_lt_one.trans c.ramification_gt_one
  letI : NeZero R := ⟨Nat.ne_of_gt hR⟩
  simp [Characteristic.orderedPairMicrolocalMass,
    Characteristic.orderedPairDifferenceNumeratorSum]

/-- Diagonal cyclic normalization is integral and equals characteristic irregularity. -/
theorem Characteristic.normalizedMicrolocalMass_eq_irregularity {R beta : ℕ}
    (c : Characteristic R beta) :
    c.orderedPairMicrolocalMass / R = c.weightedIrregularity := by
  rw [c.orderedPairMicrolocalMass_eq_numeratorSum]
  exact c.endomorphismIrregularityFromSheets_eq

/-- Mixed microlocal mass, layer by layer, on two cyclic sheet torsors. -/
noncomputable def commonPairMicrolocalMass {R S : ℕ} (D : ℕ)
    (hDR : D ∣ R) (hDS : D ∣ S) :
    List (ReducedCommonExponent R S) → ℕ → ℕ
  | [], fissionNumerator =>
      Nat.card (commonDifferenceHom hDR hDS).ker * directedRankOneMass fissionNumerator
  | k :: rest, fissionNumerator =>
      Nat.card (CommonPairLayer D hDR hDS k) * directedRankOneMass k.leftNumerator +
        commonPairMicrolocalMass (Nat.lcm D k.denominator)
          (Nat.lcm_dvd hDR k.denominator_dvd_left)
          (Nat.lcm_dvd hDS k.denominator_dvd_right) rest fissionNumerator

/-- Layerwise cellular Morse mass equals actual ordered-pair numerator mass. -/
theorem commonPairMicrolocalMass_eq_numeratorMass {R S D : ℕ}
    (hDR : D ∣ R) (hDS : D ∣ S)
    (levels : List (ReducedCommonExponent R S)) (fissionNumerator : ℕ) :
    commonPairMicrolocalMass D hDR hDS levels fissionNumerator =
      commonPairNumeratorMass D hDR hDS levels fissionNumerator := by
  induction levels generalizing D with
  | nil => simp [commonPairMicrolocalMass, commonPairNumeratorMass, Nat.mul_comm]
  | cons k rest ih =>
      rw [commonPairMicrolocalMass, commonPairNumeratorMass, directedRankOneMass_eq,
        ih (Nat.lcm_dvd hDR k.denominator_dvd_left)
          (Nat.lcm_dvd hDS k.denominator_dvd_right)]
      ring

/-- **Mixed Galois microlocal integrality.** After cyclic normalization, integer microstalk mass
is exactly mixed Hom coarea. -/
theorem normalizedCommonPairMicrolocalMass_eq_coarea {R S D : ℕ}
    (hR : 0 < R) (hS : 0 < S) (hD : 0 < D) (hDR : D ∣ R) (hDS : D ∣ S)
    (levels : List (ReducedCommonExponent R S)) (fissionNumerator : ℕ) :
    commonPairMicrolocalMass D hDR hDS levels fissionNumerator / R =
      commonPairCoarea D levels fissionNumerator := by
  rw [commonPairMicrolocalMass_eq_numeratorMass]
  rw [← commonPairIrregularityFromSheets_eq_coarea hR hS hD hDR hDS]
  rfl

end
end IrregularStokes
end GaloisForLFunctions
