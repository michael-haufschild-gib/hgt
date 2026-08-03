import GaloisForLFunctions.HTGeometry.AiryTowerEnumeration
import GaloisForLFunctions.HTGeometry.AiryTowerSeparatedCore
import GaloisForLFunctions.HTGeometry.ElementaryStokesPairSpectrum

namespace GaloisForLFunctions.IrregularStokes

/-- Ramification-two simple Airy head. -/
def exampleAiryHead2 : AiryHead 2 where
  nextRamification := 1
  firstFactor := 2
  next_pos := by omega
  factor_ge_two := by omega
  ramification_eq := by omega

/-- Ramification-three simple Airy head. -/
def exampleAiryHead3 : AiryHead 3 where
  nextRamification := 1
  firstFactor := 3
  next_pos := by omega
  factor_ge_two := by omega
  ramification_eq := by omega

/-- Ramification-four Airy head with first drop `4 → 2`. -/
def exampleAiryHead4 : AiryHead 4 where
  nextRamification := 2
  firstFactor := 2
  next_pos := by omega
  factor_ge_two := by omega
  ramification_eq := by omega

/-- Exact decorated edge triple of the all-ramified example. -/
theorem allRamified_example_edges :
    separatedEdge exampleAiryHead2 exampleAiryHead3 = 3 ∧
    separatedEdge exampleAiryHead2 exampleAiryHead4 = 4 ∧
    separatedEdge exampleAiryHead3 exampleAiryHead4 = 6 := by
  norm_num [separatedEdge, exampleAiryHead2, exampleAiryHead3, exampleAiryHead4]

/-- Edge multiplicity three is impossible for two ramification-two elementary vertices. -/
theorem ramificationTwo_edge_three_forbidden :
    IsEmpty (ElementaryPairPresentation 2 2 3) := by
  rw [isEmpty_iff]
  intro p
  have hspectrum := (nonempty_elementaryPairPresentation_iff_spectrum 2 2 3).mp ⟨p⟩
  simp [InElementaryPairSpectrum] at hspectrum
  obtain ⟨k, hk, heq⟩ := hspectrum
  omega

/-- An infinite arithmetic progression of two-vertex graphs passes every triangle test vacuously
but is excluded by the exact local spectrum. -/
theorem ramificationTwo_four_mul_add_three_forbidden (k : ℕ) :
    IsEmpty (ElementaryPairPresentation 2 2 (4 * k + 3)) := by
  rw [isEmpty_iff]
  intro p
  have hspectrum :=
    (nonempty_elementaryPairPresentation_iff_spectrum 2 2 (4 * k + 3)).mp ⟨p⟩
  simp only [InElementaryPairSpectrum] at hspectrum
  rcases hspectrum with h | h | h | h | h
  · omega
  · omega
  · omega
  · omega
  · rcases h with ⟨_, _, hlow | ⟨m, hm, heq⟩⟩
    · omega
    · omega

/-- An undecorated zero-loop vertex retains its hidden ramification. -/
structure UndecoratedSimpleAiryVertex where
  ramification : ℕ
  ramified : 1 < ramification
  characteristic : Characteristic ramification (ramification + 1)
  isAiry : characteristic.IsAiryTower
  loop_zero : characteristic.diagonalLoop = 0

def simpleAiryVertex (n : ℕ) : UndecoratedSimpleAiryVertex := by
  let R := n + 2
  have hR : 1 < R := by omega
  have hbeta : 0 < R + 1 := by omega
  have hgcd : Nat.gcd R (R + 1) = 1 := by
    rw [Nat.gcd_comm]
    calc
      Nat.gcd (R + 1) R = Nat.gcd (1 + R * 1) R := by
        simp [Nat.add_comm]
      _ = Nat.gcd 1 R := Nat.gcd_add_mul_left_left R 1 1
      _ = 1 := by simp
  let c : Characteristic R (R + 1) := Characteristic.terminal hR hbeta hgcd
  exact
    { ramification := R
      ramified := hR
      characteristic := c
      isAiry := by simp [c, Characteristic.IsAiryTower]
      loop_zero :=
        (Characteristic.diagonalLoop_eq_zero_iff_isAiryTower c).mpr
          (by simp [c, Characteristic.IsAiryTower]) }

theorem simpleAiryVertex_injective : Function.Injective simpleAiryVertex := by
  intro m n h
  have hr := congrArg UndecoratedSimpleAiryVertex.ramification h
  simp [simpleAiryVertex] at hr
  omega

/-- Forgetting ramification gives an infinite zero-loop vertex fibre. -/
theorem undecorated_simpleAiry_range_infinite :
    (Set.range simpleAiryVertex).Infinite :=
  Set.infinite_range_of_injective simpleAiryVertex_injective

end GaloisForLFunctions.IrregularStokes
