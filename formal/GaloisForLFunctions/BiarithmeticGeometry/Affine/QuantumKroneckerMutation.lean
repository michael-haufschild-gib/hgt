import GaloisForLFunctions.HTGeometry.QuantumLaurentScalarAlgebra

/-!
# A quantum Kronecker mutation in the Laurent division ring

The first rank-two exchange has an explicit two-word Laurent expansion.
Both ordered exchange equations hold, the new seed reverses the commutation
orientation, and mutating the same coordinate back recovers the original
generator. Nonvanishing follows from the coefficient trace, including at
roots of unity and in positive characteristic.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
variable {F : Type*} [Field F]

/-- First quantum-torus generator. -/
def kroneckerSeedX (c : Fˣ) : QuantumLaurentDivisionRing c := quantumLaurentWord c 1 0

/-- Second quantum-torus generator. -/
def kroneckerSeedY (c : Fˣ) : QuantumLaurentDivisionRing c := quantumLaurentWord c 0 1

/-- Laurent expansion of the first Kronecker cluster mutation. -/
def kroneckerMutatedX (c : Fˣ) : QuantumLaurentDivisionRing c :=
  quantumLaurentWord c (-1) 0 + (↑c⁻¹ : F) • quantumLaurentWord c (-1) 2

private theorem kroneckerSeedY_sq (c : Fˣ) :
    kroneckerSeedY c ^ 2 = quantumLaurentWord c 0 2 := by
  simp [kroneckerSeedY, pow_two, quantumLaurentWord_mul]

/-- The original seed is a quantum Weyl pair at the actual scalar parameter. -/
theorem kroneckerSeed_commutation (c : Fˣ) :
    kroneckerSeedX c * kroneckerSeedY c =
      (c : F) • (kroneckerSeedY c * kroneckerSeedX c) := by
  simp [kroneckerSeedX, kroneckerSeedY, quantumLaurentWord_mul]

/-- The two ordered exchange equations differ by inversion of the quantum parameter. -/
theorem kroneckerMutation_exchange (c : Fˣ) :
    kroneckerSeedX c * kroneckerMutatedX c = 1 + (c : F) • kroneckerSeedY c ^ 2 ∧
    kroneckerMutatedX c * kroneckerSeedX c = 1 + (↑c⁻¹ : F) • kroneckerSeedY c ^ 2 := by
  rw [kroneckerSeedY_sq]
  constructor
  · simp [kroneckerSeedX, kroneckerMutatedX, mul_add,
      quantumLaurentWord_mul, smul_smul]
    congr 1
    rw [zpow_two, ← mul_assoc, inv_mul_cancel₀ c.ne_zero, one_mul]
  · simp [kroneckerSeedX, kroneckerMutatedX, add_mul,
      quantumLaurentWord_mul]

/-- The new ordered pair has the same quantum commutation parameter. -/
theorem kroneckerMutation_commutation (c : Fˣ) :
    kroneckerSeedY c * kroneckerMutatedX c =
      (c : F) • (kroneckerMutatedX c * kroneckerSeedY c) := by
  simp [kroneckerSeedY, kroneckerMutatedX, mul_add, add_mul,
    quantumLaurentWord_mul, smul_add, smul_smul]

/-- The mutated cluster variable never vanishes; the constant coefficient of its
exchange product is one. -/
theorem kroneckerMutatedX_ne_zero (c : Fˣ) : kroneckerMutatedX c ≠ 0 := by
  intro h
  have he := congrArg (quantumLaurentTrace c) (kroneckerMutation_exchange c).1
  rw [h, mul_zero, map_zero, map_add, quantumLaurentTrace_one,
    quantumLaurentTrace_smul, kroneckerSeedY_sq, quantumLaurentTrace_word] at he
  norm_num at he

/-- The reverse mutation recovers the first coordinate without a nonvanishing premise. -/
theorem kroneckerMutation_involutive (c : Fˣ) :
    (kroneckerMutatedX c)⁻¹ * (1 + (↑c⁻¹ : F) • kroneckerSeedY c ^ 2) =
      kroneckerSeedX c := by
  rw [← (kroneckerMutation_exchange c).2, ← mul_assoc,
    inv_mul_cancel₀ (kroneckerMutatedX_ne_zero c), one_mul]

end GaloisForLFunctions.HTGeometry
