import GaloisForLFunctions.HTGeometry.InvolutiveDescentExactSequenceLaw

/-!
# Real reflection-odd interface witnesses

`InvolutiveDescentExactSequenceLaw` gives the universal complex coequalizer law.  This file exposes
its real-valued odd projection through the older `OddUnder` interface used by completion and
observation theorems.
-/

namespace GaloisForLFunctions.HTGeometry

/-- The reflection-odd part of every real observable is odd under an involution. -/
theorem reflectionOddPart_oddUnder
    {X : Type*} {σ : X → X} (hσ : Function.Involutive σ) (τ : X → ℝ) :
    OddUnder X σ (reflectionOddPart σ τ) := by
  intro x
  rw [reflectionOddPart, reflectionOddPart, hσ x]
  ring

/-- The zero charge is reflection odd for every reflection candidate. -/
theorem oddUnder_zero {X : Type*} (σ : X → X) :
    OddUnder X σ (fun _ => 0) := by
  intro x
  simp

/-- **Exact real odd-projection law.**  A real charge is a reflection-odd projection exactly when
it is odd under the involution. -/
theorem exists_reflectionOddPart_preimage_iff_oddUnder
    {X : Type*} {σ : X → X} (hσ : Function.Involutive σ) (χ : X → ℝ) :
    (∃ τ : X → ℝ, reflectionOddPart σ τ = χ) ↔ OddUnder X σ χ := by
  constructor
  · rintro ⟨τ, rfl⟩
    exact reflectionOddPart_oddUnder hσ τ
  · intro hχ
    refine ⟨χ, ?_⟩
    funext x
    rw [reflectionOddPart, hχ x]
    ring

end GaloisForLFunctions.HTGeometry
