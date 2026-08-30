import GaloisForLFunctions.HTGeometry.RittSecondJetAffineConnection
import GaloisForLFunctions.HTGeometry.RittPrefixFieldStability

/-!
# The second-order case of Ritt's implication

Collecting the collapse and the two coprime descents: if the first two jets of a linearizer are
independent and the *second* jet is algebraic over the field they generate, then the map carries a
rational affine connection.

The collapse upgrades "algebraic over the prefix field" to "in the prefix field", and the two
slicings — first in the jet ratio `τ / d τ` over `K⟮τ⟯`, then in `τ` over `K` — turn membership into
the equation `ψ(a)·ρ = a − dK ρ / ρ`.

Together with `rittForm_or_jet_mem_jetPrefixField` this settles Ritt's implication for every
differentially algebraic linearizer whose minimal algebraic jet order is at most two.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem jetPrefixField_two (Fr : RittFrame K L) (τ : L) :
    Fr.jetPrefixField τ 2 = IntermediateField.adjoin K ({τ, Fr.d τ} : Set L) := by
  have hset : {x : L | ∃ j < 2, x = Fr.d^[j] τ} = ({τ, Fr.d τ} : Set L) := by
    ext x
    constructor
    · rintro ⟨j, hj, rfl⟩
      interval_cases j
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | hx)
      · exact ⟨0, by omega, rfl⟩
      · exact ⟨1, by omega, by simpa using hx⟩
  rw [RittFrame.jetPrefixField, hset]

/-- **The second-order case of Ritt's implication.**  Independent first two jets and an algebraic
second jet force a rational affine connection. -/
theorem exists_affineConnection_of_secondJet_isAlgebraic (Fr : RittFrame K L) [CharZero L]
    {τ : L} {q : K} (hτ : τ ≠ 0) (hdτ : Fr.d τ ≠ 0) (hq : q ≠ 0) (hqconst : Fr.dK q = 0)
    (hshift : Fr.σ τ = algebraMap K L q * τ)
    (hτtr : Transcendental K τ)
    (hdτtr : Transcendental ↥(IntermediateField.adjoin K ({τ} : Set L)) (Fr.d τ))
    (halg : IsAlgebraic ↥(Fr.jetPrefixField τ 2) (Fr.d^[2] τ)) :
    ∃ a : K, Fr.ψ a * Fr.ρ = a - Fr.dK Fr.ρ / Fr.ρ := by
  have hmem : Fr.d^[2] τ ∈ Fr.jetPrefixField τ 2 :=
    jet_mem_jetPrefixField_of_isAlgebraic Fr hτ hdτ hq hqconst hshift (le_refl 2) halg
  rw [jetPrefixField_two] at hmem
  exact exists_affineConnection_of_secondJet_mem Fr hτ hdτ hq hqconst hshift hτtr hdτtr
    (by simpa using hmem)

end GaloisForLFunctions.HTGeometry
