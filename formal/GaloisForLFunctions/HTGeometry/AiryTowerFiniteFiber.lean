import GaloisForLFunctions.HTGeometry.AiryTowerFactorization

/-!
# Finite fibres of decorated Stokes characteristic data

This module proves the finite-type core of the decorated finite-fibre theorem.  For fixed
ramification and first exponent, the full strict characteristic type is finite.  Strict divisor
chains are finite at fixed ramification.  Finally, fixing weighted irregularity leaves only
finitely many complete characteristic data.
-/

namespace GaloisForLFunctions
namespace IrregularStokes

namespace Characteristic

/-- The first exponent is bounded by the full weighted irregularity. -/
theorem firstExponent_le_weightedIrregularity {R beta : ℕ} (c : Characteristic R beta) :
    beta ≤ c.weightedIrregularity := by
  have hdrop : 1 ≤ R - c.nextRamification := by
    have := c.nextRamification_lt
    omega
  have hmul : beta ≤ beta * (R - c.nextRamification) := by
    calc
      beta = beta * 1 := by simp
      _ ≤ beta * (R - c.nextRamification) := Nat.mul_le_mul_left beta hdrop
  exact hmul.trans c.firstContribution_le_weightedIrregularity

/-- Finite constructor code for a characteristic with fixed initial indices. -/
private def Code (R beta : ℕ) : Type :=
  { _u : Unit // 1 < R ∧ 0 < beta ∧ Nat.gcd R beta = 1 } ⊕
  (Σ E : Fin R, Σ gamma : Fin beta,
    { _tail : Characteristic E gamma //
      (1 : ℕ) < (E : ℕ) ∧ 0 < beta ∧ Nat.gcd R beta = (E : ℕ) })

/-- Full characteristic data form a finite type once ramification and first exponent are fixed. -/
theorem finite (R beta : ℕ) : Finite (Characteristic R beta) := by
  revert beta
  induction R using Nat.strong_induction_on with
  | h R ih =>
      intro beta
      letI tailFinite (E : Fin R) (gamma : Fin beta) :
          Finite (Characteristic (E : ℕ) (gamma : ℕ)) :=
        ih (E : ℕ) E.isLt (gamma : ℕ)
      let decode : Code R beta → Characteristic R beta
        | .inl h => Characteristic.terminal h.property.1 h.property.2.1 h.property.2.2
        | .inr ⟨E, gamma, tail⟩ =>
            Characteristic.step E.isLt tail.property.1 tail.property.2.1 tail.property.2.2
              gamma.isLt tail.1
      haveI : Finite (Code R beta) := by
        unfold Code
        infer_instance
      apply Finite.of_surjective decode
      intro c
      cases c with
      | terminal hR hbeta hgcd =>
          exact ⟨Sum.inl ⟨(), hR, hbeta, hgcd⟩, rfl⟩
      | @step R E beta gamma hER hE hbeta hgcd hgamma tail =>
          exact ⟨Sum.inr ⟨⟨E, hER⟩, ⟨gamma, hgamma⟩, ⟨tail, hE, hbeta, hgcd⟩⟩, rfl⟩

end Characteristic

/-- Strict divisor chains at fixed ramification form a finite type. -/
theorem finite_strictDivisorChain (R : ℕ) : Finite (StrictDivisorChain R) := by
  let Encoding := Σ beta : Fin (2 * R), Characteristic R beta
  let encode : StrictDivisorChain R → Encoding := fun d =>
    ⟨⟨d.firstExponent, d.firstExponent_lt_twice⟩, d.toCharacteristic⟩
  let decode : Encoding → StrictDivisorChain R := fun e => e.2.toStrictDivisorChain
  have hleft : Function.LeftInverse decode encode := by
    intro d
    exact d.toStrictDivisorChain_toCharacteristic
  letI characteristicFinite (beta : Fin (2 * R)) : Finite (Characteristic R beta) :=
    Characteristic.finite R beta
  haveI : Finite Encoding := inferInstance
  exact Finite.of_injective encode hleft.injective

/-- Complete local characteristic data with fixed ramification and weighted irregularity. -/
structure FixedWeightedCharacteristic (R W : ℕ) where
  firstExponent : ℕ
  characteristic : Characteristic R firstExponent
  weighted_eq : characteristic.weightedIrregularity = W

/-- Fixed diagonal multiplicity and fixed ramification leave only finitely many local
characteristic data. -/
theorem finite_fixedWeightedCharacteristic (R W : ℕ) :
    Finite (FixedWeightedCharacteristic R W) := by
  let Encoding := Σ beta : Fin (W + 1),
    { c : Characteristic R beta // c.weightedIrregularity = W }
  let encode : FixedWeightedCharacteristic R W → Encoding := fun c =>
    ⟨⟨c.firstExponent, Nat.lt_succ_of_le <| by
        calc
          c.firstExponent ≤ c.characteristic.weightedIrregularity :=
            c.characteristic.firstExponent_le_weightedIrregularity
          _ = W := c.weighted_eq⟩,
      ⟨c.characteristic, c.weighted_eq⟩⟩
  let decode : Encoding → FixedWeightedCharacteristic R W := fun e =>
    { firstExponent := e.1
      characteristic := e.2.1
      weighted_eq := e.2.2 }
  have hleft : Function.LeftInverse decode encode := by
    rintro ⟨beta, c, hw⟩
    rfl
  letI characteristicFinite (beta : Fin (W + 1)) : Finite (Characteristic R beta) :=
    Characteristic.finite R beta
  haveI : Finite Encoding := inferInstance
  exact Finite.of_injective encode hleft.injective

end IrregularStokes
end GaloisForLFunctions
