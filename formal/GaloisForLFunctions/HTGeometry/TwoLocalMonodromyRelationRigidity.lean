import GaloisForLFunctions.HTGeometry.SpectralMonodromyRelationRigidity
import GaloisForLFunctions.HTGeometry.AnalyticSpectralRelationEscape
import GaloisForLFunctions.HTGeometry.TwoLocalCommonBaseEdgeMonodromy

/-!
# Two-local monodromy erases every projective spectral character

The universal complexified two-local family realizes every permutation of
its simple spectrum by a closed loop at one fixed diagonal Hamiltonian.
Consequently, a constant-coefficient linear relation that vanishes after
every realized continuation has constant coefficients.  For a balanced
integer character, constancy forces the character to be zero.

This is the exact algebraic obstruction behind generic all-order
nonresonance: no nonzero projective spectral character is invariant under
two-local spectral continuation.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

/-- Value of one constant-coefficient spectral character after continuation
by a permutation at the fixed common two-local base. -/
noncomputable def commonBaseTwoLocalSpectralRelation
    (m : ℕ)
    (coefficient : (Fin (m + 1) → Bool) → ℂ)
    (perm : Equiv.Perm (Fin (m + 1) → Bool)) : ℂ :=
  ∑ x, coefficient x *
    commonTwoLocalDiagonalRoot m (perm x)

/-- A spectral character vanishes after every closed simple-spectrum
continuation realized by the universal two-local family. -/
def CommonBaseTwoLocalMonodromyInvariantRelation
    (m : ℕ)
    (coefficient : (Fin (m + 1) → Bool) → ℂ) : Prop :=
  ∀ perm,
    commonBaseTwoLocalRealizedPermutation m perm →
      commonBaseTwoLocalSpectralRelation m coefficient perm = 0

/-- **Two-local monodromy relation rigidity.**  Every linear relation
preserved by all closed two-local spectral continuations has constant
coefficients. -/
theorem
    coefficients_constant_of_commonBaseTwoLocalMonodromyInvariantRelation
    (m : ℕ)
    (coefficient : (Fin (m + 1) → Bool) → ℂ)
    (hrelation :
      CommonBaseTwoLocalMonodromyInvariantRelation
        m coefficient) :
    ∀ x y, coefficient x = coefficient y := by
  apply coefficients_eq_of_all_permuted_relations
    coefficient
    (commonTwoLocalDiagonalRoot m)
    (commonTwoLocalDiagonalRoot_injective m)
  intro perm
  simpa [commonBaseTwoLocalSpectralRelation] using
    hrelation perm
      (everyPermutation_has_exact_commonBase_twoLocalLoop
        m perm)

/-- **Complex projective monodromy rigidity.** A complex spectral
covector whose coefficients sum to zero cannot vanish after every
realized closed two-local continuation unless the covector itself is
zero.  Unlike the integer-character corollary below, this statement
controls every affine direction in the projective spectrum. -/
theorem
    complexBalancedCoefficient_eq_zero_of_commonBaseTwoLocalMonodromyInvariant
    (m : ℕ)
    (coefficient : (Fin (m + 1) → Bool) → ℂ)
    (hbalanced : ∑ x, coefficient x = 0)
    (hinvariant :
      CommonBaseTwoLocalMonodromyInvariantRelation m coefficient) :
    coefficient = 0 := by
  have hconstant : ∀ x y, coefficient x = coefficient y :=
    coefficients_constant_of_commonBaseTwoLocalMonodromyInvariantRelation
      m coefficient hinvariant
  let x₀ : Fin (m + 1) → Bool := fun _ => false
  have hsum :
      (∑ x, coefficient x) =
        (Fintype.card (Fin (m + 1) → Bool) : ℂ) * coefficient x₀ := by
    calc
      (∑ x, coefficient x) = ∑ _x, coefficient x₀ := by
        apply Finset.sum_congr rfl
        intro x _hx
        exact hconstant x x₀
      _ = (Fintype.card (Fin (m + 1) → Bool) : ℂ) * coefficient x₀ := by
        simp
  have hmul :
      (Fintype.card (Fin (m + 1) → Bool) : ℂ) * coefficient x₀ = 0 := by
    rw [← hsum]
    exact hbalanced
  have hcard :
      (Fintype.card (Fin (m + 1) → Bool) : ℂ) ≠ 0 := by
    exact_mod_cast
      (Fintype.card_ne_zero :
        Fintype.card (Fin (m + 1) → Bool) ≠ 0)
  have hx₀ : coefficient x₀ = 0 :=
    (mul_eq_zero.mp hmul).resolve_left hcard
  funext x
  rw [hconstant x x₀, hx₀]
  rfl

/-- A spectral action takes one value after every closed simple-spectrum
continuation realized by the universal two-local family. -/
def CommonBaseTwoLocalMonodromyInvariantAction
    (m : ℕ)
    (coefficient : (Fin (m + 1) → Bool) → ℂ) : Prop :=
  ∃ z : ℂ, ∀ perm,
    commonBaseTwoLocalRealizedPermutation m perm →
      commonBaseTwoLocalSpectralRelation m coefficient perm = z

/-- Full two-local monodromy forces every invariant spectral action to
have constant coefficients. -/
theorem
    coefficients_constant_of_commonBaseTwoLocalMonodromyInvariantAction
    (m : ℕ)
    (coefficient : (Fin (m + 1) → Bool) → ℂ)
    (haction :
      CommonBaseTwoLocalMonodromyInvariantAction m coefficient) :
    ∀ x y, coefficient x = coefficient y := by
  obtain ⟨z, hz⟩ := haction
  apply coefficients_eq_of_all_permuted_sums_eq
    coefficient
    (commonTwoLocalDiagonalRoot m)
    (commonTwoLocalDiagonalRoot_injective m)
    z
  intro perm
  simpa [commonBaseTwoLocalSpectralRelation] using
    hz perm (everyPermutation_has_exact_commonBase_twoLocalLoop m perm)

/-- **No hidden projective spectral action.** If a balanced complex
spectral action has one common value after every realized closed two-local
continuation, then its coefficient covector is zero. -/
theorem
    complexBalancedCoefficient_eq_zero_of_commonBaseTwoLocalMonodromyInvariantAction
    (m : ℕ)
    (coefficient : (Fin (m + 1) → Bool) → ℂ)
    (hbalanced : ∑ x, coefficient x = 0)
    (haction :
      CommonBaseTwoLocalMonodromyInvariantAction m coefficient) :
    coefficient = 0 := by
  obtain ⟨z, hz⟩ := haction
  apply complexBalancedCoefficient_eq_zero_of_commonBaseTwoLocalMonodromyInvariant
    m coefficient hbalanced
  intro perm hperm
  have hconst :=
    coefficients_constant_of_commonBaseTwoLocalMonodromyInvariantAction
      m coefficient ⟨z, hz⟩
  let x₀ : Fin (m + 1) → Bool := fun _ => false
  have hsum :
      commonBaseTwoLocalSpectralRelation m coefficient perm =
        coefficient x₀ * ∑ x, commonTwoLocalDiagonalRoot m (perm x) := by
    unfold commonBaseTwoLocalSpectralRelation
    calc
      (∑ x, coefficient x * commonTwoLocalDiagonalRoot m (perm x)) =
          ∑ x, coefficient x₀ * commonTwoLocalDiagonalRoot m (perm x) := by
            apply Finset.sum_congr rfl
            intro x _hx
            rw [hconst x x₀]
      _ = coefficient x₀ * ∑ x, commonTwoLocalDiagonalRoot m (perm x) := by
            rw [Finset.mul_sum]
  have hx₀ : coefficient x₀ = 0 := by
    have hcard :
        (Fintype.card (Fin (m + 1) → Bool) : ℂ) ≠ 0 := by
      exact_mod_cast
        (Fintype.card_ne_zero :
          Fintype.card (Fin (m + 1) → Bool) ≠ 0)
    have hbal :
        (Fintype.card (Fin (m + 1) → Bool) : ℂ) * coefficient x₀ = 0 := by
      calc
        (Fintype.card (Fin (m + 1) → Bool) : ℂ) * coefficient x₀ =
            ∑ _x : (Fin (m + 1) → Bool), coefficient x₀ := by
          symm
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ = ∑ x, coefficient x := by
          apply Finset.sum_congr rfl
          intro x _hx
          exact (hconst x x₀).symm
        _ = 0 := hbalanced
    exact (mul_eq_zero.mp hbal).resolve_left hcard
  rw [hsum, hx₀, zero_mul]

/-- **No hidden projective resonance.**  A balanced integer character
cannot vanish after every realized closed two-local continuation unless it
is the zero character. -/
theorem
    balancedCharacter_eq_zero_of_commonBaseTwoLocalMonodromyInvariant
    (m : ℕ)
    (k : (Fin (m + 1) → Bool) → ℤ)
    (hbalanced : SpectralCharacterBalanced k)
    (hinvariant :
      CommonBaseTwoLocalMonodromyInvariantRelation
        m (fun x => (k x : ℂ))) :
    k = 0 := by
  have hconstant :
      ∀ x y, (k x : ℂ) = (k y : ℂ) :=
    coefficients_constant_of_commonBaseTwoLocalMonodromyInvariantRelation
      m (fun x => (k x : ℂ)) hinvariant
  have hconstantInt : ∀ x y, k x = k y := by
    intro x y
    exact Int.cast_injective (hconstant x y)
  let x₀ : Fin (m + 1) → Bool := fun _ => false
  have hsum :
      (∑ x, k x) =
        (Fintype.card (Fin (m + 1) → Bool) : ℤ) * k x₀ := by
    calc
      (∑ x, k x) = ∑ _x, k x₀ := by
        apply Finset.sum_congr rfl
        intro x _hx
        exact hconstantInt x x₀
      _ = (Fintype.card (Fin (m + 1) → Bool) : ℤ) * k x₀ := by
        simp
  have hmul :
      (Fintype.card (Fin (m + 1) → Bool) : ℤ) * k x₀ = 0 := by
    rw [← hsum]
    exact hbalanced
  have hcard :
      (Fintype.card (Fin (m + 1) → Bool) : ℤ) ≠ 0 := by
    exact_mod_cast
      (Fintype.card_ne_zero :
        Fintype.card (Fin (m + 1) → Bool) ≠ 0)
  have hx₀ : k x₀ = 0 :=
    (mul_eq_zero.mp hmul).resolve_left hcard
  funext x
  rw [hconstantInt x x₀, hx₀]
  rfl

/-- Every nonzero balanced character is broken by one exact closed
simple-spectrum loop of the universal two-local family. -/
theorem
    exists_commonBaseTwoLocalLoop_breaking_balancedCharacter
    (m : ℕ)
    (k : (Fin (m + 1) → Bool) → ℤ)
    (hbalanced : SpectralCharacterBalanced k)
    (hk : k ≠ 0) :
    ∃ perm : Equiv.Perm (Fin (m + 1) → Bool),
      commonBaseTwoLocalRealizedPermutation m perm ∧
      commonBaseTwoLocalSpectralRelation
        m (fun x => (k x : ℂ)) perm ≠ 0 := by
  by_contra hnone
  push Not at hnone
  have hinvariant :
      CommonBaseTwoLocalMonodromyInvariantRelation
        m (fun x => (k x : ℂ)) := by
    intro perm hperm
    exact hnone perm hperm
  exact hk
    (balancedCharacter_eq_zero_of_commonBaseTwoLocalMonodromyInvariant
      m k hbalanced hinvariant)

end GaloisForLFunctions.HTGeometry
