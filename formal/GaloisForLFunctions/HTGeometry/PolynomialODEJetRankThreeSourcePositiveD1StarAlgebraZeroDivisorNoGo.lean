import GaloisForLFunctions.HTGeometry.PolynomialODEJetRankThreeSourcePositiveD1InfiniteOperatorContravariantNoGo

/-!
# Algebraic zero-divisor obstruction for contravariant D1 carriers

The bounded-operator obstruction is purely algebraic.  The exact D1-generated vacuum string gives
nonzero polynomials `u,v` with `Eu=0`, `Fv=u`, and `Ev≠0`.  For a right contravariant coefficient
`c`, the pair `(u,v)` forces `pair u u * c = 0`.  For a left coefficient it forces
`c * pair u u = 0`; a faithful involution and Hermitian diagonal reverse this to the same
left-cancellation problem.  If the vacuum diagonal is left regular, the coefficient vanishes, and
the pair `(v,Ev)` then forces the nonzero vector `Ev` to have a zero diagonal.

Consequently every algebra-valued contravariant carrier containing actual D1 has a nonzero source
vector whose diagonal value is a left zero divisor.  This classification uses no positivity,
topology, boundedness, dimension, norm, completeness, or Hilbert structure.  It rules out every
regular `*`-algebra realization on both canonical sides, including common-domain unbounded or
indefinite realizations whenever their D1 diagonals remain left regular.  A surviving
contravariant construction must therefore be genuinely singular on the actual D1 cyclic string;
changing channel size or signature cannot by itself orient the TCD/S6F boundary flux.
-/

open Complex Real

namespace HTGeometry

noncomputable section

section AlgebraCancellation

variable {A : Type*} [NonUnitalRing A]

/-- A left-regular factor cancels a zero product. -/
theorem eq_zero_of_leftRegular_mul_eq_zero
    {a c : A} (ha : IsLeftRegular a) (hac : a * c = 0) : c = 0 := by
  apply ha
  simpa using hac

variable [StarRing A]

/-- A Hermitian left-regular right factor cancels after taking the faithful involution. -/
theorem eq_zero_of_mul_eq_zero_of_star_fixed_leftRegular
    {a c : A} (ha : IsLeftRegular a) (hstar : star a = a)
    (hca : c * a = 0) : c = 0 := by
  have hs := congrArg (fun x : A => star x) hca
  rw [star_mul, star_zero, hstar] at hs
  have hsc : star c = 0 := by
    apply ha
    simpa using hs
  exact star_eq_zero.mp hsc

end AlgebraCancellation

section NontrivialAlgebra

variable {A : Type*} [NonUnitalRing A] [Nontrivial A]

/-- Zero is never left regular in a nontrivial multiplicative zero structure. -/
theorem not_isLeftRegular_zero : ¬ IsLeftRegular (0 : A) := by
  intro h
  obtain ⟨a, ha⟩ := exists_ne (0 : A)
  apply ha
  apply h
  simp

end NontrivialAlgebra

section RightCarrier

variable {A : Type*} [NonUnitalRing A]

/-- Algebra-valued right contravariant data on a source-`sl₂`-stable carrier containing D1. -/
structure ModularThetaSourcePositiveD1RightStarAlgebraContravariantCarrier where
  carrier : Submodule ℂ ModularThetaSourcePositivePolynomial
  d1_mem : modularThetaSourcePositiveReflectedEighthPolynomial ∈ carrier
  sl2E_mem : ∀ P : ModularThetaSourcePositivePolynomial,
    P ∈ carrier →
      modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E P ∈ carrier
  sl2F_mem : ∀ P : ModularThetaSourcePositivePolynomial,
    P ∈ carrier →
      modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2F P ∈ carrier
  coefficient : A
  pair : ModularThetaSourcePositivePolynomial →
    ModularThetaSourcePositivePolynomial → A
  pair_zero_left : ∀ q : ModularThetaSourcePositivePolynomial, pair 0 q = 0
  contravariant : ∀ p q : ModularThetaSourcePositivePolynomial,
    p ∈ carrier → q ∈ carrier →
      pair (modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E p) q =
        pair p (modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2F q) *
          coefficient

theorem ModularThetaSourcePositiveD1RightStarAlgebraContravariantCarrier.sl2FIterate_mem
    (B : ModularThetaSourcePositiveD1RightStarAlgebraContravariantCarrier (A := A))
    (n : ℕ) {P : ModularThetaSourcePositivePolynomial} (hP : P ∈ B.carrier) :
    modularThetaSourcePositiveSl2FIterate n P ∈ B.carrier := by
  induction n with
  | zero => exact hP
  | succ n ih => exact B.sl2F_mem _ ih

variable [Nontrivial A]

/-- Every algebra-valued right contravariant D1 carrier develops a nonzero vector whose diagonal
pairing is a left zero divisor. -/
theorem ModularThetaSourcePositiveD1RightStarAlgebraContravariantCarrier.exists_nonzero_diagonal_not_leftRegular
    (B : ModularThetaSourcePositiveD1RightStarAlgebraContravariantCarrier (A := A)) :
    ∃ p : ModularThetaSourcePositivePolynomial,
      p ∈ B.carrier ∧ p ≠ 0 ∧ ¬ IsLeftRegular (B.pair p p) := by
  rcases exists_modularThetaSourcePositiveReflectedEighth_vacuumString with
    ⟨n, v, u, hvgen, hugen, hu, hFv, hEu, _hHv, hEv⟩
  have hcomponent : modularThetaSourcePositiveAdaptedComponent (n + 1)
      modularThetaSourcePositiveReflectedEighthPolynomial ∈ B.carrier :=
    modularThetaSourcePositiveAdaptedComponent_mem_of_sl2EFInvariant
      B.carrier B.sl2E_mem B.sl2F_mem B.d1_mem (n + 1)
  have hvMem : v ∈ B.carrier := by
    rw [hvgen]
    exact B.sl2FIterate_mem n hcomponent
  have huMem : u ∈ B.carrier := by
    rw [hugen]
    exact B.sl2FIterate_mem (n + 1) hcomponent
  have hEvMem : modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E v ∈
      B.carrier := B.sl2E_mem v hvMem
  by_cases hreg : IsLeftRegular (B.pair u u)
  · have hcontra := B.contravariant u v huMem hvMem
    rw [hEu, hFv, B.pair_zero_left] at hcontra
    have hcoefficient : B.coefficient = 0 :=
      eq_zero_of_leftRegular_mul_eq_zero hreg hcontra.symm
    have hcontraEv := B.contravariant v
      (modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E v)
      hvMem hEvMem
    rw [hcoefficient, mul_zero] at hcontraEv
    have hnotRegular : ¬ IsLeftRegular (B.pair
        (modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E v)
        (modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E v)) := by
      rw [hcontraEv]
      exact not_isLeftRegular_zero
    exact ⟨modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E v,
      hEvMem, hEv, hnotRegular⟩
  · exact ⟨u, huMem, hu, hreg⟩

/-- A right contravariant D1 carrier with left-regular diagonals. -/
structure ModularThetaSourcePositiveD1RightRegularStarAlgebraContravariantCarrier extends
    ModularThetaSourcePositiveD1RightStarAlgebraContravariantCarrier (A := A) where
  diagonal_leftRegular : ∀ p : ModularThetaSourcePositivePolynomial,
    p ∈ carrier → p ≠ 0 → IsLeftRegular (pair p p)

/-- No left-regular algebra-valued right contravariant carrier contains actual D1. -/
theorem modularThetaSourcePositive_no_D1_rightRegularStarAlgebraContravariantCarrier :
    ¬ Nonempty
      (ModularThetaSourcePositiveD1RightRegularStarAlgebraContravariantCarrier (A := A)) := by
  rintro ⟨B⟩
  obtain ⟨p, hpMem, hp, hnot⟩ :=
    B.toModularThetaSourcePositiveD1RightStarAlgebraContravariantCarrier.exists_nonzero_diagonal_not_leftRegular
  exact hnot (B.diagonal_leftRegular p hpMem hp)

end RightCarrier

section LeftCarrier

variable {A : Type*} [NonUnitalRing A] [StarRing A]

/-- Hermitian algebra-valued left contravariant data on a source-`sl₂`-stable carrier containing
D1. Only diagonal Hermiticity is needed. -/
structure ModularThetaSourcePositiveD1LeftStarAlgebraContravariantCarrier where
  carrier : Submodule ℂ ModularThetaSourcePositivePolynomial
  d1_mem : modularThetaSourcePositiveReflectedEighthPolynomial ∈ carrier
  sl2E_mem : ∀ P : ModularThetaSourcePositivePolynomial,
    P ∈ carrier →
      modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E P ∈ carrier
  sl2F_mem : ∀ P : ModularThetaSourcePositivePolynomial,
    P ∈ carrier →
      modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2F P ∈ carrier
  coefficient : A
  pair : ModularThetaSourcePositivePolynomial →
    ModularThetaSourcePositivePolynomial → A
  pair_zero_left : ∀ q : ModularThetaSourcePositivePolynomial, pair 0 q = 0
  diagonal_star : ∀ p : ModularThetaSourcePositivePolynomial,
    p ∈ carrier → p ≠ 0 → star (pair p p) = pair p p
  contravariant : ∀ p q : ModularThetaSourcePositivePolynomial,
    p ∈ carrier → q ∈ carrier →
      pair (modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E p) q =
        coefficient *
          pair p (modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2F q)

theorem ModularThetaSourcePositiveD1LeftStarAlgebraContravariantCarrier.sl2FIterate_mem
    (B : ModularThetaSourcePositiveD1LeftStarAlgebraContravariantCarrier (A := A))
    (n : ℕ) {P : ModularThetaSourcePositivePolynomial} (hP : P ∈ B.carrier) :
    modularThetaSourcePositiveSl2FIterate n P ∈ B.carrier := by
  induction n with
  | zero => exact hP
  | succ n ih => exact B.sl2F_mem _ ih

variable [Nontrivial A]

/-- Every Hermitian algebra-valued left contravariant D1 carrier develops a nonzero vector whose
diagonal pairing is a left zero divisor. -/
theorem ModularThetaSourcePositiveD1LeftStarAlgebraContravariantCarrier.exists_nonzero_diagonal_not_leftRegular
    (B : ModularThetaSourcePositiveD1LeftStarAlgebraContravariantCarrier (A := A)) :
    ∃ p : ModularThetaSourcePositivePolynomial,
      p ∈ B.carrier ∧ p ≠ 0 ∧ ¬ IsLeftRegular (B.pair p p) := by
  rcases exists_modularThetaSourcePositiveReflectedEighth_vacuumString with
    ⟨n, v, u, hvgen, hugen, hu, hFv, hEu, _hHv, hEv⟩
  have hcomponent : modularThetaSourcePositiveAdaptedComponent (n + 1)
      modularThetaSourcePositiveReflectedEighthPolynomial ∈ B.carrier :=
    modularThetaSourcePositiveAdaptedComponent_mem_of_sl2EFInvariant
      B.carrier B.sl2E_mem B.sl2F_mem B.d1_mem (n + 1)
  have hvMem : v ∈ B.carrier := by
    rw [hvgen]
    exact B.sl2FIterate_mem n hcomponent
  have huMem : u ∈ B.carrier := by
    rw [hugen]
    exact B.sl2FIterate_mem (n + 1) hcomponent
  have hEvMem : modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E v ∈
      B.carrier := B.sl2E_mem v hvMem
  by_cases hreg : IsLeftRegular (B.pair u u)
  · have hcontra := B.contravariant u v huMem hvMem
    rw [hEu, hFv, B.pair_zero_left] at hcontra
    have hcoefficient : B.coefficient = 0 :=
      eq_zero_of_mul_eq_zero_of_star_fixed_leftRegular hreg
        (B.diagonal_star u huMem hu) hcontra.symm
    have hcontraEv := B.contravariant v
      (modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E v)
      hvMem hEvMem
    rw [hcoefficient, zero_mul] at hcontraEv
    have hnotRegular : ¬ IsLeftRegular (B.pair
        (modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E v)
        (modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E v)) := by
      rw [hcontraEv]
      exact not_isLeftRegular_zero
    exact ⟨modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E v,
      hEvMem, hEv, hnotRegular⟩
  · exact ⟨u, huMem, hu, hreg⟩

/-- A Hermitian left contravariant D1 carrier with left-regular diagonals. -/
structure ModularThetaSourcePositiveD1LeftRegularStarAlgebraContravariantCarrier extends
    ModularThetaSourcePositiveD1LeftStarAlgebraContravariantCarrier (A := A) where
  diagonal_leftRegular : ∀ p : ModularThetaSourcePositivePolynomial,
    p ∈ carrier → p ≠ 0 → IsLeftRegular (pair p p)

/-- No left-regular Hermitian algebra-valued left contravariant carrier contains actual D1. -/
theorem modularThetaSourcePositive_no_D1_leftRegularStarAlgebraContravariantCarrier :
    ¬ Nonempty
      (ModularThetaSourcePositiveD1LeftRegularStarAlgebraContravariantCarrier (A := A)) := by
  rintro ⟨B⟩
  obtain ⟨p, hpMem, hp, hnot⟩ :=
    B.toModularThetaSourcePositiveD1LeftStarAlgebraContravariantCarrier.exists_nonzero_diagonal_not_leftRegular
  exact hnot (B.diagonal_leftRegular p hpMem hp)

end LeftCarrier

section Capstone

variable {A : Type*} [NonUnitalRing A] [StarRing A] [Nontrivial A]

/-- **Algebraic D1 zero-divisor obstruction.** Neither canonical contravariant side can carry
actual D1 with left-regular diagonal values in any nontrivial involutive algebra. -/
theorem modularThetaSourcePositive_no_D1_regularStarAlgebraContravariantCarrier :
    (¬ Nonempty
      (ModularThetaSourcePositiveD1RightRegularStarAlgebraContravariantCarrier (A := A))) ∧
    (¬ Nonempty
      (ModularThetaSourcePositiveD1LeftRegularStarAlgebraContravariantCarrier (A := A))) :=
  ⟨modularThetaSourcePositive_no_D1_rightRegularStarAlgebraContravariantCarrier,
    modularThetaSourcePositive_no_D1_leftRegularStarAlgebraContravariantCarrier⟩

end Capstone

end

end HTGeometry
