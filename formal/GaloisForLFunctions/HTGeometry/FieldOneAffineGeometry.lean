import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.GroupWithZero.WithZero
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Set.Finite.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Affine and projective monoid geometry over the field-one core

The free pointed commutative monoid on a set `I` consists of an absorbing zero
and finitely supported natural exponent vectors. This file proves its contracted
base extension is the multivariate polynomial semiring, classifies all prime
monoid ideals by subsets of variables, and derives exact affine and projective
monoid-spectrum point counts.
-/

namespace GaloisForLFunctions.HTGeometry.FieldOneCore

open scoped BigOperators

/-- Free pointed commutative monoid on `I`. -/
abbrev AffineCoordinateMonoid (I : Type*) :=
  WithZero (Multiplicative (I →₀ ℕ))

/-- Contracted base extension of the free coordinate monoid. -/
abbrev AffineContractedBaseChange (R I : Type*) [CommSemiring R] :=
  MonoidAlgebra R (Multiplicative (I →₀ ℕ))

/-- Contracted base extension is the ordinary multivariate polynomial semiring. -/
noncomputable def affineContractedBaseChangeEquiv (R I : Type*) [CommSemiring R] :
    AffineContractedBaseChange R I ≃+* MvPolynomial I R :=
  (AddMonoidAlgebra.toMultiplicative R (I →₀ ℕ)).symm

/-- A multiplicative ideal in a commutative monoid with zero. -/
structure MonoidZeroIdeal (A : Type*) [CommMonoidWithZero A] where
  carrier : Set A
  zero_mem : (0 : A) ∈ carrier
  mul_mem_right : ∀ {a : A}, a ∈ carrier → ∀ b : A, a * b ∈ carrier

namespace MonoidZeroIdeal

instance {A : Type*} [CommMonoidWithZero A] : SetLike (MonoidZeroIdeal A) A where
  coe := carrier
  coe_injective' P Q h := by
    cases P
    cases Q
    cases h
    rfl

@[ext]
theorem ext {A : Type*} [CommMonoidWithZero A] {P Q : MonoidZeroIdeal A}
    (h : ∀ x, x ∈ P ↔ x ∈ Q) : P = Q :=
  SetLike.ext h

@[simp]
theorem zero_mem' {A : Type*} [CommMonoidWithZero A] (P : MonoidZeroIdeal A) :
    (0 : A) ∈ P :=
  P.zero_mem

theorem mul_mem_left {A : Type*} [CommMonoidWithZero A] (P : MonoidZeroIdeal A)
    {a : A} (ha : a ∈ P) (b : A) : b * a ∈ P := by
  rw [mul_comm]
  exact P.mul_mem_right ha b

/-- A proper multiplicative ideal satisfying the prime-product condition. -/
def IsPrime {A : Type*} [CommMonoidWithZero A] (P : MonoidZeroIdeal A) : Prop :=
  (1 : A) ∉ P ∧ ∀ a b : A, a * b ∈ P → a ∈ P ∨ b ∈ P

end MonoidZeroIdeal

/-- Coordinate variable in the free pointed monoid. -/
noncomputable def coordinateVariable {I : Type*} (i : I) : AffineCoordinateMonoid I :=
  (Multiplicative.ofAdd (Finsupp.single i 1) : Multiplicative (I →₀ ℕ))

/-- Prime coordinate ideal associated to a subset of variables. -/
def coordinatePrime {I : Type*} (S : Set I) :
    MonoidZeroIdeal (AffineCoordinateMonoid I) where
  carrier x :=
    x = 0 ∨ ∃ (e : I →₀ ℕ), x = (Multiplicative.ofAdd e :
      Multiplicative (I →₀ ℕ)) ∧ ∃ i ∈ S, 0 < e i
  zero_mem := Or.inl rfl
  mul_mem_right := by
    intro a ha b
    rcases ha with rfl | ⟨e, rfl, i, hiS, hie⟩
    · exact Or.inl (zero_mul b)
    · induction b using WithZero.recZeroCoe with
      | zero => exact Or.inl (mul_zero _)
      | coe f =>
          right
          refine ⟨e + f.toAdd, ?_, i, hiS, ?_⟩
          · rfl
          · simpa using lt_of_lt_of_le hie (Nat.le_add_right (e i) (f.toAdd i))

/-- Every coordinate ideal associated to a subset of variables is prime. -/
theorem coordinatePrime_isPrime {I : Type*} (S : Set I) :
    (coordinatePrime S).IsPrime := by
  constructor
  · intro h
    rcases h with h | ⟨e, he, i, hiS, hie⟩
    · exact one_ne_zero h
    · have : e = 0 := by
        exact WithZero.coe_injective (he.symm.trans rfl)
      simp [this] at hie
  · intro a b hab
    induction a using WithZero.recZeroCoe with
    | zero => exact Or.inl (coordinatePrime S).zero_mem
    | coe e =>
        induction b using WithZero.recZeroCoe with
        | zero => exact Or.inr (coordinatePrime S).zero_mem
        | coe f =>
            rcases hab with hzero | ⟨g, hg, i, hiS, hig⟩
            · exact False.elim (WithZero.coe_ne_zero hzero)
            · have hgf : g = e.toAdd + f.toAdd := by
                exact WithZero.coe_injective (hg.symm.trans rfl)
              rw [hgf, Finsupp.add_apply] at hig
              rcases Nat.add_pos_iff_pos_or_pos.mp hig with hie | hif
              · exact Or.inl (Or.inr ⟨e.toAdd, rfl, i, hiS, hie⟩)
              · exact Or.inr (Or.inr ⟨f.toAdd, rfl, i, hiS, hif⟩)

/-- Every exponent vector factors into powers of basis exponent vectors. -/
theorem coordinateExponent_eq_prod {I : Type*} (e : I →₀ ℕ) :
    (Multiplicative.ofAdd e : Multiplicative (I →₀ ℕ)) =
      ∏ i ∈ e.support,
        (Multiplicative.ofAdd (Finsupp.single i 1) :
          Multiplicative (I →₀ ℕ)) ^ e i := by
  classical
  apply Multiplicative.toAdd.injective
  ext i
  simpa [Finsupp.sum] using
    congrArg (fun f : I →₀ ℕ => f i) (Finsupp.sum_single e).symm

/-- Every nonzero coordinate monomial factors into powers of coordinate variables. -/
theorem coordinateMonomial_eq_prod {I : Type*} (e : I →₀ ℕ) :
    ((Multiplicative.ofAdd e : Multiplicative (I →₀ ℕ)) :
      AffineCoordinateMonoid I) =
      ∏ i ∈ e.support, coordinateVariable i ^ e i := by
  classical
  rw [coordinateExponent_eq_prod e]
  simpa only [coordinateVariable, map_pow] using
    map_prod (WithZero.coeMonoidHom (α := Multiplicative (I →₀ ℕ)))
      (fun i => (Multiplicative.ofAdd (Finsupp.single i 1) :
        Multiplicative (I →₀ ℕ)) ^ e i) e.support

namespace MonoidZeroIdeal

theorem pow_mem_of_mem {A : Type*} [CommMonoidWithZero A] (P : MonoidZeroIdeal A)
    {a : A} (ha : a ∈ P) {n : ℕ} (hn : 0 < n) : a ^ n ∈ P := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [pow_succ]
  exact P.mul_mem_left ha _

theorem mem_of_pow_mem {A : Type*} [CommMonoidWithZero A] {P : MonoidZeroIdeal A}
    (hP : P.IsPrime) {a : A} : ∀ n : ℕ, a ^ n ∈ P → a ∈ P
  | 0, h => False.elim (hP.1 (by simpa using h))
  | n + 1, h => by
      rw [pow_succ] at h
      rcases hP.2 _ _ h with hn | ha
      · exact mem_of_pow_mem hP n hn
      · exact ha

theorem exists_mem_of_prod_mem {A I : Type*} [CommMonoidWithZero A]
    {P : MonoidZeroIdeal A} (hP : P.IsPrime) (s : Finset I) (f : I → A)
    (hprod : ∏ i ∈ s, f i ∈ P) : ∃ i ∈ s, f i ∈ P := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact False.elim (hP.1 (by simpa using hprod))
  | @insert i s hi ih =>
      have hmul : f i * ∏ j ∈ s, f j ∈ P := by
        simpa [hi] using hprod
      rcases hP.2 _ _ hmul with hfi | hrest
      · exact ⟨i, Finset.mem_insert_self i s, hfi⟩
      · obtain ⟨j, hjs, hfj⟩ := ih hrest
        exact ⟨j, Finset.mem_insert_of_mem hjs, hfj⟩

theorem prod_mem_of_mem {A I : Type*} [CommMonoidWithZero A]
    (P : MonoidZeroIdeal A) (s : Finset I) (f : I → A)
    {i : I} (his : i ∈ s) (hfi : f i ∈ P) : ∏ j ∈ s, f j ∈ P := by
  classical
  rw [← Finset.insert_erase his]
  rw [Finset.prod_insert (Finset.notMem_erase i s)]
  exact P.mul_mem_right hfi _

end MonoidZeroIdeal

/-- Variables whose coordinate monomials lie in a monoid ideal. -/
noncomputable def variablesOfIdeal {I : Type*}
    (P : MonoidZeroIdeal (AffineCoordinateMonoid I)) : Set I :=
  {i | coordinateVariable i ∈ P}

/-- Every prime ideal of a free coordinate monoid is generated by a subset of variables. -/
theorem prime_eq_coordinatePrime {I : Type*}
    (P : MonoidZeroIdeal (AffineCoordinateMonoid I)) (hP : P.IsPrime) :
    P = coordinatePrime (variablesOfIdeal P) := by
  ext x
  constructor
  · intro hx
    induction x using WithZero.recZeroCoe with
    | zero => exact (coordinatePrime (variablesOfIdeal P)).zero_mem
    | coe e =>
        have hprod : ∏ i ∈ e.toAdd.support, coordinateVariable i ^ e.toAdd i ∈ P := by
          rw [← coordinateMonomial_eq_prod]
          exact hx
        obtain ⟨i, hisupp, hipow⟩ :=
          MonoidZeroIdeal.exists_mem_of_prod_mem hP e.toAdd.support
            (fun i => coordinateVariable i ^ e.toAdd i) hprod
        have hiP : coordinateVariable i ∈ P :=
          MonoidZeroIdeal.mem_of_pow_mem hP (e.toAdd i) hipow
        exact Or.inr ⟨e.toAdd, rfl, i, hiP,
          Finsupp.mem_support_iff.mp hisupp |>.bot_lt⟩
  · intro hx
    rcases hx with rfl | ⟨e, rfl, i, hiP, hie⟩
    · exact P.zero_mem
    · rw [coordinateMonomial_eq_prod]
      apply MonoidZeroIdeal.prod_mem_of_mem P e.support
        (fun j => coordinateVariable j ^ e j)
      · exact Finsupp.mem_support_iff.mpr (Nat.ne_of_gt hie)
      · exact MonoidZeroIdeal.pow_mem_of_mem P hiP hie

/-- A coordinate variable belongs to `P_S` exactly when its index belongs to `S`. -/
theorem coordinateVariable_mem_coordinatePrime_iff {I : Type*} (S : Set I) (i : I) :
    coordinateVariable i ∈ coordinatePrime S ↔ i ∈ S := by
  classical
  constructor
  · intro h
    rcases h with hzero | ⟨e, he, j, hjS, hje⟩
    · exact False.elim (WithZero.coe_ne_zero hzero)
    · have heq : e = Finsupp.single i 1 := by
        apply Multiplicative.ofAdd.injective
        exact (WithZero.coe_injective he).symm
      subst e
      have hji : j = i := by
        by_contra hne
        simp [hne] at hje
      simpa [hji] using hjS
  · intro hi
    exact Or.inr ⟨Finsupp.single i 1, rfl, i, hi, by simp⟩

/-- Inclusion of coordinate primes is exactly inclusion of variable subsets. -/
theorem coordinatePrime_subset_iff {I : Type*} (S T : Set I) :
    (∀ ⦃x⦄, x ∈ coordinatePrime S → x ∈ coordinatePrime T) ↔ S ⊆ T := by
  constructor
  · intro h i hi
    apply (coordinateVariable_mem_coordinatePrime_iff T i).mp
    exact h ((coordinateVariable_mem_coordinatePrime_iff S i).mpr hi)
  · intro h x hx
    rcases hx with rfl | ⟨e, rfl, i, hiS, hie⟩
    · exact (coordinatePrime T).zero_mem
    · exact Or.inr ⟨e, rfl, i, h hiS, hie⟩

/-- Prime ideals of affine coordinate monoids are canonically subsets of variables. -/
noncomputable def coordinatePrimeEquiv (I : Type*) :
    Set I ≃ {P : MonoidZeroIdeal (AffineCoordinateMonoid I) // P.IsPrime} where
  toFun S := ⟨coordinatePrime S, coordinatePrime_isPrime S⟩
  invFun P := variablesOfIdeal P.1
  left_inv S := by
    ext i
    exact coordinateVariable_mem_coordinatePrime_iff S i
  right_inv P := by
    apply Subtype.ext
    exact (prime_eq_coordinatePrime P.1 P.2).symm

/-- Affine `n`-space over the multiplicative core has `2^n` monoid-spectrum points. -/
theorem card_affineMonoidSpectrum (n : ℕ) :
    Nat.card {P : MonoidZeroIdeal (AffineCoordinateMonoid (Fin n)) // P.IsPrime} =
      2 ^ n := by
  rw [Nat.card_congr (coordinatePrimeEquiv (Fin n)).symm]
  rw [Nat.card_eq_fintype_card, Fintype.card_set, Fintype.card_fin]

/-- Point set of monoid-Proj: proper coordinate subsets, excluding the irrelevant ideal. -/
abbrev ProjectiveMonoidPoint (I : Type*) := {S : Set I // S ≠ Set.univ}

/-- Projective `(n-1)`-space has `2^n - 1` underlying monoid-Proj points. -/
theorem card_projectiveMonoidSpectrum (n : ℕ) :
    Nat.card (ProjectiveMonoidPoint (Fin n)) = 2 ^ n - 1 := by
  classical
  rw [Nat.card_eq_fintype_card]
  change Fintype.card {S : Set (Fin n) // S ≠ Set.univ} = 2 ^ n - 1
  have h := Set.card_ne_eq (α := Set (Fin n)) (Set.univ : Set (Fin n))
  rw [Fintype.card_set, Fintype.card_fin] at h
  exact h

end GaloisForLFunctions.HTGeometry.FieldOneCore
