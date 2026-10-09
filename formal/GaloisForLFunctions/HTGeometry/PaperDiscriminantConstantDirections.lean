import GaloisForLFunctions.HTGeometry.PaperConstantVectorFieldTermination
import GaloisForLFunctions.HTGeometry.PaperIntegralDiscriminant

/-!
# Exact constant directions fixing the universal discriminant

The source factorial-closure theorem forces every root difference to be
fixed whenever a native constant vector field fixes their product. Thus
the discriminant permits exactly simultaneous translation of all roots.
All local-nilpotence requirements are discharged by the native Taylor
formula; no termination premise is imposed on the velocity vector.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial StableCoordinate
open scoped BigOperators

noncomputable section

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

private theorem fixed_factor_of_dvd
    (D : Derivation K (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) K))
    (hD : IsLocallyNilpotent D) {a b : MvPolynomial (Fin n) K}
    (hb : b ≠ 0) (hab : a ∣ b) (hDb : D b = 0) : D a = 0 := by
  obtain ⟨c, rfl⟩ := hab
  exact (lnd_factorial_closure D hD (mul_ne_zero_iff.mp hb).1
    (mul_ne_zero_iff.mp hb).2 hDb).1

omit [CharZero K] in
private theorem fixed_product {ι : Type*}
    (D : Derivation K (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) K))
    (s : Finset ι) (f : ι → MvPolynomial (Fin n) K)
    (h : ∀ i ∈ s, D (f i) = 0) : D (∏ i ∈ s, f i) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, Derivation.map_one_eq_zero]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, D.leibniz, h i (Finset.mem_insert_self i s),
      ih (fun j hj => h j (Finset.mem_insert_of_mem hj))]
    simp

omit [CharZero K] in
private theorem difference_dvd_vandermonde {i j : Fin n} (hij : i < j) :
    (X j - X i : MvPolynomial (Fin n) K) ∣ paperUniversalVandermonde K n := by
  have hi : (X j - X i : MvPolynomial (Fin n) K) ∣
      ∏ k ∈ Finset.Ioi i, (X k - X i : MvPolynomial (Fin n) K) :=
    Finset.dvd_prod_of_mem (fun k : Fin n => (X k - X i : MvPolynomial (Fin n) K))
      (Finset.mem_Ioi.mpr hij)
  have ho : (∏ k ∈ Finset.Ioi i, (X k - X i : MvPolynomial (Fin n) K)) ∣
      ∏ l : Fin n, ∏ k ∈ Finset.Ioi l, (X k - X l : MvPolynomial (Fin n) K) :=
    Finset.dvd_prod_of_mem
      (fun l : Fin n => ∏ k ∈ Finset.Ioi l, (X k - X l : MvPolynomial (Fin n) K))
      (Finset.mem_univ i)
  exact hi.trans ho

omit [CharZero K] in
/-- Every ordered universal root difference divides the full Vandermonde. -/
theorem paperVariableDifference_dvd_vandermonde {i j : Fin n} (hij : i < j) :
    (X j - X i : MvPolynomial (Fin n) K) ∣ paperUniversalVandermonde K n :=
  difference_dvd_vandermonde hij

/-- A constant root motion fixes the Vandermonde exactly when all roots have equal velocity. -/
theorem paperConstantVectorField_vandermonde_eq_zero_iff (v : Fin n → K) :
    constVectorField v (paperUniversalVandermonde K n) = 0 ↔
      ∀ i j, v i = v j := by
  constructor
  · intro h
    have hV : paperUniversalVandermonde K n ≠ 0 :=
      vandermondeProd_ne_zero X_injective
    have hlt : ∀ i j : Fin n, i < j → v i = v j := by
      intro i j hij
      have hd := fixed_factor_of_dvd (constVectorField v)
        (paperConstantVectorField_locallyNilpotent v) hV (difference_dvd_vandermonde hij) h
      rw [map_sub, constVectorField_X, constVectorField_X] at hd
      exact (C_injective (Fin n) K (sub_eq_zero.mp hd)).symm
    intro i j
    rcases lt_trichotomy i j with hij | hij | hij
    · exact hlt i j hij
    · exact congrArg v hij
    · exact (hlt j i hij).symm
  · intro hv
    unfold paperUniversalVandermonde vandermondeProd
    apply fixed_product
    intro i _
    apply fixed_product
    intro j _
    simp only [map_sub, constVectorField_X, hv j i, sub_self]

/-- Squaring the Vandermonde introduces no extra constant invariant direction. -/
theorem paperConstantVectorField_vandermonde_sq_eq_zero_iff (v : Fin n → K) :
    constVectorField v (paperUniversalVandermonde K n ^ 2) = 0 ↔
      ∀ i j, v i = v j := by
  rw [← paperConstantVectorField_vandermonde_eq_zero_iff v, pow_two]
  constructor
  · intro h
    have hV : paperUniversalVandermonde K n ≠ 0 :=
      vandermondeProd_ne_zero X_injective
    exact (lnd_factorial_closure (constVectorField v)
      (paperConstantVectorField_locallyNilpotent v) hV hV h).1
  · intro h
    rw [Derivation.leibniz, h]
    simp

/-- The native universal coefficient discriminant has exactly the same root directions. -/
theorem paperConstantVectorField_discriminant_eq_zero_iff (v : Fin n → K) :
    constVectorField v
      (aeval (fun i : Fin n => esymm (Fin n) K (i.val + 1))
        (paperIntegralDiscriminantPolynomial K n)) = 0 ↔
      ∀ i j, v i = v j := by
  rw [paperIntegralDiscriminantPolynomial_spec, ← pow_two]
  exact paperConstantVectorField_vandermonde_sq_eq_zero_iff v

end

end GaloisForLFunctions.HTGeometry
