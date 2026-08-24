import GaloisForLFunctions.HTGeometry.ForwardRecurrenceFieldConfinement

/-!
# Prime-cyclotomic coefficient-field escape

A primitive root of order `n` has rational minpoly degree `φ(n)`.  Hence a number field containing
such a root has degree at least `φ(n)`.  Primitive roots whose prime orders form an injective
sequence cannot all lie in one number field.  The same remains true after multiplication by
arbitrary nonzero rational magnitudes.
-/

open scoped IntermediateField

namespace GaloisForLFunctions.HTGeometry

/-- The rational minimal polynomial of a primitive `n`-th root has degree `φ(n)`. -/
theorem minpoly_natDegree_of_isPrimitiveRoot
    {L : Type*} [Field L] [CharZero L] {n : ℕ} (hn : 0 < n)
    {u : L} (hu : IsPrimitiveRoot u n) :
    (minpoly ℚ u).natDegree = n.totient := by
  have hroot : Polynomial.aeval u (Polynomial.cyclotomic n ℚ) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
      Polynomial.map_cyclotomic]
    exact (hu.isRoot_cyclotomic hn).eq_zero
  rw [← minpoly.eq_of_irreducible
    (Polynomial.cyclotomic.irreducible_rat hn) hroot]
  have hp0 : Polynomial.cyclotomic n ℚ ≠ 0 :=
    (Polynomial.cyclotomic.irreducible_rat hn).ne_zero
  have hlc : (Polynomial.cyclotomic n ℚ).leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hp0
  rw [Polynomial.natDegree_mul hp0
    (Polynomial.C_ne_zero.mpr (inv_ne_zero hlc))]
  simp [Polynomial.natDegree_cyclotomic]

/-- A number field containing a primitive `n`-th root has degree at least `φ(n)`. -/
theorem totient_le_finrank_of_isPrimitiveRoot_mem
    (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K]
    {n : ℕ} (hn : 0 < n) {u : ℂ} (hu : IsPrimitiveRoot u n) (hmem : u ∈ K) :
    n.totient ≤ Module.finrank ℚ K := by
  let uK : K := ⟨u, hmem⟩
  have huK : IsPrimitiveRoot uK n :=
    hu.of_map_of_injective K.val.injective
  rw [← minpoly_natDegree_of_isPrimitiveRoot hn huK]
  exact minpoly.natDegree_le uK

/-- Prime-order specialization of the cyclotomic degree bound. -/
theorem prime_sub_one_le_finrank_of_isPrimitiveRoot_mem
    (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K]
    {p : ℕ} (hp : p.Prime) {u : ℂ} (hu : IsPrimitiveRoot u p) (hmem : u ∈ K) :
    p - 1 ≤ Module.finrank ℚ K := by
  rw [← Nat.totient_prime hp]
  exact totient_le_finrank_of_isPrimitiveRoot_mem K hp.pos hu hmem

/-- An injective sequence of natural numbers is unbounded. -/
theorem nat_sequence_unbounded_of_injective (f : ℕ → ℕ)
    (hf : Function.Injective f) (B : ℕ) : ∃ n, B < f n := by
  by_contra h
  have hbound : ∀ n, f n ≤ B := by
    intro n
    exact Nat.le_of_not_gt fun hn => h ⟨n, hn⟩
  have hrange : Set.range f ⊆ Set.Iic B := by
    rintro y ⟨n, rfl⟩
    exact hbound n
  have hfinite : (Set.range f).Finite := Set.finite_Iic B |>.subset hrange
  exact Set.infinite_range_of_injective hf hfinite

/-- Unbounded primitive prime-order roots cannot all belong to one number field. -/
theorem not_coefficientsConfinedToNumberField_of_unbounded_primitive_prime_roots
    (p : ℕ → ℕ) (u : ℕ → ℂ)
    (hp : ∀ n, (p n).Prime) (hu : ∀ n, IsPrimitiveRoot (u n) (p n))
    (hunbounded : ∀ B, ∃ n, B + 1 < p n) :
    ¬ CoefficientsConfinedToNumberField u := by
  rintro ⟨K, hfinite, hmem⟩
  letI : FiniteDimensional ℚ K := hfinite.some
  obtain ⟨n, hn⟩ := hunbounded (Module.finrank ℚ K)
  have hdegree := prime_sub_one_le_finrank_of_isPrimitiveRoot_mem
    K (hp n) (hu n) (hmem n)
  omega

/-- Pairwise-distinct primitive prime-order roots cannot all belong to one number field. -/
theorem not_coefficientsConfinedToNumberField_of_injective_primitive_prime_roots
    (p : ℕ → ℕ) (u : ℕ → ℂ) (hp_inj : Function.Injective p)
    (hp : ∀ n, (p n).Prime) (hu : ∀ n, IsPrimitiveRoot (u n) (p n)) :
    ¬ CoefficientsConfinedToNumberField u := by
  apply not_coefficientsConfinedToNumberField_of_unbounded_primitive_prime_roots p u hp hu
  intro B
  exact nat_sequence_unbounded_of_injective p hp_inj (B + 1)

/-- Nonzero rational rescaling cannot hide an unbounded primitive-prime cyclotomic tower inside one
number field. -/
theorem not_coefficientsConfinedToNumberField_of_scaled_unbounded_primitive_prime_roots
    (p : ℕ → ℕ) (u : ℕ → ℂ) (r : ℕ → ℚ)
    (hp : ∀ n, (p n).Prime) (hu : ∀ n, IsPrimitiveRoot (u n) (p n))
    (hr : ∀ n, r n ≠ 0) (hunbounded : ∀ B, ∃ n, B + 1 < p n) :
    ¬ CoefficientsConfinedToNumberField (fun n => (r n : ℂ) * u n) := by
  intro hex
  apply not_coefficientsConfinedToNumberField_of_unbounded_primitive_prime_roots
    p u hp hu hunbounded
  obtain ⟨K, hfinite, hcoeff⟩ := hex
  refine ⟨K, hfinite, fun n => ?_⟩
  have hrC : (r n : ℂ) ≠ 0 := by exact_mod_cast hr n
  have hrat : (r n : ℂ) ∈ K := K.algebraMap_mem (r n)
  have hprod := K.mul_mem (K.inv_mem hrat) (hcoeff n)
  simpa [hrC, mul_assoc] using hprod

/-- Exact pairwise-distinct prime-order version used by the coefficient-field escape card. -/
theorem not_coefficientsConfinedToNumberField_of_scaled_injective_primitive_prime_roots
    (p : ℕ → ℕ) (u : ℕ → ℂ) (r : ℕ → ℚ)
    (hp_inj : Function.Injective p) (hp : ∀ n, (p n).Prime)
    (hu : ∀ n, IsPrimitiveRoot (u n) (p n)) (hr : ∀ n, r n ≠ 0) :
    ¬ CoefficientsConfinedToNumberField (fun n => (r n : ℂ) * u n) := by
  apply not_coefficientsConfinedToNumberField_of_scaled_unbounded_primitive_prime_roots
    p u r hp hu hr
  intro B
  exact nat_sequence_unbounded_of_injective p hp_inj (B + 1)

end GaloisForLFunctions.HTGeometry
