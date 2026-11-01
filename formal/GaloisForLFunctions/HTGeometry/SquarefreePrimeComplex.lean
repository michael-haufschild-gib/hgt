import GaloisForLFunctions.RHTower.MertensOddWindowKnapsack
import Mathlib.AlgebraicTopology.SimplicialComplex.Basic

/-!
# The squarefree prime complex and the star of two

The prime-support faces form an abstract simplicial complex. Its augmented
star at two is a cone. Complementary faces are facets with every proper subface in
the star, and correspond exactly to odd squarefree integers in the upper half-window.
-/

set_option autoImplicit false
open Finset
namespace GaloisForLFunctions.HTGeometry
open _root_.RHTower

/-- Membership in the prime-support face family. -/
theorem mem_primeSets_iff {N : ℕ} {S : Finset ℕ} :
    S ∈ primeSets N ↔ (∀ p ∈ S, p.Prime) ∧ ∏ p ∈ S, p ≤ N := by
  simp only [primeSets, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    intro p hp
    apply Finset.mem_range.mpr
    have hpos : 0 < ∏ q ∈ S, q := Finset.prod_pos fun q hq => (h.1 q hq).pos
    have hdiv : p ∣ ∏ q ∈ S, q := Finset.dvd_prod_of_mem (fun q : ℕ => q) hp
    exact Nat.lt_succ_of_le ((Nat.le_of_dvd hpos hdiv).trans h.2)

/-- Prime-support faces are downward closed, including the augmented empty face. -/
theorem primeSets_down_closed {N : ℕ} {S T : Finset ℕ}
    (hS : S ∈ primeSets N) (hTS : T ⊆ S) : T ∈ primeSets N := by
  rw [mem_primeSets_iff] at hS ⊢
  refine ⟨fun p hp => hS.1 p (hTS hp), ?_⟩
  exact (Finset.prod_le_prod_of_subset_of_one_le' hTS
    (fun p hp _ => (hS.1 p hp).one_lt.le)).trans hS.2

/-- The literal nonempty prime-support complex, using mathlib's abstract-complex type. -/
def squarefreePrimeComplex (N : ℕ) : PreAbstractSimplicialComplex ℕ where
  faces := {S | S ∈ primeSets N ∧ S.Nonempty}
  isRelLowerSet_faces := by
    intro S hS
    exact ⟨hS.2, fun T hTS hT => ⟨primeSets_down_closed hS.1 hTS, hT⟩⟩

/-- The augmented star of prime two consists of faces to which two can be adjoined. -/
def primeTwoStar (N : ℕ) : Finset (Finset ℕ) :=
  (primeSets N).filter (fun S => insert 2 S ∈ primeSets N)

/-- For a prime-support face, star membership is exactly closure under adjoining two. -/
theorem mem_primeTwoStar_iff {N : ℕ} {S : Finset ℕ} :
    S ∈ primeTwoStar N ↔ insert 2 S ∈ primeSets N := by
  simp only [primeTwoStar, Finset.mem_filter]
  exact ⟨And.right, fun h => ⟨primeSets_down_closed h (Finset.subset_insert _ _), h⟩⟩

/-- The star is a cone: adjoining its apex preserves membership. -/
theorem insert_two_mem_primeTwoStar_iff {N : ℕ} {S : Finset ℕ} :
    insert 2 S ∈ primeTwoStar N ↔ S ∈ primeTwoStar N := by
  simp only [mem_primeTwoStar_iff, Finset.insert_idem]

/-- Faces outside the star are the odd prime supports in the upper half of the cutoff. -/
theorem primeSets_not_mem_star_iff {N : ℕ} {S : Finset ℕ} (hS : S ∈ primeSets N) :
    S ∉ primeTwoStar N ↔ 2 ∉ S ∧ N < 2 * ∏ p ∈ S, p := by
  rw [mem_primeTwoStar_iff]
  by_cases h2 : 2 ∈ S
  · simp only [Finset.insert_eq_of_mem h2, hS, not_true_eq_false, h2, false_and]
  · rw [mem_primeSets_iff]
    have hp : ∀ p ∈ insert 2 S, p.Prime := by
      intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact Nat.prime_two
      · exact (mem_primeSets_iff.mp hS).1 p hp
    rw [and_iff_right hp, Finset.prod_insert h2, not_le]
    simp only [h2, not_false_eq_true, true_and]

/-- Every proper subface of a complementary face lies in the star of two. -/
theorem proper_subface_mem_primeTwoStar {N : ℕ} {S T : Finset ℕ}
    (hS : S ∈ primeSets N) (hstar : S ∉ primeTwoStar N) (hTS : T ⊂ S) :
    T ∈ primeTwoStar N := by
  obtain ⟨h2, _⟩ := (primeSets_not_mem_star_iff hS).mp hstar
  obtain ⟨p, hpS, hpT⟩ := Finset.exists_of_ssubset hTS
  have hprime := (mem_primeSets_iff.mp hS).1
  have h2T : 2 ∉ T := fun h => h2 (hTS.le h)
  rw [mem_primeTwoStar_iff, mem_primeSets_iff]
  refine ⟨?_, ?_⟩
  · intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact Nat.prime_two
    · exact hprime q (hTS.le hq)
  · rw [Finset.prod_insert h2T]
    have hsub : insert p T ⊆ S := Finset.insert_subset hpS hTS.le
    have hprod := (mem_primeSets_iff.mp (primeSets_down_closed hS hsub)).2
    rw [Finset.prod_insert hpT] at hprod
    exact (Nat.mul_le_mul_right (∏ q ∈ T, q) (hprime p hpS).two_le).trans hprod

/-- A complementary face is a facet: a proper coface would put it in the star. -/
theorem primeSets_outside_star_facet {N : ℕ} {S T : Finset ℕ}
    (_hS : S ∈ primeSets N) (hstar : S ∉ primeTwoStar N)
    (hT : T ∈ primeSets N) (hST : S ⊆ T) : S = T := by
  by_contra hne
  have hproper : S ⊂ T := Finset.ssubset_iff_subset_ne.mpr ⟨hST, hne⟩
  by_cases hTstar : T ∈ primeTwoStar N
  · have hi : insert 2 S ⊆ insert 2 T := Finset.insert_subset_insert 2 hST
    exact hstar (mem_primeTwoStar_iff.mpr (primeSets_down_closed
      (mem_primeTwoStar_iff.mp hTstar) hi))
  · exact hstar (proper_subface_mem_primeTwoStar hT hTstar hproper)

/-- An all-prime product is odd exactly when its support omits two. -/
theorem primeSupport_odd_prod_iff {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    Odd (∏ p ∈ S, p) ↔ 2 ∉ S := by
  constructor
  · intro ho h2
    exact (Nat.not_even_iff_odd.mpr ho)
      (even_iff_two_dvd.mpr (Finset.dvd_prod_of_mem (fun p : ℕ => p) h2))
  · intro h2
    have hodd : ∀ p ∈ S, Odd p := by
      intro p hp
      rcases (hS p hp).eq_two_or_odd' with h | h
      · exact (h2 (h ▸ hp)).elim
      · exact h
    clear hS h2
    revert hodd
    induction S using Finset.induction_on with
    | empty => intro _; norm_num
    | @insert p T hp ih =>
      intro hodd
      rw [Finset.prod_insert hp]
      exact (hodd p (Finset.mem_insert_self _ _)).mul
        (ih (fun q hq => hodd q (Finset.mem_insert_of_mem hq)))

/-- The complementary faces are canonically the odd squarefree integers in the upper half-window. -/
def primeTwoComplementEquiv (N : ℕ) :
    {S : Finset ℕ // S ∈ primeSets N ∧ S ∉ primeTwoStar N} ≃
      {m : ℕ // 1 ≤ m ∧ m ≤ N ∧ Odd m ∧ Squarefree m ∧ N < 2 * m} where
  toFun S := by
    have hS := mem_primeSets_iff.mp S.property.1
    have hstar := (primeSets_not_mem_star_iff S.property.1).mp S.property.2
    refine ⟨∏ p ∈ S.val, p, ?_, hS.2, ?_, ?_, hstar.2⟩
    · exact Finset.prod_pos fun p hp => (hS.1 p hp).pos
    · exact (primeSupport_odd_prod_iff hS.1).mpr hstar.1
    · exact GibbsGas.squarefree_prod_primes hS.1
  invFun m := by
    have hp : ∀ p ∈ m.val.primeFactors, p.Prime :=
      fun p hp => Nat.prime_of_mem_primeFactors hp
    have heq := Nat.prod_primeFactors_of_squarefree m.property.2.2.2.1
    have hface : m.val.primeFactors ∈ primeSets N := by
      apply mem_primeSets_iff.mpr
      refine ⟨hp, ?_⟩
      rw [heq]
      exact m.property.2.1
    refine ⟨m.val.primeFactors, hface, ?_⟩
    apply (primeSets_not_mem_star_iff hface).mpr
    refine ⟨?_, ?_⟩
    · apply (primeSupport_odd_prod_iff hp).mp
      simpa only [heq] using m.property.2.2.1
    · rw [heq]
      exact m.property.2.2.2.2
  left_inv S := by
    apply Subtype.ext
    exact Nat.primeFactors_prod (mem_primeSets_iff.mp S.property.1).1
  right_inv m := by
    apply Subtype.ext
    exact Nat.prod_primeFactors_of_squarefree m.property.2.2.2.1

end GaloisForLFunctions.HTGeometry
