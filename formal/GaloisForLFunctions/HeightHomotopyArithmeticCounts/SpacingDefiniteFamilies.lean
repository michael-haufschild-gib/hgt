import GaloisForLFunctions.HeightHomotopyArithmeticCounts.TorsionPrimePairProbes
import GaloisForLFunctions.HTGeometry.CofinitePacketCriterion

/-!
# Arbitrarily large definite families of torsion probes

Distinct odd-prime pairs have disjoint arithmetic interaction. Their eventual
negative energy and the positive prime diagonals give orthogonal families of
both signs in every positive conductor weight. Finite synthesis retains their
exact diagonal quadratic form.
-/

noncomputable section
open Finset Filter
namespace GaloisForLFunctions.HeightHomotopyArithmeticCounts
open ArithmeticIntersectionTheory

/-- Any prescribed finite number of distinct primes can lie beyond any conductor cutoff. -/
theorem spacing_exists_prime_family (N m : ℕ) :
    ∃ q : Fin (m+1) → Nat.Primes, Function.Injective q ∧ ∀ i, N≤(q i).val := by
  have hfin : {p : Nat.Primes | p.val<N}.Finite :=
    (Set.finite_Iio N).preimage (Set.injOn_of_injective Subtype.val_injective)
  have hinf : {p : Nat.Primes | N≤p.val}.Infinite := by
    have hi := (Set.infinite_univ (α:=Nat.Primes)).sdiff hfin
    have he : (Set.univ \ {p : Nat.Primes | p.val<N}) = {p : Nat.Primes | N≤p.val} := by
      ext p
      simp only [Set.mem_sdiff,Set.mem_univ,true_and,Set.mem_setOf_eq,not_lt]
    rw [he] at hi
    exact hi
  exact HTGeometry.exists_injective_primes_mem m hinf

/-- Negative prime-pair probes occur in arbitrary finite orthogonal families. -/
theorem spacing_exists_negative_family (δ : ℝ) (hδ : 0<δ) (m : ℕ) :
    ∃ u : Fin (m+1) → WeightedProbe δ,
      (∀ i, spacingLimitOperator δ hδ (u i) (u i)<0) ∧
      ∀ i j, i≠j → spacingLimitOperator δ hδ (u i) (u j)=0 := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp eventually_spacingPrimePair_energy_neg
  obtain ⟨q,hq,hbound⟩ := spacing_exists_prime_family (max N 3) m
  have h2 (i) : 2<(q i).val := lt_of_lt_of_le (by omega : 2<3)
    ((le_max_right N 3).trans (hbound i))
  refine ⟨fun i => spacingPrimePairProbe δ (q i),?_,?_⟩
  · intro i
    rw [spacingPrimePairProbe_energy δ hδ (q i) (h2 i),
      spacing_tameDifferent_prime (q i).val (q i).property]
    exact hN _ ((le_max_left N 3).trans (hbound i))
  · intro i j hij
    exact spacingPrimePairProbe_orthogonal δ hδ (q i) (q j) (h2 i) (h2 j)
      (fun h => hij (hq h))

/-- Positive prime probes occur in arbitrary finite orthogonal families. -/
theorem spacing_exists_positive_family (δ : ℝ) (hδ : 0<δ) (m : ℕ) :
    ∃ u : Fin (m+1) → WeightedProbe δ,
      (∀ i, 0<spacingLimitOperator δ hδ (u i) (u i)) ∧
      ∀ i j, i≠j → spacingLimitOperator δ hδ (u i) (u j)=0 := by
  obtain ⟨q,hq,hbound⟩ := spacing_exists_prime_family 3 m
  refine ⟨fun i => spacingPrimeProbe δ (q i),fun i => spacingPrimeProbe_energy_pos δ hδ (q i),?_⟩
  intro i j hij
  exact spacingPrimeProbe_orthogonal δ hδ (q i) (q j) (by have h:=hbound i; omega)
    (by have h:=hbound j; omega) (fun h => hij (hq h))

/-- Finite synthesis of actual Hilbert probes. -/
def spacingProbeSynthesis {ι : Type*} [Fintype ι] (δ : ℝ)
    (u : ι → WeightedProbe δ) : (ι → ℝ) →ₗ[ℝ] WeightedProbe δ where
  toFun a := ∑ i, a i • u i
  map_add' a b := by simp only [Pi.add_apply,add_smul,sum_add_distrib]
  map_smul' c a := by simp only [Pi.smul_apply,smul_eq_mul,smul_smul,Finset.smul_sum,RingHom.id_apply]

/-- Orthogonal arithmetic probes give an exact diagonal quadratic form on coefficients. -/
theorem spacingProbeSynthesis_energy {ι : Type*} [Fintype ι] (δ : ℝ) (hδ : 0<δ)
    (u : ι → WeightedProbe δ)
    (horth : ∀ i j, i≠j → spacingLimitOperator δ hδ (u i) (u j)=0) (a : ι → ℝ) :
    spacingLimitOperator δ hδ (spacingProbeSynthesis δ u a) (spacingProbeSynthesis δ u a) =
      ∑ i, (a i)^2*spacingLimitOperator δ hδ (u i) (u i) := by
  classical
  change spacingLimitOperator δ hδ (∑ i, a i • u i) (∑ j, a j • u j)=_
  simp only [map_sum,_root_.sum_apply,map_smul,smul_apply,
    smul_eq_mul,mul_sum]
  apply sum_congr rfl
  intro i hi
  rw [sum_eq_single i]
  · ring
  · intro j hj hji
    rw [horth j i hji,mul_zero,mul_zero]
  · exact fun h => (h (mem_univ i)).elim

#print axioms spacing_exists_prime_family
#print axioms spacing_exists_negative_family
#print axioms spacing_exists_positive_family
#print axioms spacingProbeSynthesis_energy
end GaloisForLFunctions.HeightHomotopyArithmeticCounts
