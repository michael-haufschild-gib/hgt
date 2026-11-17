import GaloisForLFunctions.HilbertMetric.QuantumInformation.ExteriorReflection
import GaloisForLFunctions.HTGeometry.StabilizerSignOrthogonality

/-!
# Orthogonality of exterior reflection characters

Exterior reflection traces are sums of the existing subset sign characters.
Their orthogonality over all sign patterns has squared norm equal to the
number of patterns times the dimension of the particle sector. The same
identity is an exact Krawtchouk coefficient orthogonality law.
-/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace GaloisForLFunctions.HilbertMetric.ExteriorReflection
open HTGeometry _root_.RHTower _root_.RHTower.ParityForecast

/-- Negative one-particle coordinates selected by a binary sign pattern. -/
def negativeCoordinates {r : ℕ} (ε : Fin r → ZMod 2) : Finset (Fin r) :=
  Finset.univ.filter (fun i => ε i = 1)

/-- Trace of the actual exterior reflection associated with a binary sign pattern. -/
def sectorCharacter {r : ℕ} (ε : Fin r → ZMod 2) (k : ℕ) : ℂ :=
  LinearMap.trace ℂ (⋀[ℂ]^k (FiniteIndexClockSpace (Fin r)))
    (exteriorPower.map k (signOperator (negativeCoordinates ε)))

private theorem signOf_subset_sum {r : ℕ} (ε : Fin r → ZMod 2) (T : Finset (Fin r)) :
    signOf (∑ i ∈ T, ε i) = ∏ i ∈ T, signOf (ε i) := by
  classical
  induction T using Finset.induction with
  | empty => simp [signOf]
  | insert i T hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, signOf_add, ih]

/-- The exterior trace is the sum of subset characters of the prescribed particle number. -/
theorem sectorCharacter_eq_subsetSum {r : ℕ} (ε : Fin r → ZMod 2) (k : ℕ) :
    sectorCharacter ε k =
      ∑ T : Set.powersetCard (Fin r) k, signOf (∑ i ∈ T.val, ε i) := by
  rw [sectorCharacter, exterior_signOperator_trace]
  apply Finset.sum_congr rfl
  intro T _
  rw [signOf_subset_sum]
  apply Finset.prod_congr rfl
  intro i _
  rcases zmodTwo_cases (ε i) with hi | hi <;>
    simp [negativeCoordinates, signOf, hi]

/-- Exterior reflection characters are real, so their product orthogonality is Hermitian orthogonality. -/
theorem conj_sectorCharacter {r : ℕ} (ε : Fin r → ZMod 2) (k : ℕ) :
    conj (sectorCharacter ε k) = sectorCharacter ε k := by
  rw [sectorCharacter_eq_subsetSum]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro T _
  by_cases h : (∑ i ∈ T.val, ε i) = 0 <;> simp [signOf, h]

private theorem sector_dimension (r k : ℕ) :
    Fintype.card (Set.powersetCard (Fin r) k) = r.choose k := by
  rw [← Nat.card_eq_fintype_card, Set.powersetCard.card]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin]

/-- Distinct particle sectors are orthogonal over all binary reflections, with exact binomial norms. -/
theorem sectorCharacter_orthogonality (r k l : ℕ) :
    (∑ ε : Fin r → ZMod 2, sectorCharacter ε k * sectorCharacter ε l) =
      if k = l then (2 : ℂ) ^ r * (r.choose k : ℂ) else 0 := by
  classical
  simp_rw [sectorCharacter_eq_subsetSum, Finset.sum_mul, Finset.mul_sum]
  have hswap :
      (∑ ε : Fin r → ZMod 2, ∑ T : Set.powersetCard (Fin r) k,
        ∑ U : Set.powersetCard (Fin r) l,
          signOf (∑ i ∈ T.val, ε i) * signOf (∑ i ∈ U.val, ε i)) =
      ∑ T : Set.powersetCard (Fin r) k, ∑ U : Set.powersetCard (Fin r) l,
        ∑ ε : Fin r → ZMod 2,
          signOf (∑ i ∈ T.val, ε i) * signOf (∑ i ∈ U.val, ε i) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro T _
    exact Finset.sum_comm
  rw [hswap]
  simp_rw [sum_signOf_subsetSum_mul]
  by_cases hkl : k = l
  · subst l
    simp only [Subtype.val_inj, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      sector_dimension]
    ring
  · rw [if_neg hkl]
    apply Finset.sum_eq_zero
    intro T _
    apply Finset.sum_eq_zero
    intro U _
    apply if_neg
    intro hTU
    apply hkl
    exact T.prop.symm.trans ((congrArg Finset.card hTU).trans U.prop)

/-- The character is an actual Krawtchouk coefficient indexed by negative reflection multiplicity. -/
theorem sectorCharacter_eq_krawtchouk {r : ℕ} (ε : Fin r → ZMod 2) (k : ℕ) :
    sectorCharacter ε k =
      ((1 - Polynomial.X : Polynomial ℂ) ^ (negativeCoordinates ε).card *
        (1 + Polynomial.X) ^ (r - (negativeCoordinates ε).card)).coeff k :=
  exterior_signOperator_trace_krawtchouk (negativeCoordinates ε) k

/-- Exact orthogonality of the Krawtchouk coefficients realized by all actual sign involutions. -/
theorem krawtchouk_coefficient_orthogonality (r k l : ℕ) :
    (∑ ε : Fin r → ZMod 2,
      (((1 - Polynomial.X : Polynomial ℂ) ^ (negativeCoordinates ε).card *
        (1 + Polynomial.X) ^ (r - (negativeCoordinates ε).card)).coeff k) *
      (((1 - Polynomial.X : Polynomial ℂ) ^ (negativeCoordinates ε).card *
        (1 + Polynomial.X) ^ (r - (negativeCoordinates ε).card)).coeff l)) =
      if k = l then (2 : ℂ) ^ r * (r.choose k : ℂ) else 0 := by
  simpa only [sectorCharacter_eq_krawtchouk] using sectorCharacter_orthogonality r k l

#print axioms sectorCharacter_eq_subsetSum
#print axioms conj_sectorCharacter
#print axioms sectorCharacter_orthogonality
#print axioms sectorCharacter_eq_krawtchouk
#print axioms krawtchouk_coefficient_orthogonality
end GaloisForLFunctions.HilbertMetric.ExteriorReflection
