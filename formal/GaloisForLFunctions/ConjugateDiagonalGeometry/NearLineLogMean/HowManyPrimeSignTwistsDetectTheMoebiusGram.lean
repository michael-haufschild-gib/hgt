import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FourthMomentsAndLargeValuesOfBlockCharacters
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.PrimeSignAveragesOfTheMoebiusGram

/-!
# How many prime-sign twists see the primitive Möbius spectrum?

Each occupied squarefree product carries one prime-sign character.
The fourth-moment price of its coefficient is three per prime divisor.
Consequently a measured proportion of completely multiplicative twists
exhibits at least half the mean-square signal of the original spectral
window. The kernel may be signed.
-/

open Finset GaloisForLFunctions.ArithmeticHarmonicAnalysis
open GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
open GaloisForLFunctions.ArithmeticCorrelationGeometry
noncomputable section
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.MoebiusGram

/-- Under this twist exactly the primes in A receive a minus sign. -/
def signsFromPrimeSubset (P A : Finset ℕ) (p : P) : ℤˣ := if (p:ℕ)∈A then -1 else 1

private theorem squarefree_subset_twist {N m : ℕ} (hm : m∈primitiveSignProducts N) (A : Finset ℕ) :
    let P := (range (N+1)).filter Nat.Prime
    primeSignTwist P (signsFromPrimeSubset P A) m=blockCharacter m.primeFactors A := by
  intro P
  let sign (p : ℕ) : ℤ := if p∈A then -1 else 1
  have hs := (mem_filter.mp hm).2
  have point (p : P) : ((signsFromPrimeSubset P A p:ℤˣ):ℤ) = sign p := by
    unfold signsFromPrimeSubset sign
    split <;> rfl
  simp only [primeSignTwist,point]
  rw [prod_coe_sort (s:=P) (f:=fun p : ℕ => sign p ^ m.factorization p)]
  have subset : m.primeFactors⊆P := sign_product_support hm
  rw [←prod_subset (f:=fun p => sign p ^ m.factorization p) subset (fun p _ hp => by
    have e : m.factorization p=0 := by
      simpa only [← Nat.support_factorization,Finsupp.notMem_support_iff] using hp
    rw [e,pow_zero])]
  apply prod_congr rfl
  intro p hp
  have pos : m.factorization p≠0 := by
    simpa only [← Nat.support_factorization,Finsupp.mem_support_iff] using hp
  have le := hs.natFactorization_le_one p
  rw [show m.factorization p=1 by omega,pow_one]

private def modesAtHorizon (N : ℕ) := (primitiveSignProducts N).image Nat.primeFactors

private def moebiusBlockCoefficient (N : ℕ) (K : ℝ → ℝ) (T : Finset ℕ) : ℝ :=
  if T∈modesAtHorizon N then primitiveProductReading N (∏ p ∈ T, p) K else 0

private theorem support_injective {N m n : ℕ} (hm : m∈primitiveSignProducts N)
    (hn : n∈primitiveSignProducts N) (eq : m.primeFactors=n.primeFactors) : m=n := by
  calc m = ∏ p ∈ m.primeFactors, p := (Nat.prod_primeFactors_of_squarefree (mem_filter.mp hm).2).symm
       _ = ∏ p ∈ n.primeFactors, p := by rw [eq]
       _ = n := Nat.prod_primeFactors_of_squarefree (mem_filter.mp hn).2

private theorem sum_mode_support (N : ℕ) (f : Finset ℕ → ℝ) :
    let P := (range (N+1)).filter Nat.Prime
    (∑ T ∈ P.powerset, if T∈modesAtHorizon N then f T else 0) =
      ∑ m ∈ primitiveSignProducts N, f m.primeFactors := by
  intro P
  have subset : modesAtHorizon N⊆P.powerset := by
    intro T hT
    obtain ⟨m,hm,rfl⟩ := mem_image.mp hT
    exact mem_powerset.mpr (sign_product_support hm)
  have he : P.powerset.filter (fun T => T∈modesAtHorizon N)=modesAtHorizon N := by
    ext T
    exact ⟨fun h => (mem_filter.mp h).2,fun h => mem_filter.mpr ⟨subset h,h⟩⟩
  rw [←sum_filter,he,modesAtHorizon,sum_image (fun _ hm _ hn e => support_injective hm hn e)]

/-- Squared strength at rank weight r. At r=1 it is the exact ordinary
second moment; at r=3 it controls the fourth moment. -/
def moebiusProductRankEnergy (N : ℕ) (K : ℝ → ℝ) (r : ℝ) : ℝ :=
  ∑ m ∈ primitiveSignProducts N, r^m.primeFactors.card*(primitiveProductReading N m K)^2

private theorem product_rank_energy (N : ℕ) (K : ℝ → ℝ) (r : ℝ) :
    let P := (range (N+1)).filter Nat.Prime
    blockRankEnergy P r (moebiusBlockCoefficient N K)=moebiusProductRankEnergy N K r := by
  intro P
  let f (T : Finset ℕ) := r^T.card*(primitiveProductReading N (∏ p ∈ T, p) K)^2
  have e T : r^T.card*(moebiusBlockCoefficient N K T)^2 =
      if T∈modesAtHorizon N then f T else 0 := by
    by_cases h : T∈modesAtHorizon N <;> simp [moebiusBlockCoefficient,f,h]
  rw [blockRankEnergy,sum_congr rfl (fun T _ => e T),sum_mode_support]
  apply sum_congr rfl
  intro m hm
  simp only [f,Nat.prod_primeFactors_of_squarefree (mem_filter.mp hm).2]

private theorem subset_synthesis_eq_reading (N : ℕ) (K : ℝ → ℝ) (A : Finset ℕ) :
    let P := (range (N+1)).filter Nat.Prime
    blockSynthesis P (moebiusBlockCoefficient N K) A=signedRatioReading N P (signsFromPrimeSubset P A) K := by
  intro P
  let f (T : Finset ℕ) := primitiveProductReading N (∏ p ∈ T, p) K*(blockCharacter T A:ℝ)
  have e T : moebiusBlockCoefficient N K T*(blockCharacter T A:ℝ) =
      if T∈modesAtHorizon N then f T else 0 := by
    by_cases h : T∈modesAtHorizon N <;> simp [moebiusBlockCoefficient,f,h]
  rw [blockSynthesis,sum_congr rfl (fun T _ => e T),sum_mode_support,signed_product_expansion]
  apply sum_congr rfl
  intro m hm
  have twist : primeSignTwist P (signsFromPrimeSubset P A) m = blockCharacter m.primeFactors A :=
    squarefree_subset_twist hm A
  simp only [f,Nat.prod_primeFactors_of_squarefree (mem_filter.mp hm).2,twist,mul_comm]

/-- At least the squared ratio of ordinary to rank-weighted energy,
divided by four, of all sign masks have a large off-diagonal signal. -/
theorem many_prime_signs_detect_gram (N : ℕ) (K : ℝ → ℝ) :
    let P := (range (N+1)).filter Nat.Prime
    let E := moebiusProductRankEnergy N K 1
    let B := moebiusProductRankEnergy N K 3
    let large := P.powerset.filter (fun A => E/2≤
      (signedRatioReading N P (signsFromPrimeSubset P A) K)^2)
    (2:ℝ)^P.card*E^2 ≤ 4*large.card*B^2 := by
  simpa only [product_rank_energy,subset_synthesis_eq_reading] using
    block_large_value_count ((range (N+1)).filter Nat.Prime) (moebiusBlockCoefficient N K)

/-- A window supported on products of at most q primes is detected at a
dimension-independent proportion of all completely multiplicative twists. -/
theorem many_prime_signs_at_bounded_rank (N q : ℕ) (K : ℝ → ℝ)
    (rank : ∀ m ∈ primitiveSignProducts N, primitiveProductReading N m K≠0 → m.primeFactors.card≤q) :
    let P := (range (N+1)).filter Nat.Prime
    let E := moebiusProductRankEnergy N K 1
    2^P.card ≤ 4*9^q*(P.powerset.filter (fun A => E/2≤
      (signedRatioReading N P (signsFromPrimeSubset P A) K)^2)).card := by
  intro P E
  have degree T (_ : T∈P.powerset) (h : moebiusBlockCoefficient N K T≠0) : T.card≤q := by
    by_cases ht : T∈modesAtHorizon N
    · obtain ⟨m,hm,rfl⟩ := mem_image.mp ht
      apply rank m hm
      simpa only [moebiusBlockCoefficient,if_pos ht,Nat.prod_primeFactors_of_squarefree (mem_filter.mp hm).2] using h
    · exact False.elim (h (if_neg ht))
  simpa only [P,E,product_rank_energy,subset_synthesis_eq_reading] using
    block_low_rank_large_fraction P (moebiusBlockCoefficient N K) q degree

end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.MoebiusGram
