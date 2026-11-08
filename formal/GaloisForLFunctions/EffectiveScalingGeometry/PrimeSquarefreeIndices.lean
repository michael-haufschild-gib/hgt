import GaloisForLFunctions.EffectiveScalingGeometry.PrimeCriticalCoordinates
import GaloisForLFunctions.HTGeometry.SquarefreePrimeComplex

/-!
# Squarefree integer labels for exterior prime faces

Multiplication identifies prime supports of cardinality `k` with squarefree
integers having exactly `k` distinct prime factors. The inverse takes the prime
divisor set and retains its prime-label proofs. Odd supports are exactly odd
products, and the equivalence preserves the critical interval `m ≤ N < 2m`.
These canonical labels reindex persistence without changing its height maps.
-/

noncomputable section
open RHTower
namespace GaloisForLFunctions.EffectiveScalingGeometry
attribute [local instance] primeLabelLinearOrder

/-- Forgetting the primality proof is an embedding of prime labels. -/
def primeLabelValueEmbedding : Nat.Primes ↪ ℕ :=
  ⟨fun p => p.val,Subtype.val_injective⟩

/-- The natural-number support of an exterior prime face. -/
def primeFaceNumbers {k : ℕ} (s : Set.powersetCard Nat.Primes k) : Finset ℕ :=
  s.val.map primeLabelValueEmbedding

theorem primeFaceNumbers_prime {k : ℕ} (s : Set.powersetCard Nat.Primes k) :
    ∀ p ∈ primeFaceNumbers s, p.Prime := by
  intro p hp
  obtain ⟨q,_,rfl⟩ := Finset.mem_map.mp hp
  exact q.property

theorem primeFaceNumbers_prod {k : ℕ} (s : Set.powersetCard Nat.Primes k) :
    (∏ p ∈ primeFaceNumbers s, p) = primeFaceProduct s := by
  rw [primeFaceNumbers,Finset.prod_map]
  rfl

theorem primeFaceNumbers_card {k : ℕ} (s : Set.powersetCard Nat.Primes k) :
    (primeFaceNumbers s).card = k := (Finset.card_map _).trans s.property

theorem primeFaceNumbers_mem {k : ℕ} (s : Set.powersetCard Nat.Primes k) (p : Nat.Primes) :
    p.val ∈ primeFaceNumbers s ↔ p ∈ s.val := by
  constructor
  · intro h
    obtain ⟨q,hq,he⟩ := Finset.mem_map.mp h
    have hqp : q = p := Subtype.ext he
    simpa only [hqp] using hq
  · intro h
    exact Finset.mem_map.mpr ⟨p,h,rfl⟩

theorem primeFaceProduct_primeFactors {k : ℕ} (s : Set.powersetCard Nat.Primes k) :
    (primeFaceProduct s).primeFactors = primeFaceNumbers s := by
  rw [← primeFaceNumbers_prod]
  exact Nat.primeFactors_prod (primeFaceNumbers_prime s)

theorem primeFaceProduct_injective (k : ℕ) :
    Function.Injective (primeFaceProduct (k := k)) := by
  intro s t h
  have he : primeFaceNumbers s = primeFaceNumbers t := by
    rw [← primeFaceProduct_primeFactors,← primeFaceProduct_primeFactors,h]
  apply Subtype.ext
  ext p
  rw [← primeFaceNumbers_mem s p,he,primeFaceNumbers_mem t p]

/-- Squarefree integers with a fixed number of distinct prime factors. -/
def SquarefreeDegree (k : ℕ) := {m : ℕ // Squarefree m ∧ m.primeFactors.card = k}

theorem primeFaceProduct_squarefree {k : ℕ} (s : Set.powersetCard Nat.Primes k) :
    Squarefree (primeFaceProduct s) := by
  rw [← primeFaceNumbers_prod]
  exact RHTower.GibbsGas.squarefree_prod_primes (primeFaceNumbers_prime s)

/-- Prime divisors carry their canonical prime-label proofs. -/
def primeFactorsLabelEmbedding (m : ℕ) : {p : ℕ // p ∈ m.primeFactors} ↪ Nat.Primes :=
  ⟨fun p => ⟨p.val,Nat.prime_of_mem_primeFactors p.property⟩,
    fun _ _ h => Subtype.ext (congrArg (fun z : Nat.Primes => z.val) h)⟩

/-- The prime divisors of a squarefree integer as a face of prime labels. -/
def squarefreeDegreeFace (k : ℕ) (m : SquarefreeDegree k) : Set.powersetCard Nat.Primes k :=
  ⟨m.val.primeFactors.attach.map (primeFactorsLabelEmbedding m.val),
    (Finset.card_map _).trans (Finset.card_attach.trans m.property.2)⟩

theorem squarefreeDegreeFace_numbers (k : ℕ) (m : SquarefreeDegree k) :
    primeFaceNumbers (squarefreeDegreeFace k m) = m.val.primeFactors := by
  unfold primeFaceNumbers squarefreeDegreeFace
  rw [Finset.map_map]
  exact Finset.attach_map_val

theorem squarefreeDegreeFace_product (k : ℕ) (m : SquarefreeDegree k) :
    primeFaceProduct (squarefreeDegreeFace k m) = m.val := by
  rw [← primeFaceNumbers_prod,squarefreeDegreeFace_numbers]
  exact Nat.prod_primeFactors_of_squarefree m.property.1

/-- Finite prime supports and squarefree integers have the same degree and product. -/
def primeFaceSquarefreeEquiv (k : ℕ) : Set.powersetCard Nat.Primes k ≃ SquarefreeDegree k where
  toFun s := ⟨primeFaceProduct s,primeFaceProduct_squarefree s,
    (congrArg Finset.card (primeFaceProduct_primeFactors s)).trans (primeFaceNumbers_card s)⟩
  invFun := squarefreeDegreeFace k
  left_inv _ := primeFaceProduct_injective k (squarefreeDegreeFace_product k _)
  right_inv m := Subtype.ext (squarefreeDegreeFace_product k m)

theorem primeFaceProduct_odd_iff {k : ℕ} (s : Set.powersetCard Nat.Primes k) :
    Odd (primeFaceProduct s) ↔ primeTwoLabel ∉ s.val := by
  rw [← primeFaceNumbers_prod,HTGeometry.primeSupport_odd_prod_iff (primeFaceNumbers_prime s)]
  exact not_congr (primeFaceNumbers_mem s primeTwoLabel)

/-- Arithmetic interval labels alive at the specified height. -/
def squarefreeCriticalLabels (k N : ℕ) : Set (SquarefreeDegree k) :=
  {m | Odd m.val ∧ m.val ≤ N ∧ N < 2*m.val}

theorem primeFaceSquarefreeEquiv_critical (k N : ℕ) (s : Set.powersetCard Nat.Primes k) :
    primeFaceSquarefreeEquiv k s ∈ squarefreeCriticalLabels k N ↔ s ∈ primeCriticalFaces k N := by
  change Odd (primeFaceProduct s) ∧ primeFaceProduct s ≤ N ∧ N < 2*primeFaceProduct s ↔ _
  rw [primeFaceProduct_odd_iff]
  change (_ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _)
  tauto

#print axioms primeFaceSquarefreeEquiv
#print axioms primeFaceSquarefreeEquiv_critical
end GaloisForLFunctions.EffectiveScalingGeometry
