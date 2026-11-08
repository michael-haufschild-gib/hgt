import GaloisForLFunctions.EffectiveScalingGeometry.PrimeTwoPrimeBlockEmbeddings
import GaloisForLFunctions.EffectiveScalingGeometry.PrimeWeightedSquarefreeIndices

/-!
# Squarefree arithmetic labels for large-prime cores

Multiplication bijects finite prime supports omitting two and three with
squarefree integers coprime to six. The bijection retains the exact product
height and sends exterior cardinality to the number of distinct prime factors.
It supplies integer labels for the two branches of weighted homology.
-/

noncomputable section
open RHTower
namespace GaloisForLFunctions.EffectiveScalingGeometry

/-- The height of a large-prime core is squarefree and coprime to six. -/
theorem twoPrimeCoreHeight_arithmetic (c : TwoPrimeCoreFace) :
    Squarefree (twoPrimeCoreHeight c) ∧ Nat.Coprime (twoPrimeCoreHeight c) 6 := by
  let s : Set.powersetCard Nat.Primes c.val.card := ⟨c.val,rfl⟩
  exact ⟨primeFaceProduct_squarefree s,(primeFaceProduct_coprime_six_iff s).mpr c.property⟩

/-- The number of prime factors of a core height is its exterior degree. -/
theorem twoPrimeCoreHeight_degree (c : TwoPrimeCoreFace) :
    (twoPrimeCoreHeight c).primeFactors.card = c.val.card := by
  let s : Set.powersetCard Nat.Primes c.val.card := ⟨c.val,rfl⟩
  exact (congrArg Finset.card (primeFaceProduct_primeFactors s)).trans (primeFaceNumbers_card s)

/-- The arithmetic height uniquely determines its large-prime core. -/
theorem twoPrimeCoreHeight_injective : Function.Injective twoPrimeCoreHeight := by
  intro c d h
  let s : Set.powersetCard Nat.Primes c.val.card := ⟨c.val,rfl⟩
  let t : Set.powersetCard Nat.Primes d.val.card := ⟨d.val,rfl⟩
  apply Subtype.ext
  ext p
  change p ∈ s.val ↔ p ∈ t.val
  rw [← primeFaceNumbers_mem s p,← primeFaceNumbers_mem t p,
    ← primeFaceProduct_primeFactors,← primeFaceProduct_primeFactors]
  change p.val ∈ (twoPrimeCoreHeight c).primeFactors ↔
    p.val ∈ (twoPrimeCoreHeight d).primeFactors
  rw [h]

/-- Squarefree integers coprime to six are exactly the arithmetic core labels. -/
def TwoPrimeArithmeticCore := {m : ℕ // Squarefree m ∧ Nat.Coprime m 6}

/-- Multiplication reindexes all large-prime cores without changing height. -/
def twoPrimeCoreArithmeticEquiv : TwoPrimeCoreFace ≃ TwoPrimeArithmeticCore :=
  Equiv.ofBijective (fun c => ⟨twoPrimeCoreHeight c,twoPrimeCoreHeight_arithmetic c⟩) (by
    constructor
    · intro c d h
      exact twoPrimeCoreHeight_injective (congrArg Subtype.val h)
    · intro m
      let a : SquarefreeDegree m.val.primeFactors.card := ⟨m.val,m.property.1,rfl⟩
      let s := squarefreeDegreeFace m.val.primeFactors.card a
      have hp : primeFaceProduct s=m.val := squarefreeDegreeFace_product _ a
      have hs : primeTwoLabel ∉ s.val ∧ primeThreeLabel ∉ s.val :=
        (primeFaceProduct_coprime_six_iff s).mp (hp.symm ▸ m.property.2)
      exact ⟨⟨s.val,hs⟩,Subtype.ext hp⟩)

theorem twoPrimeCoreArithmeticEquiv_height (c : TwoPrimeCoreFace) :
    (twoPrimeCoreArithmeticEquiv c).val = twoPrimeCoreHeight c := rfl

#print axioms twoPrimeCoreArithmeticEquiv
#print axioms twoPrimeCoreHeight_degree
end GaloisForLFunctions.EffectiveScalingGeometry
