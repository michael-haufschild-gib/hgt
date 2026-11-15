import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Torus.PairedBranchContraction

/-!
# Minimal primes and irreducible components for arbitrary neutral ideals

For any ideal `J` of `K[hᵢ]`, the minimal primes of its extension under
`hᵢ ↦ zᵢwᵢ` are indexed by a minimal prime `P` over `J`, together with one
binary choice for each coordinate satisfying `hᵢ ∈ P`.

Contraction recovers `P` exactly. To prove exhaustiveness, choose a minimal
neutral prime below the contraction of a paired minimal prime, then a branch
inside that paired prime. Minimality forces equality. Conversely, contraction
reduces minimality of a branch to the already known prime-neutral case.

This gives canonical equivalences with native minimal primes and irreducible
components, identifies each fiber of prime contraction, and expresses the
radical of the extended ideal as the intersection of all these branches.
The neutral ideal need not be prime, radical, or proper.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open MvPolynomial Module Classical
variable {ι : Type*} [Fintype ι] (K : Type*) [Field K]

/-- A branch over a minimal neutral prime is minimal over the original extended ideal. -/
theorem pairedBranchIdeal_mem_minimalPrimes_of_neutral (J P : Ideal (MvPolynomial ι K))
    (hP : P ∈ J.minimalPrimes) (ε : ι → Bool) :
    pairedBranchIdeal K P ε ∈ (J.map (invariantSubstitution K)).minimalPrimes := by
  letI := hP.isPrime
  refine ⟨⟨pairedBranchIdeal_isPrime K P ε,
    (Ideal.map_mono hP.le).trans (extended_le_pairedBranchIdeal K P ε)⟩, ?_⟩
  intro Q hQ hle
  letI := hQ.1
  have hc : Q.comap (invariantSubstitution K) ≤ P := by
    have h := Ideal.comap_mono hle (f := invariantSubstitution K)
    rw [pairedBranchIdeal_comap] at h
    exact h
  have hPq : P ≤ Q.comap (invariantSubstitution K) :=
    hP.2 ⟨inferInstance, Ideal.map_le_iff_le_comap.mp hQ.2⟩ hc
  exact (pairedBranchIdeal_mem_minimalPrimes K P ε).2
    ⟨hQ.1, Ideal.map_le_iff_le_comap.mpr hPq⟩ hle

/-- Every paired minimal prime is a branch over some minimal neutral prime. -/
theorem exists_pairedMinimalBranch_of_minimalPrime (J : Ideal (MvPolynomial ι K))
    (Q : Ideal (MvPolynomial (ι ⊕ ι) K))
    (hQ : Q ∈ (J.map (invariantSubstitution K)).minimalPrimes) :
    ∃ P : J.minimalPrimes, ∃ ε : PairedZeroCoordinate K P.1 → Bool,
      pairedMinimalBranchIdeal K P.1 ε = Q := by
  letI := hQ.isPrime
  obtain ⟨P, hP, hPQ⟩ := Ideal.exists_minimalPrimes_le
    (Ideal.map_le_iff_le_comap.mp hQ.le)
  letI := hP.isPrime
  obtain ⟨ε, hε⟩ := exists_pairedBranchIdeal_le K P Q
    (Ideal.map_le_iff_le_comap.mpr hPQ)
  have hm := pairedBranchIdeal_mem_minimalPrimes_of_neutral K J P hP ε
  have he : pairedBranchIdeal K P ε = Q :=
    le_antisymm hε (hQ.2 hm.1 hε)
  exact ⟨⟨P, hP⟩, fun i => ε i.1,
    (pairedBranchIdeal_eq_minimalBranch K P ε).symm.trans he⟩

/-- A minimal neutral prime together with orientations on its vanishing coordinates. -/
def PairedMinimalBranchIndex (J : Ideal (MvPolynomial ι K)) :=
  Σ P : J.minimalPrimes, PairedZeroCoordinate K P.1 → Bool

/-- The prime branch selected by a minimal neutral prime and its coordinate orientations. -/
def pairedGeneralMinimalBranchIdeal (J : Ideal (MvPolynomial ι K))
    (b : PairedMinimalBranchIndex K J) : Ideal (MvPolynomial (ι ⊕ ι) K) :=
  pairedMinimalBranchIdeal K b.1.1 b.2

/-- Contraction recovers the neutral minimal prime in the branch index. -/
theorem pairedGeneralMinimalBranchIdeal_comap (J : Ideal (MvPolynomial ι K))
    (b : PairedMinimalBranchIndex K J) :
    (pairedGeneralMinimalBranchIdeal K J b).comap (invariantSubstitution K) = b.1.1 :=
  pairedMinimalBranchIdeal_comap K b.1.1 b.2

/-- Neutral contraction and orientation uniqueness distinguish every branch index. -/
theorem pairedGeneralMinimalBranchIdeal_injective (J : Ideal (MvPolynomial ι K)) :
    Function.Injective (pairedGeneralMinimalBranchIdeal K J) := by
  rintro ⟨⟨P, hP⟩, ε⟩ ⟨⟨Q, hQ⟩, δ⟩ he
  have hPQ := congrArg (fun I : Ideal (MvPolynomial (ι ⊕ ι) K) =>
    I.comap (invariantSubstitution K)) he
  rw [pairedGeneralMinimalBranchIdeal_comap, pairedGeneralMinimalBranchIdeal_comap] at hPQ
  dsimp at hPQ
  subst Q
  letI := hP.isPrime
  have hεδ : ε = δ := pairedMinimalBranchIdeal_injective K P he
  subst δ
  rfl

/-- The indexed branches are exactly the native minimal primes of the paired extension. -/
theorem pairedGeneralMinimalPrimes_eq_range (J : Ideal (MvPolynomial ι K)) :
    (J.map (invariantSubstitution K)).minimalPrimes =
      Set.range (pairedGeneralMinimalBranchIdeal K J) := by
  ext Q
  constructor
  · intro hQ
    obtain ⟨P, ε, he⟩ := exists_pairedMinimalBranch_of_minimalPrime K J Q hQ
    exact ⟨⟨P, ε⟩, he⟩
  · rintro ⟨⟨P, ε⟩, rfl⟩
    exact pairedBranchIdeal_mem_minimalPrimes_of_neutral K J P.1 P.2
      (extendPairedBranch K P.1 ε)

/-- Intersecting all minimal neutral branches recovers the radical of the extended ideal. -/
theorem iInf_pairedGeneralMinimalBranchIdeal (J : Ideal (MvPolynomial ι K)) :
    (⨅ b : PairedMinimalBranchIndex K J, pairedGeneralMinimalBranchIdeal K J b) =
      (J.map (invariantSubstitution K)).radical := by
  rw [← sInf_range, ← pairedGeneralMinimalPrimes_eq_range, Ideal.sInf_minimalPrimes]

/-- Minimal paired primes are canonically classified by minimal neutral primes and binary choices. -/
def pairedGeneralMinimalPrimeEquiv (J : Ideal (MvPolynomial ι K)) :
    PairedMinimalBranchIndex K J ≃ (J.map (invariantSubstitution K)).minimalPrimes :=
  Equiv.ofBijective
    (fun b => ⟨pairedGeneralMinimalBranchIdeal K J b,
      pairedBranchIdeal_mem_minimalPrimes_of_neutral K J b.1.1 b.1.2
        (extendPairedBranch K b.1.1 b.2)⟩)
    ⟨fun _ _ he => pairedGeneralMinimalBranchIdeal_injective K J (congrArg Subtype.val he), by
      intro Q
      obtain ⟨P, ε, he⟩ := exists_pairedMinimalBranch_of_minimalPrime K J Q.1 Q.2
      exact ⟨⟨P, ε⟩, Subtype.ext he⟩⟩

/-- The classification sends ideal contraction to the first projection of the branch index. -/
theorem pairedGeneralMinimalPrimeEquiv_comap (J : Ideal (MvPolynomial ι K))
    (b : PairedMinimalBranchIndex K J) :
    (pairedGeneralMinimalPrimeEquiv K J b).1.comap (invariantSubstitution K) = b.1.1 :=
  pairedGeneralMinimalBranchIdeal_comap K J b

/-- Contracting a minimal paired prime gives a minimal neutral prime. -/
theorem pairedMinimalPrime_comap_mem (J : Ideal (MvPolynomial ι K))
    (Q : (J.map (invariantSubstitution K)).minimalPrimes) :
    Q.1.comap (invariantSubstitution K) ∈ J.minimalPrimes := by
  obtain ⟨b, rfl⟩ := (pairedGeneralMinimalPrimeEquiv K J).surjective Q
  rw [pairedGeneralMinimalPrimeEquiv_comap]
  exact b.1.2

/-- Actual ideal contraction, restricted to native minimal-prime sets. -/
def pairedMinimalPrimeContraction (J : Ideal (MvPolynomial ι K))
    (Q : (J.map (invariantSubstitution K)).minimalPrimes) : J.minimalPrimes :=
  ⟨Q.1.comap (invariantSubstitution K), pairedMinimalPrime_comap_mem K J Q⟩

/-- Under the canonical classification, contraction is the neutral-prime projection. -/
theorem pairedMinimalPrimeContraction_equiv (J : Ideal (MvPolynomial ι K))
    (b : PairedMinimalBranchIndex K J) :
    pairedMinimalPrimeContraction K J (pairedGeneralMinimalPrimeEquiv K J b) = b.1 :=
  Subtype.ext (pairedGeneralMinimalPrimeEquiv_comap K J b)

/-- Every minimal neutral prime has a minimal paired prime above it. -/
theorem pairedMinimalPrimeContraction_surjective (J : Ideal (MvPolynomial ι K)) :
    Function.Surjective (pairedMinimalPrimeContraction K J) := by
  intro P
  exact ⟨pairedGeneralMinimalPrimeEquiv K J ⟨P, fun _ => true⟩,
    pairedMinimalPrimeContraction_equiv K J ⟨P, fun _ => true⟩⟩

/-- The fiber above a minimal neutral prime consists exactly of its binary coordinate choices. -/
def pairedMinimalPrimeFiberEquiv (J : Ideal (MvPolynomial ι K)) (P : J.minimalPrimes) :
    (PairedZeroCoordinate K P.1 → Bool) ≃
      {Q : (J.map (invariantSubstitution K)).minimalPrimes //
        Q.1.comap (invariantSubstitution K) = P.1} := by
  letI := P.2.isPrime
  refine Equiv.ofBijective
    (fun ε => ⟨⟨pairedMinimalBranchIdeal K P.1 ε,
      pairedBranchIdeal_mem_minimalPrimes_of_neutral K J P.1 P.2
        (extendPairedBranch K P.1 ε)⟩, pairedMinimalBranchIdeal_comap K P.1 ε⟩) ⟨?_, ?_⟩
  · intro ε δ h
    apply pairedMinimalBranchIdeal_injective K P.1
    exact congrArg (fun Q => Q.1.1) h
  · rintro ⟨Q, hQ⟩
    obtain ⟨⟨P', hP'⟩, ε, he⟩ := exists_pairedMinimalBranch_of_minimalPrime K J Q.1 Q.2
    have hbase : P' = P.1 := by
      calc
        P' = (pairedMinimalBranchIdeal K P' ε).comap (invariantSubstitution K) :=
          (pairedMinimalBranchIdeal_comap K P' ε).symm
        _ = Q.1.comap (invariantSubstitution K) := congrArg
          (fun I : Ideal (MvPolynomial (ι ⊕ ι) K) => I.comap (invariantSubstitution K)) he
        _ = P.1 := hQ
    subst P'
    exact ⟨ε, Subtype.ext (Subtype.ext he)⟩

/-- The same branch indices canonically classify the native Zariski irreducible components. -/
def pairedGeneralIrreducibleComponentsEquiv (J : Ideal (MvPolynomial ι K)) :
    PairedMinimalBranchIndex K J ≃ irreducibleComponents (PrimeSpectrum.zeroLocus
      ((J.map (invariantSubstitution K)) : Set (MvPolynomial (ι ⊕ ι) K))) :=
  (pairedGeneralMinimalPrimeEquiv K J).trans
    (Ideal.minimalPrimes.equivIrreducibleComponents (J.map (invariantSubstitution K))).toEquiv

end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedGeneralMinimalPrimeEquiv
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.iInf_pairedGeneralMinimalBranchIdeal
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedGeneralMinimalPrimeEquiv_comap
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedMinimalPrime_comap_mem
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedMinimalPrimeContraction_surjective
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedMinimalPrimeFiberEquiv
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedGeneralIrreducibleComponentsEquiv
