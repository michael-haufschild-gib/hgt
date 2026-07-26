import GaloisForLFunctions.RHTower.XiRootDeletedGaussianGraphicConnector
import GaloisForLFunctions.RHTower.XiTransverseValuationCanonicalReconstruction
import GaloisForLFunctions.HTGeometry.UpperEndDifferentialInstances

/-!
# Root-deleted canonical reconstruction and Xi graphic universality

Deleting a distinguished zero-shift root leaves `N` vertices.  Their first `N` valuation
increments form one fixed square sampling problem, enumerated without choice by `root.succAbove`.
Exact dual coefficient recovery for that one matrix is equivalent to injectivity of the complete
rooted labeling.

This identifies a single prescribed HilbertMetric reconstruction with every cofinite HTGeometry
prime-jet realization, the full Gaussian collision metric at any prime and positive bandwidth,
and the arbitrary-edge differential graphic-network package over both valuation bases.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open scoped ComplexOrder Differential

open scoped UpperEndDifferentialInstances

/-- Exact first-valuation dual reconstruction on every vertex except the distinguished root.
`root.succAbove` gives the canonical enumeration of the `N` nonroot vertices. -/
def XiTransverseRootDeletedPrimeValuationCanonicalReconstruction
    {N : ℕ} (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (p : Nat.Primes) : Prop :=
  XiTransversePrimeValuationCanonicalReconstruction
    (fun j : Fin N => shift (root.succAbove j)) p

/-- **Root-deleted canonical reconstruction classification.**  When the root label is zero, one
fixed nonroot valuation matrix has exact dual coefficient recovery exactly when the complete
vertex labeling is injective, including separation from the deleted root. -/
theorem
    xiTransverseRootDeletedPrimeValuationCanonicalReconstruction_iff_injective
    {N : ℕ} (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (hroot : shift root = 0) (p : Nat.Primes) :
    XiTransverseRootDeletedPrimeValuationCanonicalReconstruction root shift p ↔
      Function.Injective shift := by
  rw [XiTransverseRootDeletedPrimeValuationCanonicalReconstruction,
    xiTransversePrimeValuationCanonicalReconstruction_iff_injective_ne_zero]
  constructor
  · rintro ⟨hinjective, hnonzero⟩ x y hxy
    by_cases hx : x = root
    · subst x
      by_contra hy
      obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq (Ne.symm hy)
      exact hnonzero j (by
        rw [hj]
        exact hxy.symm.trans hroot)
    · by_cases hy : y = root
      · subst y
        obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hx
        exact False.elim (hnonzero i (by
          rw [hi]
          exact hxy.trans hroot))
      · obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hx
        obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hy
        rw [← hi, ← hj] at hxy ⊢
        exact congrArg root.succAbove (hinjective hxy)
  · intro hinjective
    constructor
    · exact hinjective.comp root.succAboveEmb.injective
    · intro j hj
      exact Fin.succAbove_ne root j
        (hinjective (hj.trans hroot.symm))

/-- Root-deleted canonical reconstruction is independent of the prime used for its fixed
valuation sampling matrix. -/
theorem
    xiTransverseRootDeletedPrimeValuationCanonicalReconstruction_prime_invariant
    {N : ℕ} (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (hroot : shift root = 0) (p r : Nat.Primes) :
    XiTransverseRootDeletedPrimeValuationCanonicalReconstruction root shift p ↔
      XiTransverseRootDeletedPrimeValuationCanonicalReconstruction root shift r := by
  rw [
    xiTransverseRootDeletedPrimeValuationCanonicalReconstruction_iff_injective
      root shift hroot p,
    xiTransverseRootDeletedPrimeValuationCanonicalReconstruction_iff_injective
      root shift hroot r]

/-- **Fixed reconstruction/cofinite HTGeometry connector.**  One prescribed nonroot valuation
matrix admits exact dual recovery iff every finite prime deletion still admits a positive
prime-jet Gram realization, at every fixed jet depth. -/
theorem
    xiTransverseRootDeletedPrimeValuationCanonicalReconstruction_iff_cofiniteApertureGram
    {N : ℕ} (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (hroot : shift root = 0) (p : Nat.Primes) (m : ℕ) :
    XiTransverseRootDeletedPrimeValuationCanonicalReconstruction root shift p ↔
      ∀ forbidden : Set Nat.Primes, forbidden.Finite →
        ∃ points : {v : Fin (N + 1) // v ≠ root} × Fin (m + 1) →
            {r : Nat.Primes // r ∉ forbidden},
          (xiTransversePrimeJetApertureGram
            (fun v : {v : Fin (N + 1) // v ≠ root} => shift v)
            m forbidden points).PosDef := by
  calc
    _ ↔ Function.Injective shift :=
      xiTransverseRootDeletedPrimeValuationCanonicalReconstruction_iff_injective
        root shift hroot p
    _ ↔ _ :=
      (xiTransverse_rootDeletedCofiniteApertureGram_iff_injective
        root shift hroot m).symm

/-- **Fixed/deletion-robust reconstruction equivalence.**  Exact recovery from one prescribed
nonroot valuation matrix is equivalent to complete exact dual recovery after every finite prime
deletion, at every fixed jet depth. -/
theorem
    xiTransverseRootDeletedPrimeValuationCanonicalReconstruction_iff_cofiniteApertureHilbertReconstruction
    {N : ℕ} (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (hroot : shift root = 0) (p : Nat.Primes) (m : ℕ) :
    XiTransverseRootDeletedPrimeValuationCanonicalReconstruction root shift p ↔
      XiTransverseRootDeletedPrimeJetApertureCofiniteHilbertReconstruction
        root shift m := by
  rw [
    xiTransverseRootDeletedPrimeValuationCanonicalReconstruction_iff_injective
      root shift hroot p,
    xiTransverseRootDeletedPrimeJetApertureCofiniteHilbertReconstruction_iff_injective
      root shift hroot m]

/-- **Fixed reconstruction/full Gaussian connector.**  At every positive bandwidth, exact
nonroot dual reconstruction at one prime is equivalent to strict positivity of the full Gaussian
collision Gram at any other prime. -/
theorem
    xiTransverseRootDeletedPrimeValuationCanonicalReconstruction_iff_fullGaussianGramAt_posDef
    {N : ℕ} (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (hroot : shift root = 0) (p r : Nat.Primes) {t : ℝ} (ht : 0 < t) :
    XiTransverseRootDeletedPrimeValuationCanonicalReconstruction root shift p ↔
      (xiTransversePrimeFirstValuationGaussianGramMatrixAt shift r t).PosDef := by
  rw [
    xiTransverseRootDeletedPrimeValuationCanonicalReconstruction_iff_injective
      root shift hroot p,
    xiTransversePrimeFirstValuationGaussianGramMatrixAt_posDef_iff_injective
      shift r ht]

/-- Unit-bandwidth form of the fixed-reconstruction/full-Gaussian equivalence. -/
theorem
    xiTransverseRootDeletedPrimeValuationCanonicalReconstruction_iff_fullGaussianGram_posDef
    {N : ℕ} (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (hroot : shift root = 0) (p r : Nat.Primes) :
    XiTransverseRootDeletedPrimeValuationCanonicalReconstruction root shift p ↔
      (xiTransversePrimeFirstValuationGaussianGramMatrix shift r).PosDef := by
  simpa only [xiTransversePrimeFirstValuationGaussianGramMatrix] using
    xiTransverseRootDeletedPrimeValuationCanonicalReconstruction_iff_fullGaussianGramAt_posDef
      root shift hroot p r (by norm_num : (0 : ℝ) < 1)

/-- **Canonical-reconstruction discharge of Xi graphic universality.**  One fixed square dual
reconstruction on the nonroot shifts is equivalent to complete rooted-incidence realization of
every chosen edge family over both differential bases, together with base invariance. -/
theorem
    xiTransverseRootDeletedPrimeValuationCanonicalReconstruction_iff_graphicNetworkUniversality
    {N : ℕ} {E : Type} [Fintype E] [DecidableEq E]
    (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (hroot : shift root = 0) (tail head : E → Fin (N + 1))
    (p : Nat.Primes) :
    XiTransverseRootDeletedPrimeValuationCanonicalReconstruction root shift p ↔
      Function.Injective shift ∧
        differentialFamilyMatroid
            (F := upperEndRationalCoordinateField)
            (xiTransverseShiftPairDifferenceUpperEndCarrier shift tail head) =
          rootedIncidenceMatroid
            (C := upperEndRationalCoordinateField) root tail head ∧
        differentialFamilyMatroid
            (F := analyticScalarValuationLayerDifferentialField)
            (xiTransverseShiftPairDifferenceUpperEndCarrier shift tail head) =
          rootedIncidenceMatroid
            (C := analyticScalarValuationLayerDifferentialField) root tail head ∧
        differentialFamilyMatroid
            (F := upperEndRationalCoordinateField)
            (xiTransverseShiftPairDifferenceUpperEndCarrier shift tail head) =
          differentialFamilyMatroid
            (F := analyticScalarValuationLayerDifferentialField)
            (xiTransverseShiftPairDifferenceUpperEndCarrier shift tail head) := by
  calc
    _ ↔
        (xiTransversePrimeFirstValuationGaussianGramMatrix shift p).PosDef :=
      xiTransverseRootDeletedPrimeValuationCanonicalReconstruction_iff_fullGaussianGram_posDef
        root shift hroot p p
    _ ↔ _ :=
      xiTransverse_fullGaussianGram_posDef_iff_graphicNetworkUniversality
        root shift hroot tail head p

end

end RHTower
