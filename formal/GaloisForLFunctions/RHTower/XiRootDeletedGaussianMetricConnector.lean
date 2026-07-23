import GaloisForLFunctions.RHTower.XiTransverseGaussianDifferentialMatroidConnector

/-!
# Root-deleted Xi prime metrics and the full Gaussian collision metric

Deleting a distinguished zero-shift root turns the transverse prime-jet metric into an exact
certificate for injectivity of the whole vertex labeling.  The HilbertMetric Gaussian completion
detects that same condition without deleting the root: zero is an ordinary Gaussian feature, while
every repeated shift remains a collision.

Consequently deletion-robust positivity of all nonroot prime-source packets is equivalent to
strict positivity of one full finite Gaussian Gram.  This replaces an infinite family of cofinite
existence statements by one literal matrix certificate at any chosen prime and positive bandwidth.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open Matrix
open scoped ComplexOrder

/-- Complete exact-recovery phase of the transverse prime-jet aperture after deleting a
distinguished vertex.  Every finite prime deletion must still admit distinct sampling points,
dual coefficient recovery, strict Gram positivity, and positive Hilbert volume. -/
def XiTransverseRootDeletedPrimeJetApertureCofiniteHilbertReconstruction
    {N : ℕ} (root : Fin N) (shift : Fin N → ℕ) (m : ℕ) : Prop :=
  XiTransversePrimeJetApertureCofiniteHilbertReconstruction
    (fun v : {v : Fin N // v ≠ root} => shift v) m

/-- **Exact root-deleted metric classification.**  When the distinguished root has shift zero,
cofinite positive realization of every nonroot prime-jet packet is equivalent to injectivity of
the complete vertex shift map, including separation from the root. -/
theorem xiTransverse_rootDeletedCofiniteApertureGram_iff_injective
    {N : ℕ} (root : Fin N) (shift : Fin N → ℕ) (hroot : shift root = 0)
    (m : ℕ) :
    (∀ forbidden : Set Nat.Primes, forbidden.Finite →
      ∃ points : {v : Fin N // v ≠ root} × Fin (m + 1) →
          {p : Nat.Primes // p ∉ forbidden},
        (xiTransversePrimeJetApertureGram
          (fun v : {v : Fin N // v ≠ root} => shift v) m forbidden points).PosDef) ↔
      Function.Injective shift := by
  rw [xiTransversePrimeJetApertureGram_cofinite_posDef_iff_injective_ne_zero]
  constructor
  · rintro ⟨hinjective, hnonzero⟩
    intro x y hxy
    by_cases hx : x = root
    · subst x
      by_contra hy
      exact hnonzero ⟨y, Ne.symm hy⟩ (hxy.symm.trans hroot)
    · by_cases hy : y = root
      · subst y
        exact False.elim (hnonzero ⟨x, hx⟩ (hxy.trans hroot))
      · exact congrArg Subtype.val
          (hinjective
            (show shift (⟨x, hx⟩ : {v : Fin N // v ≠ root}) =
              shift (⟨y, hy⟩ : {v : Fin N // v ≠ root}) from hxy))
  · intro hinjective
    constructor
    · intro x y hxy
      exact Subtype.ext (hinjective hxy)
    · intro v hv
      exact v.property (hinjective (hv.trans hroot.symm))

/-- **Root-deleted Gram/reconstruction upgrade.**  The earlier cofinite positive-Gram interface
already contains full deletion-robust dual recovery and positive volume: both phases are exactly
the same restricted nonzero-collision condition. -/
theorem
    xiTransverseRootDeletedPrimeJetApertureCofiniteHilbertReconstruction_iff_cofiniteApertureGram
    {N : ℕ} (root : Fin N) (shift : Fin N → ℕ) (m : ℕ) :
    XiTransverseRootDeletedPrimeJetApertureCofiniteHilbertReconstruction
        root shift m ↔
      ∀ forbidden : Set Nat.Primes, forbidden.Finite →
        ∃ points : {v : Fin N // v ≠ root} × Fin (m + 1) →
            {p : Nat.Primes // p ∉ forbidden},
          (xiTransversePrimeJetApertureGram
            (fun v : {v : Fin N // v ≠ root} => shift v)
            m forbidden points).PosDef := by
  rw [XiTransverseRootDeletedPrimeJetApertureCofiniteHilbertReconstruction,
    xiTransversePrimeJetApertureCofiniteHilbertReconstruction_iff_injective_ne_zero,
    xiTransversePrimeJetApertureGram_cofinite_posDef_iff_injective_ne_zero]

/-- **Exact root-deleted Hilbert classification.**  With a zero-labeled distinguished root, full
dual reconstruction after every finite prime deletion is equivalent to injectivity of the entire
vertex labeling.  Nonvanishing of every retained label is discharged by root separation. -/
theorem
    xiTransverseRootDeletedPrimeJetApertureCofiniteHilbertReconstruction_iff_injective
    {N : ℕ} (root : Fin N) (shift : Fin N → ℕ) (hroot : shift root = 0)
    (m : ℕ) :
    XiTransverseRootDeletedPrimeJetApertureCofiniteHilbertReconstruction
        root shift m ↔
      Function.Injective shift := by
  calc
    _ ↔ (∀ forbidden : Set Nat.Primes, forbidden.Finite →
        ∃ points : {v : Fin N // v ≠ root} × Fin (m + 1) →
            {p : Nat.Primes // p ∉ forbidden},
          (xiTransversePrimeJetApertureGram
            (fun v : {v : Fin N // v ≠ root} => shift v)
            m forbidden points).PosDef) :=
      xiTransverseRootDeletedPrimeJetApertureCofiniteHilbertReconstruction_iff_cofiniteApertureGram
        root shift m
    _ ↔ _ :=
      xiTransverse_rootDeletedCofiniteApertureGram_iff_injective
        root shift hroot m

/-- **Root-deleted HTGeometry/full HilbertMetric connector.**  At every positive Gaussian
bandwidth, deletion-robust positivity on the nonroot prime source is equivalent to strict
positivity of the full first-valuation Gaussian Gram, with the zero root retained. -/
theorem xiTransverse_rootDeletedCofiniteApertureGram_iff_fullGaussianGramAt_posDef
    {N : ℕ} (root : Fin N) (shift : Fin N → ℕ) (hroot : shift root = 0)
    (m : ℕ) (p : Nat.Primes) {t : ℝ} (ht : 0 < t) :
    (∀ forbidden : Set Nat.Primes, forbidden.Finite →
      ∃ points : {v : Fin N // v ≠ root} × Fin (m + 1) →
          {r : Nat.Primes // r ∉ forbidden},
        (xiTransversePrimeJetApertureGram
          (fun v : {v : Fin N // v ≠ root} => shift v) m forbidden points).PosDef) ↔
      (xiTransversePrimeFirstValuationGaussianGramMatrixAt shift p t).PosDef := by
  calc
    _ ↔ Function.Injective shift :=
      xiTransverse_rootDeletedCofiniteApertureGram_iff_injective root shift hroot m
    _ ↔ _ :=
      (xiTransversePrimeFirstValuationGaussianGramMatrixAt_posDef_iff_injective
        shift p ht).symm

/-- Unit-bandwidth form: one fixed-prime Gaussian matrix exactly replaces every cofinite nonroot
prime-jet positivity certificate. -/
theorem xiTransverse_rootDeletedCofiniteApertureGram_iff_fullGaussianGram_posDef
    {N : ℕ} (root : Fin N) (shift : Fin N → ℕ) (hroot : shift root = 0)
    (m : ℕ) (p : Nat.Primes) :
    (∀ forbidden : Set Nat.Primes, forbidden.Finite →
      ∃ points : {v : Fin N // v ≠ root} × Fin (m + 1) →
          {r : Nat.Primes // r ∉ forbidden},
        (xiTransversePrimeJetApertureGram
          (fun v : {v : Fin N // v ≠ root} => shift v) m forbidden points).PosDef) ↔
      (xiTransversePrimeFirstValuationGaussianGramMatrix shift p).PosDef := by
  simpa only [xiTransversePrimeFirstValuationGaussianGramMatrix] using
    xiTransverse_rootDeletedCofiniteApertureGram_iff_fullGaussianGramAt_posDef
      root shift hroot m p (by norm_num : (0 : ℝ) < 1)

/-- **Exact-recovery/full-Gaussian connector.**  At any positive bandwidth, deletion-robust
nonroot dual recovery is equivalent to strict positivity of the full Gaussian collision metric,
with the distinguished zero root retained in that metric. -/
theorem
    xiTransverseRootDeletedPrimeJetApertureCofiniteHilbertReconstruction_iff_fullGaussianGramAt_posDef
    {N : ℕ} (root : Fin N) (shift : Fin N → ℕ) (hroot : shift root = 0)
    (m : ℕ) (p : Nat.Primes) {t : ℝ} (ht : 0 < t) :
    XiTransverseRootDeletedPrimeJetApertureCofiniteHilbertReconstruction
        root shift m ↔
      (xiTransversePrimeFirstValuationGaussianGramMatrixAt shift p t).PosDef := by
  calc
    _ ↔ Function.Injective shift :=
      xiTransverseRootDeletedPrimeJetApertureCofiniteHilbertReconstruction_iff_injective
        root shift hroot m
    _ ↔ _ :=
      (xiTransversePrimeFirstValuationGaussianGramMatrixAt_posDef_iff_injective
        shift p ht).symm

/-- Unit-bandwidth exact-recovery/full-Gaussian equivalence. -/
theorem
    xiTransverseRootDeletedPrimeJetApertureCofiniteHilbertReconstruction_iff_fullGaussianGram_posDef
    {N : ℕ} (root : Fin N) (shift : Fin N → ℕ) (hroot : shift root = 0)
    (m : ℕ) (p : Nat.Primes) :
    XiTransverseRootDeletedPrimeJetApertureCofiniteHilbertReconstruction
        root shift m ↔
      (xiTransversePrimeFirstValuationGaussianGramMatrix shift p).PosDef := by
  simpa only [xiTransversePrimeFirstValuationGaussianGramMatrix] using
    xiTransverseRootDeletedPrimeJetApertureCofiniteHilbertReconstruction_iff_fullGaussianGramAt_posDef
      root shift hroot m p (by norm_num : (0 : ℝ) < 1)

end

end RHTower
