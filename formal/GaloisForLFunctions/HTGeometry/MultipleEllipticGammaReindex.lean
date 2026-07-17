import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaFieldHierarchy

/-!
# Reindexing invariance of multiple elliptic gamma

All kernels and products depend only on the finite parameter family, not on its chosen finite index
type.  This is the type-level bridge needed to identify iterated coordinate-deletion faces with
one product on the final complementary parameter set.
-/

open Complex Set Filter
open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

variable {ι κ : Type} [Fintype ι] [Fintype κ]

/-- Reindex a multi-index along an equivalence of finite parameter types. -/
def multipleEllipticGammaReindexMultiIndex (e : κ ≃ ι) :
    (κ → ℕ) ≃ (ι → ℕ) where
  toFun n i := n (e.symm i)
  invFun n k := n (e k)
  left_inv n := by funext k; simp
  right_inv n := by funext i; simp

theorem multipleEllipticGammaForwardArgument_reindex
    (e : κ ≃ ι) (p : ι → ℂ) (x : ℂ) (n : κ → ℕ) :
    multipleEllipticGammaForwardArgument (fun k => p (e k)) x n =
      multipleEllipticGammaForwardArgument p x
        (multipleEllipticGammaReindexMultiIndex e n) := by
  rw [multipleEllipticGammaForwardArgument,
    multipleEllipticGammaForwardArgument]
  congr 1
  apply Fintype.prod_equiv e
  intro k
  simp [multipleEllipticGammaReindexMultiIndex]

theorem multipleEllipticGammaBackwardArgument_reindex
    (e : κ ≃ ι) (p : ι → ℂ) (x : ℂ) (n : κ → ℕ) :
    multipleEllipticGammaBackwardArgument (fun k => p (e k)) x n =
      multipleEllipticGammaBackwardArgument p x
        (multipleEllipticGammaReindexMultiIndex e n) := by
  rw [multipleEllipticGammaBackwardArgument,
    multipleEllipticGammaBackwardArgument]
  congr 1
  apply Fintype.prod_equiv e
  intro k
  simp [multipleEllipticGammaReindexMultiIndex]

theorem multipleEllipticGammaLogSign_reindex (e : κ ≃ ι) :
    multipleEllipticGammaLogSign κ = multipleEllipticGammaLogSign ι := by
  rw [multipleEllipticGammaLogSign, multipleEllipticGammaLogSign,
    Fintype.card_congr e]

theorem multipleEllipticGammaLogSummand_reindex
    (e : κ ≃ ι) (p : ι → ℂ) (x : ℂ) (n : κ → ℕ) :
    multipleEllipticGammaLogSummand (fun k => p (e k)) x n =
      multipleEllipticGammaLogSummand p x
        (multipleEllipticGammaReindexMultiIndex e n) := by
  rw [multipleEllipticGammaLogSummand, multipleEllipticGammaLogSummand,
    multipleEllipticGammaForwardArgument_reindex,
    multipleEllipticGammaBackwardArgument_reindex,
    multipleEllipticGammaLogSign_reindex e]

/-- The convergent logarithmic kernel is invariant under every parameter reindexing. -/
theorem multipleEllipticGammaLogKernel_reindex
    (e : κ ≃ ι) (p : ι → ℂ) (x : ℂ) :
    multipleEllipticGammaLogKernel (fun k => p (e k)) x =
      multipleEllipticGammaLogKernel p x := by
  rw [multipleEllipticGammaLogKernel, multipleEllipticGammaLogKernel,
    ← (multipleEllipticGammaReindexMultiIndex e).tsum_eq
      (multipleEllipticGammaLogSummand p x)]
  apply tsum_congr
  intro n
  exact multipleEllipticGammaLogSummand_reindex e p x n

theorem multipleEllipticGammaAdditiveLogKernel_reindex
    (e : κ ≃ ι) (τ : ι → ℂ) (z : ℂ) :
    multipleEllipticGammaAdditiveLogKernel (fun k => τ (e k)) z =
      multipleEllipticGammaAdditiveLogKernel τ z := by
  rw [multipleEllipticGammaAdditiveLogKernel,
    multipleEllipticGammaAdditiveLogKernel,
    multipleEllipticGammaLogKernel_reindex e (fun i => ellipticNome (τ i))
      (multipleEllipticGammaCoordinate z)]

theorem multipleEllipticGammaForwardFactor_reindex
    (e : κ ≃ ι) (τ : ι → ℂ) (n : κ → ℕ) (z : ℂ) :
    multipleEllipticGammaForwardFactor (fun k => τ (e k)) n z =
      multipleEllipticGammaForwardFactor τ
        (multipleEllipticGammaReindexMultiIndex e n) z := by
  rw [multipleEllipticGammaForwardFactor,
    multipleEllipticGammaForwardFactor,
    multipleEllipticGammaForwardArgument_reindex e (fun i => ellipticNome (τ i))
      (multipleEllipticGammaCoordinate z) n]

theorem multipleEllipticGammaBackwardFactor_reindex
    (e : κ ≃ ι) (τ : ι → ℂ) (n : κ → ℕ) (z : ℂ) :
    multipleEllipticGammaBackwardFactor (fun k => τ (e k)) n z =
      multipleEllipticGammaBackwardFactor τ
        (multipleEllipticGammaReindexMultiIndex e n) z := by
  rw [multipleEllipticGammaBackwardFactor,
    multipleEllipticGammaBackwardFactor,
    multipleEllipticGammaBackwardArgument_reindex e (fun i => ellipticNome (τ i))
      (multipleEllipticGammaCoordinate z) n]

theorem multipleEllipticGammaForwardProduct_reindex
    (e : κ ≃ ι) (τ : ι → ℂ) (z : ℂ) :
    multipleEllipticGammaForwardProduct (fun k => τ (e k)) z =
      multipleEllipticGammaForwardProduct τ z := by
  rw [multipleEllipticGammaForwardProduct,
    multipleEllipticGammaForwardProduct,
    ← (multipleEllipticGammaReindexMultiIndex e).tprod_eq
      (fun n => multipleEllipticGammaForwardFactor τ n z)]
  apply tprod_congr
  intro n
  exact multipleEllipticGammaForwardFactor_reindex e τ n z

theorem multipleEllipticGammaBackwardProduct_reindex
    (e : κ ≃ ι) (τ : ι → ℂ) (z : ℂ) :
    multipleEllipticGammaBackwardProduct (fun k => τ (e k)) z =
      multipleEllipticGammaBackwardProduct τ z := by
  rw [multipleEllipticGammaBackwardProduct,
    multipleEllipticGammaBackwardProduct,
    ← (multipleEllipticGammaReindexMultiIndex e).tprod_eq
      (fun n => multipleEllipticGammaBackwardFactor τ n z)]
  apply tprod_congr
  intro n
  exact multipleEllipticGammaBackwardFactor_reindex e τ n z

/-- The genuine parity-dependent multiple elliptic gamma product is reindexing invariant. -/
theorem multipleEllipticGammaProduct_reindex
    (e : κ ≃ ι) (τ : ι → ℂ) :
    multipleEllipticGammaProduct (fun k => τ (e k)) =
      multipleEllipticGammaProduct τ := by
  funext z
  rw [multipleEllipticGammaProduct, multipleEllipticGammaProduct,
    Fintype.card_congr e,
    multipleEllipticGammaForwardProduct_reindex,
    multipleEllipticGammaBackwardProduct_reindex]

/-- The global analytic forward product is independent of the finite parameter indexing type. -/
theorem multipleEllipticGammaForwardAnalytic_reindex
    (e : κ ≃ ι) (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) :
    multipleEllipticGammaForwardAnalytic (fun k => τ (e k)) (fun k => hτ (e k)) =
      multipleEllipticGammaForwardAnalytic τ hτ := by
  apply Subtype.ext
  change Germ.coeRingHom (𝓟 Set.univ)
      (multipleEllipticGammaForwardProduct fun k => τ (e k)) =
    Germ.coeRingHom (𝓟 Set.univ) (multipleEllipticGammaForwardProduct τ)
  congr 1
  funext z
  exact multipleEllipticGammaForwardProduct_reindex e τ z

/-- The global analytic backward product is independent of the finite parameter indexing type. -/
theorem multipleEllipticGammaBackwardAnalytic_reindex
    (e : κ ≃ ι) (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) :
    multipleEllipticGammaBackwardAnalytic (fun k => τ (e k)) (fun k => hτ (e k)) =
      multipleEllipticGammaBackwardAnalytic τ hτ := by
  apply Subtype.ext
  change Germ.coeRingHom (𝓟 Set.univ)
      (multipleEllipticGammaBackwardProduct fun k => τ (e k)) =
    Germ.coeRingHom (𝓟 Set.univ) (multipleEllipticGammaBackwardProduct τ)
  congr 1
  funext z
  exact multipleEllipticGammaBackwardProduct_reindex e τ z

/-- The genuine global meromorphic multiple elliptic gamma is invariant under parameter
reindexing. -/
theorem multipleEllipticGammaMero_reindex
    (e : κ ≃ ι) (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) :
    multipleEllipticGammaMero (fun k => τ (e k)) (fun k => hτ (e k)) =
      multipleEllipticGammaMero τ hτ := by
  rw [multipleEllipticGammaMero, multipleEllipticGammaMero,
    Fintype.card_congr e,
    multipleEllipticGammaForwardAnalytic_reindex,
    multipleEllipticGammaBackwardAnalytic_reindex]

/-- The genuine meromorphic logarithmic derivative is invariant under every finite parameter
reindexing. -/
theorem multipleEllipticGammaLogDerivMero_reindex
    (e : κ ≃ ι) (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) :
    multipleEllipticGammaLogDerivMero (fun k => τ (e k)) (fun k => hτ (e k)) =
      multipleEllipticGammaLogDerivMero τ hτ := by
  letI := meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty
  simp only [multipleEllipticGammaLogDerivMero]
  rw [multipleEllipticGammaMero_reindex e τ hτ]

end

end GaloisForLFunctions
