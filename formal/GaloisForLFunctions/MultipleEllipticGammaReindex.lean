import GaloisForLFunctions.MultipleEllipticGammaFieldHierarchy

/-!
# Reindexing invariance of multiple elliptic gamma

All kernels and products depend only on the finite parameter family, not on its chosen finite index
type.  This is the type-level bridge needed to identify iterated coordinate-deletion faces with
one product on the final complementary parameter set.
-/

open Complex Set
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
    multipleEllipticGammaLogKernel_reindex]

theorem multipleEllipticGammaForwardFactor_reindex
    (e : κ ≃ ι) (τ : ι → ℂ) (n : κ → ℕ) (z : ℂ) :
    multipleEllipticGammaForwardFactor (fun k => τ (e k)) n z =
      multipleEllipticGammaForwardFactor τ
        (multipleEllipticGammaReindexMultiIndex e n) z := by
  rw [multipleEllipticGammaForwardFactor,
    multipleEllipticGammaForwardFactor,
    multipleEllipticGammaForwardArgument_reindex]

theorem multipleEllipticGammaBackwardFactor_reindex
    (e : κ ≃ ι) (τ : ι → ℂ) (n : κ → ℕ) (z : ℂ) :
    multipleEllipticGammaBackwardFactor (fun k => τ (e k)) n z =
      multipleEllipticGammaBackwardFactor τ
        (multipleEllipticGammaReindexMultiIndex e n) z := by
  rw [multipleEllipticGammaBackwardFactor,
    multipleEllipticGammaBackwardFactor,
    multipleEllipticGammaBackwardArgument_reindex]

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

end

end GaloisForLFunctions
