/-
# Algebraic laws for Hilbert--Schmidt kernels

The coordinate kernel product is defined by an infinite matrix sum.  This file proves that the
kernel-to-operator realization preserves that product, and consequently that the product is
associative on Hilbert--Schmidt kernels.  These laws let source-built Gram families be collapsed
to genuine Hankel moment sequences without hiding a Fubini interchange.
-/
import GaloisForLFunctions.HilbertSchmidtMatrix

open scoped BigOperators

namespace HilbertSchmidt

variable {ι : Type*} [DecidableEq ι]

/-- Realization of Hilbert--Schmidt kernels on `ℓ²` preserves matrix composition. -/
theorem toOperator_hsComp {K L : ι × ι → ℂ} (hK : IsHS K) (hL : IsHS L) :
    toOperator (isHS_hsComp hK hL) = toOperator hK ∘L toOperator hL := by
  refine ContinuousLinearMap.ext_on
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr (lpBasis ι).dense_span) ?_
  rintro x ⟨j, rfl⟩
  rw [lpBasis_apply]
  apply lp.ext
  funext i
  rw [toOperator_single (isHS_hsComp hK hL) i j]
  change hsComp K L (i, j) = toOperator hK (toOperator hL (lp.single 2 j 1)) i
  rw [toOperator_apply]
  exact tsum_congr fun k => by rw [toOperator_single hL k j]

/-- Matrix composition is associative on Hilbert--Schmidt kernels. -/
theorem hsComp_assoc {K L M : ι × ι → ℂ}
    (hK : IsHS K) (hL : IsHS L) (hM : IsHS M) :
    hsComp (hsComp K L) M = hsComp K (hsComp L M) := by
  have hop : toOperator (isHS_hsComp (isHS_hsComp hK hL) hM) =
      toOperator (isHS_hsComp hK (isHS_hsComp hL hM)) := by
    rw [toOperator_hsComp (isHS_hsComp hK hL) hM,
      toOperator_hsComp hK hL,
      toOperator_hsComp hK (isHS_hsComp hL hM),
      toOperator_hsComp hL hM]
    exact ContinuousLinearMap.comp_assoc _ _ _
  have hmatrix := congrArg matrixOf hop
  simpa only [matrixOf_toOperator] using hmatrix

/-- The shifted kernel powers multiply with the expected shifted exponent. -/
theorem hsComp_hsPow {K : ι × ι → ℂ} (hK : IsHS K) (m n : ℕ) :
    hsComp (hsPow K m) (hsPow K n) = hsPow K (m + n + 1) := by
  induction m with
  | zero =>
      simp only [hsPow, zero_add]
  | succ m ih =>
      change hsComp (hsComp K (hsPow K m)) (hsPow K n) =
        hsPow K (Nat.succ m + n + 1)
      rw [hsComp_assoc hK (isHS_hsPow hK m) (isHS_hsPow hK n), ih]
      rw [show Nat.succ m + n + 1 = (m + n + 1) + 1 by omega]
      change hsComp K (hsPow K (m + n + 1)) = hsComp K (hsPow K (m + n + 1))
      rfl

end HilbertSchmidt
