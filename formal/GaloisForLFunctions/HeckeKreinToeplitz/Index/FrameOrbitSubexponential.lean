import GaloisForLFunctions.HeckeKreinToeplitz.Index.CompletedFrameRepresentation
import GaloisForLFunctions.HTGeometry.SubexponentialIntegerGrowth

/-!
# Subexponential growth of the completed cyclic column orbit

Negative coordinates are finite sums of translates of the kernel.
The invariant square bounds the positive coordinate by those negative
coordinates and one fixed initial norm. Thus scalar kernel growth controls
the full completed orbit, without an operator-norm growth assumption.
-/

noncomputable section
set_option autoImplicit false
open Complex
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HeckeKreinToeplitz.NegativeFrame

variable {k : Multiplicative ℤ → ℂ} (hk : IsHermKernel k)
    (hsub : HasSubexponentialIntegerGrowth (fun z => k (Multiplicative.ofAdd z)))

include hk hsub in
/-- Pairing a fixed column-space vector with the cyclic orbit retains subexponential growth. -/
theorem pairing_point_subexponential (v : kernelColumnSpan k) :
    HasSubexponentialIntegerGrowth
      (fun z => kernelColumnPairing k v (kernelColumnPoint k (Multiplicative.ofAdd z))) := by
  obtain ⟨n, x, c, hc⟩ := exists_kernelColumnPoint_fin_sum k v
  rw [← hc]
  simp only [kernelColumnPairing_sum_points hk]
  change HasSubexponentialIntegerGrowth
    (fun z => ∑ i, conj (c i) * k (Multiplicative.ofAdd (-Multiplicative.toAdd (x i) + z)))
  exact HasSubexponentialIntegerGrowth.sum
    (fun i => (hsub.translate (-Multiplicative.toAdd (x i))).smul (conj (c i)))

variable {m : ℕ} (e : Fin m → kernelColumnSpan k) (he : IsNegativeColumnFrame e)
    (hp : ∀ v : kernelColumnSpan k, (∀ i, kernelColumnPairing k (e i) v = 0) →
      0 ≤ (kernelColumnPairing k v v).re)

include hsub in
/-- Finite negative coordinates control the completed cyclic column orbit. -/
theorem embedding_point_subexponential : HasSubexponentialIntegerGrowth
    (fun z => embedding hk e he hp (kernelColumnPoint k (Multiplicative.ofAdd z))) := by
  let u (z : ℤ) := embedding hk e he hp (kernelColumnPoint k (Multiplicative.ofAdd z))
  have hs : HasSubexponentialIntegerGrowth (fun z => (u z).2) := by
    apply HasSubexponentialIntegerGrowth.euclidean
    intro i
    change HasSubexponentialIntegerGrowth (fun z =>
      -kernelColumnPairing k (e i) (kernelColumnPoint k (Multiplicative.ofAdd z)))
    exact (pairing_point_subexponential hk hsub (e i)).neg
  have hb (z : ℤ) : ‖u z‖ ≤ ‖u 0‖ + ‖(u z).2‖ := by
    have hq : FiniteNegative.pairing (u z) (u z) = FiniteNegative.pairing (u 0) (u 0) := by
      dsimp only [u]
      rw [embedding_pairing, embedding_pairing, kernelColumnPairing_point_left hk,
        kernelColumnPairing_point_left hk]
      change k ((Multiplicative.ofAdd z)⁻¹ * Multiplicative.ofAdd z) =
        k ((Multiplicative.ofAdd 0)⁻¹ * Multiplicative.ofAdd 0)
      rw [inv_mul_cancel, inv_mul_cancel]
    have hqr := congrArg Complex.re hq
    rw [FiniteNegative.pairing_self_re, FiniteNegative.pairing_self_re] at hqr
    have hfst2 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (norm_fst_le (u 0))
    have hcross : 0 ≤ ‖u 0‖ * ‖(u z).2‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have hf : ‖(u z).1‖ ≤ ‖u 0‖ + ‖(u z).2‖ := by
      nlinarith only [hqr, hfst2, sq_nonneg ‖(u 0).2‖, hcross,
        norm_nonneg (u z).1, norm_nonneg (u 0), norm_nonneg (u z).2]
    rw [Prod.norm_def]
    exact max_le hf (le_add_of_nonneg_left (norm_nonneg _))
  have hg := (HasSubexponentialIntegerGrowth.const ‖u 0‖).add hs.norm
  exact hg.of_norm_le (fun z => by
    rw [Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact hb z)

#print axioms embedding_point_subexponential

end GaloisForLFunctions.HeckeKreinToeplitz.NegativeFrame
