import GaloisForLFunctions.RHTower.HorizontalIsolationBlockFailureCount
import GaloisForLFunctions.RHTower.HorizontalIsolationOddVectorNorm

/-!
# The routing cost of nearly real pairs on Zeta23's windows

Counting a pair `q = ½ + ε_q + iγ_q` as a multiple real point (`oddAngle_block_route_count`)
costs `4m_q(D′(h_q) − 2‖h_q‖²)`. If the routed diagonal form satisfies `D′(h_q) ≤ R_q‖h_q‖²`, then
by `‖h_q‖² ≤ L ε_q² cosh²(ε_q L/2) ∫u²φ² / c` (`norm_sq_blockImVec_le_sq_mul_cosh`) the cost is at
most `4m_q (R_q − 2)⁺ L ε_q² cosh²(ε_q L/2) ∫u²φ² / c`, which is quadratic in `ε_q L`
(`routed_block_count_le_of_rayleigh`).
-/

open Complex MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace RHTower

open GaloisForLFunctions.HilbertMetric Zeta23 Zeta23.ZeroSide

section Block

variable {Z : ZeroConfig} {T : ℝ} {P : Params}

/-- **Routed count with quadratic pair cost.** -/
theorem routed_block_count_le_of_rayleigh (hconj : PhiHatConj T P) {c : ℝ} (hc : 0 < c)
    (hL : 0 < P.L T) (hφc : Continuous (P.phi T))
    (hsupp : ∀ u, P.L T / 2 ≤ |u| → P.phi T u = 0)
    (Pr : (blockData Z T P hconj).PairReps) (M : Finset (ZI Z T))
    (hM : M ⊆ (blockData Z T P hconj).S₁)
    (hPois : ∀ z ∈ (blockData Z T P hconj).onLine,
      ∑ k, ‖(blockData Z T P hconj).v z k‖ ^ 2 ≤ c) (S : Finset {z // z ∈ Pr.R})
    (own : {z // z ∈ M} → {q // q ∉ S}) (O : Finset {q // q ∉ S})
    (hO : ∀ x, own x ∈ O) (hOne : O.Nonempty) (β : {q // q ∉ S} → ℝ)
    (hβ0 : ∀ q ∈ O, 0 ≤ β q) (hβ1 : ∑ q ∈ O, β q ≤ 1) (good : Finset {z // z ∈ M})
    (hgood : ∀ x ∈ good,
      ((blockPacket (blockData Z T P hconj) Pr c M).routeToMultiple S).CertifiedWith own β x)
    (R : {q // q ∈ S} → ℝ)
    (hR : ∀ q : {q // q ∈ S},
      ((blockPacket (blockData Z T P hconj) Pr c M).routeToMultiple S).diagForm
          (blockImVec (blockData Z T P hconj) c (q : {z // z ∈ Pr.R})) ≤
        R q * ‖blockImVec (blockData Z T P hconj) c (q : {z // z ∈ Pr.R})‖ ^ 2) :
    4 * RHLinalg.rtrace ((blockData Z T P hconj).blockP c + (blockData Z T P hconj).blockQ c) -
        RHLinalg.frobSq ((blockData Z T P hconj).blockP c + (blockData Z T P hconj).blockQ c) -
        2 * ((blockData Z T P hconj).Ncount : ℝ) ≤
      (((blockData Z T P hconj).S₁ \ M).card : ℝ) + (Finset.univ \ good).card +
        ∑ q : {q // q ∈ S}, 4 * ((blockData Z T P hconj).m (q : {z // z ∈ Pr.R}) : ℝ) *
          max (R q - 2) 0 * (P.L T * ((((q : ZI Z T) : ℂ).re - 1 / 2) ^ 2 *
            Real.cosh ((((q : ZI Z T) : ℂ).re - 1 / 2) * (P.L T / 2)) ^ 2 *
              ∫ u in (-(P.L T / 2))..(P.L T / 2), u ^ 2 * P.phi T u ^ 2) / c) := by
  refine (oddAngle_block_route_count (blockData Z T P hconj) Pr c M hc hM hPois S own O hO hOne
    β hβ0 hβ1 good hgood).trans (add_le_add le_rfl (Finset.sum_le_sum fun q _ => ?_))
  set h := blockImVec (blockData Z T P hconj) c (q : {z // z ∈ Pr.R})
  have hm : (0 : ℝ) ≤ 4 * ((blockData Z T P hconj).m (q : {z // z ∈ Pr.R}) : ℝ) := by
    positivity
  have hB1 := norm_sq_blockImVec_le_sq_mul_cosh hconj hc hL hφc hsupp (q : ZI Z T)
  rw [mul_assoc (4 * ((blockData Z T P hconj).m (q : {z // z ∈ Pr.R}) : ℝ)) (max (R q - 2) 0)]
  refine mul_le_mul_of_nonneg_left ?_ hm
  calc _ ≤ (R q - 2) * ‖h‖ ^ 2 := by linarith [hR q]
    _ ≤ max (R q - 2) 0 * ‖h‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left hB1 (le_max_right _ _)

end Block

end RHTower
