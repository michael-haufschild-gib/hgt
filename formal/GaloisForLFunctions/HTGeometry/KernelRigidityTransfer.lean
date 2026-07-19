import GaloisForLFunctions.HTGeometry.KernelControlIndicatorRepresentation

/-!
# Transfer of kernel rigidity along a coefficient matrix

A jet kernel is often a fixed linear combination of a simpler base kernel: each coordinate is a
triangular expansion in Cauchy powers with coefficients depending only on the nodes, not on the
integration variable.

Rigidity then transfers.  A coefficient packet annihilating the composite kernel annihilates the
base kernel through the transposed coefficient matrix, so if the base kernel is rigid and the
transposed matrix is injective, the composite kernel is rigid.

The second condition is where criticality enters: the forward jet expansion exists always, but it is
injective only away from the critical locus, so rigidity of the composite kernel is not
unconditional even when the base kernel is rigid.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

noncomputable section

variable {α : Type*} [MeasurableSpace α]

/-- **Rigidity transfers along an injective transposed coefficient matrix.**  If the kernel `K`
expands in a base kernel `B` with coefficient matrix `M`, the base kernel is rigid, and no nonzero
packet is annihilated by the transpose of `M`, then `K` is rigid. -/
theorem kernel_ae_re_rigidity_of_transpose_injective
    {σ τ : Type*} [Fintype σ] [Fintype τ]
    (μ : Measure α) (B : α → τ → ℂ) (M : σ → τ → ℂ) (K : α → σ → ℂ)
    (hK : ∀ t s, K t s = ∑ k : τ, M s k * B t k)
    (hB : ∀ d : τ → ℂ, (∀ᵐ t ∂μ, (∑ k : τ, d k * B t k).re = 0) → ∀ k, d k = 0)
    (hM : ∀ c : σ → ℂ, (∀ k : τ, ∑ s : σ, c s * M s k = 0) → ∀ s, c s = 0) :
    ∀ c : σ → ℂ, (∀ᵐ t ∂μ, (∑ s : σ, c s * K t s).re = 0) → ∀ s, c s = 0 := by
  classical
  intro c hc
  -- The packet acts on the base kernel through the transposed matrix.
  set d : τ → ℂ := fun k => ∑ s : σ, c s * M s k with hd
  have hexpand : ∀ t : α, ∑ s : σ, c s * K t s = ∑ k : τ, d k * B t k := by
    intro t
    have hleft : ∑ s : σ, c s * K t s
        = ∑ s : σ, ∑ k : τ, c s * (M s k * B t k) := by
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [hK t s, Finset.mul_sum]
    have hright : ∑ k : τ, d k * B t k
        = ∑ k : τ, ∑ s : σ, c s * (M s k * B t k) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hd, Finset.sum_mul]
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [hleft, hright, Finset.sum_comm]
  have hbase : ∀ᵐ t ∂μ, (∑ k : τ, d k * B t k).re = 0 := by
    filter_upwards [hc] with t ht
    rwa [← hexpand t]
  exact hM c (hB d hbase)

end

end GaloisForLFunctions.HTGeometry
