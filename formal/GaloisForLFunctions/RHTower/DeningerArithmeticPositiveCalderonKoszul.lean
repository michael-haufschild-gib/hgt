import GaloisForLFunctions.RHTower.DeningerArithmeticUnitaryBRSTHodge
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.LinearAlgebra.Prod

/-!
# Positive Calderón--conormal and Koszul contractions

Finite arithmetic Hodge packets use a positive Dirichlet-to-Neumann
operator `A` and a linearized Milnor-incidence subspace `L`.  The
Calderón graph of `A` has trivial intersection with the conormal
`L × Lᗮ`: a vector in the intersection has zero positive energy.

The second theorem is the algebraic contraction kernel used by the
positive Hodge--Koszul argument.  If `d h + h d` is a nonzero scalar
multiple of the identity, every `d`-cycle is a `d`-boundary.

Both statements are unconditional and contain no zeta-zero or RH
premise.
-/

namespace RHTower

noncomputable section

section CalderonConormal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Linear conormal of an incidence subspace in the real cotangent
model `E × E`. -/
def deningerLinearConormal (L : Submodule ℝ E) :
    Submodule ℝ (E × E) :=
  Submodule.prod L Lᗮ

/--
`DAC_POSITIVE_GRAPH_CONORMAL_TRANSVERSALITY`, intersection part.

The graph of a strictly positive linear operator intersects the
conormal of any linear incidence subspace only at zero.  No
finite-dimensional hypothesis is needed for this kernel statement.
-/
theorem deningerPositiveCalderonGraph_inf_conormal_eq_bot
    (A : E →ₗ[ℝ] E)
    (L : Submodule ℝ E)
    (hpositive : ∀ x : E, x ≠ 0 → 0 < inner ℝ (A x) x) :
    A.graph ⊓ deningerLinearConormal L = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro z hz
  rcases hz with ⟨hgraph, hconormal⟩
  have hzgraph : z.2 = A z.1 :=
    (A.mem_graph_iff z).mp hgraph
  have hzprod :
      z.1 ∈ L ∧ z.2 ∈ Lᗮ :=
    Submodule.mem_prod.mp hconormal
  have hinner : inner ℝ (A z.1) z.1 = 0 := by
    rw [← hzgraph]
    exact
      Submodule.inner_left_of_mem_orthogonal
        hzprod.1 hzprod.2
  have hzfst : z.1 = 0 := by
    by_contra hne
    have hstrict := hpositive z.1 hne
    rw [hinner] at hstrict
    exact lt_irrefl 0 hstrict
  apply Prod.ext
  · exact hzfst
  · change z.2 = 0
    rw [hzgraph, hzfst, map_zero]

end CalderonConormal

section ScaledChainContraction

variable {𝕜 C : Type*} [Field 𝕜] [AddCommGroup C] [Module 𝕜 C]

/--
`DAC_POSITIVE_HODGE_KOSZUL_CONTRACTION`, abstract contraction kernel.

If `d h + h d = a · id` with `a ≠ 0`, then every `d`-cycle is a
`d`-boundary.  The Euler homotopy on a positive-total-degree Koszul
summand is the specialization with `a` equal to that total degree.
-/
theorem deninger_exact_of_scaled_chainContraction
    (d h : C →ₗ[𝕜] C)
    (a : 𝕜)
    (ha : a ≠ 0)
    (hcontract : ∀ x : C, d (h x) + h (d x) = a • x)
    {x : C}
    (hx : d x = 0) :
    ∃ y : C, d y = x := by
  refine ⟨a⁻¹ • h x, ?_⟩
  have hdh : d (h x) = a • x := by
    simpa [hx] using hcontract x
  rw [map_smul, hdh, ← mul_smul, inv_mul_cancel₀ ha, one_smul]

/-- Unit-scaled form of
`deninger_exact_of_scaled_chainContraction`. -/
theorem deninger_exact_of_chainContraction
    (d h : C →ₗ[𝕜] C)
    (hcontract : ∀ x : C, d (h x) + h (d x) = x)
    {x : C}
    (hx : d x = 0) :
    ∃ y : C, d y = x := by
  apply
    deninger_exact_of_scaled_chainContraction
      d h 1 one_ne_zero
  · simpa using hcontract
  · exact hx

end ScaledChainContraction

end

end RHTower
