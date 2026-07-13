import GaloisForLFunctions.HTGeometry.HullJetEmbedding
import GaloisForLFunctions.HTGeometry.SmallInductiveDimension

/-!
# The hull's dimension is bounded by the ambient space (eq. 9 reduction)

Combining the finite jet-sample embedding (`HullJetEmbedding`) with the subspace/embedding
monotonicity of small inductive dimension (`SmallInductiveDimension`), the compact hull inherits any
dimension bound from the finite-dimensional space it embeds into: `ind K ≤ ind ℂ^N`.

This reduces the finite Bohr-rank conclusion eq. (9) to a single dimension input — `ind ℂ^N ≤ 2N`
(the remaining product-subadditivity theorem) — together with the Pontryagin `dim = character-rank`
identity.
-/

open Topology

namespace GaloisForLFunctions

/-- **Hull dimension bound.**  The finite jet-sample map `J` is a continuous injection from the
compact hull `K`, hence a topological embedding and in particular inducing; so any
small-inductive-dimension bound on `ℂ^N` transfers backwards to the hull: `ind K ≤ ind ℂ^N`. -/
theorem hull_smallIndDimLE_of_ambient {K : Type*} [TopologicalSpace K] [CompactSpace K]
    {N : ℕ} {J : K → (Fin N → ℂ)} (hJcont : Continuous J) (hJinj : Function.Injective J)
    {k : ℕ} (hdim : SmallIndDimLE (Fin N → ℂ) k) : SmallIndDimLE K k :=
  SmallIndDimLE.of_isInducing (hJcont.isClosedEmbedding hJinj).isInducing hdim

end GaloisForLFunctions
