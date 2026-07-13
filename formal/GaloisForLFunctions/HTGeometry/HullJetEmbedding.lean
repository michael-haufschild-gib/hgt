import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Analysis.Complex.Basic

/-!
# The finite jet-sample embedding of the hull (eq. 9, topological reduction)

The finite-phase rank bound (§4 of the companion card) rests on the fact that the joint hull `K`,
through the finite jet-sample evaluation `J : K → ℂ^{m(n+1)}` — `(b, g) ↦ (g⁽ᵏ⁾(t_j))_{j,k}` — is a
*topological embedding* of the compact hull into a finite-dimensional space.  Injectivity of `J` is
the analytic implicit-function / ODE-uniqueness step; once it holds, this file supplies the purely
topological conclusion: the hull is homeomorphic to a compact subset of `ℂ^N`.

This reduces the finite Bohr-rank conclusion eq. (9) to the remaining topological input — covering
dimension of a compact subset of `ℂ^N = ℝ^{2N}` is `≤ 2N`, and (Pontryagin) equals the character
rank — which is the mathlib-absent piece still under construction.
-/

open Topology

namespace GaloisForLFunctions

/-- **Finite jet-sample embedding.**  A continuous injective jet-sample map from a compact hull `K`
into `ℂ^N` is a closed topological embedding: `K` is homeomorphic to a compact subset of the
finite-dimensional space `ℂ^N`. -/
theorem hull_jetSample_isClosedEmbedding {K : Type*} [TopologicalSpace K] [CompactSpace K]
    {N : ℕ} {J : K → (Fin N → ℂ)} (hJcont : Continuous J) (hJinj : Function.Injective J) :
    IsClosedEmbedding J :=
  hJcont.isClosedEmbedding hJinj

/-- The jet-sample image is a compact subset of `ℂ^N`; the hull carries no more topological
complexity than a compact set in finite-dimensional space. -/
theorem hull_jetSample_image_isCompact {K : Type*} [TopologicalSpace K] [CompactSpace K]
    {N : ℕ} {J : K → (Fin N → ℂ)} (hJcont : Continuous J) :
    IsCompact (Set.range J) :=
  isCompact_range hJcont

end GaloisForLFunctions
