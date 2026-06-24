/-
# A proper local homeomorphism is a covering map (general topology bridge)

Mathlib has the covering monodromy theorem (`IsCoveringMap.monodromy`) but no lemma turning a
proper local homeomorphism into a covering map. The Böttcher tower needs exactly this: `f_c^[n]`
is proper (`quadratic_iterate_isProperMap`), a local homeomorphism off its critical points
(`quadratic_iterate_map_nhds`), with discrete finite fibres — so off the finite critical-value set
it should be an honest `2ⁿ`-fold covering. This file builds the general bridge.

Strategy (standard): for `x` with finite fibre `{e₁,…,eₖ} ⊆ ⋃ Uᵢ` (disjoint local-homeo
neighbourhoods), properness (= closedness) shrinks the base to a `W ∋ x` whose preimage lies in
`⋃ Uᵢ`; intersecting with the homeomorphic images trivializes `f⁻¹(W')`.
-/
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Covering.Basic

open Topology Set Filter

namespace Bottcher

/-- **Shrink the base (proper/closed-map step).** For a closed map `f`, if the fibre `f⁻¹{x}` lies
in an open `U`, then a whole neighbourhood `W ∋ x` has `f⁻¹(W) ⊆ U`. This is what makes a proper
local homeomorphism a covering: it confines the preimage of a small base set to the disjoint union
of the local-homeomorphism charts at the fibre. -/
theorem exists_nhds_preimage_subset {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {f : E → X} (hf : IsClosedMap f) {x : X} {U : Set E} (hU : IsOpen U)
    (hfib : f ⁻¹' {x} ⊆ U) : ∃ W ∈ 𝓝 x, f ⁻¹' W ⊆ U := by
  refine ⟨(f '' Uᶜ)ᶜ, ?_, ?_⟩
  · refine (hf _ hU.isClosed_compl).isOpen_compl.mem_nhds ?_
    intro hx
    obtain ⟨e, heU, hex⟩ := hx
    exact heU (hfib hex)
  · intro z hz
    by_contra hzU
    exact hz ⟨z, hzU, rfl⟩

end Bottcher
