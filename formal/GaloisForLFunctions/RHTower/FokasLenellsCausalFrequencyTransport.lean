import GaloisForLFunctions.RHTower.FokasLenellsCausalFrequencyChart
import GaloisForLFunctions.RHTower.FokasLenellsCausalFrequencyCoefficient
import Mathlib.Analysis.Normed.Operator.LinearIsometry
/-! Exact chart transport of the actual closed frequency space.
The underlying chains are unchanged. The canonical isometric transport intertwines
actual frequency projections and scalar amplitudes under the exact frequency relabeling. -/
open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance causalFrequencyTransportLowerComplete : CompleteSpace (hardyL2ᗮ) := hardyL2.isClosed_orthogonal.completeSpace_coe
local instance causalFrequencyTransportChainComplete : CompleteSpace causalBoundedChain := causalBoundedChain_complete
local instance causalFrequencyTransportChainNormedGroup : NormedAddCommGroup causalBoundedChain := causalBoundedChain.normedAddCommGroup
local instance causalFrequencyTransportChainNormedSpace : NormedSpace ℂ causalBoundedChain := causalBoundedChain.normedSpace

private def sameSubmoduleIsometry
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (S T : Submodule ℂ E) (h : S = T) : S ≃ₗᵢ[ℂ] T where
  toLinearEquiv :=
    { toFun := fun u => ⟨u.val, (congrArg (fun U : Submodule ℂ E => u.val ∈ U) h).mp u.property⟩
      invFun := fun u => ⟨u.val, (congrArg (fun U : Submodule ℂ E => u.val ∈ U) h).mpr u.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  norm_map' := fun _ => rfl

private theorem sameSubmoduleIsometry_val
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (S T : Submodule ℂ E) (h : S = T) (u : S) :
    (sameSubmoduleIsometry S T h u).val = u.val := rfl

private theorem sameSubmoduleIsometry_trans
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (S T U : Submodule ℂ E) (hST : S = T) (hTU : T = U) (hSU : S = U) :
    (sameSubmoduleIsometry S T hST).trans (sameSubmoduleIsometry T U hTU) =
      sameSubmoduleIsometry S U hSU := by
  apply LinearIsometryEquiv.ext
  intro u
  apply Subtype.ext
  rfl

private theorem scalar_coefficient_transport
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (A : E ≃ₗᵢ[ℂ] F) (v : E) (w : F) (hw : ‖w‖ = 1)
    (P : E →L[ℂ] E) (Q : F →L[ℂ] F) (c : E →L[ℂ] ℂ) (d : F →L[ℂ] ℂ)
    (hv : A v = w) (hP : ∀ u, Q (A u) = A (P u))
    (hc : ∀ u, c u • v = P u) (hd : ∀ u, d u • w = Q u) (u : E) : d (A u) = c u := by
  have hn : w ≠ 0 := by intro h; rw [h, norm_zero] at hw; exact zero_ne_one hw
  apply smul_left_injective ℂ hn
  calc
    d (A u) • w = Q (A u) := hd (A u)
    _ = A (P u) := hP u
    _ = A (c u • v) := congrArg A (hc u).symm
    _ = c u • A v := map_smul A (c u) v
    _ = c u • w := congrArg (fun y : F => c u • y) hv

private theorem eigenchain_range_eq (b c : ℝ) :
    Set.range (causalBoundedUnitEigenchain b) = Set.range (causalBoundedUnitEigenchain c) := by
  ext u
  constructor
  · rintro ⟨ω, hω⟩
    exact ⟨Real.exp (c-b)*ω, (causalBoundedUnitEigenchain_rescale b c ω).trans hω⟩
  · rintro ⟨η, hη⟩
    exact ⟨Real.exp (b-c)*η, (causalBoundedUnitEigenchain_rescale c b η).trans hη⟩

/-- The actual algebraic frequency core is independent of the damping-chart parameter. -/
theorem causalFrequencyCore_eq (b c : ℝ) : causalFrequencyCore b = causalFrequencyCore c :=
  congrArg (fun A : Set causalBoundedChain => Submodule.span ℂ A) (eigenchain_range_eq b c)

/-- The actual complete closed frequency span is the same submodule in every chart. -/
theorem causalFrequencySpace_eq (b c : ℝ) : causalFrequencySpace b = causalFrequencySpace c :=
  congrArg (fun S : Submodule ℂ causalBoundedChain => S.topologicalClosure) (causalFrequencyCore_eq b c)

/-- Canonical isometric chart transport: the actual underlying derivative chain is unchanged. -/
def causalFrequencySpaceTransport (b c : ℝ) : causalFrequencySpace b ≃ₗᵢ[ℂ] causalFrequencySpace c :=
  sameSubmoduleIsometry (causalFrequencySpace b) (causalFrequencySpace c) (causalFrequencySpace_eq b c)

private theorem transport_val (b c : ℝ) (u : causalFrequencySpace b) :
    (causalFrequencySpaceTransport b c u).val = u.val := by
  simpa only [causalFrequencySpaceTransport] using!
    sameSubmoduleIsometry_val (causalFrequencySpace b) (causalFrequencySpace c) (causalFrequencySpace_eq b c) u

/-- Canonical chart transports compose exactly, with no dependence on an intermediate chart. -/
theorem causalFrequencySpaceTransport_trans (b c d : ℝ) :
    (causalFrequencySpaceTransport b c).trans (causalFrequencySpaceTransport c d) =
      causalFrequencySpaceTransport b d := by
  simpa only [causalFrequencySpaceTransport] using!
    sameSubmoduleIsometry_trans (causalFrequencySpace b) (causalFrequencySpace c) (causalFrequencySpace d)
      (causalFrequencySpace_eq b c) (causalFrequencySpace_eq c d) (causalFrequencySpace_eq b d)

/-- The unchanged actual mode receives exactly the positively rescaled frequency label. -/
theorem causalFrequencySpaceTransport_mode (b c ω : ℝ) :
    causalFrequencySpaceTransport b c (causalFrequencyMode b ω) =
      causalFrequencyMode c (Real.exp (c-b)*ω) := by
  apply Subtype.ext
  exact (transport_val b c (causalFrequencyMode b ω)).trans
    (causalBoundedUnitEigenchain_rescale b c ω).symm

/-- Actual strong-limit frequency projections commute with canonical chart transport. -/
theorem causalFrequencyProjection_transport (b c ω : ℝ) (u : causalFrequencySpace b) :
    causalFrequencyProjection c (Real.exp (c-b)*ω) (causalFrequencySpaceTransport b c u) =
      causalFrequencySpaceTransport b c (causalFrequencyProjection b ω u) := by
  have he : (fun N : ℕ => causalBoundedFrequencyMean c (Real.exp (c-b)*ω) N
      (causalFrequencySpaceTransport b c u).val) =
      (fun N : ℕ => causalBoundedFrequencyMean b ω N u.val) := by
    funext N
    exact (congrArg (fun T : causalBoundedChain →L[ℂ] causalBoundedChain =>
      T (causalFrequencySpaceTransport b c u).val) (causalBoundedFrequencyMean_rescale b c ω N)).trans
        (congrArg (causalBoundedFrequencyMean b ω N) (transport_val b c u))
  have hc := causalFrequencyProjection_tendsto c (Real.exp (c-b)*ω) (causalFrequencySpaceTransport b c u)
  have hc' : Tendsto (fun N : ℕ => causalBoundedFrequencyMean b ω N u.val) atTop
      (𝓝 (causalFrequencyProjection c (Real.exp (c-b)*ω) (causalFrequencySpaceTransport b c u)).val) :=
    (congrArg (fun f : ℕ → causalBoundedChain => Tendsto f atTop
      (𝓝 (causalFrequencyProjection c (Real.exp (c-b)*ω) (causalFrequencySpaceTransport b c u)).val)) he).mp hc
  have hv := tendsto_nhds_unique hc' (causalFrequencyProjection_tendsto b ω u)
  apply Subtype.ext
  exact hv.trans (transport_val b c (causalFrequencyProjection b ω u)).symm

/-- The actual scalar amplitude is invariant when its vector and frequency label are transported together. -/
theorem causalFrequencyCoefficient_transport (b c ω : ℝ) (u : causalFrequencySpace b) :
    causalFrequencyCoefficient c (Real.exp (c-b)*ω) (causalFrequencySpaceTransport b c u) =
      causalFrequencyCoefficient b ω u :=
  scalar_coefficient_transport (causalFrequencySpaceTransport b c)
    (causalFrequencyMode b ω) (causalFrequencyMode c (Real.exp (c-b)*ω))
    (norm_causalBoundedUnitEigenchain c (Real.exp (c-b)*ω))
    (causalFrequencyProjection b ω) (causalFrequencyProjection c (Real.exp (c-b)*ω))
    (causalFrequencyCoefficient b ω) (causalFrequencyCoefficient c (Real.exp (c-b)*ω))
    (causalFrequencySpaceTransport_mode b c ω) (causalFrequencyProjection_transport b c ω)
    (causalFrequencyCoefficient_smul_mode b ω) (causalFrequencyCoefficient_smul_mode c (Real.exp (c-b)*ω)) u
end
end RHTower.FokasLenells
