import GaloisForLFunctions.HTGeometry.SmirnovToeplitzKernel

/-!
# Exact `N⁺` Toeplitz-kernel boundary class

Makarov--Poltoratski's `N⁺[U]` is not merely quotient algebra: its forward boundary is locally
`L¹` on the real line.  This file records that condition literally and supplies the bounded-left
multiplication used in the Kapustin collision.
-/

open Complex MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A bounded analytic multiplier has a locally integrable real-line boundary representative. -/
theorem locallyIntegrable_diskMultiplierLineBoundary (phi : DiskMultiplier) :
    LocallyIntegrable (diskMultiplierLineBoundary phi) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  apply IntegrableOn.of_bound hK.measure_lt_top
  · exact (measurable_diskMultiplierLineBoundary phi).aestronglyMeasurable.restrict
  · exact (ae_norm_diskMultiplierLineBoundary_le phi).filter_mono
      (MeasureTheory.ae_restrict_le : ae (volume.restrict K) ≤ ae volume)

/-- Multiplication on the left by a globally bounded measurable function preserves local
integrability. -/
theorem locallyIntegrable_bounded_mul_left
    {f g : ℝ → ℂ} {C : ℝ}
    (hg : LocallyIntegrable g volume)
    (hf : Measurable f) (hfC : ∀ᵐ x ∂volume, ‖f x‖ ≤ C) :
    LocallyIntegrable (fun x => f x * g x) volume := by
  rw [locallyIntegrable_iff] at hg ⊢
  intro K hK
  exact (hg K hK).bdd_mul
    hf.aestronglyMeasurable.restrict
    (hfC.filter_mono
      (MeasureTheory.ae_restrict_le : ae (volume.restrict K) ≤ ae volume))

/-- A nonzero `N⁺[U]` element in the exact convention of Makarov--Poltoratski. -/
structure SmirnovToeplitzNPlusElement (U : ℝ → ℂ)
    extends SmirnovToeplitzKernelElement U where
  forward_locallyIntegrable : LocallyIntegrable toSmirnovToeplitzKernelElement.forward.boundary
    volume

/-- Forget local `L¹` admission. -/
def SmirnovToeplitzNPlusElement.toKernelElement {U : ℝ → ℂ}
    (F : SmirnovToeplitzNPlusElement U) : SmirnovToeplitzKernelElement U :=
  F.toSmirnovToeplitzKernelElement

/-- `N⁺` depends only on the almost-everywhere class of its Toeplitz symbol. -/
def SmirnovToeplitzNPlusElement.congr {U V : ℝ → ℂ}
    (F : SmirnovToeplitzNPlusElement U) (hUV : U =ᵐ[volume] V) :
    SmirnovToeplitzNPlusElement V where
  toSmirnovToeplitzKernelElement := F.toKernelElement.congr hUV
  forward_locallyIntegrable := F.forward_locallyIntegrable

/-- Every nonzero bounded analytic multiplier is an exact `N⁺` element for its phase-reflection
symbol. -/
def diskMultiplierSmirnovToeplitzNPlusElement
    (phi : DiskMultiplier) (hphi : ∃ z ∈ Metric.ball (0 : ℂ) 1, phi.fn z ≠ 0) :
    SmirnovToeplitzNPlusElement (diskMultiplierPhaseReflectionSymbol phi) where
  toSmirnovToeplitzKernelElement := diskMultiplierSmirnovToeplitzElement phi hphi
  forward_locallyIntegrable :=
    (locallyIntegrable_diskMultiplierLineBoundary phi).congr
      (DiskSmirnovBoundary.boundary_ofMultiplier_ae phi).symm

/-- Exact multiplication `Nᴺ · N⁺ ⊆ N⁺` for a bounded analytic left factor. -/
def SmirnovToeplitzNPlusElement.mul_left_multiplier
    {V : ℝ → ℂ} (phi : DiskMultiplier)
    (hphi : ∃ z ∈ Metric.ball (0 : ℂ) 1, phi.fn z ≠ 0)
    (G : SmirnovToeplitzNPlusElement V) :
    SmirnovToeplitzNPlusElement
      (smirnovToeplitzSymbolMul (diskMultiplierPhaseReflectionSymbol phi) V) where
  toSmirnovToeplitzKernelElement :=
    (diskMultiplierSmirnovToeplitzElement phi hphi).mul G.toKernelElement
  forward_locallyIntegrable := by
    let F := DiskSmirnovBoundary.ofMultiplier phi
    have hproduct : LocallyIntegrable
        (fun x => diskMultiplierLineBoundary phi x *
          G.toKernelElement.forward.boundary x) volume :=
      locallyIntegrable_bounded_mul_left G.forward_locallyIntegrable
        (measurable_diskMultiplierLineBoundary phi)
        (ae_norm_diskMultiplierLineBoundary_le phi)
    have hboundary :
        ((F.mul G.toKernelElement.forward).boundary) =ᵐ[volume]
          fun x => diskMultiplierLineBoundary phi x *
            G.toKernelElement.forward.boundary x := by
      filter_upwards [F.boundary_mul_ae G.toKernelElement.forward,
        DiskSmirnovBoundary.boundary_ofMultiplier_ae phi] with x hmul hphiBoundary
      rw [hmul, hphiBoundary]
    exact hproduct.congr hboundary.symm

end

end GaloisForLFunctions.HTGeometry
