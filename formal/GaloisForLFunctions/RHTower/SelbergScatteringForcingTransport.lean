import GaloisForLFunctions.RHTower.SelbergScatteringSourceGraph
import GaloisForLFunctions.HTGeometry.ResolventCompactness

/-!
# Exact transport of the original cutoff forcing

The completed native graph theorem identifies the original corrected source
with the actual bounded resolvent of its original forcing, at the full complex
Xi scattering energy. Composing that resolvent with the already constructed
entire covariance gives an exact bounded forcing-to-residual operator and the
normalized residual formula. No forcing cancellation or occurrence is asserted.
-/

open GaloisForLFunctions.HTGeometry
namespace RHTower.SelbergScatteringForcingTransport
open D4BMModularCore SelbergScatteringNativeResidual SelbergScatteringEntireOperator
open SelbergScatteringSourceVector SelbergScatteringSourceGraph SelbergScatteringEntireXiPackets
noncomputable section

/-- The full native scattering energy is nonreal at every actual Xi copy. -/
theorem scatteringEnergy_nonreal (q : XiZeroCopy) : (scatteringEnergy (q.1:ℂ)).im ≠ 0 := by
  exact abs_pos.mp (by rw [xi_scatteringEnergy_abs_im]; exact xiResidualFloor_pos q)

/-- The actual bounded native resolvent at the full complex Xi energy. -/
def sourceResolvent (q : XiZeroCopy) : Space →L[ℂ] Space :=
  resolventCLM energyOperator_selfAdjoint (scatteringEnergy_nonreal q)

/-- Every resolvent response lies in the original native graph domain. -/
theorem sourceResolvent_mem_domain (q : XiZeroCopy) (f : Space) :
    sourceResolvent q f ∈ energyOperator.domain :=
  resolventLinear_mem energyOperator_selfAdjoint (scatteringEnergy_nonreal q) f

/-- The exact inverse equation holds for every actual native forcing vector. -/
theorem sourceResolvent_equation (q : XiZeroCopy) (f : Space) :
    energyOperator ⟨sourceResolvent q f,sourceResolvent_mem_domain q f⟩ -
      scatteringEnergy (q.1:ℂ) • sourceResolvent q f = f :=
  shiftedMap_resolventLinear energyOperator_selfAdjoint (scatteringEnergy_nonreal q) f

/-- The native resolvent retains its positive full-Xi imaginary-part bound. -/
theorem sourceResolvent_norm_le (q : XiZeroCopy) (f : Space) :
    ‖sourceResolvent q f‖ ≤ (xiResidualFloor q)⁻¹ * ‖f‖ := by
  simpa only [sourceResolvent,resolventCLM_apply,xi_scatteringEnergy_abs_im] using
    norm_resolventLinear_le energyOperator_selfAdjoint (scatteringEnergy_nonreal q) f

/-- The constructed original source, not an independently chosen weak response,
is exactly the native resolvent of its complete original cutoff forcing. -/
theorem sourceResolvent_original_forcing (q : XiZeroCopy) :
    sourceResolvent q (SelbergScatteringCutoffForcing.forcingVector q) = sourceVector q := by
  have he := injective_shiftedMap energyOperator_selfAdjoint (scatteringEnergy_nonreal q)
    (a₁ := ⟨sourceResolvent q (SelbergScatteringCutoffForcing.forcingVector q),
      sourceResolvent_mem_domain q _⟩) (a₂ := sourceNativeDomain q)
    (by simp only [shiftedMap_apply,sourceResolvent_equation,sourceNativeDomain_equation])
  exact congrArg Subtype.val he

/-- Exact bounded transport from original native forcing to the entire residual. -/
def entireForcingTransport (q : XiZeroCopy) : Space →L[ℂ] Space :=
  ((1 : Space →L[ℂ] Space) - (2+xiEntireTarget q) • entireCovariance).comp (sourceResolvent q)

/-- The transport acts on the complete forcing response and retains the full Xi target. -/
theorem entireForcingTransport_apply (q : XiZeroCopy) (f : Space) :
    entireForcingTransport q f = sourceResolvent q f -
      (2+xiEntireTarget q) • entireCovariance (sourceResolvent q f) := rfl

/-- The original entire residual is precisely the transported original forcing. -/
theorem sourceResidual_eq_transported_forcing (q : XiZeroCopy) :
    sourceResidual q = entireForcingTransport q (SelbergScatteringCutoffForcing.forcingVector q) := by
  rw [entireForcingTransport_apply,sourceResolvent_original_forcing]
  rfl

/-- Exact entire-domain forced equation with the original differential forcing
identified through the actual bounded resolvent. -/
theorem sourceDomainVector_transported_equation (q : XiZeroCopy) :
    entireOperator (sourceDomainVector q) - xiEntireTarget q • (sourceDomainVector q : Space) =
      entireForcingTransport q (SelbergScatteringCutoffForcing.forcingVector q) := by
  rw [sourceDomainVector_equation,sourceResidual_eq_transported_forcing]

/-- Normalization leaves an exact ratio of transported original forcing to its
actual nonzero covariance response; neither numerator nor denominator is postulated. -/
theorem sourceUnitVector_transported_residual_norm (q : XiZeroCopy) :
    ‖entireOperator (sourceUnitVector q) - xiEntireTarget q • (sourceUnitVector q : Space)‖ =
      ‖entireCovariance (sourceResolvent q (SelbergScatteringCutoffForcing.forcingVector q))‖⁻¹ *
        ‖entireForcingTransport q (SelbergScatteringCutoffForcing.forcingVector q)‖ := by
  rw [sourceUnitVector_residual_norm,sourceResolvent_original_forcing,
    sourceResidual_eq_transported_forcing]

end
end RHTower.SelbergScatteringForcingTransport
