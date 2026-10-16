import GaloisForLFunctions.HTGeometry.OneChannelCanonicalSplitting
import GaloisForLFunctions.RHTower.PaperThetaNativeMeyerCompleteness
import GaloisForLFunctions.RHTower.PaperThetaNativeResonantSplitting

/-!
# Multiplicity-exact observation of the native resonant pencil

The actual Grushin inverse and theta moment form a one-channel parametrix
on the original bounded continuous function space. Native Meyer completeness
identifies its maximal root space and its dimension with the full Xi divisor
multiplicity. The first nonzero iterated source reading is therefore forced
to occur at that exact multiplicity; no simplicity or spectral premise enters.
-/

noncomputable section
open Complex Set Module
open scoped BoundedContinuousFunction

namespace RHTower.PaperThetaEndpoint
open HTGeometry

def nativeXiResonance (rho : XiDivisorSupport) : NativeResonantParameter :=
  ⟨xiSpectralPointSupport rho,Or.inr (XiC_xiSpectralPointSupport_eq_zero rho)⟩

def nativeResonantPartialInverse (z : ℂ) : NativeContinuousSpace →L[ℂ] NativeContinuousSpace :=
  (ContinuousLinearMap.fst ℂ NativeContinuousSpace ℂ).comp
    ((nativeGrushinInverse z).comp (ContinuousLinearMap.inl ℂ NativeContinuousSpace ℂ))

@[simp] theorem nativeResonantPartialInverse_apply (z : ℂ) (g : NativeContinuousSpace) :
    nativeResonantPartialInverse z g = nativeResonantParticular z g := rfl

def nativeResonantMoment (z : ℂ) : NativeContinuousSpace →L[ℂ] ℂ :=
  (nativeCounterMass : ℂ)⁻¹ • boundedThetaMomentCLM z

@[simp] theorem nativeResonantMoment_apply (z : ℂ) (g : NativeContinuousSpace) :
    nativeResonantMoment z g = boundedThetaMomentCLM z g/(nativeCounterMass : ℂ) := by
  change (nativeCounterMass : ℂ)⁻¹*boundedThetaMomentCLM z g = _
  rw [div_eq_mul_inv,mul_comm]

def nativeResonantChannel (rho : XiDivisorSupport) : OneChannelParametrix ℂ NativeContinuousSpace where
  pencil := (nativePencil (xiSpectralPointSupport rho)).toLinearMap
  partialInverse := (nativeResonantPartialInverse (xiSpectralPointSupport rho)).toLinearMap
  source := nativeCounterSource (xiSpectralPointSupport rho)
  mode := nativeResonantVector (xiSpectralPointSupport rho)
  moment := (nativeResonantMoment (xiSpectralPointSupport rho)).toLinearMap
  trace := (boundedResolventTrace nativeCompactParameter).toLinearMap
  right g := by
    change nativePencil (xiSpectralPointSupport rho) (nativeResonantPartialInverse (xiSpectralPointSupport rho) g) =
      g-nativeResonantMoment (xiSpectralPointSupport rho) g • nativeCounterSource (xiSpectralPointSupport rho)
    rw [nativeResonantPartialInverse_apply,nativeResonantMoment_apply]
    exact
      nativeResonantParticular_equation (xiSpectralPointSupport rho) g
  left g := by
    have h := ((nativeResonant_full_solution (nativeXiResonance rho)
      (nativePencil (xiSpectralPointSupport rho) g) g).mp rfl).2
    change nativeResonantParticular (xiSpectralPointSupport rho)
      (nativePencil (xiSpectralPointSupport rho) g) =
      g-boundedResolventTrace nativeCompactParameter g • nativeResonantVector (xiSpectralPointSupport rho)
    exact eq_sub_of_add_eq h.symm
  mode_kernel := nativeResonantVector_equation (nativeXiResonance rho)
  moment_range g := by
    change nativeResonantMoment (xiSpectralPointSupport rho) (nativePencil (xiSpectralPointSupport rho) g) = 0
    rw [nativeResonantMoment_apply]
    have h := ((nativeResonant_full_solution (nativeXiResonance rho)
      (nativePencil (xiSpectralPointSupport rho) g) g).mp rfl).1
    change boundedThetaMomentCLM (xiSpectralPointSupport rho)
      (nativePencil (xiSpectralPointSupport rho) g) = 0 at h
    rw [h,zero_div]
  trace_mode := nativeResonantVector_trace (xiSpectralPointSupport rho)

theorem nativeResonantChannel_root (rho : XiDivisorSupport) :
    (nativeResonantChannel rho).rootSpace = NativeXiRootBlock rho := by
  ext g
  rw [(nativeResonantChannel rho).mem_rootSpace,Module.End.mem_maxGenEigenspace]
  exact exists_congr (fun n => nativePencil_pow_kernel_iff rho n g)

instance nativeResonantChannel_finiteDimensional (rho : XiDivisorSupport) :
    FiniteDimensional ℂ (nativeResonantChannel rho).rootSpace := by
  rw [nativeResonantChannel_root]
  infer_instance

theorem nativeResonantChannel_rank (rho : XiDivisorSupport) :
    (nativeResonantChannel rho).rank = xiSupportMultiplicity rho := by
  change Module.finrank ℂ (nativeResonantChannel rho).rootSpace = _
  rw [nativeResonantChannel_root]
  exact finrank_nativeXiRootBlock rho

def nativeConfluentMoment (rho : XiDivisorSupport) (j : ℕ) : NativeContinuousSpace →L[ℂ] ℂ :=
  (nativeResonantMoment (xiSpectralPointSupport rho)).comp
    (nativeResonantPartialInverse (xiSpectralPointSupport rho)^j)

@[simp] theorem nativeConfluentMoment_apply (rho : XiDivisorSupport) (j : ℕ) (g : NativeContinuousSpace) :
    nativeConfluentMoment rho j g = (nativeResonantChannel rho).row j g := by
  change nativeResonantMoment (xiSpectralPointSupport rho)
      ((nativeResonantPartialInverse (xiSpectralPointSupport rho)^j) g) =
    nativeResonantMoment (xiSpectralPointSupport rho)
      (((nativeResonantPartialInverse (xiSpectralPointSupport rho)).toLinearMap^j) g)
  rw [← ContinuousLinearMap.coe_pow]
  rfl

/-- The first surviving actual theta reading occurs at the full original Xi multiplicity. -/
theorem nativeConfluentMoment_exact_order (rho : XiDivisorSupport) :
    (∀ j < xiSupportMultiplicity rho-1,
      nativeResonantMoment (xiSpectralPointSupport rho)
        ((nativeResonantPartialInverse (xiSpectralPointSupport rho)^j)
          (nativeResonantVector (xiSpectralPointSupport rho)))=0) ∧
    nativeResonantMoment (xiSpectralPointSupport rho)
      ((nativeResonantPartialInverse (xiSpectralPointSupport rho)^(xiSupportMultiplicity rho-1))
        (nativeResonantVector (xiSpectralPointSupport rho)))≠0 := by
  have h := (nativeResonantChannel rho).obstruction_order
  simp only [OneChannelParametrix.chain, nativeResonantChannel,
    ← ContinuousLinearMap.coe_pow, ContinuousLinearMap.coe_coe] at h
  change (∀ j < (nativeResonantChannel rho).rank-1,
      nativeResonantMoment (xiSpectralPointSupport rho)
        ((nativeResonantPartialInverse (xiSpectralPointSupport rho)^j)
          (nativeResonantVector (xiSpectralPointSupport rho)))=0) ∧
    nativeResonantMoment (xiSpectralPointSupport rho)
      ((nativeResonantPartialInverse (xiSpectralPointSupport rho)^((nativeResonantChannel rho).rank-1))
        (nativeResonantVector (xiSpectralPointSupport rho)))≠0 at h
  rwa [nativeResonantChannel_rank] at h

end RHTower.PaperThetaEndpoint
