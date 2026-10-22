import GaloisForLFunctions.RHTower.Suzuki.SuzukiFiniteShiftProjectiveHolonomy

/-!
# The finite shift is small, and its limit is the generator

The exact finite-shift carrier identities carry a nonvanishing hypothesis on the *shifted* source
`F + δ J` at the reflected point.  That hypothesis is not independent: it holds for every shift
smaller than the endpoint value, hence for all sufficiently small shifts whenever the unshifted
source is nonzero there.

On that punctured neighbourhood the exact divided difference has a limit, and the limit is the
logarithmic source generator dressed by the Cayley factor and the reflection ratio.  So the finite
identity is the global form of the infinitesimal one, with no remainder at either end.
-/

open Filter Topology Complex

namespace GaloisForLFunctions.RHTower

noncomputable section

/-! ## The shifted source is nonzero for small shifts -/

/-- A shift smaller than the endpoint value cannot cancel it. -/
theorem suzukiFiniteShiftSource_ne_zero
    {F J : ℂ → ℂ} {δ w : ℂ} (hδ : ‖δ‖ * ‖J w‖ < ‖F w‖) :
    suzukiFiniteShiftSource F J δ w ≠ 0 := by
  intro h
  rw [suzukiFiniteShiftSource] at h
  have hcancel : δ * J w = -F w := by
    linear_combination h
  have hnorm : ‖δ * J w‖ = ‖F w‖ := by
    rw [hcancel, norm_neg]
  rw [norm_mul] at hnorm
  linarith

/-- Hence the shifted source is nonzero for all sufficiently small shifts. -/
theorem eventually_suzukiFiniteShiftSource_ne_zero
    {F J : ℂ → ℂ} {w : ℂ} (hF : F w ≠ 0) :
    ∀ᶠ δ : ℂ in nhds 0, suzukiFiniteShiftSource F J δ w ≠ 0 := by
  have hcont : ContinuousAt (fun δ : ℂ => suzukiFiniteShiftSource F J δ w) 0 := by
    have h : Continuous (fun δ : ℂ => F w + δ * J w) :=
      continuous_const.add (continuous_id.mul continuous_const)
    simpa [suzukiFiniteShiftSource] using h.continuousAt
  have hval : (fun δ : ℂ => suzukiFiniteShiftSource F J δ w) 0 ≠ 0 := by
    simpa [suzukiFiniteShiftSource] using hF
  exact hcont.eventually_ne hval

/-! ## The divided difference converges to the generator -/

/-- The shifted source tends to the unshifted one. -/
theorem tendsto_suzukiFiniteShiftSource
    (F J : ℂ → ℂ) (w : ℂ) :
    Tendsto (fun δ : ℂ => suzukiFiniteShiftSource F J δ w) (nhds 0) (nhds (F w)) := by
  have h : Tendsto (fun δ : ℂ => F w + δ * J w) (nhds 0) (nhds (F w + 0 * J w)) :=
    tendsto_const_nhds.add (Filter.Tendsto.mul tendsto_id tendsto_const_nhds)
  simpa [suzukiFiniteShiftSource] using h

/-- **Finite-to-infinitesimal law, first form.**  The exact finite divided difference of the
Fourier--Livšic carrier converges, as the shift tends to zero, to the reflected tangent
determinant normalized by the squared reflected endpoint value. -/
theorem tendsto_suzukiFourierLivsic_finiteShift_dividedDifference
    {F J : ℂ → ℂ} {z : ℂ} (hz : z + I ≠ 0) (hFneg : F (-z) ≠ 0) :
    Tendsto (fun δ : ℂ =>
        (suzukiLivsicQuotient
              (suzukiFourierNumerator (suzukiFiniteShiftSource F J δ))
              (suzukiFourierDenominator (suzukiFiniteShiftSource F J δ)) z -
            suzukiLivsicQuotient (suzukiFourierNumerator F)
              (suzukiFourierDenominator F) z) / δ)
      (nhdsWithin 0 {(0 : ℂ)}ᶜ)
      (nhds (GaloisForLFunctions.HTGeometry.lineCayley z *
        (suzukiReflectionTangentNumerator F J z / (F (-z) * F (-z))))) := by
  have hden : Tendsto
      (fun δ : ℂ => suzukiFiniteShiftSource F J δ (-z) * F (-z)) (nhds 0)
      (nhds (F (-z) * F (-z))) :=
    (tendsto_suzukiFiniteShiftSource F J (-z)).mul tendsto_const_nhds
  have hquot : Tendsto (fun δ : ℂ =>
      GaloisForLFunctions.HTGeometry.lineCayley z *
        (suzukiReflectionTangentNumerator F J z /
          (suzukiFiniteShiftSource F J δ (-z) * F (-z)))) (nhds 0)
      (nhds (GaloisForLFunctions.HTGeometry.lineCayley z *
        (suzukiReflectionTangentNumerator F J z / (F (-z) * F (-z))))) :=
    tendsto_const_nhds.mul
      (tendsto_const_nhds.div hden (mul_ne_zero hFneg hFneg))
  refine (hquot.mono_left nhdsWithin_le_nhds).congr' ?_
  have hne : ∀ᶠ δ : ℂ in nhdsWithin 0 {(0 : ℂ)}ᶜ,
      suzukiFiniteShiftSource F J δ (-z) ≠ 0 :=
    nhdsWithin_le_nhds (eventually_suzukiFiniteShiftSource_ne_zero (J := J) hFneg)
  filter_upwards [hne, self_mem_nhdsWithin] with δ hδne hδzero
  exact (suzukiFourierLivsic_finiteShift_dividedDifference hδzero hz hδne hFneg).symm

/-- **Finite-to-infinitesimal law, generator form.**  The same limit is the logarithmic source
generator, dressed by the Cayley factor and the reflection ratio. -/
theorem tendsto_suzukiFourierLivsic_finiteShift_dividedDifference_generator
    {F J : ℂ → ℂ} {z : ℂ} (hz : z + I ≠ 0) (hFz : F z ≠ 0) (hFneg : F (-z) ≠ 0) :
    Tendsto (fun δ : ℂ =>
        (suzukiLivsicQuotient
              (suzukiFourierNumerator (suzukiFiniteShiftSource F J δ))
              (suzukiFourierDenominator (suzukiFiniteShiftSource F J δ)) z -
            suzukiLivsicQuotient (suzukiFourierNumerator F)
              (suzukiFourierDenominator F) z) / δ)
      (nhdsWithin 0 {(0 : ℂ)}ᶜ)
      (nhds (-(GaloisForLFunctions.HTGeometry.lineCayley z *
        (suzukiLogarithmicSourceGenerator F J z * F z / F (-z))))) := by
  have hgen :=
    suzukiLogarithmicSourceGenerator_eq_neg_reflectionTangent (G := J) hFz hFneg
  have hrewrite :
      GaloisForLFunctions.HTGeometry.lineCayley z *
          (suzukiReflectionTangentNumerator F J z / (F (-z) * F (-z))) =
        -(GaloisForLFunctions.HTGeometry.lineCayley z *
          (suzukiLogarithmicSourceGenerator F J z * F z / F (-z))) := by
    rw [hgen]
    field_simp
  rw [← hrewrite]
  exact tendsto_suzukiFourierLivsic_finiteShift_dividedDifference hz hFneg

end

end GaloisForLFunctions.RHTower
