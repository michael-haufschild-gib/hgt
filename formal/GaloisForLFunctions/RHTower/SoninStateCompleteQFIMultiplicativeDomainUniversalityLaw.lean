import GaloisForLFunctions.RHTower.SoninLogClockQFIPhysicalityUniversalityLaw
import GaloisForLFunctions.RHTower.SoninLogClockMultiplicativeDomain
import GaloisForLFunctions.HTGeometry.ConstraintCodeReducingSubspace

/-!
# Sonin state-complete QFI multiplicative-domain universality

For a self-adjoint Sonin observable, zero erased logarithmic-clock quantum Fisher information on
every normalized physical state is not merely a pointwise preservation test.  The full physical
sector is a complete test family: its QFI vanishes identically exactly when the observable lies in
the global multiplicative domain of logarithmic Fourier scattering.

The converse uses the invariant-sector projector.  QFI-zero makes its range invariant under the
observable, and self-adjointness upgrades that invariant subspace to a reducing subspace.  Since
the projector is `(1+S)/2`, reduction is exactly commutation with scattering.
-/

open Complex
open scoped InnerProductSpace

namespace RHTower

noncomputable section

/-- **Sonin state-complete QFI multiplicative-domain law.**  For a self-adjoint observable, its
complete star-Kadison defect vanishes exactly when erased QFI vanishes on every normalized
physical Sonin state. -/
theorem
    soninLogFourierObservableTwirlStarKadisonDefect_eq_zero_iff_forall_physical_erasedQFI
    (X : SoninL2 →L[ℂ] SoninL2) (hX : IsSelfAdjoint X) :
    soninLogFourierObservableTwirlStarKadisonDefect X = 0 ↔
      ∀ ψ : SoninL2, ‖ψ‖ = 1 →
        GaloisForLFunctions.PhysicalState
          (soninLogFourierScattering - 1).toLinearMap ψ →
        HTGeometry.pureStateQuantumFisherValue (‖ψ‖ ^ 2)
          (‖inner ℂ ψ ((1 - soninLogFourierInvariantAverage) (X ψ))‖)
          (‖(1 - soninLogFourierInvariantAverage) (X ψ)‖ ^ 2) = 0 := by
  constructor
  · intro hdefect ψ hψnorm hψ
    have hcomm :
        soninLogFourierScattering * X =
          X * soninLogFourierScattering :=
      (soninLogFourierObservableTwirlStarKadisonDefect_eq_zero_iff_commutes X).mp
        hdefect
    apply (soninLogClock_erasedPureStateQuantumFisherValue_eq_zero_iff_observedPhysical
      X hψnorm hψ).mpr
    rw [GaloisForLFunctions.PhysicalState] at hψ ⊢
    change (soninLogFourierScattering - 1) ψ = 0 at hψ
    change (soninLogFourierScattering - 1) (X ψ) = 0
    have hfixed : soninLogFourierScattering ψ = ψ := by
      apply sub_eq_zero.mp
      simpa only [_root_.sub_apply, one_apply_eq_self] using hψ
    change soninLogFourierScattering (X ψ) - X ψ = 0
    rw [← mul_apply_eq_comp, hcomm,
      mul_apply_eq_comp, hfixed, sub_self]
  · intro hall
    let P : SoninL2 →L[ℂ] SoninL2 := soninLogFourierInvariantAverage
    have hP2 : P * P = P :=
      soninLogFourierInvariantAverage_isIdempotentElem
    have hPadj : IsSelfAdjoint P :=
      soninLogFourierInvariantAverage_isSelfAdjoint
    have hdepart : (1 - P) * X * P = 0 := by
      apply ContinuousLinearMap.ext
      intro v
      simp only [mul_apply_eq_comp]
      let y : SoninL2 := P v
      by_cases hy : y = 0
      · simp [y, hy]
      · let c : ℂ := (‖y‖ : ℂ)⁻¹
        let ψ : SoninL2 := c • y
        have hynorm : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
        have hc : c ≠ 0 :=
          inv_ne_zero (Complex.ofReal_ne_zero.mpr hynorm)
        have hψnorm : ‖ψ‖ = 1 := by
          rw [show ψ = c • y by rfl, norm_smul]
          simp only [c, norm_inv, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (norm_nonneg y)]
          exact inv_mul_cancel₀ hynorm
        have hPy : P y = y := by
          change P (P v) = P v
          rw [← mul_apply_eq_comp, hP2]
        have hPψ : P ψ = ψ := by
          simp only [ψ, map_smul, hPy]
        have hψphysical :
            GaloisForLFunctions.PhysicalState
              (soninLogFourierScattering - 1).toLinearMap ψ :=
          (physicalState_soninLogFourierScattering_iff_invariantAverage_fixed ψ).mpr
            (by simpa only [P] using hPψ)
        have hqfi := hall ψ hψnorm hψphysical
        have hXphysical :=
          (soninLogClock_erasedPureStateQuantumFisherValue_eq_zero_iff_observedPhysical
            X hψnorm hψphysical).mp hqfi
        have hPX : P (X ψ) = X ψ :=
          (physicalState_soninLogFourierScattering_iff_invariantAverage_fixed (X ψ)).mp
            hXphysical
        have hcompψ : (1 - P) (X ψ) = 0 := by
          simp only [_root_.sub_apply, one_apply_eq_self, hPX,
            sub_self]
        have hscaled : c • ((1 - P) (X y)) = 0 := by
          simpa only [ψ, map_smul] using hcompψ
        have hcompy : (1 - P) (X y) = 0 :=
          (smul_eq_zero.mp hscaled).resolve_left hc
        simpa only [y] using hcompy
    have hPcomm : P * X = X * P :=
      (HTGeometry.orthogonalProjection_noDeparture_iff_commutes_selfAdjoint
        P X hP2 hPadj hX).mp hdepart
    have hcomm :
        soninLogFourierScattering * X =
          X * soninLogFourierScattering := by
      apply ContinuousLinearMap.ext
      intro v
      have hPcommv := congrArg (fun A : SoninL2 →L[ℂ] SoninL2 => A v) hPcomm
      simp only [mul_apply_eq_comp] at hPcommv
      change soninLogFourierInvariantAverage (X v) =
        X (soninLogFourierInvariantAverage v) at hPcommv
      rw [soninLogFourierInvariantAverage_apply,
        soninLogFourierInvariantAverage_apply, map_smul, map_add] at hPcommv
      change soninLogFourierScattering (X v) = X (soninLogFourierScattering v)
      have hscaled := congrArg (fun z : SoninL2 => (2 : ℂ) • z) hPcommv
      have hsum :
          X v + soninLogFourierScattering (X v) =
            X v + X (soninLogFourierScattering v) := by
        simpa only [smul_smul, mul_inv_cancel₀ (by norm_num : (2 : ℂ) ≠ 0),
          one_smul] using hscaled
      exact add_left_cancel hsum
    exact
      (soninLogFourierObservableTwirlStarKadisonDefect_eq_zero_iff_commutes X).mpr
        hcomm

end

end RHTower
