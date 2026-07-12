import GaloisForLFunctions.SchwartzSpectralMeasureForm

/-!
# Fourier pullback of continuous Schwartz forms

This module transports a continuous Schwartz sesquilinear form to the spectral side.  The physical
momentum `-i d/dx` becomes multiplication by the exact real coordinate `2πt`.  Consequently
momentum symmetry becomes symmetry of spectral-coordinate multiplication.  This is the local
algebraic input for a direct Bochner--Schwartz representation proof via spectral locality.
-/

open Complex Function Filter
open scoped SchwartzMap FourierTransform Topology

noncomputable section

namespace SchwartzMap

/-- The exact Fourier multiplier corresponding to physical momentum `-i d/dx`. -/
def spectralMomentumMultiplier (t : ℝ) : ℂ := ((2 * Real.pi * t : ℝ) : ℂ)

theorem spectralMomentumMultiplier_hasTemperateGrowth :
    spectralMomentumMultiplier.HasTemperateGrowth := by
  unfold spectralMomentumMultiplier
  fun_prop

/-- Multiplication by the exact real spectral momentum coordinate `2πt`. -/
def spectralMomentumCLM : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM ℂ spectralMomentumMultiplier

@[simp] theorem spectralMomentumCLM_apply (f : SchwartzMap ℝ ℂ) (t : ℝ) :
    spectralMomentumCLM f t = spectralMomentumMultiplier t * f t := by
  rw [spectralMomentumCLM, SchwartzMap.smulLeftCLM_apply_apply
    spectralMomentumMultiplier_hasTemperateGrowth]
  rfl

/-- Fourier transform intertwines physical momentum with spectral-coordinate multiplication. -/
theorem fourier_negI_deriv_eq_spectralMomentum (u : SchwartzMap ℝ ℂ) :
    FourierTransform.fourier ((-I) • derivCLM ℂ ℂ u) =
      spectralMomentumCLM (FourierTransform.fourier u) := by
  ext t
  rw [spectralMomentumCLM_apply]
  exact fourier_negI_deriv_apply u t

/-- Inverse Fourier transform intertwines spectral-coordinate multiplication with physical
momentum. -/
theorem fourierInv_spectralMomentum (f : SchwartzMap ℝ ℂ) :
    FourierTransform.fourierInv (spectralMomentumCLM f) =
      (-I) • derivCLM ℂ ℂ (FourierTransform.fourierInv f) := by
  have h := fourier_negI_deriv_eq_spectralMomentum
    (FourierTransform.fourierInv f)
  rw [FourierTransform.fourier_fourierInv_eq] at h
  have hi := congrArg
    (fun x : SchwartzMap ℝ ℂ => FourierTransform.fourierInv x) h
  simpa only [FourierTransform.fourierInv_fourier_eq] using hi.symm

/-- Pull a continuous Schwartz form to the spectral side by inverse Fourier transform in both
arguments. -/
def ContinuousSchwartzSesquilinearForm.fourierPullback
    (Q : ContinuousSchwartzSesquilinearForm) : ContinuousSchwartzSesquilinearForm where
  toFun f g := Q (FourierTransform.fourierInv f) (FourierTransform.fourierInv g)
  map_add_left f g h := by simp [Q.apply_add_left]
  map_smul_left c f g := by simp [Q.apply_smul_left]
  map_add_right f g h := by simp [Q.apply_add_right]
  map_smul_right c f g := by simp [Q.apply_smul_right]
  continuous := Q.continuous.comp
    ((ContinuousFourierInv.continuous_fourierInv.comp continuous_fst).prodMk
      (ContinuousFourierInv.continuous_fourierInv.comp continuous_snd))

@[simp] theorem ContinuousSchwartzSesquilinearForm.fourierPullback_apply
    (Q : ContinuousSchwartzSesquilinearForm) (f g : SchwartzMap ℝ ℂ) :
    Q.fourierPullback f g =
      Q (FourierTransform.fourierInv f) (FourierTransform.fourierInv g) := rfl

/-- Fourier pullback preserves nonnegativity. -/
theorem ContinuousSchwartzSesquilinearForm.fourierPullback_isNonnegative
    (Q : ContinuousSchwartzSesquilinearForm) (hQ : Q.IsNonnegative) :
    Q.fourierPullback.IsNonnegative := by
  intro f
  exact hQ (FourierTransform.fourierInv f)

/-- Physical momentum symmetry is exactly symmetry of multiplication by `2πt` for the spectral
pullback form. -/
theorem ContinuousSchwartzSesquilinearForm.fourierPullback_spectralMomentumSymmetric
    (Q : ContinuousSchwartzSesquilinearForm) (hQ : Q.MomentumSymmetric)
    (f g : SchwartzMap ℝ ℂ) :
    Q.fourierPullback (spectralMomentumCLM f) g =
      Q.fourierPullback f (spectralMomentumCLM g) := by
  rw [ContinuousSchwartzSesquilinearForm.fourierPullback_apply,
    ContinuousSchwartzSesquilinearForm.fourierPullback_apply,
    fourierInv_spectralMomentum, fourierInv_spectralMomentum]
  exact hQ _ _

/-- Symmetry propagates to every polynomial monomial in the spectral momentum coordinate. -/
theorem ContinuousSchwartzSesquilinearForm.fourierPullback_spectralMomentum_pow_symmetric
    (Q : ContinuousSchwartzSesquilinearForm) (hQ : Q.MomentumSymmetric)
    (n : ℕ) (f g : SchwartzMap ℝ ℂ) :
    Q.fourierPullback ((spectralMomentumCLM ^ n) f) g =
      Q.fourierPullback f ((spectralMomentumCLM ^ n) g) := by
  induction n generalizing f g with
  | zero => simp
  | succ n ih =>
      simp only [pow_succ, ContinuousLinearMap.mul_apply]
      calc
        Q.fourierPullback ((spectralMomentumCLM ^ n) (spectralMomentumCLM f)) g =
            Q.fourierPullback (spectralMomentumCLM f)
              ((spectralMomentumCLM ^ n) g) := ih _ _
        _ = Q.fourierPullback f
              (spectralMomentumCLM ((spectralMomentumCLM ^ n) g)) :=
          Q.fourierPullback_spectralMomentumSymmetric hQ _ _
        _ = Q.fourierPullback f
              ((spectralMomentumCLM ^ n) (spectralMomentumCLM g)) := by
          congr 1
          rw [← ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply]
          exact congrArg
            (fun A : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ => A g)
            (Commute.self_pow spectralMomentumCLM n).eq

end SchwartzMap
