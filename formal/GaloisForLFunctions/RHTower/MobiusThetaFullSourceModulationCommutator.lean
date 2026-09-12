import GaloisForLFunctions.RHTower.MobiusThetaInternalJetPrimeNormalComplexGraph
import GaloisForLFunctions.HTGeometry.L1PeriodizationFourier

/-!
# Finite modulation of the complete arithmetic source

Modulation in the original coordinate and modulation inside each translated theta packet
are different operations. Their complete source difference has an admitted Fourier--Laplace
integral equal to the difference of the actual residual multipliers times the unchanged
internal Xi jet. No derivative exchange or zero-location hypothesis enters this identity.

This identifies the source of the two-parameter multiplier variation. It does not assert
that the fixed Gamma/BV physical reader annihilates this source.
-/

open Complex Real MeasureTheory

noncomputable section
namespace RHTower

/-- Modulation in the local coordinate of each original arithmetic packet. -/
def mobiusThetaResidualLocalModulationTerm
    (k p m : ℕ) (delta : ℂ) (j : ℕ) (x : ℝ) : ℂ :=
  Complex.exp (-I * delta *
    ((x - (m : ℝ) * (Real.log (p + j) - Real.log p) : ℝ) : ℂ)) *
      mobiusThetaInternalJetPrimeNormalResidualSourceTerm k p m j x

/-- All arithmetic labels are retained before a Fourier--Laplace reader is selected. -/
def mobiusThetaResidualLocalModulationSource
    (k p m : ℕ) (delta : ℂ) (x : ℝ) : ℂ :=
  ∑' j : ℕ, mobiusThetaResidualLocalModulationTerm k p m delta j x

private def localModulationIntegrand
    (k p m : ℕ) (v delta : ℂ) (j : ℕ) (x : ℝ) : ℂ :=
  Complex.exp (-I * v * (x : ℂ)) *
    mobiusThetaResidualLocalModulationTerm k p m delta j x

private theorem thetaJet_modulation (k : ℕ) (v delta : ℂ) (y : ℝ) :
    Complex.exp (-I * delta * (y : ℂ)) * thetaCuspFourierLaplaceJetIntegrand k v y =
      thetaCuspFourierLaplaceJetIntegrand k (v + delta) y := by
  unfold thetaCuspFourierLaplaceJetIntegrand thetaCuspFourierLaplaceIntegrand
  have he : Complex.exp (-I * delta * (y : ℂ)) * Complex.exp (-I * v * (y : ℂ)) =
      Complex.exp (-I * (v + delta) * (y : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  calc
    _ = (-I * (y : ℂ)) ^ k *
        ((Complex.exp (-I * delta * (y : ℂ)) * Complex.exp (-I * v * (y : ℂ))) *
          (thetaCuspFullSource y : ℂ)) := by ring
    _ = _ := by rw [he]

private theorem localModulationIntegrand_eq
    {p : ℕ} (hp : 0 < p) (k m : ℕ) (v delta : ℂ) (j : ℕ) (x : ℝ) :
    localModulationIntegrand k p m v delta j x =
      mobiusThetaPrimeNormalResidualSpectralCoefficient p m v j *
        thetaCuspFourierLaplaceJetIntegrand k (v + delta)
          (x - (m : ℝ) * (Real.log (p + j) - Real.log p)) := by
  let y := x - (m : ℝ) * (Real.log (p + j) - Real.log p)
  calc
    _ = Complex.exp (-I * delta * (y : ℂ)) *
        mobiusThetaInternalJetPrimeNormalResidualIntegrand k p m v j x := by
      unfold localModulationIntegrand mobiusThetaResidualLocalModulationTerm
        mobiusThetaInternalJetPrimeNormalResidualIntegrand
      dsimp only [y]
      ring
    _ = mobiusThetaPrimeNormalResidualSpectralCoefficient p m v j *
        (Complex.exp (-I * delta * (y : ℂ)) *
          thetaCuspFourierLaplaceJetIntegrand k v y) := by
      rw [mobiusThetaInternalJetPrimeNormalResidualIntegrand_eq hp]
      ring
    _ = _ := by rw [thetaJet_modulation]

/-- Absolute admission and exact value of the locally modulated complete source.
The arithmetic coefficients are tested at `v`; the internal theta packet is tested at
`v + delta`. These two domain conditions are kept separate. -/
theorem mobiusThetaResidualLocalModulationSource_fourierLaplace_data
    {p m : ℕ} (hp : 0 < p) (hm : m ≠ 0) (k : ℕ) {v delta : ℂ}
    (hw : |(v + delta).im| < 1)
    (hv : 1 / (m : ℝ) < (mobiusThetaCenteredParameter v).re) :
    Integrable (fun x : ℝ => Complex.exp (-I * v * (x : ℂ)) *
      mobiusThetaResidualLocalModulationSource k p m delta x) ∧
    (∫ x : ℝ, Complex.exp (-I * v * (x : ℂ)) *
      mobiusThetaResidualLocalModulationSource k p m delta x) =
      mobiusThetaPrimeNormalResidualMultiplier p m v * iteratedDeriv k XiC (v + delta) := by
  have hi (j : ℕ) : Integrable (localModulationIntegrand k p m v delta j) := by
    change Integrable (fun x : ℝ => localModulationIntegrand k p m v delta j x)
    simp_rw [localModulationIntegrand_eq hp]
    exact ((integrable_thetaCuspFourierLaplaceJetIntegrand k hw).comp_add_right
      (-((m : ℝ) * (Real.log (p + j) - Real.log p)))).const_mul _
  have hn (j : ℕ) :
      (∫ x : ℝ, ‖localModulationIntegrand k p m v delta j x‖) =
        ‖mobiusThetaPrimeNormalResidualSpectralCoefficient p m v j‖ *
          ∫ x : ℝ, ‖thetaCuspFourierLaplaceJetIntegrand k (v + delta) x‖ := by
    simp_rw [localModulationIntegrand_eq hp, norm_mul]
    rw [integral_const_mul]
    congr 1
    simpa only [sub_eq_add_neg] using integral_add_right_eq_self
      (fun x : ℝ => ‖thetaCuspFourierLaplaceJetIntegrand k (v + delta) x‖)
      (-((m : ℝ) * (Real.log (p + j) - Real.log p)))
  have hs : Summable (fun j : ℕ => ∫ x : ℝ,
      ‖localModulationIntegrand k p m v delta j x‖) := by
    simp_rw [hn]
    exact (summable_norm_mobiusThetaPrimeNormalResidualSpectralCoefficient hm hv).mul_right _
  have he (x : ℝ) : Complex.exp (-I * v * (x : ℂ)) *
      mobiusThetaResidualLocalModulationSource k p m delta x =
        ∑' j : ℕ, localModulationIntegrand k p m v delta j x := by
    rw [mobiusThetaResidualLocalModulationSource, ← tsum_mul_left]
    rfl
  simp_rw [he]
  refine ⟨GaloisForLFunctions.HTGeometry.integrable_tsum_of_summable_integral_norm hi hs, ?_⟩
  rw [← integral_tsum_of_summable_integral_norm hi hs]
  have ht (j : ℕ) :
      (∫ x : ℝ, localModulationIntegrand k p m v delta j x) =
        mobiusThetaPrimeNormalResidualSpectralCoefficient p m v j *
          iteratedDeriv k XiC (v + delta) := by
    simp_rw [localModulationIntegrand_eq hp]
    rw [integral_const_mul]
    have hshift := integral_add_right_eq_self (μ := (volume : Measure ℝ))
      (thetaCuspFourierLaplaceJetIntegrand k (v + delta))
      (-((m : ℝ) * (Real.log (p + j) - Real.log p)))
    simp only [← sub_eq_add_neg] at hshift
    rw [hshift, ← iteratedDeriv_XiC_eq_integral_thetaCuspFourierLaplaceJet k (abs_lt.mp hw)]
  simp_rw [ht]
  rw [tsum_mul_right]
  rfl

private theorem localModulationSource_zero (k p m : ℕ) (x : ℝ) :
    mobiusThetaResidualLocalModulationSource k p m 0 x =
      mobiusThetaInternalJetPrimeNormalResidualSource k p m x := by
  simp [mobiusThetaResidualLocalModulationSource, mobiusThetaResidualLocalModulationTerm,
    mobiusThetaInternalJetPrimeNormalResidualSource]

/-- The literal difference between external modulation and local packet modulation.
This is the modulation commutator on the original complete arithmetic source. -/
def mobiusThetaFullSourceModulationCommutator
    (k p m : ℕ) (delta : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (-I * delta * (x : ℂ)) *
    mobiusThetaInternalJetPrimeNormalResidualSource k p m x -
      mobiusThetaResidualLocalModulationSource k p m delta x

/-- The retained multiplier variation is an admitted transform of the literal complete
source commutator. No trace cyclicity or physical-reader annihilation is asserted. -/
theorem mobiusThetaFullSourceModulationCommutator_fourierLaplace_data
    {p m : ℕ} (hp : 0 < p) (hm : m ≠ 0) (k : ℕ) {v delta : ℂ}
    (hw : |(v + delta).im| < 1)
    (hv : 1 / (m : ℝ) < (mobiusThetaCenteredParameter v).re)
    (hwc : 1 / (m : ℝ) < (mobiusThetaCenteredParameter (v + delta)).re) :
    Integrable (fun x : ℝ => Complex.exp (-I * v * (x : ℂ)) *
      mobiusThetaFullSourceModulationCommutator k p m delta x) ∧
    (∫ x : ℝ, Complex.exp (-I * v * (x : ℂ)) *
      mobiusThetaFullSourceModulationCommutator k p m delta x) =
      (mobiusThetaPrimeNormalResidualMultiplier p m (v + delta) -
        mobiusThetaPrimeNormalResidualMultiplier p m v) *
          iteratedDeriv k XiC (v + delta) := by
  have hlocal := mobiusThetaResidualLocalModulationSource_fourierLaplace_data hp hm k hw hv
  have horiginal :
      Integrable (fun x : ℝ => Complex.exp (-I * (v + delta) * (x : ℂ)) *
        mobiusThetaInternalJetPrimeNormalResidualSource k p m x) ∧
      (∫ x : ℝ, Complex.exp (-I * (v + delta) * (x : ℂ)) *
        mobiusThetaInternalJetPrimeNormalResidualSource k p m x) =
        mobiusThetaPrimeNormalResidualMultiplier p m (v + delta) *
          iteratedDeriv k XiC (v + delta) := by
    simpa only [add_zero, localModulationSource_zero] using
      (mobiusThetaResidualLocalModulationSource_fourierLaplace_data hp hm k
        (v := v + delta) (delta := 0) (by simpa only [add_zero] using hw) hwc)
  have he (x : ℝ) : Complex.exp (-I * v * (x : ℂ)) *
      mobiusThetaFullSourceModulationCommutator k p m delta x =
      Complex.exp (-I * (v + delta) * (x : ℂ)) *
        mobiusThetaInternalJetPrimeNormalResidualSource k p m x -
      Complex.exp (-I * v * (x : ℂ)) *
        mobiusThetaResidualLocalModulationSource k p m delta x := by
    have hphase : Complex.exp (-I * v * (x : ℂ)) *
        Complex.exp (-I * delta * (x : ℂ)) =
          Complex.exp (-I * (v + delta) * (x : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    unfold mobiusThetaFullSourceModulationCommutator
    rw [mul_sub, ← mul_assoc, hphase]
  simp_rw [he]
  refine ⟨horiginal.1.sub hlocal.1, ?_⟩
  rw [integral_sub horiginal.1 hlocal.1, horiginal.2, hlocal.2, sub_mul]

end RHTower
