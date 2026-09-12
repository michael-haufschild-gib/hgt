import GaloisForLFunctions.RHTower.MobiusThetaFullSourceModulationCommutator

/-!
# Modulation at the original arithmetic anchor

The complete raw residual retains every label `n = p + j` at its original translation.
Restoring this anchor in the modulation commutator introduces an additional complete-source
term. The admitted Fourier--Laplace transform retains both the half-density and the phase.
This source identity does not identify or annihilate the fixed Gamma/BV physical pairing.
-/

open Complex Real MeasureTheory

noncomputable section
namespace RHTower

/-- Complete residual at the original translations, before prime normalization. -/
def mobiusThetaInternalJetRawResidualSource (k p m : ℕ) (x : ℝ) : ℂ :=
  ∑' j : ℕ, mobiusThetaInternalJetRawHeadSource k (p + j) m x

/-- Modulation inside every raw packet, retaining its original arithmetic translation. -/
def mobiusThetaRawLocalModulationSource
    (k p m : ℕ) (delta : ℂ) (x : ℝ) : ℂ :=
  ∑' j : ℕ, Complex.exp (-I * delta *
    ((x - (m : ℝ) * Real.log (p + j) : ℝ) : ℂ)) *
      mobiusThetaInternalJetRawHeadSource k (p + j) m x

/-- Actual arithmetic multiplier of the complete raw residual. -/
def mobiusThetaRawResidualMultiplier (p m : ℕ) (w : ℂ) : ℂ :=
  ∑' j : ℕ, mobiusThetaPrimeRawAmplitude (p + j) m (mobiusThetaCenteredParameter w)

/-- External modulation minus packetwise modulation at the original anchor. -/
def mobiusThetaRawSourceModulationCommutator
    (k p m : ℕ) (delta : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (-I * delta * (x : ℂ)) *
    mobiusThetaInternalJetRawResidualSource k p m x -
      mobiusThetaRawLocalModulationSource k p m delta x

private abbrev halfDensity (p m : ℕ) : ℂ :=
  (((p : ℝ) ^ ((m : ℝ) / 2) : ℝ) : ℂ)

private abbrev anchor (p m : ℕ) : ℝ := (m : ℝ) * Real.log p

private theorem halfDensity_ne_zero {p : ℕ} (hp : 0 < p) (m : ℕ) :
    halfDensity p m ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (ne_of_gt
    (Real.rpow_pos_of_pos (by exact_mod_cast hp : (0 : ℝ) < p) _))

/-- Removing prime normalization recovers the complete original arithmetic multiplier. -/
theorem mobiusThetaRawResidualMultiplier_eq
    {p : ℕ} (hp : 0 < p) (m : ℕ) (w : ℂ) :
    (halfDensity p m)⁻¹ * Complex.exp (-I * w * (anchor p m : ℂ)) *
      mobiusThetaPrimeNormalResidualMultiplier p m w = mobiusThetaRawResidualMultiplier p m w := by
  have hc : mobiusThetaPrimeNormalResidualMultiplier p m w =
      (p : ℂ) ^ ((m : ℂ) * mobiusThetaCenteredParameter w) *
        mobiusThetaRawResidualMultiplier p m w := by
    unfold mobiusThetaPrimeNormalResidualMultiplier mobiusThetaPrimeNormalResidualSpectralCoefficient
      mobiusThetaRawResidualMultiplier mobiusThetaPrimeRawAmplitude
    rw [tsum_mul_left]
  have he : Complex.exp (-I * w * (anchor p m : ℂ)) *
      Complex.exp (I * w * (anchor p m : ℂ)) = 1 := by
    rw [← Complex.exp_add, show -I * w * (anchor p m : ℂ) +
      I * w * (anchor p m : ℂ) = 0 by ring, Complex.exp_zero]
  rw [hc, ← mobiusThetaPrimeNormal_halfDensityPhase hp]
  change (halfDensity p m)⁻¹ * Complex.exp (-I * w * (anchor p m : ℂ)) *
    (halfDensity p m * Complex.exp (I * w * (anchor p m : ℂ)) *
      mobiusThetaRawResidualMultiplier p m w) = _
  calc
    _ = (Complex.exp (-I * w * (anchor p m : ℂ)) *
        Complex.exp (I * w * (anchor p m : ℂ))) *
        mobiusThetaRawResidualMultiplier p m w := by field_simp [halfDensity_ne_zero hp m]
    _ = _ := by rw [he, one_mul]

private theorem residualTerm_recenter (k p m j : ℕ) (x : ℝ) :
    mobiusThetaInternalJetPrimeNormalResidualSourceTerm k p m j x =
      halfDensity p m *
        mobiusThetaInternalJetRawHeadSource k (p + j) m (x + anchor p m) := by
  have hs : x + anchor p m - (m : ℝ) * Real.log (p + j) =
      x - (m : ℝ) * (Real.log (p + j) - Real.log p) := by
    dsimp only [anchor]
    ring
  rw [mobiusThetaInternalJetPrimeNormalResidualSourceTerm,
    mobiusThetaInternalJetRawHeadSource]
  simp only [Nat.cast_add]
  rw [hs]
  ring

/-- Exact source recentering with the original half-density retained. -/
theorem mobiusThetaInternalJetRawResidualSource_recenter (k p m : ℕ) (x : ℝ) :
    mobiusThetaInternalJetPrimeNormalResidualSource k p m x =
      halfDensity p m * mobiusThetaInternalJetRawResidualSource k p m (x + anchor p m) := by
  unfold mobiusThetaInternalJetPrimeNormalResidualSource mobiusThetaInternalJetRawResidualSource
  simp_rw [residualTerm_recenter, tsum_mul_left]

private theorem localSource_recenter (k p m : ℕ) (delta : ℂ) (x : ℝ) :
    mobiusThetaResidualLocalModulationSource k p m delta x =
      halfDensity p m * mobiusThetaRawLocalModulationSource k p m delta (x + anchor p m) := by
  unfold mobiusThetaResidualLocalModulationSource mobiusThetaRawLocalModulationSource
  rw [← tsum_mul_left]
  apply tsum_congr
  intro j
  have hs : x + anchor p m - (m : ℝ) * Real.log (p + j) =
      x - (m : ℝ) * (Real.log (p + j) - Real.log p) := by
    dsimp only [anchor]
    ring
  rw [mobiusThetaResidualLocalModulationTerm, residualTerm_recenter, hs]
  ring

private theorem modulation_shift (v : ℂ) (x L : ℝ) :
    Complex.exp (-I * v * (x : ℂ)) =
      Complex.exp (-I * v * (L : ℂ)) *
        Complex.exp (-I * v * ((x - L : ℝ) : ℂ)) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Restoring the original anchor adds a full locally modulated source term.
The normalized commutator alone is therefore not the raw source commutator. -/
theorem mobiusThetaRawSourceModulationCommutator_recenter
    (k p m : ℕ) (delta : ℂ) (x : ℝ) :
    halfDensity p m * mobiusThetaRawSourceModulationCommutator k p m delta (x + anchor p m) =
      Complex.exp (-I * delta * (anchor p m : ℂ)) *
          mobiusThetaFullSourceModulationCommutator k p m delta x +
        (Complex.exp (-I * delta * (anchor p m : ℂ)) - 1) *
          mobiusThetaResidualLocalModulationSource k p m delta x := by
  have he := modulation_shift delta (x + anchor p m) (anchor p m)
  rw [add_sub_cancel_right] at he
  rw [mobiusThetaRawSourceModulationCommutator, he]
  calc
    _ = Complex.exp (-I * delta * (anchor p m : ℂ)) * Complex.exp (-I * delta * (x : ℂ)) *
          (halfDensity p m * mobiusThetaInternalJetRawResidualSource k p m (x + anchor p m)) -
        halfDensity p m * mobiusThetaRawLocalModulationSource k p m delta (x + anchor p m) := by ring
    _ = _ := by
      rw [← mobiusThetaInternalJetRawResidualSource_recenter, ← localSource_recenter,
        mobiusThetaFullSourceModulationCommutator]
      ring

private theorem rawLocalIntegrand_eq {p : ℕ} (hp : 0 < p)
    (k m : ℕ) (v delta : ℂ) (x : ℝ) :
    Complex.exp (-I * v * (x : ℂ)) * mobiusThetaRawLocalModulationSource k p m delta x =
      (halfDensity p m)⁻¹ * Complex.exp (-I * v * (anchor p m : ℂ)) *
        (Complex.exp (-I * v * ((x - anchor p m : ℝ) : ℂ)) *
          mobiusThetaResidualLocalModulationSource k p m delta (x - anchor p m)) := by
  have hs := localSource_recenter k p m delta (x - anchor p m)
  rw [sub_add_cancel] at hs
  rw [hs, modulation_shift v x (anchor p m)]
  field_simp [halfDensity_ne_zero hp m]

/-- Absolute admission of the full raw local modulation and its transform at the fixed
original translation. The internal Xi jet is not lowered or discarded. -/
theorem mobiusThetaRawLocalModulationSource_fourierLaplace_data
    {p m : ℕ} (hp : 0 < p) (hm : m ≠ 0) (k : ℕ) {v delta : ℂ}
    (hw : |(v + delta).im| < 1)
    (hv : 1 / (m : ℝ) < (mobiusThetaCenteredParameter v).re) :
    Integrable (fun x : ℝ => Complex.exp (-I * v * (x : ℂ)) *
      mobiusThetaRawLocalModulationSource k p m delta x) ∧
    (∫ x : ℝ, Complex.exp (-I * v * (x : ℂ)) *
      mobiusThetaRawLocalModulationSource k p m delta x) =
      mobiusThetaRawResidualMultiplier p m v * iteratedDeriv k XiC (v + delta) := by
  obtain ⟨hi, he⟩ := mobiusThetaResidualLocalModulationSource_fourierLaplace_data hp hm k hw hv
  simp_rw [rawLocalIntegrand_eq hp]
  constructor
  · simpa only [sub_eq_add_neg] using
      (hi.comp_add_right (-anchor p m)).const_mul
        ((halfDensity p m)⁻¹ * Complex.exp (-I * v * (anchor p m : ℂ)))
  · rw [integral_const_mul]
    have hs := integral_add_right_eq_self (μ := (volume : Measure ℝ))
      (fun x : ℝ => Complex.exp (-I * v * (x : ℂ)) *
        mobiusThetaResidualLocalModulationSource k p m delta x) (-anchor p m)
    simp only [← sub_eq_add_neg] at hs
    rw [hs, he, ← mul_assoc, mobiusThetaRawResidualMultiplier_eq hp]

private theorem rawLocalSource_zero (k p m : ℕ) (x : ℝ) :
    mobiusThetaRawLocalModulationSource k p m 0 x =
      mobiusThetaInternalJetRawResidualSource k p m x := by
  simp [mobiusThetaRawLocalModulationSource, mobiusThetaInternalJetRawResidualSource]

/-- Admitted transform of the complete commutator at its original source anchor.
The raw multiplier retains every original arithmetic coefficient and the native Xi jet. -/
theorem mobiusThetaRawSourceModulationCommutator_fourierLaplace_data
    {p m : ℕ} (hp : 0 < p) (hm : m ≠ 0) (k : ℕ) {v delta : ℂ}
    (hw : |(v + delta).im| < 1)
    (hv : 1 / (m : ℝ) < (mobiusThetaCenteredParameter v).re)
    (hwc : 1 / (m : ℝ) < (mobiusThetaCenteredParameter (v + delta)).re) :
    Integrable (fun x : ℝ => Complex.exp (-I * v * (x : ℂ)) *
      mobiusThetaRawSourceModulationCommutator k p m delta x) ∧
    (∫ x : ℝ, Complex.exp (-I * v * (x : ℂ)) *
      mobiusThetaRawSourceModulationCommutator k p m delta x) =
      (mobiusThetaRawResidualMultiplier p m (v + delta) -
        mobiusThetaRawResidualMultiplier p m v) * iteratedDeriv k XiC (v + delta) := by
  obtain ⟨hi, he⟩ := mobiusThetaRawLocalModulationSource_fourierLaplace_data
    hp hm k hw hv
  have hw0 : |((v + delta) + 0).im| < 1 := by simpa only [add_zero] using hw
  obtain ⟨hj, hf⟩ := mobiusThetaRawLocalModulationSource_fourierLaplace_data
    hp hm k hw0 hwc
  simp only [rawLocalSource_zero, add_zero] at hj hf
  have hg (x : ℝ) : Complex.exp (-I * v * (x : ℂ)) *
      mobiusThetaRawSourceModulationCommutator k p m delta x =
      Complex.exp (-I * (v + delta) * (x : ℂ)) *
          mobiusThetaInternalJetRawResidualSource k p m x -
        Complex.exp (-I * v * (x : ℂ)) * mobiusThetaRawLocalModulationSource k p m delta x := by
    have hexp : Complex.exp (-I * v * (x : ℂ)) * Complex.exp (-I * delta * (x : ℂ)) =
        Complex.exp (-I * (v + delta) * (x : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    rw [mobiusThetaRawSourceModulationCommutator, mul_sub, ← mul_assoc, hexp]
  simp_rw [hg]
  refine ⟨hj.sub hi, ?_⟩
  rw [integral_sub hj hi, hf, he]
  ring

end RHTower
