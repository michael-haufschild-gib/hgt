import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingArakiWoodsDaviesMixingEndpoint
import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedOrientedWallLightIncidence

/-!
# Hawking KMS commutator reconstruction of the Suzuki reflected wall current

The Hartle--Hawking Araki--Woods double acts on a source amplitude `F` by the exact
absorption/emission coefficients

`sqrt (1 / (1-q))` and `sqrt (q / (1-q))`, `q = exp (-2 pi omega / kappa)`.

This module feeds Suzuki's phase-carrying prime-power wall field through that genuine KMS
two-mode scattering dilation and then through the reflected quarter-turn light readout.  Complex
conjugation reverses the emission readout orientation.  Consequently the oriented sum of the
absorption and emission currents is temperature-independent: the Bose factors cancel by the CCR
identity and the result is exactly Suzuki's anti-diagonal wall current.

This closes an amplitude-level Hawking/Suzuki seam without asserting the remaining global Ward
sign.  At spectral center the reconstructed current still vanishes while negative-light reserve is
strictly positive, so thermality and conservative scattering alone cannot finish the RH-bearing
assembly.
-/

open Complex Real

noncomputable section
namespace RHTower

/-! ## Exact thermal SU(1,1) dilation -/

/-- Positive-frequency coefficient in the Hawking Araki--Woods double. -/
def thetaCuspHawkingWallKMSDownCoefficient (kappa omega : ℝ) : ℝ :=
  Real.sqrt (1 / (1 - thetaCuspHawkingKMSBoltzmannRatio kappa omega))

/-- Negative-Liouville-frequency coefficient in the Hawking Araki--Woods double. -/
def thetaCuspHawkingWallKMSUpCoefficient (kappa omega : ℝ) : ℝ :=
  Real.sqrt (thetaCuspHawkingKMSBoltzmannRatio kappa omega /
    (1 - thetaCuspHawkingKMSBoltzmannRatio kappa omega))

theorem thetaCuspHawkingWallKMSDownCoefficient_sq
    {kappa omega : ℝ} (hkappa : 0 < kappa) (homega : 0 < omega) :
    thetaCuspHawkingWallKMSDownCoefficient kappa omega ^ (2 : ℕ) =
      1 / (1 - thetaCuspHawkingKMSBoltzmannRatio kappa omega) := by
  rw [thetaCuspHawkingWallKMSDownCoefficient, Real.sq_sqrt]
  exact one_div_nonneg.mpr
    (sub_nonneg.mpr (thetaCuspHawkingKMSBoltzmannRatio_lt_one hkappa homega).le)

theorem thetaCuspHawkingWallKMSUpCoefficient_sq
    {kappa omega : ℝ} (hkappa : 0 < kappa) (homega : 0 < omega) :
    thetaCuspHawkingWallKMSUpCoefficient kappa omega ^ (2 : ℕ) =
      thetaCuspHawkingKMSBoltzmannRatio kappa omega /
        (1 - thetaCuspHawkingKMSBoltzmannRatio kappa omega) := by
  rw [thetaCuspHawkingWallKMSUpCoefficient, Real.sq_sqrt]
  exact div_nonneg
    (thetaCuspHawkingKMSBoltzmannRatio_pos kappa omega).le
    (sub_nonneg.mpr (thetaCuspHawkingKMSBoltzmannRatio_lt_one hkappa homega).le)

/-- Exact Araki--Woods coefficient CCR: absorption minus emission weight is one. -/
theorem thetaCuspHawkingWallKMSCoefficient_sub_sq
    {kappa omega : ℝ} (hkappa : 0 < kappa) (homega : 0 < omega) :
    thetaCuspHawkingWallKMSDownCoefficient kappa omega ^ (2 : ℕ) -
        thetaCuspHawkingWallKMSUpCoefficient kappa omega ^ (2 : ℕ) = 1 := by
  rw [thetaCuspHawkingWallKMSDownCoefficient_sq hkappa homega,
    thetaCuspHawkingWallKMSUpCoefficient_sq hkappa homega]
  have hden : 1 - thetaCuspHawkingKMSBoltzmannRatio kappa omega ≠ 0 :=
    ne_of_gt (sub_pos.mpr
      (thetaCuspHawkingKMSBoltzmannRatio_lt_one hkappa homega))
  field_simp

/-- Thermal double is an exact two-mode bosonic `SU(1,1)` fibre. -/
theorem thetaCuspHawkingWallKMS_isTwoModeBosonicCCR
    {kappa omega : ℝ} (hkappa : 0 < kappa) (homega : 0 < omega) :
    IsTwoModeBosonicCCR
      (thetaCuspHawkingWallKMSDownCoefficient kappa omega)
      (thetaCuspHawkingWallKMSUpCoefficient kappa omega : ℂ) := by
  unfold IsTwoModeBosonicCCR
  rw [show ‖(thetaCuspHawkingWallKMSUpCoefficient kappa omega : ℂ)‖ =
      thetaCuspHawkingWallKMSUpCoefficient kappa omega by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    exact Real.sqrt_nonneg _]
  exact thetaCuspHawkingWallKMSCoefficient_sub_sq hkappa homega

/-- Exterior output of the exact Hawking KMS two-mode scattering block. -/
def thetaCuspHawkingWallKMSPositiveOutput
    (kappa omega : ℝ) (x y : ℂ) : ℂ :=
  (thetaCuspHawkingWallKMSDownCoefficient kappa omega : ℂ) * x +
    (thetaCuspHawkingWallKMSUpCoefficient kappa omega : ℂ) * y

/-- Partner output of the exact Hawking KMS two-mode scattering block. -/
def thetaCuspHawkingWallKMSPartnerOutput
    (kappa omega : ℝ) (x y : ℂ) : ℂ :=
  (thetaCuspHawkingWallKMSUpCoefficient kappa omega : ℂ) * x +
    (thetaCuspHawkingWallKMSDownCoefficient kappa omega : ℂ) * y

/-- Nonperturbative KMS scattering preserves the Nambu signed Hermitian form. -/
theorem thetaCuspHawkingWallKMS_preserves_signedHermitian
    {kappa omega : ℝ} (hkappa : 0 < kappa) (homega : 0 < omega)
    (x y : ℂ) :
    (starRingEnd ℂ) (thetaCuspHawkingWallKMSPositiveOutput kappa omega x y) *
          thetaCuspHawkingWallKMSPositiveOutput kappa omega x y -
        (starRingEnd ℂ) (thetaCuspHawkingWallKMSPartnerOutput kappa omega x y) *
          thetaCuspHawkingWallKMSPartnerOutput kappa omega x y =
      (starRingEnd ℂ) x * x - (starRingEnd ℂ) y * y := by
  let a : ℝ := thetaCuspHawkingWallKMSDownCoefficient kappa omega
  let b : ℝ := thetaCuspHawkingWallKMSUpCoefficient kappa omega
  have hccr := thetaCuspHawkingWallKMSCoefficient_sub_sq hkappa homega
  have hccrC := congrArg (fun r : ℝ => (r : ℂ)) hccr
  push_cast at hccrC
  change (a : ℂ) ^ (2 : ℕ) - (b : ℂ) ^ (2 : ℕ) = 1 at hccrC
  change (starRingEnd ℂ) ((a : ℂ) * x + (b : ℂ) * y) *
      ((a : ℂ) * x + (b : ℂ) * y) -
    (starRingEnd ℂ) ((b : ℂ) * x + (a : ℂ) * y) *
      ((b : ℂ) * x + (a : ℂ) * y) =
        (starRingEnd ℂ) x * x - (starRingEnd ℂ) y * y
  simp only [map_add, map_mul, Complex.conj_ofReal]
  linear_combination
    ((starRingEnd ℂ) x * x - (starRingEnd ℂ) y * y) * hccrC

/-- Signed adjoint of the KMS scattering block. -/
def thetaCuspHawkingWallKMSInversePositiveOutput
    (kappa omega : ℝ) (x y : ℂ) : ℂ :=
  (thetaCuspHawkingWallKMSDownCoefficient kappa omega : ℂ) * x -
    (thetaCuspHawkingWallKMSUpCoefficient kappa omega : ℂ) * y

def thetaCuspHawkingWallKMSInversePartnerOutput
    (kappa omega : ℝ) (x y : ℂ) : ℂ :=
  -(thetaCuspHawkingWallKMSUpCoefficient kappa omega : ℂ) * x +
    (thetaCuspHawkingWallKMSDownCoefficient kappa omega : ℂ) * y

/-- Signed adjoint is an exact inverse: thermal block is full scattering, not a rate ansatz. -/
theorem thetaCuspHawkingWallKMS_inverse_after_scattering
    {kappa omega : ℝ} (hkappa : 0 < kappa) (homega : 0 < omega)
    (x y : ℂ) :
    thetaCuspHawkingWallKMSInversePositiveOutput kappa omega
        (thetaCuspHawkingWallKMSPositiveOutput kappa omega x y)
        (thetaCuspHawkingWallKMSPartnerOutput kappa omega x y) = x ∧
      thetaCuspHawkingWallKMSInversePartnerOutput kappa omega
        (thetaCuspHawkingWallKMSPositiveOutput kappa omega x y)
        (thetaCuspHawkingWallKMSPartnerOutput kappa omega x y) = y := by
  let a : ℝ := thetaCuspHawkingWallKMSDownCoefficient kappa omega
  let b : ℝ := thetaCuspHawkingWallKMSUpCoefficient kappa omega
  have hccr := thetaCuspHawkingWallKMSCoefficient_sub_sq hkappa homega
  have hccrC := congrArg (fun r : ℝ => (r : ℂ)) hccr
  push_cast at hccrC
  change (a : ℂ) ^ (2 : ℕ) - (b : ℂ) ^ (2 : ℕ) = 1 at hccrC
  constructor
  · change (a : ℂ) * ((a : ℂ) * x + (b : ℂ) * y) -
      (b : ℂ) * ((b : ℂ) * x + (a : ℂ) * y) = x
    linear_combination x * hccrC
  · change -(b : ℂ) * ((a : ℂ) * x + (b : ℂ) * y) +
      (a : ℂ) * ((b : ℂ) * x + (a : ℂ) * y) = y
    linear_combination y * hccrC

/-! ## Reflected phase readout -/

/-- Passive quarter-turn positive-light readout of a reflected scalar field. -/
def thetaCuspHawkingReflectedPositiveReadout
    (field : ℝ → ℂ) (t : ℝ) : ℂ :=
  (field t + I * field (-t)) / 2

/-- Passive quarter-turn negative-light readout of a reflected scalar field. -/
def thetaCuspHawkingReflectedNegativeReadout
    (field : ℝ → ℂ) (t : ℝ) : ℂ :=
  (field t - I * field (-t)) / 2

/-- Population difference measured after the passive reflected quarter-turn. -/
def thetaCuspHawkingReflectedReadoutCurrent
    (field : ℝ → ℂ) (t : ℝ) : ℝ :=
  Complex.normSq (thetaCuspHawkingReflectedPositiveReadout field t) -
    Complex.normSq (thetaCuspHawkingReflectedNegativeReadout field t)

theorem thetaCuspHawkingReflectedReadoutCurrent_real_scale
    (c : ℝ) (field : ℝ → ℂ) (t : ℝ) :
    thetaCuspHawkingReflectedReadoutCurrent
        (fun s => (c : ℂ) * field s) t =
      c ^ (2 : ℕ) * thetaCuspHawkingReflectedReadoutCurrent field t := by
  unfold thetaCuspHawkingReflectedReadoutCurrent
    thetaCuspHawkingReflectedPositiveReadout
    thetaCuspHawkingReflectedNegativeReadout
  rw [show ((c : ℂ) * field t + I * ((c : ℂ) * field (-t))) / 2 =
      (c : ℂ) * ((field t + I * field (-t)) / 2) by ring,
    show ((c : ℂ) * field t - I * ((c : ℂ) * field (-t))) / 2 =
      (c : ℂ) * ((field t - I * field (-t)) / 2) by ring,
    Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_ofReal]
  ring

theorem thetaCuspHawkingReflectedPositiveReadout_conj
    (field : ℝ → ℂ) (t : ℝ) :
    thetaCuspHawkingReflectedPositiveReadout
        (fun s => (starRingEnd ℂ) (field s)) t =
      (starRingEnd ℂ) (thetaCuspHawkingReflectedNegativeReadout field t) := by
  unfold thetaCuspHawkingReflectedPositiveReadout
    thetaCuspHawkingReflectedNegativeReadout
  simp only [map_div₀, map_sub, map_mul, Complex.conj_I, map_ofNat]
  ring

theorem thetaCuspHawkingReflectedNegativeReadout_conj
    (field : ℝ → ℂ) (t : ℝ) :
    thetaCuspHawkingReflectedNegativeReadout
        (fun s => (starRingEnd ℂ) (field s)) t =
      (starRingEnd ℂ) (thetaCuspHawkingReflectedPositiveReadout field t) := by
  unfold thetaCuspHawkingReflectedPositiveReadout
    thetaCuspHawkingReflectedNegativeReadout
  simp only [map_div₀, map_add, map_mul, Complex.conj_I, map_ofNat]
  ring

/-- Araki--Woods conjugation reverses the passive readout orientation. -/
theorem thetaCuspHawkingReflectedReadoutCurrent_conj
    (field : ℝ → ℂ) (t : ℝ) :
    thetaCuspHawkingReflectedReadoutCurrent
        (fun s => (starRingEnd ℂ) (field s)) t =
      -thetaCuspHawkingReflectedReadoutCurrent field t := by
  rw [thetaCuspHawkingReflectedReadoutCurrent,
    thetaCuspHawkingReflectedPositiveReadout_conj,
    thetaCuspHawkingReflectedNegativeReadout_conj,
    Complex.normSq_conj, Complex.normSq_conj]
  unfold thetaCuspHawkingReflectedReadoutCurrent
  ring

/-! ## Source-faithful Suzuki wall double -/

/-- Positive-frequency Araki--Woods lift of one actual Suzuki prime-power wall field. -/
def thetaCuspHawkingWallArakiWoodsDownField
    (kappa omega t : ℝ) (p : Nat.Primes) (e : ℕ) : ℂ :=
  (thetaCuspHawkingWallKMSDownCoefficient kappa omega : ℂ) *
    suzukiCriticalWallField t p e

/-- Negative-frequency Araki--Woods lift; physical thermal doubling conjugates source phase. -/
def thetaCuspHawkingWallArakiWoodsUpField
    (kappa omega t : ℝ) (p : Nat.Primes) (e : ℕ) : ℂ :=
  (thetaCuspHawkingWallKMSUpCoefficient kappa omega : ℂ) *
    (starRingEnd ℂ) (suzukiCriticalWallField t p e)

def thetaCuspHawkingWallKMSDownReadoutCurrent
    (kappa omega t : ℝ) (p : Nat.Primes) (e : ℕ) : ℝ :=
  thetaCuspHawkingReflectedReadoutCurrent
    (fun s => thetaCuspHawkingWallArakiWoodsDownField kappa omega s p e) t

def thetaCuspHawkingWallKMSUpReadoutCurrent
    (kappa omega t : ℝ) (p : Nat.Primes) (e : ℕ) : ℝ :=
  thetaCuspHawkingReflectedReadoutCurrent
    (fun s => thetaCuspHawkingWallArakiWoodsUpField kappa omega s p e) t

/-- Untempered reflected readout is exactly Suzuki's signed wall current. -/
theorem thetaCuspHawkingReflectedReadoutCurrent_suzukiWall
    (t : ℝ) (p : Nat.Primes) (e : ℕ) :
    thetaCuspHawkingReflectedReadoutCurrent
        (fun s => suzukiCriticalWallField s p e) t =
      ((suzukiCriticalWallField t p e) ^ (2 : ℕ)).im := by
  change Complex.normSq (suzukiCriticalWallPositiveLightAmplitude t p e) -
      Complex.normSq (suzukiCriticalWallNegativeLightAmplitude t p e) = _
  exact normSq_suzukiCriticalWallPositiveLightAmplitude_sub_negative t p e

theorem thetaCuspHawkingWallKMSDownReadoutCurrent_eq
    {kappa omega : ℝ} (hkappa : 0 < kappa) (homega : 0 < omega)
    (t : ℝ) (p : Nat.Primes) (e : ℕ) :
    thetaCuspHawkingWallKMSDownReadoutCurrent kappa omega t p e =
      (1 / (1 - thetaCuspHawkingKMSBoltzmannRatio kappa omega)) *
        ((suzukiCriticalWallField t p e) ^ (2 : ℕ)).im := by
  unfold thetaCuspHawkingWallKMSDownReadoutCurrent
    thetaCuspHawkingWallArakiWoodsDownField
  rw [thetaCuspHawkingReflectedReadoutCurrent_real_scale,
    thetaCuspHawkingReflectedReadoutCurrent_suzukiWall,
    thetaCuspHawkingWallKMSDownCoefficient_sq hkappa homega]

theorem thetaCuspHawkingWallKMSUpReadoutCurrent_eq
    {kappa omega : ℝ} (hkappa : 0 < kappa) (homega : 0 < omega)
    (t : ℝ) (p : Nat.Primes) (e : ℕ) :
    thetaCuspHawkingWallKMSUpReadoutCurrent kappa omega t p e =
      -(thetaCuspHawkingKMSBoltzmannRatio kappa omega /
          (1 - thetaCuspHawkingKMSBoltzmannRatio kappa omega)) *
        ((suzukiCriticalWallField t p e) ^ (2 : ℕ)).im := by
  unfold thetaCuspHawkingWallKMSUpReadoutCurrent
    thetaCuspHawkingWallArakiWoodsUpField
  rw [thetaCuspHawkingReflectedReadoutCurrent_real_scale,
    thetaCuspHawkingReflectedReadoutCurrent_conj,
    thetaCuspHawkingReflectedReadoutCurrent_suzukiWall,
    thetaCuspHawkingWallKMSUpCoefficient_sq hkappa homega]
  ring

/-- Exact oriented KMS detailed balance after reflected phase readout. -/
theorem thetaCuspHawkingWallKMSUpReadoutCurrent_eq_neg_ratio_mul_down
    {kappa omega : ℝ} (hkappa : 0 < kappa) (homega : 0 < omega)
    (t : ℝ) (p : Nat.Primes) (e : ℕ) :
    thetaCuspHawkingWallKMSUpReadoutCurrent kappa omega t p e =
      -thetaCuspHawkingKMSBoltzmannRatio kappa omega *
        thetaCuspHawkingWallKMSDownReadoutCurrent kappa omega t p e := by
  rw [thetaCuspHawkingWallKMSUpReadoutCurrent_eq hkappa homega,
    thetaCuspHawkingWallKMSDownReadoutCurrent_eq hkappa homega]
  ring

/-- Oriented absorption plus emission current in the Hawking thermal double. -/
def thetaCuspHawkingWallKMSCommutatorCurrent
    (kappa omega t : ℝ) (p : Nat.Primes) (e : ℕ) : ℝ :=
  thetaCuspHawkingWallKMSDownReadoutCurrent kappa omega t p e +
    thetaCuspHawkingWallKMSUpReadoutCurrent kappa omega t p e

/-- **KMS commutator reconstruction.** Bose stimulation cancels exactly and leaves the raw,
phase-sensitive Suzuki reflected wall current, at every temperature and finite coupling. -/
theorem thetaCuspHawkingWallKMSCommutatorCurrent_eq_suzukiWall
    {kappa omega : ℝ} (hkappa : 0 < kappa) (homega : 0 < omega)
    (t : ℝ) (p : Nat.Primes) (e : ℕ) :
    thetaCuspHawkingWallKMSCommutatorCurrent kappa omega t p e =
      ((suzukiCriticalWallField t p e) ^ (2 : ℕ)).im := by
  rw [thetaCuspHawkingWallKMSCommutatorCurrent,
    thetaCuspHawkingWallKMSDownReadoutCurrent_eq hkappa homega,
    thetaCuspHawkingWallKMSUpReadoutCurrent_eq hkappa homega]
  have hden : 1 - thetaCuspHawkingKMSBoltzmannRatio kappa omega ≠ 0 :=
    ne_of_gt (sub_pos.mpr
      (thetaCuspHawkingKMSBoltzmannRatio_lt_one hkappa homega))
  field_simp
  ring

/-- Complex form: reconstructed KMS current is Suzuki's diagonal FE-reflected kernel. -/
theorem ofReal_thetaCuspHawkingWallKMSCommutatorCurrent_eq_reflectedKernel
    {kappa omega : ℝ} (hkappa : 0 < kappa) (homega : 0 < omega)
    (t : ℝ) (p : Nat.Primes) (e : ℕ) :
    (thetaCuspHawkingWallKMSCommutatorCurrent kappa omega t p e : ℂ) =
      suzukiCriticalWallReflectedCurrentKernel t t p e := by
  rw [thetaCuspHawkingWallKMSCommutatorCurrent_eq_suzukiWall hkappa homega,
    suzukiCriticalWallReflectedCurrentKernel_diagonal]

/-- Prime-power specialization: actual Hawking KMS commutator readout recovers the literal
critical-Mellin sine current with its full von-Mangoldt coefficient. -/
theorem thetaCuspHawkingWallKMSCommutatorCurrent_eq_criticalMellinSine
    {kappa omega : ℝ} (hkappa : 0 < kappa) (homega : 0 < omega)
    (xi : ℝ) (p : Nat.Primes) (e : ℕ) :
    thetaCuspHawkingWallKMSCommutatorCurrent
        kappa omega (2 * Real.pi * xi) p e =
      criticalMellinAtomWeight (xiGammaEulerValuationNat (p, e)) *
        Real.sin (2 * Real.pi *
          Real.log (xiGammaEulerValuationNat (p, e)) * xi) := by
  calc
    thetaCuspHawkingWallKMSCommutatorCurrent
        kappa omega (2 * Real.pi * xi) p e =
        ccmActualHeadMatchedWallLightImbalance p e xi := by
      rw [thetaCuspHawkingWallKMSCommutatorCurrent_eq_suzukiWall hkappa homega]
      unfold ccmActualHeadMatchedWallLightImbalance
      exact
        (normSq_suzukiCriticalWallPositiveLightAmplitude_sub_negative
          (2 * Real.pi * xi) p e).symm
    _ = _ := ccmActualHeadMatchedWallLightImbalance_eq p e xi

@[simp] theorem thetaCuspHawkingWallKMSCommutatorCurrent_zero
    {kappa omega : ℝ} (hkappa : 0 < kappa) (homega : 0 < omega)
    (p : Nat.Primes) (e : ℕ) :
    thetaCuspHawkingWallKMSCommutatorCurrent kappa omega 0 p e = 0 := by
  simpa using thetaCuspHawkingWallKMSCommutatorCurrent_eq_criticalMellinSine
    hkappa homega 0 p e

/-- **Center-blindness no-go.** Exact KMS scattering and phase-sensitive commutator readout still
cannot dominate negative-light reserve: current vanishes at center while reserve is positive. -/
theorem not_negativeLight_le_abs_thetaCuspHawkingWallKMSCommutatorCurrent
    {kappa omega : ℝ} (hkappa : 0 < kappa) (homega : 0 < omega)
    (p : Nat.Primes) (e : ℕ) :
    ¬ ∀ xi : ℝ,
      Complex.normSq
          (suzukiCriticalWallNegativeLightAmplitude (2 * Real.pi * xi) p e) ≤
        |thetaCuspHawkingWallKMSCommutatorCurrent
          kappa omega (2 * Real.pi * xi) p e| := by
  intro h
  have hzero := h 0
  simp only [mul_zero] at hzero
  rw [thetaCuspHawkingWallKMSCommutatorCurrent_zero hkappa homega] at hzero
  simp only [abs_zero] at hzero
  have hpos : 0 < Complex.normSq
      (suzukiCriticalWallNegativeLightAmplitude 0 p e) := by
    simpa using
      normSq_suzukiCriticalWallNegativeLightAmplitude_two_pi_zero_pos p e
  exact (not_le_of_gt hpos) hzero

end RHTower
