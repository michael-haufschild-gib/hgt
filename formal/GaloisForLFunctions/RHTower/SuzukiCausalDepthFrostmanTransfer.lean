import GaloisForLFunctions.RHTower.SuzukiCriticalEntryWallQuarterShiftGreenLaw
import GaloisForLFunctions.RHTower.CCMPrimeTransverseFrostmanProfile
import GaloisForLFunctions.RHTower.PrimeLogIncommensuratePhaseClock

/-!
# Suzuki causal depth fusion as an exact Frostman transfer

The aperture-dressed critical wall has height-flat energy when valuation depths are squared
coordinatewise.  The causal entry-wall Green law prescribes a different source operation: sum one
prime's calibrated valuation-depth forcings before taking the square.  This file proves that the
resulting diagonal is exactly the CCM transverse Frostman Poisson profile.

For two distinct primes, simultaneous equality in the two profile caps recovers both prime-log
phases.  Incommensurability then makes the joint cap unique at the true height origin and yields a
translation-invariant nonnegative height separator.

No Xi zero, RH premise, numerical computation, fitted transfer, or target positivity hypothesis is
used.  This identifies a concrete non-flat diagonal component; the restricted-Weil/Robin/Gamma/
holonomy cross-prime transfer and its rectangular Ward lower bound remain open.
-/

open Complex
open scoped ComplexConjugate

namespace RHTower

noncomputable section

/-! ## Source-selected radius, phase, and causal fusion -/

/-- Positive radial part of one Suzuki critical aperture depth step. -/
def suzukiCriticalApertureDepthFusionRadius
    (h a : ℝ) (p : Nat.Primes) : ℝ :=
  Real.exp (-(1 / 4 : ℝ) * Real.log (p : ℝ)) *
    xiMobiusContinuousApertureDiskNode ((h / 2) * a) p ^ 2

/-- Half-prime-log phase carried by every valuation step on one prime ray. -/
def suzukiCriticalApertureDepthFusionPhase
    (t : ℝ) (p : Nat.Primes) : ℂ :=
  HTGeometry.phaseClockValue (Real.log (p : ℝ)) (t / 2)

/-- Causal fusion of all dressed entry-wall depths on one prime ray before a Gram square. -/
def suzukiCriticalApertureDepthFusedAtom
    (h a t : ℝ) (p : Nat.Primes) : ℂ :=
  ∑' e : ℕ, suzukiCriticalApertureBoundaryAtom h a t p e

theorem suzukiCriticalApertureDepthFusionRadius_pos
    (h a : ℝ) (p : Nat.Primes) :
    0 < suzukiCriticalApertureDepthFusionRadius h a p := by
  exact mul_pos (Real.exp_pos _) (sq_pos_of_pos
    (xiMobiusContinuousApertureDiskNode_pos _ p))

/-- The depth-zero calibrated endpoint amplitude is strictly positive at positive aperture. -/
theorem suzukiCriticalEntryWallEndpointAmplitude_zero_pos
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (p : Nat.Primes) :
    0 < suzukiCriticalEntryWallEndpointAmplitude h a p 0 := by
  rw [suzukiCriticalEntryWallEndpointAmplitude]
  apply mul_pos
  · apply Real.sqrt_pos.2
    exact mul_pos
      (div_pos (Real.log_pos (by exact_mod_cast p.property.one_lt))
        (by exact_mod_cast Nat.pow_pos p.property.pos))
      (Real.exp_pos _)
  · rw [xiMobiusCubicNormalizedInnovationFeature,
      xiMobiusContinuousApertureDyadicInnovationFeature,
      xiMobiusPrimeContinuousApertureDyadicInnovationFeature]
    simp only [pow_zero, mul_one]
    apply mul_pos
    · exact inv_pos.mpr (mul_pos hh (Real.sqrt_pos.2 hh))
    · apply mul_pos
      · exact div_pos (xiTransversePrimeApertureDiskNode_pos 1 p)
          (by linarith [xiTransversePrimeApertureDiskNode_pos 1 p])
      · exact sq_pos_of_pos (sub_pos.mpr
          (xiMobiusContinuousApertureDiskNode_lt_one
            (mul_pos (half_pos hh) ha) p))

theorem suzukiCriticalApertureDepthFusionRadius_lt_one
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (p : Nat.Primes) :
    suzukiCriticalApertureDepthFusionRadius h a p < 1 := by
  have hlog : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.property.one_lt)
  have hexp : Real.exp (-(1 / 4 : ℝ) * Real.log (p : ℝ)) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith
  have hr0 := xiMobiusContinuousApertureDiskNode_pos ((h / 2) * a) p
  have hr1 := xiMobiusContinuousApertureDiskNode_lt_one
    (mul_pos (half_pos hh) ha) p
  rw [suzukiCriticalApertureDepthFusionRadius]
  exact mul_lt_one_of_nonneg_of_lt_one_left (Real.exp_nonneg _) hexp
    (by nlinarith : xiMobiusContinuousApertureDiskNode ((h / 2) * a) p ^ 2 ≤ 1)

/-- The existing complex depth ratio is exactly positive radius times prime-log phase. -/
theorem suzukiCriticalApertureDepthRatio_eq_radius_mul_phase
    (h a t : ℝ) (p : Nat.Primes) :
    suzukiCriticalApertureDepthRatio h a t p =
      (suzukiCriticalApertureDepthFusionRadius h a p : ℂ) *
        suzukiCriticalApertureDepthFusionPhase t p := by
  have hphase :
      Complex.exp ((((t * Real.log (p : ℝ) / 2 : ℝ) : ℂ) * I)) =
        suzukiCriticalApertureDepthFusionPhase t p := by
    rw [suzukiCriticalApertureDepthFusionPhase, HTGeometry.phaseClockValue]
    congr 1
    push_cast
    ring
  rw [suzukiCriticalApertureDepthRatio, suzukiCriticalGammaDepthRatio,
    suzukiCriticalApertureDepthFusionRadius, hphase]
  push_cast
  ring

/-- The depth-zero forcing is real endpoint amplitude times the same prime-log phase. -/
theorem suzukiCriticalApertureBoundaryAtom_zero_eq_endpoint_mul_phase
    (h a t : ℝ) (p : Nat.Primes) :
    suzukiCriticalApertureBoundaryAtom h a t p 0 =
      (suzukiCriticalEntryWallEndpointAmplitude h a p 0 : ℂ) *
        suzukiCriticalApertureDepthFusionPhase t p := by
  have hphase :
      Complex.exp ((((t * Real.log (p : ℝ) / 2 : ℝ) : ℂ) * I)) =
        suzukiCriticalApertureDepthFusionPhase t p := by
    rw [suzukiCriticalApertureDepthFusionPhase, HTGeometry.phaseClockValue]
    congr 1
    push_cast
    ring
  rw [suzukiCriticalApertureBoundaryAtom_eq_entryWallAmplitude_mul_kernel]
  congr 1
  rw [suzukiOscillatoryKernel_primePowerEntryWall_eq_criticalPhase]
  convert hphase using 1
  norm_num [xiGammaEulerValuationNat]

/-- **Causal depth Möbius law.**  The actual source fusion is endpoint amplitude times the
prime-log phase divided by its source-selected disk resolvent. -/
theorem suzukiCriticalApertureDepthFusedAtom_eq_mobius
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (t : ℝ) (p : Nat.Primes) :
    suzukiCriticalApertureDepthFusedAtom h a t p =
      (suzukiCriticalEntryWallEndpointAmplitude h a p 0 : ℂ) *
        suzukiCriticalApertureDepthFusionPhase t p *
          (1 - (suzukiCriticalApertureDepthFusionRadius h a p : ℂ) *
            suzukiCriticalApertureDepthFusionPhase t p)⁻¹ := by
  rw [suzukiCriticalApertureDepthFusedAtom,
    tsum_suzukiCriticalApertureBoundaryAtom_eq_resolvent hh ha,
    suzukiCriticalApertureBoundaryAtom_zero_eq_endpoint_mul_phase,
    suzukiCriticalApertureDepthRatio_eq_radius_mul_phase]

/-! ## Exact diagonal and Frostman identification -/

private theorem normSq_one_sub_real_mul_exp_I (r θ : ℝ) :
    Complex.normSq (1 - (r : ℂ) * Complex.exp ((θ : ℂ) * I)) =
      1 - 2 * r * Real.cos θ + r ^ 2 := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
    Complex.add_re, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, mul_zero, sub_zero, add_zero, mul_one, Complex.sub_im,
    Complex.one_im, zero_sub]
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- Exact diagonal of the depth-fused causal entry current. -/
theorem normSq_suzukiCriticalApertureDepthFusedAtom_eq
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (t : ℝ) (p : Nat.Primes) :
    Complex.normSq (suzukiCriticalApertureDepthFusedAtom h a t p) =
      suzukiCriticalEntryWallEndpointAmplitude h a p 0 ^ 2 /
        (1 - 2 * suzukiCriticalApertureDepthFusionRadius h a p *
            Real.cos (t * Real.log (p : ℝ) / 2) +
          suzukiCriticalApertureDepthFusionRadius h a p ^ 2) := by
  rw [suzukiCriticalApertureDepthFusedAtom_eq_mobius hh ha,
    Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_ofReal,
    Complex.normSq_inv]
  have hphase : Complex.normSq
      (suzukiCriticalApertureDepthFusionPhase t p) = 1 := by
    rw [← Complex.sq_norm, suzukiCriticalApertureDepthFusionPhase,
      HTGeometry.norm_phaseClockValue]
    norm_num
  rw [hphase, mul_one]
  rw [suzukiCriticalApertureDepthFusionPhase, HTGeometry.phaseClockValue]
  rw [normSq_one_sub_real_mul_exp_I]
  simp only [inv_eq_one_div]
  ring

/-- Normalized causal-depth diagonal, expressed in the corpus CCM Frostman coordinates. -/
def suzukiCriticalApertureDepthFrostmanProfile
    (h a t : ℝ) (p : Nat.Primes) : ℝ :=
  ccmFrostmanPoissonProfile
    (suzukiCriticalApertureDepthFusionRadius h a p)⁻¹
    (t * Real.log (p : ℝ) / 2)

theorem one_lt_inv_suzukiCriticalApertureDepthFusionRadius
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (p : Nat.Primes) :
    1 < (suzukiCriticalApertureDepthFusionRadius h a p)⁻¹ := by
  rw [one_lt_inv₀ (suzukiCriticalApertureDepthFusionRadius_pos h a p)]
  exact suzukiCriticalApertureDepthFusionRadius_lt_one hh ha p

/-- **Suzuki--CCM Frostman transfer.**  Causal fusion before the square multiplies the central
energy by exactly the CCM transverse Poisson profile. -/
theorem normSq_suzukiCriticalApertureDepthFusedAtom_eq_zero_mul_frostmanProfile
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (t : ℝ) (p : Nat.Primes) :
    Complex.normSq (suzukiCriticalApertureDepthFusedAtom h a t p) =
      Complex.normSq (suzukiCriticalApertureDepthFusedAtom h a 0 p) *
        suzukiCriticalApertureDepthFrostmanProfile h a t p := by
  rw [normSq_suzukiCriticalApertureDepthFusedAtom_eq hh ha,
    normSq_suzukiCriticalApertureDepthFusedAtom_eq hh ha]
  simp only [zero_mul, zero_div, Real.cos_zero]
  have hr0 := suzukiCriticalApertureDepthFusionRadius_pos h a p
  have hr1 := suzukiCriticalApertureDepthFusionRadius_lt_one hh ha p
  have hr : suzukiCriticalApertureDepthFusionRadius h a p ≠ 0 := ne_of_gt hr0
  have hD : 0 < 1 - 2 * suzukiCriticalApertureDepthFusionRadius h a p *
      Real.cos (t * Real.log (p : ℝ) / 2) +
        suzukiCriticalApertureDepthFusionRadius h a p ^ 2 := by
    have hc := Real.cos_le_one (t * Real.log (p : ℝ) / 2)
    nlinarith [sq_pos_of_pos (sub_pos.mpr hr1)]
  have hprofile : suzukiCriticalApertureDepthFrostmanProfile h a t p =
      (1 - suzukiCriticalApertureDepthFusionRadius h a p) ^ 2 /
        (1 - 2 * suzukiCriticalApertureDepthFusionRadius h a p *
            Real.cos (t * Real.log (p : ℝ) / 2) +
          suzukiCriticalApertureDepthFusionRadius h a p ^ 2) := by
    rw [suzukiCriticalApertureDepthFrostmanProfile, ccmFrostmanPoissonProfile]
    field_simp [hr, hD.ne']
  rw [hprofile]
  have hD0eq :
      1 - 2 * suzukiCriticalApertureDepthFusionRadius h a p * 1 +
          suzukiCriticalApertureDepthFusionRadius h a p ^ 2 =
        (1 - suzukiCriticalApertureDepthFusionRadius h a p) ^ 2 := by
    ring
  rw [hD0eq]
  have hs : 1 - suzukiCriticalApertureDepthFusionRadius h a p ≠ 0 :=
    sub_ne_zero.mpr hr1.ne'
  field_simp [hD.ne', hs]

/-- Central fused energy is strictly positive, so the normalized profile is a genuine ratio. -/
theorem normSq_suzukiCriticalApertureDepthFusedAtom_zero_pos
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (p : Nat.Primes) :
    0 < Complex.normSq (suzukiCriticalApertureDepthFusedAtom h a 0 p) := by
  rw [normSq_suzukiCriticalApertureDepthFusedAtom_eq hh ha]
  simp only [zero_mul, zero_div, Real.cos_zero]
  apply div_pos
  · exact sq_pos_of_pos (suzukiCriticalEntryWallEndpointAmplitude_zero_pos hh ha p)
  · nlinarith [sq_pos_of_pos (sub_pos.mpr
      (suzukiCriticalApertureDepthFusionRadius_lt_one hh ha p))]

/-- Division form of the Suzuki--CCM identity, justified by positive central energy. -/
theorem normSq_suzukiCriticalApertureDepthFusedAtom_div_zero_eq_frostmanProfile
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (t : ℝ) (p : Nat.Primes) :
    Complex.normSq (suzukiCriticalApertureDepthFusedAtom h a t p) /
        Complex.normSq (suzukiCriticalApertureDepthFusedAtom h a 0 p) =
      suzukiCriticalApertureDepthFrostmanProfile h a t p := by
  rw [normSq_suzukiCriticalApertureDepthFusedAtom_eq_zero_mul_frostmanProfile
    hh ha]
  exact mul_div_cancel_left₀ _
    (normSq_suzukiCriticalApertureDepthFusedAtom_zero_pos hh ha p).ne'

theorem suzukiCriticalApertureDepthFrostmanProfile_floor_le
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (t : ℝ) (p : Nat.Primes) :
    ccmFrostmanProfileFloor
        (suzukiCriticalApertureDepthFusionRadius h a p)⁻¹ ≤
      suzukiCriticalApertureDepthFrostmanProfile h a t p := by
  exact ccmFrostmanProfileFloor_le
    (one_lt_inv_suzukiCriticalApertureDepthFusionRadius hh ha p)

theorem suzukiCriticalApertureDepthFrostmanProfile_le_one
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (t : ℝ) (p : Nat.Primes) :
    suzukiCriticalApertureDepthFrostmanProfile h a t p ≤ 1 := by
  exact ccmFrostmanPoissonProfile_le_one
    (one_lt_inv_suzukiCriticalApertureDepthFusionRadius hh ha p)

@[simp] theorem suzukiCriticalApertureDepthFrostmanProfile_zero
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (p : Nat.Primes) :
    suzukiCriticalApertureDepthFrostmanProfile h a 0 p = 1 := by
  rw [suzukiCriticalApertureDepthFrostmanProfile]
  simpa using ccmFrostmanPoissonProfile_zero
    (one_lt_inv_suzukiCriticalApertureDepthFusionRadius hh ha p).ne'

private theorem ccmFrostmanPoissonProfile_eq_one_iff_cos
    {q θ : ℝ} (hq : 1 < q) :
    ccmFrostmanPoissonProfile q θ = 1 ↔ Real.cos θ = 1 := by
  have hD : 0 < q ^ 2 - 2 * q * Real.cos θ + 1 :=
    ccmFrostman_denominator_pos hq
  rw [ccmFrostmanPoissonProfile, div_eq_one_iff_eq hD.ne']
  constructor <;> intro h
  · nlinarith
  · rw [h]
    ring

private theorem phaseClockValue_eq_zero_iff_cos (rate time : ℝ) :
    HTGeometry.phaseClockValue rate time = HTGeometry.phaseClockValue rate 0 ↔
      Real.cos (rate * time) = 1 := by
  rw [HTGeometry.phaseClockValue, HTGeometry.phaseClockValue]
  simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero]
  constructor
  · intro heq
    have hsq := normSq_one_sub_exp_I_mul (rate * time)
    rw [heq] at hsq
    norm_num at hsq
    linarith
  · intro hcos
    have hsq := normSq_one_sub_exp_I_mul (rate * time)
    have hzero : Complex.normSq
        (1 - Complex.exp ((((rate * time : ℝ) : ℂ) * I))) = 0 := by
      rw [hsq, hcos]
      ring
    have hz : 1 - Complex.exp ((((rate * time : ℝ) : ℂ) * I)) = 0 :=
      Complex.normSq_eq_zero.mp hzero
    exact (sub_eq_zero.mp hz).symm

/-- The normalized fused energy reaches its central cap exactly when the underlying prime phase
returns to its central value. -/
theorem suzukiCriticalApertureDepthFrostmanProfile_eq_one_iff_phase
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (t : ℝ) (p : Nat.Primes) :
    suzukiCriticalApertureDepthFrostmanProfile h a t p = 1 ↔
      suzukiCriticalApertureDepthFusionPhase t p =
        suzukiCriticalApertureDepthFusionPhase 0 p := by
  rw [suzukiCriticalApertureDepthFrostmanProfile,
    ccmFrostmanPoissonProfile_eq_one_iff_cos
      (one_lt_inv_suzukiCriticalApertureDepthFusionRadius hh ha p)]
  have hphase := phaseClockValue_eq_zero_iff_cos (Real.log (p : ℝ)) (t / 2)
  rw [suzukiCriticalApertureDepthFusionPhase,
    suzukiCriticalApertureDepthFusionPhase]
  symm
  convert hphase using 1 <;> ring

/-! ## Two-prime faithful height separator -/

/-- Sum of two normalized causal-depth Frostman diagonals. -/
def suzukiCriticalApertureDepthFrostmanPairProfile
    (h a t : ℝ) (p q : Nat.Primes) : ℝ :=
  suzukiCriticalApertureDepthFrostmanProfile h a t p +
    suzukiCriticalApertureDepthFrostmanProfile h a t q

theorem suzukiCriticalApertureDepthFrostmanPairProfile_le_two
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a)
    (p q : Nat.Primes) (t : ℝ) :
    suzukiCriticalApertureDepthFrostmanPairProfile h a t p q ≤ 2 := by
  have hp_le := suzukiCriticalApertureDepthFrostmanProfile_le_one hh ha t p
  have hq_le := suzukiCriticalApertureDepthFrostmanProfile_le_one hh ha t q
  rw [suzukiCriticalApertureDepthFrostmanPairProfile]
  linarith

/-- **Two-prime unique cap.**  Distinct prime-log phases can simultaneously maximize their fused
Frostman energies only at the real height origin. -/
theorem suzukiCriticalApertureDepthFrostmanPairProfile_eq_two_iff
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a)
    {p q : Nat.Primes} (hpq : p ≠ q) (t : ℝ) :
    suzukiCriticalApertureDepthFrostmanPairProfile h a t p q = 2 ↔ t = 0 := by
  have hp_le := suzukiCriticalApertureDepthFrostmanProfile_le_one hh ha t p
  have hq_le := suzukiCriticalApertureDepthFrostmanProfile_le_one hh ha t q
  constructor
  · intro hsum
    have hp_one : suzukiCriticalApertureDepthFrostmanProfile h a t p = 1 := by
      rw [suzukiCriticalApertureDepthFrostmanPairProfile] at hsum
      linarith
    have hq_one : suzukiCriticalApertureDepthFrostmanProfile h a t q = 1 := by
      rw [suzukiCriticalApertureDepthFrostmanPairProfile] at hsum
      linarith
    have hp_phase :=
      (suzukiCriticalApertureDepthFrostmanProfile_eq_one_iff_phase hh ha t p).mp
        hp_one
    have hq_phase :=
      (suzukiCriticalApertureDepthFrostmanProfile_eq_one_iff_phase hh ha t q).mp
        hq_one
    have hpair : primeLogPhaseClockPair (p : ℕ) (q : ℕ) (t / 2) =
        primeLogPhaseClockPair (p : ℕ) (q : ℕ) 0 := by
      apply Prod.ext
      · simpa [primeLogPhaseClockPair, HTGeometry.phaseClockPair,
          suzukiCriticalApertureDepthFusionPhase] using hp_phase
      · simpa [primeLogPhaseClockPair, HTGeometry.phaseClockPair,
          suzukiCriticalApertureDepthFusionPhase] using hq_phase
    have htime := primeLogPhaseClockPair_injective p.property q.property
      (fun h => hpq (Subtype.ext h)) hpair
    linarith
  · rintro rfl
    rw [suzukiCriticalApertureDepthFrostmanPairProfile]
    simp [suzukiCriticalApertureDepthFrostmanProfile_zero hh ha]
    norm_num

/-- Translation-invariant deficit from the two-prime causal-depth cap. -/
def suzukiCriticalApertureDepthFrostmanSeparation
    (h a : ℝ) (p q : Nat.Primes) (t u : ℝ) : ℝ :=
  2 - suzukiCriticalApertureDepthFrostmanPairProfile h a (t - u) p q

theorem suzukiCriticalApertureDepthFrostmanSeparation_nonneg
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a)
    (p q : Nat.Primes) (t u : ℝ) :
    0 ≤ suzukiCriticalApertureDepthFrostmanSeparation h a p q t u := by
  rw [suzukiCriticalApertureDepthFrostmanSeparation]
  linarith [suzukiCriticalApertureDepthFrostmanPairProfile_le_two
    hh ha p q (t - u)]

/-- **Faithful height separation.**  Two distinct causal-depth prime profiles have zero joint
deficit exactly at equal real heights. -/
theorem suzukiCriticalApertureDepthFrostmanSeparation_eq_zero_iff
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a)
    {p q : Nat.Primes} (hpq : p ≠ q) (t u : ℝ) :
    suzukiCriticalApertureDepthFrostmanSeparation h a p q t u = 0 ↔ t = u := by
  rw [suzukiCriticalApertureDepthFrostmanSeparation, sub_eq_zero]
  constructor
  · intro h
    exact sub_eq_zero.mp
      ((suzukiCriticalApertureDepthFrostmanPairProfile_eq_two_iff
        hh ha hpq (t - u)).mp h.symm)
  · intro h
    exact ((suzukiCriticalApertureDepthFrostmanPairProfile_eq_two_iff
      hh ha hpq (t - u)).mpr (sub_eq_zero.mpr h)).symm

end

end RHTower
