import GaloisForLFunctions.RHTower.HedenmalmContinuousApertureEndpointDoublet
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Exact domain of the source-derived Hedenmalm endpoint doublet

The even/odd endpoint pair obtained from center and aperture differentiation of the theta-source
window has no prime-clock coordinate in its energy.  This file proves its exact finite-cutoff
decomposition into prime harmonic mass plus radial reflected energy, then classifies its
sub-`log^(2 : ℕ)` domain.

This closes multiplicity-safe receiver geometry.  It does not prove that Xi root blocks enter the
closed all-prime source domain.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

open HedenmalmContinuousAperture

/-- Energy of one actual source-derived even/odd endpoint symbol. -/
def hedenmalmPrimeEndpointDoubletTerm (p : ℕ) (z : ℂ) : ℝ :=
  ‖hedenmalmPrimeEvenSolder
      (centeredApertureMarkedCharacter (Real.log p) z)‖ ^ (2 : ℕ) +
    ‖-Complex.I * hedenmalmPrimeOddSolder
      (centeredApertureMarkedCharacter (Real.log p) z)‖ ^ (2 : ℕ)

/-- Finite energy of the actual source-derived even/odd endpoint symbols. -/
def hedenmalmPrimeEndpointDoubletEnergy (N : ℕ) (z : ℂ) : ℝ :=
  ∑ p ∈ Nat.primesLE N, hedenmalmPrimeEndpointDoubletTerm p z

/-- Prime reciprocal mass at a finite cutoff. -/
def hedenmalmPrimeReciprocalCutoffMass (N : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE N, 1 / (p : ℝ)

/-- The source-derived endpoint energy is pointwise radial: no real spectral coordinate remains. -/
theorem hedenmalmPrimeEndpointDoubletEnergy_eq_cosh (N : ℕ) (z : ℂ) :
    hedenmalmPrimeEndpointDoubletEnergy N z =
      ∑ p ∈ Nat.primesLE N,
        4 / (p : ℝ) * Real.cosh (z.im * Real.log p) := by
  rw [hedenmalmPrimeEndpointDoubletEnergy]
  apply Finset.sum_congr rfl
  intro p hp
  let P : Nat.Primes := ⟨p, (Nat.mem_primesLE.mp hp).2⟩
  simpa only [hedenmalmPrimeEndpointDoubletTerm, P] using
    prime_endpointSymbol_energy_eq_cosh P z

/-- **Clock-free endpoint decomposition.** The marked endpoint doublet is exactly prime harmonic
mass plus twice the radial reflected energy. -/
theorem hedenmalmPrimeEndpointDoubletEnergy_eq_mass_add_radial (N : ℕ) (z : ℂ) :
    hedenmalmPrimeEndpointDoubletEnergy N z =
      4 * hedenmalmPrimeReciprocalCutoffMass N +
        2 * primeClockCutoffEnergy N (z.im / 2) := by
  rw [hedenmalmPrimeEndpointDoubletEnergy_eq_cosh,
    hedenmalmPrimeReciprocalCutoffMass, primeClockCutoffEnergy_eq_sinh,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hhalf :
      Real.cosh (z.im * Real.log p) =
        1 + 2 * Real.sinh ((z.im / 2) * Real.log p) ^ (2 : ℕ) := by
    have h := Real.cosh_two_mul ((z.im / 2) * Real.log p)
    rw [show 2 * ((z.im / 2) * Real.log p) = z.im * Real.log p by ring] at h
    nlinarith [Real.cosh_sq_sub_sinh_sq ((z.im / 2) * Real.log p)]
  rw [hhalf]
  ring

theorem hedenmalmPrimeReciprocalCutoffMass_nonneg (N : ℕ) :
    0 ≤ hedenmalmPrimeReciprocalCutoffMass N := by
  rw [hedenmalmPrimeReciprocalCutoffMass]
  apply Finset.sum_nonneg
  intro p hp
  positivity

/-- Prime reciprocal cutoff mass is bounded by the ordinary harmonic number. -/
theorem hedenmalmPrimeReciprocalCutoffMass_le_harmonic (N : ℕ) :
    hedenmalmPrimeReciprocalCutoffMass N ≤ (harmonic N : ℝ) := by
  rw [hedenmalmPrimeReciprocalCutoffMass, Nat.primesLE_eq_filter_Icc_one,
    harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset Nat.Prime (Finset.Icc 1 N))
    (fun p _ _ => inv_nonneg.mpr (by exact_mod_cast (Nat.zero_le p)))

/-- The endpoint doublet energy is nonnegative. -/
theorem hedenmalmPrimeEndpointDoubletEnergy_nonneg (N : ℕ) (z : ℂ) :
    0 ≤ hedenmalmPrimeEndpointDoubletEnergy N z := by
  rw [hedenmalmPrimeEndpointDoubletEnergy]
  apply Finset.sum_nonneg
  intro p hp
  rw [hedenmalmPrimeEndpointDoubletTerm]
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

/-- The `o(log^(2 : ℕ) N)` finite-domain condition for the source-derived endpoint doublet. -/
def HedenmalmPrimeEndpointDoubletSubLogSquare (z : ℂ) : Prop :=
  Tendsto
    (fun N : ℕ => hedenmalmPrimeEndpointDoubletEnergy N z / Real.log N ^ (2 : ℕ))
    atTop (𝓝 0)

/-- Every centered-real point belongs to the endpoint-doublet sub-`log^(2 : ℕ)` domain. -/
theorem hedenmalmPrimeEndpointDoubletSubLogSquare_of_im_eq_zero
    {z : ℂ} (hz : z.im = 0) :
    HedenmalmPrimeEndpointDoubletSubLogSquare z := by
  rw [HedenmalmPrimeEndpointDoubletSubLogSquare]
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinvlog : Tendsto (fun N : ℕ => (8 : ℝ) / Real.log N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  apply squeeze_zero'
  · exact Eventually.of_forall fun N =>
      div_nonneg (hedenmalmPrimeEndpointDoubletEnergy_nonneg N z) (sq_nonneg _)
  · filter_upwards [eventually_ge_atTop 3] with N hN
    have hlogone : 1 ≤ Real.log N := by
      have h3 : Real.exp 1 < (3 : ℝ) := Real.exp_one_lt_d9.trans_le (by norm_num)
      have hNreal : (3 : ℝ) ≤ N := by exact_mod_cast hN
      calc
        1 = Real.log (Real.exp 1) := by rw [Real.log_exp]
        _ ≤ Real.log N := Real.log_le_log (Real.exp_pos 1) (h3.le.trans hNreal)
    have henergy : hedenmalmPrimeEndpointDoubletEnergy N z ≤
        4 * (harmonic N : ℝ) := by
      rw [hedenmalmPrimeEndpointDoubletEnergy_eq_mass_add_radial, hz, zero_div,
        primeClockCutoffEnergy_zero, mul_zero, add_zero]
      gcongr
      exact hedenmalmPrimeReciprocalCutoffMass_le_harmonic N
    have hharm : (harmonic N : ℝ) ≤ 1 + Real.log N :=
      harmonic_le_one_add_log N
    have hlogpos : 0 < Real.log N := lt_of_lt_of_le zero_lt_one hlogone
    calc
      hedenmalmPrimeEndpointDoubletEnergy N z / Real.log N ^ (2 : ℕ) ≤
          (4 * (harmonic N : ℝ)) / Real.log N ^ (2 : ℕ) :=
        div_le_div_of_nonneg_right henergy (sq_nonneg _)
      _ ≤ (4 * (1 + Real.log N)) / Real.log N ^ (2 : ℕ) := by
        gcongr
      _ ≤ 8 / Real.log N := by
        rw [div_le_div_iff₀ (sq_pos_of_pos hlogpos) hlogpos]
        nlinarith
  · exact hinvlog

/-- Sub-`log^(2 : ℕ)` endpoint-doublet energy forces zero radial displacement. -/
theorem im_eq_zero_of_hedenmalmPrimeEndpointDoubletSubLogSquare
    {z : ℂ} (h : HedenmalmPrimeEndpointDoubletSubLogSquare z) :
    z.im = 0 := by
  have hradial : Tendsto
      (fun N : ℕ => primeClockCutoffEnergy N (z.im / 2) / Real.log N ^ (2 : ℕ))
      atTop (𝓝 0) := by
    have hnonneg : ∀ᶠ N : ℕ in atTop,
        0 ≤ primeClockCutoffEnergy N (z.im / 2) / Real.log N ^ (2 : ℕ) :=
      Eventually.of_forall fun N =>
        div_nonneg (primeClockCutoffEnergy_nonneg N (z.im / 2)) (sq_nonneg _)
    have hle : ∀ᶠ N : ℕ in atTop,
        primeClockCutoffEnergy N (z.im / 2) / Real.log N ^ (2 : ℕ) ≤
          hedenmalmPrimeEndpointDoubletEnergy N z / Real.log N ^ (2 : ℕ) := by
      filter_upwards with N
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      rw [hedenmalmPrimeEndpointDoubletEnergy_eq_mass_add_radial]
      have hm := hedenmalmPrimeReciprocalCutoffMass_nonneg N
      have hr := primeClockCutoffEnergy_nonneg N (z.im / 2)
      nlinarith
    exact squeeze_zero' hnonneg hle h
  have hzero :=
    tendsto_horizontalDisplacement_zero_of_energy_div_log_sq_tendsto_zero
      (fun _ : ℕ => z.im / 2) hradial
  have heq : z.im / 2 = 0 := tendsto_nhds_unique tendsto_const_nhds hzero
  linarith

/-- **Exact clock-free endpoint domain classification.** -/
theorem hedenmalmPrimeEndpointDoubletSubLogSquare_iff_im_eq_zero (z : ℂ) :
    HedenmalmPrimeEndpointDoubletSubLogSquare z ↔ z.im = 0 := by
  exact ⟨im_eq_zero_of_hedenmalmPrimeEndpointDoubletSubLogSquare,
    hedenmalmPrimeEndpointDoubletSubLogSquare_of_im_eq_zero⟩

/-- Zero-fibre endpoint-domain premise; source-domain construction remains open. -/
def XiCZeroHedenmalmPrimeEndpointDoubletSubLogSquare : Prop :=
  ∀ z : ℂ, XiC z = 0 → HedenmalmPrimeEndpointDoubletSubLogSquare z

/-- RH consumer for the source-derived endpoint doublet. -/
theorem riemannHypothesis_of_xiCZeroHedenmalmPrimeEndpointDoubletSubLogSquare
    (h : XiCZeroHedenmalmPrimeEndpointDoubletSubLogSquare) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_xiCZeroHedenmalmPrimeNormalSubLogSquare
  intro z hz
  exact hedenmalmPrimeNormalSubLogSquare_of_im_eq_zero
    ((hedenmalmPrimeEndpointDoubletSubLogSquare_iff_im_eq_zero z).mp (h z hz))

end

end RHTower

