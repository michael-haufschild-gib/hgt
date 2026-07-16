import GaloisForLFunctions.RHTower.PrimeArchBernsteinRpowPacketGrowth

/-!
# Real-p Bernstein growth of the completed Xi source

The endpoint Bernstein coefficient vector is viewed as a triangular complex packet.  The abstract
finite-packet theorem then gives its exact real-`p` growth for every `p >= 1`.

Under RH all divisor atoms have neutral affine amplitude one.  Under failure of RH the existing
dominant-mode theorem supplies a source-attained maximal amplitude `B > 1` and an eventually
surviving unit-circle pencil mode.  Consequently the packet's `p`-energy has nth-root limit
`1` under RH and `B^p` under failure of RH.
-/

open Complex Filter Topology
open scoped BigOperators Polynomial
open Polynomial

namespace RHTower

noncomputable section

/-- The endpoint prime--archimedean Bernstein coefficient packet, embedded in `Complex`. -/
def primeArchEndpointBernsteinPacket : ℕ → ℕ → ℂ :=
  fun n i =>
    (bernsteinCoefficient
      (radiusNormalizedMoment primeArchEndpointHausdorffRadius normalizedPrimeArchMoment)
      n i : ℂ)

/-- The endpoint packet's real-`p` energy. -/
def primeArchEndpointBernsteinRpowEnergy (p : ℝ) (n : ℕ) : ℝ :=
  finitePacketRpowEnergy primeArchEndpointBernsteinPacket p n

/-- Generic packet `l1` is the previously defined endpoint Bernstein total variation. -/
lemma finitePacketL1_primeArchEndpointBernsteinPacket (n : ℕ) :
    finitePacketL1 primeArchEndpointBernsteinPacket n =
      primeArchEndpointBernsteinTotalVariation n := by
  simp only [finitePacketL1, primeArchEndpointBernsteinPacket,
    primeArchEndpointBernsteinTotalVariation, bernsteinCoefficientL1,
    Complex.norm_real, Real.norm_eq_abs]

/-- Generic packet transform is the prime--archimedean Bernstein coefficient transform. -/
lemma finitePacketTransform_primeArchEndpointBernsteinPacket (n : ℕ) (w : ℂ) :
    finitePacketTransform primeArchEndpointBernsteinPacket n w =
      bernsteinCoefficientTransform
        (radiusNormalizedMoment primeArchEndpointHausdorffRadius normalizedPrimeArchMoment)
        n w := by
  rfl

/-- At `w = 1`, every endpoint coefficient transform equals the conserved zeroth source mass. -/
lemma finitePacketTransform_primeArchEndpointBernsteinPacket_one (n : ℕ) :
    finitePacketTransform primeArchEndpointBernsteinPacket n 1 =
      (normalizedPrimeArchMoment 0 : ℂ) := by
  rw [finitePacketTransform_primeArchEndpointBernsteinPacket,
    bernsteinCoefficientTransform]
  simp only [one_pow, mul_one]
  rw [sum_bernsteinCoefficient]
  simp [radiusNormalizedMoment]

/-- Under RH every endpoint atom has affine amplitude exactly one. -/
lemma xiEndpointBernsteinAtomAmplitudeBase_eq_one_of_riemannHypothesis
    (hRH : RiemannHypothesis) (q : XiZeroCopy) :
    xiEndpointBernsteinAtomAmplitudeBase q = 1 := by
  exact xiEndpointBernsteinAtomAmplitudeBase_eq_one_of_onLine q
    (xi_divisor_support_re_eq_half_of_rh hRH q.1)

/-- Under RH every finite real-`p` endpoint packet energy has nth-root limit one. -/
theorem tendsto_primeArchEndpointBernsteinRpowEnergy_rpow_inv_natCast_of_rh
    {p : ℝ} (hp : 1 ≤ p) (hRH : RiemannHypothesis) :
    Tendsto
      (fun n : ℕ => primeArchEndpointBernsteinRpowEnergy p n ^ ((n : ℝ)⁻¹))
      atTop (nhds 1) := by
  have hupper (n : ℕ) :
      finitePacketL1 primeArchEndpointBernsteinPacket n ≤
        xiReciprocalSquareAbsoluteMass * 1 ^ n := by
    rw [finitePacketL1_primeArchEndpointBernsteinPacket]
    exact primeArchEndpointBernsteinTotalVariation_le_of_atomAmplitudeBase 1
      (fun q => (xiEndpointBernsteinAtomAmplitudeBase_eq_one_of_riemannHypothesis hRH q).le) n
  have hlower : ∀ᶠ n : ℕ in atTop,
      normalizedPrimeArchMoment 0 * 1 ^ n ≤
        ‖finitePacketTransform primeArchEndpointBernsteinPacket n 1‖ := by
    filter_upwards with n
    rw [finitePacketTransform_primeArchEndpointBernsteinPacket_one,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos normalizedPrimeArchMoment_zero_pos, one_pow, mul_one]
  have h := tendsto_finitePacketRpowEnergy_rpow_inv_natCast
    primeArchEndpointBernsteinPacket hp xiReciprocalSquareAbsoluteMass_nonneg
    (by norm_num : (0 : ℝ) < 1) normalizedPrimeArchMoment_zero_pos
    (by norm_num : ‖(1 : ℂ)‖ ≤ 1) hupper hlower
  simpa only [primeArchEndpointBernsteinRpowEnergy, Real.one_rpow] using h

/-- Under failure of RH, a source-attained maximal atom amplitude controls every finite real-`p`
endpoint packet energy exactly. -/
theorem exists_attained_tendsto_primeArchEndpointBernsteinRpowEnergy_of_not_rh
    {p : ℝ} (hp : 1 ≤ p) (hRH : ¬ RiemannHypothesis) :
    ∃ B : ℝ,
      1 < B ∧ B < xiSectorConfinedBernsteinAmplitudeBase ∧
      (∃ q : XiZeroCopy, xiEndpointBernsteinAtomAmplitudeBase q = B) ∧
      (∀ q : XiZeroCopy, xiEndpointBernsteinAtomAmplitudeBase q ≤ B) ∧
      Tendsto
        (fun n : ℕ => primeArchEndpointBernsteinRpowEnergy p n ^ ((n : ℝ)⁻¹))
        atTop (nhds (B ^ p)) := by
  obtain ⟨w, B, delta, hw, hB, hdelta, hmax, hattained, hevent⟩ :=
    exists_maximalAmplitude_unit_xiCentralBernsteinPencil_eventually_exponential_of_not_rh hRH
  have hBpos : 0 < B := lt_trans zero_lt_one hB
  have hBsector : B < xiSectorConfinedBernsteinAmplitudeBase := by
    obtain ⟨q, hq⟩ := hattained
    rw [← hq]
    exact xiEndpointBernsteinAtomAmplitudeBase_lt_sectorConfined q
  have hupper (n : ℕ) :
      finitePacketL1 primeArchEndpointBernsteinPacket n ≤
        xiReciprocalSquareAbsoluteMass * B ^ n := by
    rw [finitePacketL1_primeArchEndpointBernsteinPacket]
    exact primeArchEndpointBernsteinTotalVariation_le_of_atomAmplitudeBase B hmax n
  have hlower : ∀ᶠ n : ℕ in atTop,
      delta * B ^ n ≤
        ‖finitePacketTransform primeArchEndpointBernsteinPacket n w‖ := by
    filter_upwards [hevent] with n hn
    have hBpow : 0 < B ^ n := pow_pos hBpos n
    have hn' : delta ≤
        ‖xiCentralBernsteinPencil primeArchEndpointHausdorffRadius n w‖ / B ^ n := by
      simpa only [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hBpos] using hn
    have hpencil : delta * B ^ n ≤
        ‖xiCentralBernsteinPencil primeArchEndpointHausdorffRadius n w‖ :=
      (le_div_iff₀ hBpow).mp hn'
    rwa [finitePacketTransform_primeArchEndpointBernsteinPacket,
      bernsteinCoefficientTransform_source_eq_xiCentralBernsteinPencil]
  refine ⟨B, hB, hBsector, hattained, hmax, ?_⟩
  have h := tendsto_finitePacketRpowEnergy_rpow_inv_natCast
    primeArchEndpointBernsteinPacket hp xiReciprocalSquareAbsoluteMass_nonneg
    hBpos hdelta hw.le hupper hlower
  simpa only [primeArchEndpointBernsteinRpowEnergy] using h

/-- **All-real-`p` endpoint growth criterion for RH.**  For every finite `p >= 1`, RH is
equivalent to neutral nth-root growth of the source-defined endpoint Bernstein `p`-energy. -/
theorem riemannHypothesis_iff_tendsto_primeArchEndpointBernsteinRpowEnergy
    {p : ℝ} (hp : 1 ≤ p) :
    RiemannHypothesis ↔
      Tendsto
        (fun n : ℕ => primeArchEndpointBernsteinRpowEnergy p n ^ ((n : ℝ)⁻¹))
        atTop (nhds 1) := by
  constructor
  · exact tendsto_primeArchEndpointBernsteinRpowEnergy_rpow_inv_natCast_of_rh hp
  · intro hneutral
    by_contra hRH
    obtain ⟨B, hB, hBsector, hattained, hmax, hgrowth⟩ :=
      exists_attained_tendsto_primeArchEndpointBernsteinRpowEnergy_of_not_rh hp hRH
    have heq : B ^ p = 1 := tendsto_nhds_unique hgrowth hneutral
    have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
    have hgt : 1 < B ^ p := by
      simpa only [Real.one_rpow] using Real.rpow_lt_rpow_of_exponent_lt hB hp0
    linarith

end

end RHTower
