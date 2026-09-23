import GaloisForLFunctions.RHTower.XiPhysicalPrimeApertureThetaAbelEnergyPrimeCanonicalSelectedContour

/-!
# Vanishing-error canonical corrected-prime contour limit

The fixed selected contour array used a uniform error radius one.  Here the radius-`m` rectangle is
selected with error `1 / (m + 1)`.  The canonical packets are cofinal and the error tends to zero,
so the corrected literal prime contours converge exactly to complete physical theta--Abel Weil
energy.  Removing the explicit archimedean correction gives an exact limit formula for the raw
continued-prime contour.

This limit yields an asymptotic zero-floor criterion: at every admissible logarithmic scale, the
selected corrected-prime real parts are eventually above every negative epsilon exactly when RH
holds.
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

/-- Pole-crossing canonical-radius approximation contract at arbitrary positive accuracy. -/
def XiPhysicalThetaAbelEnergyCanonicalApproxRectangleSpecAt
    (L A c a ε : ℝ) (m : ℕ) (z : ℂ × ℂ) : Prop :=
  z.1.re < z.2.re ∧ z.1.im < z.2.im ∧
  z.1.re < 0 ∧ 0 < z.2.re ∧
  z.1.im < -(1 / 2) ∧ -(1 / 2) < z.2.im ∧ z.2.im < 1 / 2 ∧
  (∀ q ∈ xiPhysicalThetaAbelEnergyCanonicalPacket m,
    q ∈ xiZeroCopyClosedRectangle z.1 z.2) ∧
  (∀ x ∈ uIcc z.1.re z.2.re,
    XiExplicitAdmissible ((x : ℂ) + z.1.im * I)) ∧
  (∀ x ∈ uIcc z.1.re z.2.re,
    XiExplicitAdmissible ((x : ℂ) + z.2.im * I)) ∧
  (∀ y ∈ uIcc z.1.im z.2.im,
    XiExplicitAdmissible ((z.2.re : ℂ) + y * I)) ∧
  (∀ y ∈ uIcc z.1.im z.2.im,
    XiExplicitAdmissible ((z.1.re : ℂ) + y * I)) ∧
  dist (xiPhysicalThetaAbelEnergyNormalizedSourceContour L A c a z.1 z.2)
    (xiWeilPolarization
      (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a)
      (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a)) < ε

/-- The arbitrary-accuracy canonical approximation contract is inhabited. -/
theorem exists_canonicalApproxRectangleSpecAt
    {A c : ℝ} (hA : 0 < A) (hc : 0 < c) (L a ε : ℝ) (m : ℕ)
    (hε : 0 < ε) :
    ∃ z : ℂ × ℂ,
      XiPhysicalThetaAbelEnergyCanonicalApproxRectangleSpecAt
        L A c a ε m z := by
  obtain ⟨z₁, z₂, hre, him, hleftGeom, hrightGeom, hbelow, habove, htopGeom,
      hpacket, hbot, htop, hright, hleft, hdist⟩ :=
    exists_poleCrossing_admissible_physicalThetaAbelEnergySourceContour_containing_approximates_weil
      hA hc L a (xiPhysicalThetaAbelEnergyCanonicalPacket m) hε
  exact ⟨(z₁, z₂), hre, him, hleftGeom, hrightGeom, hbelow, habove, htopGeom,
    hpacket, hbot, htop, hright, hleft, hdist⟩

/-- Fixed radius-`m` canonical rectangle selected at accuracy `1 / (m + 1)`. -/
noncomputable def xiPhysicalThetaAbelEnergyCanonicalVanishingApproxRectangle
    {A c : ℝ} (hA : 0 < A) (hc : 0 < c) (L a : ℝ) (m : ℕ) : ℂ × ℂ :=
  Classical.choose (exists_canonicalApproxRectangleSpecAt hA hc L a
    (1 / ((m : ℝ) + 1)) m (by positivity))

/-- The vanishing-error selected rectangle satisfies its full contract. -/
theorem xiPhysicalThetaAbelEnergyCanonicalVanishingApproxRectangle_spec
    {A c : ℝ} (hA : 0 < A) (hc : 0 < c) (L a : ℝ) (m : ℕ) :
    XiPhysicalThetaAbelEnergyCanonicalApproxRectangleSpecAt
      L A c a (1 / ((m : ℝ) + 1)) m
      (xiPhysicalThetaAbelEnergyCanonicalVanishingApproxRectangle hA hc L a m) :=
  Classical.choose_spec (exists_canonicalApproxRectangleSpecAt hA hc L a
    (1 / ((m : ℝ) + 1)) m (by positivity))

/-- Corrected literal prime-contour value on the vanishing-error selected rectangle. -/
noncomputable def xiPhysicalThetaAbelEnergyCanonicalVanishingCorrectedPrimeSample
    {A c : ℝ} (hA : 0 < A) (hc : 0 < c) (L a : ℝ) (m : ℕ) : ℂ :=
  xiPhysicalThetaAbelEnergyCorrectedPrimeSourceContour L A c a
    (xiPhysicalThetaAbelEnergyCanonicalVanishingApproxRectangle hA hc L a m).1
    (xiPhysicalThetaAbelEnergyCanonicalVanishingApproxRectangle hA hc L a m).2

/-- Raw normalized continued-prime contour on the same vanishing-error selected rectangle. -/
noncomputable def xiPhysicalThetaAbelEnergyCanonicalVanishingPrimeSample
    {A c : ℝ} (hA : 0 < A) (hc : 0 < c) (L a : ℝ) (m : ℕ) : ℂ :=
  xiPhysicalThetaAbelEnergyNormalizedPrimeSourceContour L A c a
    (xiPhysicalThetaAbelEnergyCanonicalVanishingApproxRectangle hA hc L a m).1
    (xiPhysicalThetaAbelEnergyCanonicalVanishingApproxRectangle hA hc L a m).2

/-- Quantitative vanishing error for the selected corrected-prime samples. -/
theorem dist_canonicalVanishingCorrectedPrimeSample_weil_lt
    {A c : ℝ} (hA : 0 < A) (hc : 0 < c) (L a : ℝ) (m : ℕ) :
    dist (xiPhysicalThetaAbelEnergyCanonicalVanishingCorrectedPrimeSample
      hA hc L a m)
      (xiWeilPolarization
        (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a)
        (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a)) <
      1 / ((m : ℝ) + 1) := by
  obtain ⟨hre, him, hleftGeom, hrightGeom, hbelow, habove, htopGeom,
      _hpacket, hbot, htop, hright, hleft, hdist⟩ :=
    xiPhysicalThetaAbelEnergyCanonicalVanishingApproxRectangle_spec
      hA hc L a m
  rw [xiPhysicalThetaAbelEnergyCanonicalVanishingCorrectedPrimeSample,
    ← xiPhysicalThetaAbelEnergyNormalizedSourceContour_eq_correctedPrime
      hbot htop hright hleft him hleftGeom hrightGeom hbelow habove htopGeom]
  exact hdist

/-- Exact corrected-prime contour limit along the canonical vanishing-error radius schedule. -/
theorem tendsto_canonicalVanishingCorrectedPrimeSample_weil
    {A c : ℝ} (hA : 0 < A) (hc : 0 < c) (L a : ℝ) :
    Tendsto (fun m : ℕ =>
      xiPhysicalThetaAbelEnergyCanonicalVanishingCorrectedPrimeSample
        hA hc L a m) atTop
      (nhds (xiWeilPolarization
        (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a)
        (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a))) := by
  refine Metric.tendsto_atTop.mpr ?_
  intro ε hε
  have hevent : ∀ᶠ m : ℕ in atTop, 1 / ((m : ℝ) + 1) < ε := by
    exact (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (Iio_mem_nhds hε)
  rw [eventually_atTop] at hevent
  obtain ⟨M, hM⟩ := hevent
  exact ⟨M, fun m hm =>
    (dist_canonicalVanishingCorrectedPrimeSample_weil_lt
      hA hc L a m).trans (hM m hm)⟩

/-- Exact raw-prime contour limit: the only missing term is the explicit centered archimedean
residue square. -/
theorem tendsto_canonicalVanishingPrimeSample_weil_sub_archSq
    {A c : ℝ} (hA : 0 < A) (hc : 0 < c) (L a : ℝ) :
    Tendsto (fun m : ℕ =>
      xiPhysicalThetaAbelEnergyCanonicalVanishingPrimeSample hA hc L a m) atTop
      (nhds (xiWeilPolarization
        (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a)
        (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a) -
        (((Real.exp (a / 2) * 2 * (1 - Real.exp (-(L / 2))) * c * A : ℝ) : ℂ) ^ (2 : ℕ)))) := by
  have h := tendsto_canonicalVanishingCorrectedPrimeSample_weil hA hc L a
  let K : ℂ :=
    (((Real.exp (a / 2) * 2 * (1 - Real.exp (-(L / 2))) * c * A : ℝ) : ℂ) ^ (2 : ℕ))
  have hconst : Tendsto (fun _ : ℕ => K) atTop (nhds K) := tendsto_const_nhds
  have hsub := h.sub hconst
  dsimp only [K] at hsub
  simpa [xiPhysicalThetaAbelEnergyCanonicalVanishingCorrectedPrimeSample,
    xiPhysicalThetaAbelEnergyCanonicalVanishingPrimeSample,
    xiPhysicalThetaAbelEnergyCorrectedPrimeSourceContour] using hsub

/-- Asymptotic zero-floor condition for the vanishing-error selected corrected-prime array. -/
def XiPhysicalThetaAbelEnergyCanonicalVanishingAsymptoticallyNonnegative
    {A c : ℝ} (hA : 0 < A) (hc : 0 < c) (L : ℝ) : Prop :=
  ∀ n : ℕ, L < Real.log n / 2 → ∀ ε : ℝ, 0 < ε →
    ∀ᶠ m : ℕ in atTop,
      -ε < (xiPhysicalThetaAbelEnergyCanonicalVanishingCorrectedPrimeSample
        hA hc L (Real.log n / 2) m).re

/-- Exact asymptotic prime-contour criterion: eventual lower bounds at every negative epsilon along
the canonical vanishing-error schedule hold exactly under RH. -/
theorem canonicalVanishingAsymptoticallyNonnegative_iff_riemannHypothesis
    {L A c : ℝ} (hL : 0 < L) (hA : 0 < A) (hc : 0 < c) :
    XiPhysicalThetaAbelEnergyCanonicalVanishingAsymptoticallyNonnegative hA hc L ↔
      RiemannHypothesis := by
  constructor
  · intro hasym
    rw [riemannHypothesis_iff_physicalThetaAbelEnergy_logSample_weil_nonneg
      hL hA hc]
    intro n hLn
    let W : ℂ := xiWeilPolarization
      (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c (Real.log n / 2))
      (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c (Real.log n / 2))
    have hrelim : Tendsto
        (fun m : ℕ =>
          (xiPhysicalThetaAbelEnergyCanonicalVanishingCorrectedPrimeSample
            hA hc L (Real.log n / 2) m).re) atTop (nhds W.re) :=
      (Complex.continuous_re.tendsto _).comp
        (tendsto_canonicalVanishingCorrectedPrimeSample_weil
          hA hc L (Real.log n / 2))
    by_contra hW
    have hWneg : W.re < 0 := lt_of_not_ge hW
    let ε : ℝ := -W.re / 2
    have hε : 0 < ε := by dsimp only [ε]; linarith
    have hlower := hasym n hLn ε hε
    have hupper : ∀ᶠ m : ℕ in atTop,
        (xiPhysicalThetaAbelEnergyCanonicalVanishingCorrectedPrimeSample
          hA hc L (Real.log n / 2) m).re < -ε := by
      exact hrelim.eventually (Iio_mem_nhds (by
        dsimp only [ε]
        linarith))
    obtain ⟨m, hmLower, hmUpper⟩ := (hlower.and hupper).exists
    linarith
  · intro hRH n _hLn ε hε
    let W : ℂ := xiWeilPolarization
      (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c (Real.log n / 2))
      (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c (Real.log n / 2))
    have hweil : 0 ≤ W.re :=
      (riemannHypothesis_iff_xiWeilPolarization_nonneg.mp hRH)
        (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c (Real.log n / 2))
        (xiPhysicalThetaAbelEnergyTwoEdgeTransform_squareSummable
          hA hc L (Real.log n / 2))
    have hrelim : Tendsto
        (fun m : ℕ =>
          (xiPhysicalThetaAbelEnergyCanonicalVanishingCorrectedPrimeSample
            hA hc L (Real.log n / 2) m).re) atTop (nhds W.re) :=
      (Complex.continuous_re.tendsto _).comp
        (tendsto_canonicalVanishingCorrectedPrimeSample_weil
          hA hc L (Real.log n / 2))
    exact hrelim.eventually
      (Ioi_mem_nhds (lt_of_lt_of_le (neg_lt_zero.mpr hε) hweil))

/-- Premise-free unit-parameter asymptotic corrected-prime criterion. -/
theorem unitCanonicalVanishingAsymptoticallyNonnegative_iff_riemannHypothesis :
    XiPhysicalThetaAbelEnergyCanonicalVanishingAsymptoticallyNonnegative
      (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1) 1 ↔
      RiemannHypothesis := by
  exact canonicalVanishingAsymptoticallyNonnegative_iff_riemannHypothesis
    (by norm_num) (by norm_num) (by norm_num)

end

end RHTower
