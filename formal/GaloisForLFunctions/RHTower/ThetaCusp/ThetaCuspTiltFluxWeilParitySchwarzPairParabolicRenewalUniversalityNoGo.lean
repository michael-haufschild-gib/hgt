import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspTiltFluxWeilParitySchwarzPairParabolicRenewalWeld

/-!
# External-aperture universality no-go for Schwarz-pair Weyl renewal

The normalized terminal Weyl increment is not an arithmetic producer of the Schwarz-pair normal
coefficient.  Its value is universally the height of an externally supplied upper-half-plane
aperture, independently of the shifted-Xi moment sequence.  The previous Xi-indexed construction
is exactly the specialization obtained by choosing that height to be the absolute spectral
displacement.

On the explicit parabolic admission schedule, every positive real target is therefore realized
exactly by choosing the corresponding external aperture.  Consequently this renewal coordinate
cannot distinguish an off-line Xi copy from arbitrary positive external data and supplies no
vanishing pressure toward RH.  Any viable continuation must use a source-native quantity whose
value is fixed before the reporter aperture is chosen.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- Purely imaginary external aperture with prescribed real height. -/
def xiSchwarzPairExternalWeylAperture (h : ℝ) : ℂ :=
  (h : ℂ) * Complex.I

@[simp] theorem xiSchwarzPairExternalWeylAperture_im (h : ℝ) :
    (xiSchwarzPairExternalWeylAperture h).im = h := by
  simp [xiSchwarzPairExternalWeylAperture]

/-- Normalized degree increment obtained from an arbitrary external aperture height. -/
def xiSchwarzPairExternalWeylNormalizedIncrement
    (h w : ℝ) (n : ℕ) : ℝ :=
  let z := xiSchwarzPairExternalWeylAperture h
  let Wnext := xiShiftedCanonicalAdmissionCompletedSourceWeylAggregateComplex w (n + 1) z
  let Wcurrent := xiShiftedCanonicalAdmissionCompletedSourceWeylAggregateComplex w n z
  (-Wnext.im) / Complex.normSq Wnext -
    HTGeometry.monicOrthoBeta (xiShiftedRealMomentSequence w) n * (-Wcurrent.im)

/-- The Xi-indexed normal increment is definitionally only an external-aperture specialization. -/
theorem xiSchwarzPairCompletedSourceWeylNormalizedIncrement_eq_external
    (q : XiZeroCopy) (w : ℝ) (n : ℕ) :
    xiSchwarzPairCompletedSourceWeylNormalizedIncrement q w n =
      xiSchwarzPairExternalWeylNormalizedIncrement
        |(xiSpectralPoint q).im| w n := by
  rfl

/-- Exact external-aperture law: every admitted nonlinear renewal returns the chosen height. -/
theorem xiSchwarzPairExternalWeylNormalizedIncrement_eq_height
    {h w : ℝ} {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 3)).PosDef)
    (hh : 0 < h) :
    xiSchwarzPairExternalWeylNormalizedIncrement h w n = h := by
  have hz : 0 < (xiSchwarzPairExternalWeylAperture h).im := by
    simpa using hh
  simpa only [xiSchwarzPairExternalWeylNormalizedIncrement,
    xiSchwarzPairExternalWeylAperture_im] using
    xiShiftedCanonicalAdmissionCompletedSourceWeylAggregateComplex_normalized_increment
      hn hH hz

/-- On the explicit parabolic schedule, every positive external target is reproduced exactly at
every degree. -/
theorem xiSchwarzPairExternalParabolicWeylNormalizedIncrement_eq_height
    {h : ℝ} (hh : 0 < h) (n : ℕ) :
    xiSchwarzPairExternalWeylNormalizedIncrement h
        (xiSchwarzPairParabolicNormalRenewalSchedule n) (n + 1) = h := by
  have hHbig := xiSchwarzPairParabolicNormalRenewalSchedule_posDef n
  have hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence (xiSchwarzPairParabolicNormalRenewalSchedule n))
      (n + 4)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hHbig
  exact xiSchwarzPairExternalWeylNormalizedIncrement_eq_height
    (by omega : 0 < n + 1) hH hh

/-- The positive range of the parabolic normalized increment is the entire positive half-line;
it is selected solely by the external aperture. -/
theorem range_xiSchwarzPairExternalParabolicWeylNormalizedIncrement (n : ℕ) :
    Set.range (fun h : Set.Ioi (0 : ℝ) =>
      xiSchwarzPairExternalWeylNormalizedIncrement h.1
        (xiSchwarzPairParabolicNormalRenewalSchedule n) (n + 1)) =
      Set.Ioi (0 : ℝ) := by
  ext c
  constructor
  · rintro ⟨h, rfl⟩
    simpa only [xiSchwarzPairExternalParabolicWeylNormalizedIncrement_eq_height h.2 n]
      using h.2
  · intro hc
    exact ⟨⟨c, hc⟩, xiSchwarzPairExternalParabolicWeylNormalizedIncrement_eq_height hc n⟩

/-- The apparent Xi-normal renewal is exactly the arbitrary external target obtained by setting
the aperture height equal to the spectral displacement. -/
theorem xiSchwarzPairParabolicWeylIncrement_eq_externalTarget
    (q : XiZeroCopy) (n : ℕ) :
    xiSchwarzPairCompletedSourceWeylNormalizedIncrement q
        (xiSchwarzPairParabolicNormalRenewalSchedule n) (n + 1) =
      xiSchwarzPairExternalWeylNormalizedIncrement |(xiSpectralPoint q).im|
        (xiSchwarzPairParabolicNormalRenewalSchedule n) (n + 1) := by
  exact xiSchwarzPairCompletedSourceWeylNormalizedIncrement_eq_external _ _ _

end

end RHTower
