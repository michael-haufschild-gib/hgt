import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCanonicalLeftResponseWard
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSourceFaithfulBranchCovarianceNoGo

/-!
# Canonical BM left-action covariance endpoint

The global Peierls construction already realizes exact BM incidence for canonical left-coordinate
source packets on every Xi fibre. The remaining two-branch question is whether FE reflection sends
the canonical regular left source to the complementary one.

This module separates those burdens exactly. Actual action incidence holds unconditionally, while
canonical left-source covariance at one fibre holds exactly on the critical line. Consequently the
global package "constructed action incidence plus canonical branch covariance" is equivalent to
RH, to unit canonical left-response stationarity, and to canonical FE--Schwarz orbit optical
darkness.

On every tilted fibre, incidence survives, branch covariance fails, and orbit optical power is
strictly positive. Thus failure of a two-branch Schwarz lift cannot be blamed on missing Peierls
incidence; the positive survivor is the four-sector FE--Schwarz orbit landing.

`[NEW] [ACTION INCIDENCE] [BRANCH COVARIANCE] [EXACT RH ENDPOINT] [LEAN-PROVED]`
-/

open Complex

namespace RHTower

noncomputable section

/-- Exact unit-amplitude canonical left-coordinate incidence for the constructed global Peierls
propagator. -/
def HBXiPeierlsCanonicalLeftActionIncidence (n : ℕ) : Prop :=
  ∀ q : XiZeroCopy,
    d4GaugeFixedTeukolskyPeierlsSourcePairing hbXiPeierlsPairing
        (hbXiPeierlsPropagator n)
        (hbXiPeierlsPlusLeftSource n 1 q)
        (hbXiPeierlsMinusLeftSource n 1 q) =
      d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n 1 q

/-- FE reflection exchanges the unit canonical regular and complementary left source packets on
every Xi fibre. -/
def HBXiPeierlsCanonicalLeftBranchCovariance (n : ℕ) : Prop :=
  ∀ q : XiZeroCopy,
    hbXiPeierlsPlusLeftSource n 1 (xiZeroCopyReflectEquiv q) =
      hbXiPeierlsMinusLeftSource n 1 q

/-- Canonical left-action endpoint: actual Peierls incidence together with two-branch FE
covariance. -/
def HBXiPeierlsCanonicalLeftActionCovariance (n : ℕ) : Prop :=
  HBXiPeierlsCanonicalLeftActionIncidence n ∧
    HBXiPeierlsCanonicalLeftBranchCovariance n

/-- Nonzero canonical left sources are FE-covariant exactly on the critical wall. -/
theorem hbXiPeierlsCanonicalLeftSource_reflect_eq_iff
    (n : ℕ) {amplitude : ℂ} (ha : amplitude ≠ 0) (q : XiZeroCopy) :
    hbXiPeierlsPlusLeftSource n amplitude (xiZeroCopyReflectEquiv q) =
        hbXiPeierlsMinusLeftSource n amplitude q ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [hbXiPeierlsPlusLeftSource_eq, hbXiPeierlsMinusLeftSource_eq]
  exact hbXiPeierlsPlusSource_reflect_eq_minusSource_iff ha q

/-- At unit amplitude, canonical left-source covariance and canonical left-response stationarity
are the same fibrewise equation. -/
theorem hbXiPeierlsCanonicalUnitLeftSourceCovariance_iff_regularLeftCurrent_zero
    (n : ℕ) (q : XiZeroCopy) :
    hbXiPeierlsPlusLeftSource n 1 (xiZeroCopyReflectEquiv q) =
        hbXiPeierlsMinusLeftSource n 1 q ↔
      d4BMXiSecondHarmonicCanonicalRegularLeftResponseCurrent n 1 q = 0 := by
  rw [hbXiPeierlsCanonicalLeftSource_reflect_eq_iff n (by norm_num),
    d4BMXiSecondHarmonicCanonicalRegularLeftResponseCurrent_eq_zero_iff]
  norm_num

/-- Constructed global Peierls action has exact canonical left-coordinate incidence
unconditionally. -/
theorem hbXiPeierlsCanonicalLeftActionIncidence_holds (n : ℕ) :
    HBXiPeierlsCanonicalLeftActionIncidence n := by
  intro q
  exact hbXiPeierls_BM_leftSource_incidence n 1 q

/-- Universal canonical left-source FE covariance is exactly RH. -/
theorem hbXiPeierlsCanonicalLeftBranchCovariance_iff_rh (n : ℕ) :
    HBXiPeierlsCanonicalLeftBranchCovariance n ↔ RiemannHypothesis := by
  unfold HBXiPeierlsCanonicalLeftBranchCovariance
  simpa only [hbXiPeierlsCanonicalUnitLeftSourceCovariance_iff_regularLeftCurrent_zero,
    one_ne_zero, false_or] using
    forall_d4BMXiSecondHarmonicCanonicalRegularLeftResponseCurrent_eq_zero_iff n 1

/-- Actual canonical left-action incidence plus two-branch FE covariance is exactly RH. -/
theorem hbXiPeierlsCanonicalLeftActionCovariance_iff_rh (n : ℕ) :
    HBXiPeierlsCanonicalLeftActionCovariance n ↔ RiemannHypothesis := by
  constructor
  · intro h
    exact (hbXiPeierlsCanonicalLeftBranchCovariance_iff_rh n).mp h.2
  · intro hRH
    exact ⟨hbXiPeierlsCanonicalLeftActionIncidence_holds n,
      (hbXiPeierlsCanonicalLeftBranchCovariance_iff_rh n).mpr hRH⟩

/-- Unit canonical regular-left response stationarity is exactly RH. -/
theorem hbXiPeierlsCanonicalRegularUnitLeftWard_iff_rh (n : ℕ) :
    (∀ q : XiZeroCopy,
      d4BMXiSecondHarmonicCanonicalRegularLeftResponseCurrent n 1 q = 0) ↔
      RiemannHypothesis := by
  simpa only [one_ne_zero, false_or] using
    forall_d4BMXiSecondHarmonicCanonicalRegularLeftResponseCurrent_eq_zero_iff n 1

/-- The actual left-action covariance endpoint is the unit canonical left-response Ward. -/
theorem hbXiPeierlsCanonicalLeftActionCovariance_iff_regularUnitLeftWard
    (n : ℕ) :
    HBXiPeierlsCanonicalLeftActionCovariance n ↔
      ∀ q : XiZeroCopy,
        d4BMXiSecondHarmonicCanonicalRegularLeftResponseCurrent n 1 q = 0 :=
  (hbXiPeierlsCanonicalLeftActionCovariance_iff_rh n).trans
    (hbXiPeierlsCanonicalRegularUnitLeftWard_iff_rh n).symm

/-- The actual left-action covariance endpoint is canonical FE--Schwarz optical darkness. -/
theorem hbXiPeierlsCanonicalLeftActionCovariance_iff_opticalWard
    (n : ℕ) :
    HBXiPeierlsCanonicalLeftActionCovariance n ↔
      ∀ q : XiZeroCopy,
        hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower n q = 0 :=
  (hbXiPeierlsCanonicalLeftActionCovariance_iff_rh n).trans
    (forall_hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower_eq_zero_iff_rh n).symm

/-- Tilted fibres retain exact action incidence but lose two-branch covariance and carry strictly
positive canonical orbit optical power. -/
theorem hbXiPeierlsCanonicalLeftAction_tilted_incidence_noCovariance_positiveOptical
    (n : ℕ) (q : XiZeroCopy) (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    d4GaugeFixedTeukolskyPeierlsSourcePairing hbXiPeierlsPairing
          (hbXiPeierlsPropagator n)
          (hbXiPeierlsPlusLeftSource n 1 q)
          (hbXiPeierlsMinusLeftSource n 1 q) =
        d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n 1 q ∧
      hbXiPeierlsPlusLeftSource n 1 (xiZeroCopyReflectEquiv q) ≠
        hbXiPeierlsMinusLeftSource n 1 q ∧
      0 < hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower n q := by
  refine ⟨hbXiPeierls_BM_leftSource_incidence n 1 q, ?_,
    (d4BMXiSecondHarmonicCrossPairCancellation_nontrivial_of_tilt n q htilt).2.2⟩
  exact (hbXiPeierlsCanonicalLeftSource_reflect_eq_iff n (by norm_num) q).not.mpr htilt

end


end RHTower
