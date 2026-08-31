import GaloisForLFunctions.RHTower.RiemannVonMangoldt
import GaloisForLFunctions.RHTower.SimultaneousPhaseRecurrence

/-!
# Dyadic reciprocal Xi phase amplification

Riemann--von Mangoldt supplies order `T log T` multiplicity copies in every sufficiently high
dyadic ordinate band.  Their reciprocal mass is therefore order `log T`, not merely divergent.
Simultaneous recurrence then returns the Hilbert-rotated finite band to a fixed fraction of its
fully coherent value at arbitrarily late times.  Consequently these exact, multiplicity-aware
Xi packets are cofinally unbounded.

This is the spectral amplification premise for the hostile audit of the CCM--FU/Suzuki
first-moment producer.  A uniformly bounded square-root-normalized Chebyshev error would bound
every constant-`L¹` dyadic bandpass.  The remaining no-go weld is the arithmetic explicit formula
identifying that bandpass with this packet plus uniformly bounded polar and Archimedean terms.
-/

open Complex Filter Set Topology GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Every sufficiently high symmetric dyadic band contains at least a fixed `T log T` mass of
multiplicity copies. -/
theorem eventually_card_xiCopiesBand_mul_two_lower :
    ∀ᶠ T : ℝ in atTop,
      (1 / (4 * Real.pi)) * (T * Real.log T) ≤
        ((xiCopiesBand T (2 * T)).card : ℝ) := by
  obtain ⟨T₀, hT₀, hclose⟩ :=
    exists_xiSymmetricMass_close (1 / (8 * Real.pi)) (by positivity)
  filter_upwards [eventually_ge_atTop T₀] with T hT
  have hT4 : 4 ≤ T := hT₀.trans hT
  have hT0 : 0 < T := by linarith
  have hT1 : 1 < T := by linarith
  have hlog0 : 0 < Real.log T := Real.log_pos hT1
  have h2T : T₀ ≤ 2 * T := by linarith
  have hTclose := hclose T hT
  have h2Tclose := hclose (2 * T) h2T
  have hTupper :
      (xiSymmetricMass T : ℝ) ≤
        (1 / Real.pi + 1 / (8 * Real.pi)) * (T * Real.log T) := by
    rw [abs_le] at hTclose
    linarith
  have h2Tlower :
      (1 / Real.pi - 1 / (8 * Real.pi)) *
          ((2 * T) * Real.log (2 * T)) ≤
        (xiSymmetricMass (2 * T) : ℝ) := by
    rw [abs_le] at h2Tclose
    linarith
  have hlog_mono : Real.log T ≤ Real.log (2 * T) := by
    exact Real.log_le_log hT0 (by linarith)
  have hbandReal :
      (((xiCopiesBand T (2 * T)).card : ℤ) : ℝ) =
        (xiSymmetricMass (2 * T) : ℝ) - (xiSymmetricMass T : ℝ) := by
    rw [← Int.cast_sub]
    exact_mod_cast (xiSymmetricMass_diff_eq_card hT0.le (by linarith : T ≤ 2 * T)).symm
  have hbandReal' :
      ((xiCopiesBand T (2 * T)).card : ℝ) =
        (xiSymmetricMass (2 * T) : ℝ) - (xiSymmetricMass T : ℝ) := by
    exact_mod_cast hbandReal
  rw [hbandReal']
  have hpi : 0 < Real.pi := Real.pi_pos
  have hmain :
      (1 / (4 * Real.pi)) * (T * Real.log T) ≤
        (1 / Real.pi - 1 / (8 * Real.pi)) *
            ((2 * T) * Real.log (2 * T)) -
          (1 / Real.pi + 1 / (8 * Real.pi)) * (T * Real.log T) := by
    calc
      (1 / (4 * Real.pi)) * (T * Real.log T) ≤
          (1 / Real.pi - 1 / (8 * Real.pi)) *
              ((2 * T) * Real.log T) -
            (1 / Real.pi + 1 / (8 * Real.pi)) * (T * Real.log T) := by
        field_simp
        nlinarith [mul_pos hT0 hlog0]
      _ ≤ (1 / Real.pi - 1 / (8 * Real.pi)) *
              ((2 * T) * Real.log (2 * T)) -
            (1 / Real.pi + 1 / (8 * Real.pi)) * (T * Real.log T) := by
        have hcoef : 0 ≤ 1 / Real.pi - 1 / (8 * Real.pi) := by
          field_simp
          linarith
        gcongr
  linarith

/-- Reciprocal ordinate mass in a symmetric dyadic Xi band. -/
def xiDyadicBandReciprocalMass (T : ℝ) : ℝ :=
  ∑ q ∈ xiCopiesBand T (2 * T), 1 / |(q.1 : ℂ).im|

/-- The reciprocal mass of a sufficiently high dyadic band is at least a fixed multiple of
`log T`. -/
theorem eventually_xiDyadicBandReciprocalMass_log_lower :
    ∀ᶠ T : ℝ in atTop,
      (1 / (8 * Real.pi)) * Real.log T ≤
        xiDyadicBandReciprocalMass T := by
  filter_upwards [eventually_card_xiCopiesBand_mul_two_lower,
    eventually_ge_atTop (4 : ℝ)] with T hcard hT4
  have hT0 : 0 < T := by linarith
  have hterm : ∀ q ∈ xiCopiesBand T (2 * T),
      1 / (2 * T) ≤ 1 / |(q.1 : ℂ).im| := by
    intro q hq
    have hmem := mem_xiCopiesBand.mp hq
    have himpos : 0 < |(q.1 : ℂ).im| := hT0.trans hmem.1
    exact one_div_le_one_div_of_le himpos hmem.2
  have hsum :
      ((xiCopiesBand T (2 * T)).card : ℝ) * (1 / (2 * T)) ≤
        xiDyadicBandReciprocalMass T := by
    rw [xiDyadicBandReciprocalMass]
    calc
      ((xiCopiesBand T (2 * T)).card : ℝ) * (1 / (2 * T)) =
          ∑ q ∈ xiCopiesBand T (2 * T), 1 / (2 * T) := by simp
      _ ≤ _ := Finset.sum_le_sum hterm
  calc
    (1 / (8 * Real.pi)) * Real.log T =
        ((1 / (4 * Real.pi)) * (T * Real.log T)) * (1 / (2 * T)) := by
      field_simp [hT0.ne']
      ring
    _ ≤ ((xiCopiesBand T (2 * T)).card : ℝ) * (1 / (2 * T)) := by
      exact mul_le_mul_of_nonneg_right hcard (by positivity)
    _ ≤ xiDyadicBandReciprocalMass T := hsum

/-- Hilbert-rotated reciprocal Xi packet in one symmetric dyadic ordinate band. -/
def xiDyadicBandReciprocalPhase (T t : ℝ) : ℝ :=
  ∑ q ∈ xiCopiesBand T (2 * T),
    (1 / |(q.1 : ℂ).im|) *
      (GaloisForLFunctions.bohrChar |(q.1 : ℂ).im| t).re

/-- Every dyadic reciprocal packet returns cofinally to at least half of its coherent mass. -/
theorem exists_xiDyadicBandReciprocalPhase_ge_half_mass (T L : ℝ) :
    ∃ t : ℝ, L ≤ t ∧
      xiDyadicBandReciprocalMass T / 2 ≤
        xiDyadicBandReciprocalPhase T t := by
  let S : Finset XiZeroCopy := xiCopiesBand T (2 * T)
  let B : {q : XiZeroCopy // q ∈ S} → ℝ := fun q => |(q.1.1 : ℂ).im|
  obtain ⟨t, ht, hrec⟩ :=
    exists_simultaneous_phase_recurrence B
      (ε := (1 / 2 : ℝ)) (by norm_num) L
  refine ⟨t, ht, ?_⟩
  have hre : ∀ q : {q : XiZeroCopy // q ∈ S},
      (1 / 2 : ℝ) ≤
        (GaloisForLFunctions.bohrChar (B q) t).re := by
    intro q
    have habs := Complex.abs_re_le_norm
      (GaloisForLFunctions.bohrChar (B q) t - 1)
    have hnorm := hrec q
    have hreal :
        (GaloisForLFunctions.bohrChar (B q) t - 1).re =
          (GaloisForLFunctions.bohrChar (B q) t).re - 1 := by simp
    rw [hreal] at habs
    have hlow := neg_le_of_abs_le (habs.trans hnorm)
    linarith
  have hsum :
      (1 / 2 : ℝ) *
          (∑ q : {q : XiZeroCopy // q ∈ S}, 1 / |(q.1.1 : ℂ).im|) ≤
        ∑ q : {q : XiZeroCopy // q ∈ S},
          (1 / |(q.1.1 : ℂ).im|) *
            (GaloisForLFunctions.bohrChar (B q) t).re := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro q hq
    have himpos : 0 < |(q.1.1 : ℂ).im| := abs_pos.mpr (xiSupport_im_ne_zero q.1.1)
    simpa [mul_comm] using
      mul_le_mul_of_nonneg_left (hre q) (one_div_nonneg.mpr himpos.le)
  have hmass :
      (∑ q : {q : XiZeroCopy // q ∈ S}, 1 / |(q.1.1 : ℂ).im|) =
        xiDyadicBandReciprocalMass T := by
    simpa [xiDyadicBandReciprocalMass, S] using
      Finset.sum_attach S (fun q : XiZeroCopy => 1 / |(q.1 : ℂ).im|)
  have hphase :
      (∑ q : {q : XiZeroCopy // q ∈ S},
          (1 / |(q.1.1 : ℂ).im|) *
            (GaloisForLFunctions.bohrChar (B q) t).re) =
        xiDyadicBandReciprocalPhase T t := by
    simpa [xiDyadicBandReciprocalPhase, S, B] using
      Finset.sum_attach S (fun q : XiZeroCopy =>
        (1 / |(q.1 : ℂ).im|) *
          (GaloisForLFunctions.bohrChar |(q.1 : ℂ).im| t).re)
  rw [hmass, hphase] at hsum
  linarith

/-- The Hilbert-rotated dyadic reciprocal Xi packets have arbitrarily large cofinal excursions. -/
theorem xiDyadicBandReciprocalPhase_cofinally_unbounded :
    ∀ C L : ℝ, ∃ T t : ℝ,
      L ≤ t ∧ C < xiDyadicBandReciprocalPhase T t := by
  intro C L
  have hlog : ∀ᶠ T : ℝ in atTop,
      16 * Real.pi * C + 1 ≤ Real.log T :=
    Real.tendsto_log_atTop.eventually_ge_atTop (16 * Real.pi * C + 1)
  have hlarge : ∀ᶠ T : ℝ in atTop,
      C < xiDyadicBandReciprocalMass T / 2 := by
    filter_upwards [eventually_xiDyadicBandReciprocalMass_log_lower,
      hlog] with T hmass hlogT
    have hpi : 0 < Real.pi := Real.pi_pos
    have hC : C < (1 / (16 * Real.pi)) * Real.log T := by
      have hinvpos : 0 < 1 / (16 * Real.pi) := by positivity
      calc
        C < C + 1 / (16 * Real.pi) := by linarith
        _ = (1 / (16 * Real.pi)) * (16 * Real.pi * C + 1) := by
          field_simp
        _ ≤ (1 / (16 * Real.pi)) * Real.log T := by
          exact mul_le_mul_of_nonneg_left hlogT (by positivity)
    have hhalf :
        (1 / (16 * Real.pi)) * Real.log T ≤
          xiDyadicBandReciprocalMass T / 2 := by
      calc
        (1 / (16 * Real.pi)) * Real.log T =
            (1 / 2) * ((1 / (8 * Real.pi)) * Real.log T) := by ring
        _ ≤ (1 / 2) * xiDyadicBandReciprocalMass T := by
          exact mul_le_mul_of_nonneg_left hmass (by norm_num)
        _ = xiDyadicBandReciprocalMass T / 2 := by ring
    exact hC.trans_le hhalf
  obtain ⟨T, hT⟩ := hlarge.exists
  obtain ⟨t, htL, ht⟩ :=
    exists_xiDyadicBandReciprocalPhase_ge_half_mass T L
  exact ⟨T, t, htL, hT.trans_le ht⟩

end

end RHTower
