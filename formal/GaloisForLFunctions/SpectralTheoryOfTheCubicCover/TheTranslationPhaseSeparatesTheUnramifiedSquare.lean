import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheTranslatedThetaProductHasOneCuspSubtraction
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheSquaredThetaSeriesSplitsIntoNineTwists

/-!
# The translation phase separates the unramified square

The source is invariant under translation by one. Among its nonzero Fourier
coefficients, the remaining translation by `ω` has phase one exactly at
frequencies divisible by three. Pairing opposite frequencies gives weight two
on that layer and minus one on its complement.
-/

noncomputable section
open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.SpectralTheoryOfTheCubicCover

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein
  MetaplecticMobiusDescent.CubicEisenstein

/-- The two integral translation phases detect divisibility by three. -/
theorem three_dvd_of_two_translation_phases (h : O)
    (h1 : tracePhase (cuspFrequency h) = 1)
    (hω : tracePhase (cuspFrequency h * ringComplex omega) = 1) : (3 : O) ∣ h := by
  have hb := sourceRayPhase_coordinate h h1
  have hf : cuspFrequency (h * omega) = cuspFrequency h * ringComplex omega := by
    simp only [cuspFrequency, map_mul]
    ring
  have hω' : tracePhase (cuspFrequency (h * omega)) = 1 := by rw [hf]; exact hω
  have hab := sourceRayPhase_coordinate (h * omega) hω'
  have he : h * omega = Coordinates.eval (-(Coordinates.coords h).2)
      ((Coordinates.coords h).1 - (Coordinates.coords h).2) := by
    have hw : omega = Coordinates.eval 0 1 := by simp [Coordinates.eval]
    conv_lhs => rw [← Coordinates.eval_coords h, hw, Coordinates.eval_mul]
    simp only [mul_zero, mul_one, zero_sub, add_zero]
  rw [he, Coordinates.coords_eval] at hab
  have ha : (3 : ℤ) ∣ (Coordinates.coords h).1 := by
    simpa only [sub_add_cancel] using dvd_add hab hb
  obtain ⟨a, ha⟩ := ha
  obtain ⟨b, hb⟩ := hb
  refine ⟨Coordinates.eval a b, ?_⟩
  conv_lhs => rw [← Coordinates.eval_coords h, ha, hb]
  simp only [Coordinates.eval, Int.cast_mul, Int.cast_ofNat]
  ring

private theorem translation_phase_cube (h : O) :
    tracePhase (cuspFrequency h * ringComplex omega) ^ 3 = 1 := by
  rw [← AddChar.map_nsmul_eq_pow]
  convert cuspFrequency_period h omega using 2
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  ring

/-- Opposite translated phases equal `2` on `3O` and `−1` on the other source frequencies. -/
theorem source_translation_phase_pair (h : O)
    (hT : rationalSourceResidualFourierCoefficient h ≠ 0) :
    tracePhase (2 * (cuspFrequency h * ringComplex omega)) +
      tracePhase (-(2 * (cuspFrequency h * ringComplex omega))) =
        if (3 : O) ∣ h then 2 else -1 := by
  let z := tracePhase (cuspFrequency h * ringComplex omega)
  have h3 := translation_phase_cube h
  have h2 : tracePhase (2 * (cuspFrequency h * ringComplex omega)) = z ^ 2 := by
    simpa only [nsmul_eq_mul, Nat.cast_ofNat] using
      AddChar.map_nsmul_eq_pow tracePhase 2 (cuspFrequency h * ringComplex omega)
  have hneg : tracePhase (-(2 * (cuspFrequency h * ringComplex omega))) = z := by
    have he := AddChar.map_add_eq_mul tracePhase
      (-(2 * (cuspFrequency h * ringComplex omega)))
      (cuspFrequency h * (3 * ringComplex omega))
    rw [cuspFrequency_period, mul_one] at he
    convert he.symm using 1 <;> congr 1 <;> ring
  rw [h2, hneg]
  by_cases hd : (3 : O) ∣ h
  · rw [if_pos hd]
    obtain ⟨b, rfl⟩ := hd
    have hz : z = 1 := by
      change tracePhase (cuspFrequency (3 * b) * ringComplex omega) = 1
      have he : cuspFrequency (3 * b) * ringComplex omega =
          cuspFrequency b * (3 * ringComplex omega) := by
        simp only [cuspFrequency, map_mul, map_ofNat]
        ring
      rw [he, cuspFrequency_period]
    rw [hz]
    norm_num
  · rw [if_neg hd]
    have hh : h ≠ 0 := fun hz => hd (hz ▸ dvd_zero 3)
    have hz : z ≠ 1 := fun hz => hd (three_dvd_of_two_translation_phases h
      (sourceFourier_phase_of_ne_zero h hh hT) hz)
    have hprod : (z - 1) * (z ^ 2 + z + 1) = 0 := by
      change z ^ 3 = 1 at h3
      linear_combination h3
    have hsum := (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hz)
    linear_combination hsum

/-- The signed difference of the full and translated squares selects the unramified frequencies. -/
theorem thetaSquare_translation_selector (h : O) :
    rationalSourceResidualFourierCoefficient h ^ 2 *
      (1 - (tracePhase (2 * (cuspFrequency h * ringComplex omega)) +
        tracePhase (-(2 * (cuspFrequency h * ringComplex omega)))) / 2) =
      (3 / 2 : ℂ) * (if (3 : O) ∣ h then 0 else rationalSourceResidualFourierCoefficient h ^ 2) := by
  by_cases hT : rationalSourceResidualFourierCoefficient h = 0
  · simp only [hT, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, ite_self, mul_zero]
  · rw [source_translation_phase_pair h hT]
    split_ifs <;> ring

end GaloisForLFunctions.SpectralTheoryOfTheCubicCover
