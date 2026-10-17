import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarScaledCollar

/-!
# Exact optimization of signed collar compensation

The actual source covariance supplies the signed optimal coefficient. The zero
denominator case is discharged by the source Gram inequality. Capping the result
by the mass estimate gives global transport no worse than the previous budget.
-/

open MeasureTheory Set
open scoped CompactlySupported

namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
noncomputable section
set_option autoImplicit false

def collarQuadraticMass (f : C_c(ℝ, ℝ)) (a b c : ℝ) (N : ℕ) : ℝ :=
  (1+Real.exp c)*collarPacketBound f a b N +
    (1+1/Real.exp c)*mass N^2*collarEnergy f a b

def collarQuadraticCovariance (f : C_c(ℝ, ℝ)) (a b c : ℝ) (N : ℕ) : ℝ :=
  (1+1/Real.exp c)*mass N^2*correlationAverage f a b 0

/-- The coefficient may have either sign; zero division selects zero. -/
def collarOptimalCoefficient (f : C_c(ℝ, ℝ)) (a b c : ℝ) (N : ℕ) : ℝ :=
  collarQuadraticCovariance f a b c N / collarQuadraticMass f a b c N

def collarOptimizedValue (f : C_c(ℝ, ℝ)) (a b c : ℝ) (N : ℕ) : ℝ :=
  (1+1/Real.exp c)*mass N^2*autocorr f 0 -
    collarQuadraticCovariance f a b c N ^ 2 / collarQuadraticMass f a b c N

private theorem bound_le_quadraticMass (f : C_c(ℝ, ℝ)) (a b c : ℝ) (N : ℕ) :
    collarPacketBound f a b N ≤ collarQuadraticMass f a b c N := by
  have hs := mul_nonneg (Real.exp_pos c).le (collarPacketBound_nonneg f a b N)
  have ht : 0 ≤ (1+1/Real.exp c)*mass N^2*collarEnergy f a b :=
    mul_nonneg (by positivity) (collarEnergy_nonneg f a b)
  unfold collarQuadraticMass
  linarith only [hs, ht]

theorem collarQuadraticMass_nonneg (f : C_c(ℝ, ℝ)) (a b c : ℝ) (N : ℕ) :
    0 ≤ collarQuadraticMass f a b c N :=
  (collarPacketBound_nonneg f a b N).trans (bound_le_quadraticMass f a b c N)

private theorem covariance_zero_of_quadraticMass_zero (f : C_c(ℝ, ℝ))
    (a b c : ℝ) (N : ℕ) (hd : collarQuadraticMass f a b c N = 0) :
    collarQuadraticCovariance f a b c N = 0 := by
  have hb := thirty_mul_collarEnergy_le_bound f a b N
  have hu := bound_le_quadraticMass f a b c N
  have hn := collarEnergy_nonneg f a b
  have hz : collarEnergy f a b = 0 := by linarith only [hb, hu, hn, hd]
  have hc := collar_covariance_sq_le f a b
  rw [hz, zero_mul] at hc
  have hcz : correlationAverage f a b 0 = 0 :=
    sq_eq_zero_iff.mp (le_antisymm hc (sq_nonneg _))
  simp only [collarQuadraticCovariance, hcz, mul_zero]

private theorem trial_expansion (f : C_c(ℝ, ℝ)) (a b c : ℝ) (N : ℕ) (t : ℝ) :
    collarTrialBound f a b c N t = (1+1/Real.exp c)*mass N^2*autocorr f 0 -
      2*collarQuadraticCovariance f a b c N*t + collarQuadraticMass f a b c N*t^2 := by
  unfold collarTrialBound collarQuadraticCovariance collarQuadraticMass
  ring

/-- Exact cost of departing from the signed optimizer, including degeneracy. -/
theorem collarTrialBound_excess (f : C_c(ℝ, ℝ)) (a b c : ℝ) (N : ℕ) (t : ℝ) :
    collarTrialBound f a b c N t - collarOptimizedValue f a b c N =
      collarQuadraticMass f a b c N * (t-collarOptimalCoefficient f a b c N)^2 := by
  rw [trial_expansion]
  unfold collarOptimizedValue collarOptimalCoefficient
  by_cases hd : collarQuadraticMass f a b c N = 0
  · have he := covariance_zero_of_quadraticMass_zero f a b c N hd
    simp [hd, he]
  · field_simp
    ring

theorem collarTrialBound_at_optimum (f : C_c(ℝ, ℝ)) (a b c : ℝ) (N : ℕ) :
    collarTrialBound f a b c N (collarOptimalCoefficient f a b c N) =
      collarOptimizedValue f a b c N := by
  have h := collarTrialBound_excess f a b c N (collarOptimalCoefficient f a b c N)
  nlinarith only [h]

/-- Complete minimizer classification for the admitted quadratic family. -/
theorem collarTrialBound_eq_optimum_iff (f : C_c(ℝ, ℝ)) (a b c : ℝ) (N : ℕ) (t : ℝ) :
    collarTrialBound f a b c N t = collarOptimizedValue f a b c N ↔
      collarQuadraticMass f a b c N = 0 ∨ t = collarOptimalCoefficient f a b c N := by
  have hg := collarTrialBound_excess f a b c N t
  constructor
  · intro h
    have hz : collarQuadraticMass f a b c N * (t-collarOptimalCoefficient f a b c N)^2 = 0 := by
      linarith only [hg, h]
    rcases mul_eq_zero.mp hz with hd | ht
    · exact Or.inl hd
    · exact Or.inr (sub_eq_zero.mp (sq_eq_zero_iff.mp ht))
  · rintro (hd | ht)
    · rw [hd, zero_mul] at hg
      exact sub_eq_zero.mp hg
    · rw [ht]
      exact collarTrialBound_at_optimum f a b c N

theorem collarOptimizedValue_le_trial (f : C_c(ℝ, ℝ)) (a b c : ℝ) (N : ℕ) (t : ℝ) :
    collarOptimizedValue f a b c N ≤ collarTrialBound f a b c N t := by
  have h := collarTrialBound_excess f a b c N t
  have hn := mul_nonneg (collarQuadraticMass_nonneg f a b c N)
    (sq_nonneg (t-collarOptimalCoefficient f a b c N))
  linarith only [h, hn]

theorem packetEnergy_le_collarOptimizedValue (f : C_c(ℝ, ℝ)) (a b c : ℝ) (N : ℕ) :
    packetEnergy f N ≤ collarOptimizedValue f a b c N := by
  have h := packetEnergy_le_collarTrialBound f a b c (collarOptimalCoefficient f a b c N) N
  rwa [collarTrialBound_at_optimum] at h

/-- Retain the mass estimate as well as the optimized signed compensation. -/
def optimizedPacketBound (f : C_c(ℝ, ℝ)) (a b c : ℝ) (N : ℕ) : ℝ :=
  min (mass N^2*autocorr f 0) (collarOptimizedValue f a b c N)

theorem packetEnergy_le_optimizedPacketBound (f : C_c(ℝ, ℝ)) (a b c : ℝ) (N : ℕ) :
    packetEnergy f N ≤ optimizedPacketBound f a b c N :=
  le_min (packetEnergy_le_mass_sq f N) (packetEnergy_le_collarOptimizedValue f a b c N)

theorem optimizedPacketBound_nonneg (f : C_c(ℝ, ℝ)) (a b c : ℝ) (N : ℕ) :
    0 ≤ optimizedPacketBound f a b c N :=
  (packetEnergy_nonneg f N).trans (packetEnergy_le_optimizedPacketBound f a b c N)

theorem optimizedPacketBound_le_mass (f : C_c(ℝ, ℝ)) (a b c : ℝ) (N : ℕ) :
    optimizedPacketBound f a b c N ≤ mass N^2*autocorr f 0 := min_le_left _ _

/-- Exact eligibility threshold for strict improvement over the mass estimate. -/
theorem optimizedPacketBound_lt_mass_iff (f : C_c(ℝ, ℝ)) (a b c : ℝ) (N : ℕ) :
    optimizedPacketBound f a b c N < mass N^2*autocorr f 0 ↔
      mass N^2*autocorr f 0/Real.exp c <
        collarQuadraticCovariance f a b c N^2/collarQuadraticMass f a b c N := by
  have he : (1+1/Real.exp c)*mass N^2*autocorr f 0 =
      mass N^2*autocorr f 0 + mass N^2*autocorr f 0/Real.exp c := by ring
  unfold optimizedPacketBound collarOptimizedValue
  rw [min_lt_iff, he]
  constructor
  · rintro (h | h)
    · exact (lt_irrefl _ h).elim
    · linarith only [h]
  · intro h
    right
    linarith only [h]

theorem optimizedPacketBound_le_trial (f : C_c(ℝ, ℝ)) (a b c : ℝ) (N : ℕ) (t : ℝ) :
    optimizedPacketBound f a b c N ≤ collarTrialBound f a b c N t :=
  (min_le_right _ _).trans (collarOptimizedValue_le_trial f a b c N t)

/-- Balanced splitting recovers the old certificate at coefficient one. -/
theorem collarTrialBound_one_zero (f : C_c(ℝ, ℝ)) (a b : ℝ) (N : ℕ) :
    collarTrialBound f a b 0 N 1 = correlationGaugeBound f a b N := by
  unfold collarTrialBound collarPacketBound correlationGaugeBound collarChordEnergy
  norm_num only [Real.exp_zero, one_div_one, one_pow]
  ring

theorem optimizedPacketBound_le_correlationGaugeBound (f : C_c(ℝ, ℝ)) (a b : ℝ) (N : ℕ) :
    optimizedPacketBound f a b 0 N ≤ correlationGaugeBound f a b N := by
  have h := optimizedPacketBound_le_trial f a b 0 N 1
  rwa [collarTrialBound_one_zero] at h

/-- Exact gain over coefficient one before the additional mass cap. -/
theorem correlationGaugeBound_sub_optimum (f : C_c(ℝ, ℝ)) (a b : ℝ) (N : ℕ) :
    correlationGaugeBound f a b N - collarOptimizedValue f a b 0 N =
      collarQuadraticMass f a b 0 N * (1-collarOptimalCoefficient f a b 0 N)^2 := by
  rw [← collarTrialBound_one_zero]
  exact collarTrialBound_excess f a b 0 N 1

/-- Global coherent transport with signed optimal source compensation. -/
theorem fullPairing_sub_work_sq_le_optimized (f : C_c(ℝ, ℝ))
    (a b c u v : ℝ) (K : ℕ) :
    (fullPairing (autocorr f)-fullChebyshevWork f u v)^2 ≤
      optimizedPacketBound f a b c (sourceCutoff f+K)*collarChordEnergy f u v :=
  (fullPairing_sub_work_sq_le_coherent f u v K).trans
    (mul_le_mul_of_nonneg_right (packetEnergy_le_optimizedPacketBound f a b c _)
      (collarChordEnergy_nonneg f u v))

/-- Global Lévy transport retains independent smoothing, splitting, and transport parameters. -/
theorem abs_fullPairing_sub_work_le_optimized_levy (f : C_c(ℝ, ℝ))
    (a b c u v r : ℝ) (K : ℕ) :
    |fullPairing (autocorr f)-fullChebyshevWork f u v| ≤
      Real.exp r * (∫ y in Real.exp u..Real.exp u+Real.exp v,
        (autocorr f 0-autocorr f y)*archLevySinhWeight y) +
      optimizedPacketBound f a b c (sourceCutoff f+K)/(2*Real.exp r*Real.exp v^2) *
        ∫ y in Real.exp u..Real.exp u+Real.exp v, Real.exp (-y/2)*Real.sinh y := by
  have hi : 0 ≤ ∫ y in Real.exp u..Real.exp u+Real.exp v, Real.exp (-y/2)*Real.sinh y := by
    apply intervalIntegral.integral_nonneg (le_add_of_nonneg_right (Real.exp_pos v).le)
    intro y hy
    rw [← inv_archLevySinhWeight_eq]
    exact inv_nonneg.mpr (archLevySinhWeight_pos ((Real.exp_pos u).trans_le hy.1)).le
  apply (abs_fullPairing_sub_fullChebyshevWork_le_packet_levy f u v r K).trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_right _ hi
  exact div_le_div_of_nonneg_right (packetEnergy_le_optimizedPacketBound f a b c _) (by positivity)

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
