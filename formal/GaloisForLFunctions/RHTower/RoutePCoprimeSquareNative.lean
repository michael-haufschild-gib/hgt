import GaloisForLFunctions.RHTower.RoutePCoprimeSquareMellin
import GaloisForLFunctions.RHTower.MobiusDivisorFullHeadCompletion
import GaloisForLFunctions.RHTower.LogarithmicCoprimeEnergy

/-!
# The combined square budget belongs to the complete native head

These exact identities retain every divisor and every coprime pair. They
connect the admitted signed source to the native full head; they do not
assert separate admission of its endpoint square or its signed cross work.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex

namespace RHTower

def routePCoprimeUnitProfile (t : ℝ) : ℝ :=
  Real.sqrt (Real.exp (-t)) * divisorContinuousUnitHead (Real.exp t)

def routePCoprimeNativeProfile (t : ℝ) : ℝ :=
  Real.sqrt (Real.exp (-t)) * mobiusDivisorFullHead (Real.exp t)

private theorem exp_neg_shift (t : ℝ) {n : ℕ} (hn : 0 < n) :
    Real.exp (-(t - Real.log n)) = (n : ℝ) * Real.exp (-t) := by
  rw [show -(t - Real.log n) = Real.log n + -t by ring,
    Real.exp_add, Real.exp_log (by exact_mod_cast hn)]

theorem routePCoprimeNativeProfile_eq_mobiusInverse :
    routePCoprimeNativeProfile = logarithmicMobiusInverse routePCoprimeUnitProfile := by
  funext t
  unfold routePCoprimeNativeProfile mobiusDivisorFullHead
    logarithmicMobiusInverse logarithmicWeightedDilation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
  rw [routePCoprimeUnitProfile, exp_neg_shift t hnpos,
    Real.sqrt_mul (Nat.cast_nonneg n), Real.exp_sub,
    Real.exp_log (by exact_mod_cast hnpos)]
  ring

theorem routePCoprimeSquareWeight_exp_neg (t : ℝ) :
    routePCoprimeSquareWeight (Real.exp (-t)) = routePCoprimeUnitProfile t ^ 2 := by
  unfold routePCoprimeSquareWeight routePCoprimeUnitProfile
  rw [Real.exp_neg, inv_inv, mul_pow, Real.sq_sqrt (inv_nonneg.mpr (Real.exp_pos t).le)]

/-- Exact equality with the generic coprime energy, now for the literal full head. -/
theorem routePCoprimeSquareSource_eq_nativeCoprimeEnergy (t : ℝ) :
    routePCoprimeSquareSource (Real.exp (-t)) =
      (logarithmicCoprimeEnergy routePCoprimeNativeProfile t : ℂ) := by
  rw [routePCoprimeSquareSource_eq_sum (Real.exp_pos (-t)),
    routePCoprimeNativeProfile_eq_mobiusInverse,
    logarithmicCoprimeEnergy_mobiusInverse]
  simp only [Real.exp_neg, inv_inv, logarithmicMobiusInverse, logarithmicWeightedDilation,
    Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_intCast]
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
  congr 1
  rw [← routePCoprimeSquareWeight_exp_neg, exp_neg_shift t hnpos, Real.exp_neg]

/-- The positive endpoint and the entire signed coprime cross term are both present. -/
theorem routePCoprimeSquareSource_eq_nativeSquare_add_cross {t : ℝ} (ht : 0 ≤ t) :
    routePCoprimeSquareSource (Real.exp (-t)) =
      ((Real.exp (-t) * mobiusDivisorFullHead (Real.exp t) ^ 2 +
        logarithmicCoprimeCross routePCoprimeNativeProfile t : ℝ) : ℂ) := by
  rw [routePCoprimeSquareSource_eq_nativeCoprimeEnergy,
    logarithmicCoprimeEnergy_eq_endpoint_add_cross routePCoprimeNativeProfile ht]
  congr 1
  rw [routePCoprimeNativeProfile, mul_pow, Real.sq_sqrt (Real.exp_pos (-t)).le]

theorem routePCoprimeSquareSource_eq_nativeCoprimeEnergy_log {y : ℝ} (hy : 0 < y) :
    routePCoprimeSquareSource y =
      (logarithmicCoprimeEnergy routePCoprimeNativeProfile (-Real.log y) : ℂ) := by
  simpa only [neg_neg, Real.exp_log hy] using
    routePCoprimeSquareSource_eq_nativeCoprimeEnergy (-Real.log y)

private theorem native_mellin_integrand_eq (s : ℂ) :
    (fun y : ℝ => (y : ℂ) ^ (s - 1) • routePCoprimeSquareSource y) =ᵐ[volume.restrict (Ioi 0)]
      (fun y : ℝ => (y : ℂ) ^ (s - 1) •
        (logarithmicCoprimeEnergy routePCoprimeNativeProfile (-Real.log y) : ℂ)) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  rw [routePCoprimeSquareSource_eq_nativeCoprimeEnergy_log hy]

theorem mellin_nativeCoprimeEnergy_eq (s : ℂ) :
    mellin (fun y =>
      (logarithmicCoprimeEnergy routePCoprimeNativeProfile (-Real.log y) : ℂ)) s =
        mellin routePCoprimeSquareSource s :=
  (integral_congr_ae (native_mellin_integrand_eq s)).symm

/-- Absolute admission is for the complete native coprime energy. -/
theorem nativeCoprimeEnergy_hasMellin {s : ℂ} (hs : 1 < s.re) :
    HasMellin (fun y =>
      (logarithmicCoprimeEnergy routePCoprimeNativeProfile (-Real.log y) : ℂ)) s
      ((riemannZeta s)⁻¹ * mellin (fun y => (routePCoprimeSquareWeight y : ℂ)) s) := by
  refine ⟨(routePCoprimeSquareSource_hasMellin hs).1.congr (native_mellin_integrand_eq s), ?_⟩
  rw [mellin_nativeCoprimeEnergy_eq]
  exact (routePCoprimeSquareSource_hasMellin hs).2

/-- The native complete signed energy has the positive coefficient proved for the source. -/
theorem nativeCoprimeEnergy_simpleJet :
    Tendsto (fun ε : ℝ =>
      mellin (fun y => (logarithmicCoprimeEnergy routePCoprimeNativeProfile (-Real.log y) : ℂ))
        (1 + (ε : ℂ)) / (ε : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (routePCoprimeSquareMass : ℂ)) := by
  simpa only [mellin_nativeCoprimeEnergy_eq] using mellin_routePCoprimeSquareSource_simpleJet

theorem nativeCoprimeEnergy_tendsto_zero :
    Tendsto (fun ε : ℝ =>
      mellin (fun y => (logarithmicCoprimeEnergy routePCoprimeNativeProfile (-Real.log y) : ℂ))
        (1 + (ε : ℂ)))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
  simpa only [mellin_nativeCoprimeEnergy_eq] using mellin_routePCoprimeSquareSource_tendsto_zero

end RHTower
