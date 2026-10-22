import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCuspHermitianMean
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEisensteinActualSignedFourierUniqueness
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! Exact positive energy of the original full scalar and its Fourier coefficients. -/
open Complex MeasureTheory Set Filter Topology
namespace RHTower.D4BMCuspProjection
open D4BMAngularSeries D4BMGlobalAngularResponse
noncomputable section

/-- The complete mass of the original unsigned Fourier--Bessel coefficients. -/
def amplitudeMass (u : ℂ) (y : ℝ) : ℝ := ∑' N, ‖amplitude u y N‖^(2 : ℕ)

theorem amplitudeMass_nonneg (u : ℂ) (y : ℝ) : 0 ≤ amplitudeMass u y :=
  tsum_nonneg (fun _ => sq_nonneg _)

theorem amplitudeMass_summable (u : ℂ) {y : ℝ} (hy : 0 < y) :
    Summable (fun N => ‖amplitude u y N‖^(2 : ℕ)) := by
  simpa only [norm_pow] using amplitude_sq_norm_summable u hy

/-- The full tail's actual squared norm mean keeps all positive and negative frequencies. -/
theorem mean_tail_norm_sq (u : ℂ) {y : ℝ} (hy : 0 < y) :
    (∫ x in Ioc (-1/2:ℝ) (1/2), ‖tail u ![x,y]‖^(2 : ℕ)) = 8*amplitudeMass u y := by
  simp_rw [tail_eq_series u hy,norm_mul,mul_pow]
  simp only [Complex.norm_ofNat]
  rw [integral_const_mul,mean_series_norm_sq _ (amplitude_norm_summable u hy)]
  unfold amplitudeMass
  ring

private theorem norm_mean_add_constant (c : ℂ) (f : ℝ → ℂ) (hf : Continuous f)
    (hzero : mean f = 0) :
    (∫ x in Ioc (-1/2:ℝ) (1/2), ‖c+f x‖^(2 : ℕ)) =
      ‖c‖^(2 : ℕ)+∫ x in Ioc (-1/2:ℝ) (1/2), ‖f x‖^(2 : ℕ) := by
  have hi : IntegrableOn (fun x => c*(starRingEnd ℂ) (f x)) (Ioc (-1/2:ℝ) (1/2)) :=
    (continuous_const.mul hf.star).integrableOn_Ioc
  have hre : (∫ x in Ioc (-1/2:ℝ) (1/2), (c*(starRingEnd ℂ) (f x)).re) = 0 := by
    have he : (∫ x in Ioc (-1/2:ℝ) (1/2), (c*(starRingEnd ℂ) (f x)).re) =
        (∫ x in Ioc (-1/2:ℝ) (1/2), c*(starRingEnd ℂ) (f x)).re := integral_re hi
    rw [he,integral_const_mul,integral_conj]
    change (c*(starRingEnd ℂ) (mean f)).re = 0
    rw [hzero,map_zero,mul_zero,Complex.zero_re]
  simp_rw [← Complex.normSq_eq_norm_sq,Complex.normSq_add]
  have hn : IntegrableOn (fun x => Complex.normSq (f x)) (Ioc (-1/2:ℝ) (1/2)) :=
    (Complex.continuous_normSq.comp hf).integrableOn_Ioc
  have hr : IntegrableOn (fun x => 2*(c*(starRingEnd ℂ) (f x)).re) (Ioc (-1/2:ℝ) (1/2)) :=
    (continuous_const.mul (Complex.continuous_re.comp (continuous_const.mul hf.star))).integrableOn_Ioc
  have hsum : (∫ x in Ioc (-1/2:ℝ) (1/2), Complex.normSq c+Complex.normSq (f x)+
      2*(c*(starRingEnd ℂ) (f x)).re) =
      (∫ x in Ioc (-1/2:ℝ) (1/2), Complex.normSq c+Complex.normSq (f x))+
        ∫ x in Ioc (-1/2:ℝ) (1/2), 2*(c*(starRingEnd ℂ) (f x)).re :=
    integral_add ((integrable_const (Complex.normSq c)).add hn) hr
  have hsum0 : (∫ x in Ioc (-1/2:ℝ) (1/2), Complex.normSq c+Complex.normSq (f x)) =
      (∫ _x in Ioc (-1/2:ℝ) (1/2), Complex.normSq c)+
        ∫ x in Ioc (-1/2:ℝ) (1/2), Complex.normSq (f x) :=
    integral_add (integrable_const (Complex.normSq c)) hn
  rw [hsum,hsum0,integral_const_mul,hre]
  norm_num

/-- The original scalar energy splits into its constant coefficient and the complete Fourier mass. -/
theorem mean_scalar_norm_sq (u : ℂ) {y : ℝ} (hy : 0 < y) :
    (∫ x in Ioc (-1/2:ℝ) (1/2), ‖scalar u ![x,y]‖^(2 : ℕ)) =
      ‖principal u ![0,y]‖^(2 : ℕ)+8*amplitudeMass u y := by
  have ht : Continuous (fun x => tail u ![x,y]) := by
    have he : (fun x => tail u ![x,y]) = fun x => 2*series (amplitude u y) x :=
      funext (tail_eq_series u hy)
    rw [he]
    exact continuous_const.mul (series_continuous _ (amplitude_norm_summable u hy))
  have he (x : ℝ) : scalar u ![x,y] = principal u ![0,y]+tail u ![x,y] := rfl
  simp_rw [he]
  rw [norm_mean_add_constant _ _ ht (mean_tail u hy),mean_tail_norm_sq u hy]

/-- The exact energy identity also holds on the original unfolding interval. -/
theorem unit_mean_scalar_norm_sq (u : ℂ) {y : ℝ} (hy : 0 < y) :
    (∫ x in Ico (0:ℝ) 1, ‖scalar u ![x,y]‖^(2 : ℕ)) =
      ‖principal u ![0,y]‖^(2 : ℕ)+8*amplitudeMass u y := by
  have hp : Function.Periodic (fun x : ℝ => ‖scalar u ![x,y]‖^(2 : ℕ)) 1 := by
    intro x
    have he : scalar u ![x+1,y] = scalar u ![x,y] := by
      simpa [scalar] using d4BM_completedEisensteinCuspLeg_scalar_periodic u y x
    dsimp only
    rw [he]
  have h := hp.intervalIntegral_add_eq 0 (-1/2)
  have he : (∫ x in (0:ℝ)..1, ‖scalar u ![x,y]‖^(2 : ℕ)) =
      ∫ x in (-1/2:ℝ)..(1/2:ℝ), ‖scalar u ![x,y]‖^(2 : ℕ) := by
    convert h using 1 <;> norm_num
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
    intervalIntegral.integral_of_le (by norm_num : (-1/2:ℝ)≤1/2)] at he
  rw [integral_Ico_eq_integral_Ioc,he,mean_scalar_norm_sq u hy]

end
end RHTower.D4BMCuspProjection
