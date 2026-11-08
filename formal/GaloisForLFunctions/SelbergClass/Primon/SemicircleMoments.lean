import GaloisForLFunctions.SelbergClass.Primon.KestenJacobiMoments
import GaloisForLFunctions.SelbergClass.Primon.KestenSemicircleLimit
import GaloisForLFunctions.HTGeometry.MixedEvenTrigMoments
import Mathlib.Combinatorics.Enumerative.Catalan.Basic

/-!
# Catalan moments of the limiting prime phase law

The mixed Wallis integral identifies the moments of `2 sin²(πt)` in the
coordinate `x = 2 cos(πt)`: odd moments vanish and even moments are Catalan
numbers. The prime phase moments converge to these actual integrals.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- Powers of the normalized Hecke coordinate, viewed as continuous phase observables. -/
def phasePowerObservable (n : ℕ) : C(ℝ, ℝ) :=
  ⟨fun t => (2 * Real.cos (Real.pi * t)) ^ n, by fun_prop⟩

/-- Actual integral moments of the limiting phase density. -/
def semicircleMoment (n : ℕ) : ℝ := semicircleObservableAverage (phasePowerObservable n)

@[simp] theorem kestenObservableAverage_phasePower (p : Nat.Primes) (n : ℕ) :
    kestenObservableAverage p (phasePowerObservable n) = kestenMoment p n := rfl

/-- Every prime Hecke moment tends to the corresponding semicircle phase integral. -/
theorem tendsto_kestenMoment (n : ℕ) :
    Tendsto (fun p => kestenMoment p n) cofinite (𝓝 (semicircleMoment n)) :=
  tendsto_kestenObservableAverage (phasePowerObservable n)

private theorem evenTrigHalf_eq_two_quarter (n : ℕ) :
    (∫ x in (0 : ℝ)..Real.pi, Real.sin x ^ 2 * Real.cos x ^ (2 * n)) =
      2 * mixedEvenTrigQuarterIntegral 1 n := by
  let f : ℝ → ℝ := fun x => Real.sin x ^ 2 * Real.cos x ^ (2 * n)
  have hc : Continuous f := by dsimp [f]; fun_prop
  have hp : Function.Periodic f Real.pi := by
    intro x
    simp only [f, Real.sin_add_pi, Real.cos_add_pi, pow_mul, neg_sq]
  have hr (x : ℝ) : f (Real.pi - x) = f x := by
    simp only [f, Real.sin_pi_sub, Real.cos_pi_sub, pow_mul, neg_sq]
  have hq := integral_zero_two_pi_eq_four_mul_quarter hc hp hr
  have h2 := hp.intervalIntegral_add_zsmul_eq (2 : ℤ) (0 : ℝ)
    (fun a b => hc.intervalIntegrable a b)
  have hh : (∫ x in (0 : ℝ)..2 * Real.pi, f x) =
      2 * ∫ x in (0 : ℝ)..Real.pi, f x := by
    convert h2 using 1 <;> norm_num
  change (∫ x in (0 : ℝ)..Real.pi, f x) =
    2 * ∫ x in (0 : ℝ)..Real.pi / 2, f x
  linarith only [hh, hq]

/-- Exact even moments: the limiting prime phase law has Catalan moments. -/
theorem semicircleMoment_even (n : ℕ) : semicircleMoment (2 * n) = (catalan n : ℝ) := by
  let f : ℝ → ℝ := fun x => Real.sin x ^ 2 * Real.cos x ^ (2 * n)
  change (∫ t in Ioo (0 : ℝ) 1,
    2 * Real.sin (Real.pi * t) ^ 2 * (2 * Real.cos (Real.pi * t)) ^ (2 * n)) = _
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
  have he : (fun t : ℝ => 2 * Real.sin (Real.pi * t) ^ 2 *
      (2 * Real.cos (Real.pi * t)) ^ (2 * n)) =
      fun t => (2 * (2 : ℝ) ^ (2 * n)) * f (Real.pi * t) := by
    funext t
    dsimp [f]
    rw [mul_pow]
    ring
  rw [he, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left f Real.pi_ne_zero]
  simp only [mul_zero, mul_one, smul_eq_mul]
  change (2 * (2 : ℝ) ^ (2 * n)) *
      (Real.pi⁻¹ * ∫ x in (0 : ℝ)..Real.pi, Real.sin x ^ 2 * Real.cos x ^ (2 * n)) = _
  rw [evenTrigHalf_eq_two_quarter, mixedEvenTrigQuarterIntegral_closed]
  have h1 : normalizedCentralBinom 1 = 1 / 2 := by
    norm_num [normalizedCentralBinom, Nat.centralBinom]
  rw [h1, normalizedCentralBinom, Nat.choose_one_right, Nat.add_comm 1 n]
  have hc : ((n : ℝ) + 1) * (catalan n : ℝ) = (Nat.centralBinom n : ℝ) := by
    exact_mod_cast succ_mul_catalan_eq_centralBinom n
  have h4 : (4 : ℝ) ^ n ≠ 0 := by positivity
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have hpow : (2 : ℝ) ^ (2 * n) = 4 ^ n := by rw [pow_mul]; norm_num
  rw [hpow, ← hc]
  push_cast
  field_simp [Real.pi_ne_zero, h4, hn]

/-- Odd coordinate moments vanish by reflection of the phase interval. -/
theorem semicircleMoment_odd (n : ℕ) : semicircleMoment (2 * n + 1) = 0 := by
  let f : ℝ → ℝ := fun t =>
    semicirclePhaseDensity t * (2 * Real.cos (Real.pi * t)) ^ (2 * n + 1)
  have hf (t : ℝ) : f (1 - t) = -f t := by
    dsimp [f, semicirclePhaseDensity]
    rw [show Real.pi * (1 - t) = Real.pi - Real.pi * t by ring,
      Real.sin_pi_sub, Real.cos_pi_sub]
    simp only [mul_neg, pow_add, pow_mul, pow_one, neg_sq]
  have hr := intervalIntegral.integral_comp_sub_left (a := 0) (b := 1) f 1
  simp only [sub_self, sub_zero] at hr
  simp_rw [hf] at hr
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo] at hr
  change (∫ t in Ioo (0 : ℝ) 1, f t) = 0
  linarith only [hr]

@[simp] theorem semicircleMoment_zero : semicircleMoment 0 = 1 := by
  simpa using semicircleMoment_even 0

/-- The limiting phase density is normalized by an exact integral identity. -/
theorem integral_semicirclePhaseDensity :
    (∫ t in Ioo (0 : ℝ) 1, semicirclePhaseDensity t) = 1 := by
  simpa [semicircleMoment, semicircleObservableAverage, phasePowerObservable] using
    semicircleMoment_zero

end
end GaloisForLFunctions.SelbergClass.Primon
