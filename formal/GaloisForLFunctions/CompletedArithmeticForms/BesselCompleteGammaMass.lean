import GaloisForLFunctions.CompletedArithmeticForms.BesselWeightedTail
import GaloisForLFunctions.RHTower.WeilWorkDeficitProductKernelMellin
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Complete Gamma masses of the weighted Bessel tails

The scaled Mellin identity identifies the zero-cutoff mass with a Gamma
modulus squared. Absolute convergence makes this mass the actual limit
of the positive-cutoff tails, retaining the frequency scale at every power.
-/

open Complex Filter Set MeasureTheory
open scoped ComplexConjugate Topology
noncomputable section
namespace GaloisForLFunctions.CompletedArithmeticForms
open GaloisForLFunctions.HTGeometry

private theorem mellin_chamber {p : ℝ} (hp : -1 < p) (τ : ℝ) :
    |((((2 * τ : ℝ) : ℂ) * I)).re| < ((p : ℂ) + 1).re := by
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, zero_mul, sub_zero, abs_zero,
    Complex.add_re, Complex.one_re]
  linarith only [hp]

private theorem radial_integrand_eq_re {u : ℝ} (hu : 0 < u) (p τ : ℝ) :
    u ^ p * besselRadialValue τ u =
      ((u : ℂ) ^ (((p : ℂ) + 1) - 1) *
        modifiedBesselKOrder (2 * u) (((2 * τ : ℝ) : ℂ) * I)).re := by
  rw [add_sub_cancel_right, ← Complex.ofReal_cpow hu.le]
  simp only [besselRadialValue, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]

/-- The complete Mellin ray is absolutely integrable for every power above minus one. -/
theorem integrableOn_besselPowerIntegrand_zero {p : ℝ} (hp : -1 < p) (τ : ℝ) :
    IntegrableOn (fun u : ℝ => u ^ p * besselRadialValue τ u) (Ioi 0) := by
  have hi := _root_.RHTower.WeilWorkDeficitMellin.scaled_integrable
    (mellin_chamber hp τ) (by norm_num : (0 : ℝ) < 2)
  refine (Complex.reCLM.integrable_comp hi).congr_fun (fun u hu => ?_) measurableSet_Ioi
  exact (radial_integrand_eq_re hu p τ).symm

/-- The full radial Mellin mass has exactly the natural Gamma frequency scale. -/
theorem besselPowerTail_zero_eq_gamma {p : ℝ} (hp : -1 < p) (τ : ℝ) :
    besselPowerTail p τ 0 =
      (1 / 4 : ℝ) * ‖Complex.Gamma (((p : ℂ) + 1) / 2 + (τ : ℂ) * I)‖ ^ 2 := by
  let z : ℂ := ((p : ℂ) + 1) / 2 + (τ : ℂ) * I
  have hi := _root_.RHTower.WeilWorkDeficitMellin.scaled_integrable
    (mellin_chamber hp τ) (by norm_num : (0 : ℝ) < 2)
  have hm := _root_.RHTower.WeilWorkDeficitMellin.scaled_mellin
    (mellin_chamber hp τ) (by norm_num : (0 : ℝ) < 2)
  have hplus : (((p : ℂ) + 1) + (((2 * τ : ℝ) : ℂ) * I)) / 2 = z := by
    dsimp only [z]
    push_cast
    ring
  have hminus : (((p : ℂ) + 1) - (((2 * τ : ℝ) : ℂ) * I)) / 2 = conj z := by
    dsimp only [z]
    simp only [map_add, map_div₀, map_one, map_ofNat, map_mul,
      Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have hpow : (2 : ℂ) ^ (-((p : ℂ) + 1)) *
      (2 : ℂ) ^ (((p : ℂ) + 1) - 2) = (1 / 4 : ℂ) := by
    rw [← Complex.cpow_add _ _ (by norm_num),
      show -((p : ℂ) + 1) + (((p : ℂ) + 1) - 2) = -(2 : ℂ) by ring,
      Complex.cpow_neg]
    norm_num
  rw [hplus, hminus, Complex.Gamma_conj] at hm
  have hmass : (∫ u in Ioi (0 : ℝ),
      (u : ℂ) ^ (((p : ℂ) + 1) - 1) *
        modifiedBesselKOrder (2 * u) (((2 * τ : ℝ) : ℂ) * I)) =
      (1 / 4 : ℂ) * (Complex.normSq (Complex.Gamma z) : ℂ) := by
    rw [hm]
    calc
      _ = ((2 : ℂ) ^ (-((p : ℂ) + 1)) * (2 : ℂ) ^ (((p : ℂ) + 1) - 2)) *
          (conj (Complex.Gamma z) * Complex.Gamma z) := by ring
      _ = _ := by rw [hpow, ← Complex.normSq_eq_conj_mul_self]
  calc
    besselPowerTail p τ 0 = ∫ u in Ioi (0 : ℝ),
        ((u : ℂ) ^ (((p : ℂ) + 1) - 1) *
          modifiedBesselKOrder (2 * u) (((2 * τ : ℝ) : ℂ) * I)).re := by
      apply setIntegral_congr_fun measurableSet_Ioi
      exact fun u hu => radial_integrand_eq_re hu p τ
    _ = _ := by
      rw [integral_re hi, hmass]
      norm_num [Complex.normSq_eq_norm_sq, z]

/-- No mass is lost when the lower endpoint tends to zero from the positive ray. -/
theorem tendsto_besselPowerTail_zero {p : ℝ} (hp : -1 < p) (τ : ℝ) :
    Tendsto (besselPowerTail p τ) (𝓝[>] (0 : ℝ))
      (𝓝 ((1 / 4 : ℝ) * ‖Complex.Gamma (((p : ℂ) + 1) / 2 + (τ : ℂ) * I)‖ ^ 2)) := by
  have hc := (integrableOn_besselPowerIntegrand_zero hp τ).continuousOn_Ici_primitive_Ioi
  have ht : ContinuousWithinAt (besselPowerTail p τ) (Ici 0) 0 := hc 0 (by simp)
  rw [← besselPowerTail_zero_eq_gamma hp τ]
  exact ht.mono Ioi_subset_Ici_self

#print axioms besselPowerTail_zero_eq_gamma
#print axioms tendsto_besselPowerTail_zero

end GaloisForLFunctions.CompletedArithmeticForms
