import GaloisForLFunctions.RHTower.FiniteOfflineCauchyEnergy
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open MeasureTheory Set
open scoped BigOperators

noncomputable section

namespace RHTower

def finiteOfflineMode {n : ℕ} (a gamma : Fin n → ℝ) (m : Fin n → ℕ)
    (j : Fin n) (t : ℝ) : ℂ :=
  (2 * (m j : ℂ)) * Complex.exp
    (-((a j : ℝ) : ℂ) * t - Complex.I * (gamma j : ℂ) * t)

def finiteOfflineProfile {n : ℕ} (a gamma : Fin n → ℝ) (m : Fin n → ℕ)
    (t : ℝ) : ℂ :=
  ∑ j, finiteOfflineMode a gamma m j t

def finiteOfflinePairIntegrand {n : ℕ} (a gamma : Fin n → ℝ) (m : Fin n → ℕ)
    (j k : Fin n) (t : ℝ) : ℂ :=
  (4 * (m j : ℂ) * (m k : ℂ)) *
    Complex.exp ((-((a j + a k : ℝ) : ℂ) +
      Complex.I * ((gamma j - gamma k : ℝ) : ℂ)) * t)

theorem finiteOfflinePairIntegrand_eq {n : ℕ}
    (a gamma : Fin n → ℝ) (m : Fin n → ℕ) (j k : Fin n) (t : ℝ) :
    (starRingEnd ℂ) (finiteOfflineMode a gamma m j t) *
        finiteOfflineMode a gamma m k t =
      finiteOfflinePairIntegrand a gamma m j k t := by
  unfold finiteOfflineMode finiteOfflinePairIntegrand
  rw [map_mul, map_mul, map_ofNat, map_natCast, ← Complex.exp_conj]
  have hconj : (starRingEnd ℂ)
      (-((a j : ℝ) : ℂ) * t - Complex.I * (gamma j : ℂ) * t) =
      -((a j : ℝ) : ℂ) * t + Complex.I * (gamma j : ℂ) * t := by
    simp
  rw [hconj]
  calc
    (2 * (m j : ℂ)) *
          Complex.exp (-((a j : ℝ) : ℂ) * t + Complex.I * (gamma j : ℂ) * t) *
        ((2 * (m k : ℂ)) *
          Complex.exp (-((a k : ℝ) : ℂ) * t - Complex.I * (gamma k : ℂ) * t)) =
      (4 * (m j : ℂ) * (m k : ℂ)) *
        (Complex.exp (-((a j : ℝ) : ℂ) * t + Complex.I * (gamma j : ℂ) * t) *
          Complex.exp (-((a k : ℝ) : ℂ) * t - Complex.I * (gamma k : ℂ) * t)) := by ring
    _ = (4 * (m j : ℂ) * (m k : ℂ)) *
        Complex.exp ((-((a j + a k : ℝ) : ℂ) +
          Complex.I * ((gamma j - gamma k : ℝ) : ℂ)) * t) := by
      rw [← Complex.exp_add]
      congr 2
      push_cast
      ring

theorem finiteOfflinePairIntegrand_integrableOn {n : ℕ}
    {a gamma : Fin n → ℝ} (m : Fin n → ℕ) (ha : ∀ j, 0 < a j) (j k : Fin n) :
    IntegrableOn (finiteOfflinePairIntegrand a gamma m j k) (Ioi 0) := by
  unfold finiteOfflinePairIntegrand
  apply Integrable.const_mul
  apply integrableOn_exp_mul_complex_Ioi
  simp
  nlinarith [ha j, ha k]

theorem integral_finiteOfflinePairIntegrand {n : ℕ}
    {a gamma : Fin n → ℝ} (m : Fin n → ℕ) (ha : ∀ j, 0 < a j) (j k : Fin n) :
    ∫ t in Ioi (0 : ℝ), finiteOfflinePairIntegrand a gamma m j k t =
      (4 * (m j : ℂ) * (m k : ℂ)) *
        ((((a j + a k : ℝ) : ℂ) -
          Complex.I * ((gamma j - gamma k : ℝ) : ℂ))⁻¹) := by
  unfold finiteOfflinePairIntegrand
  rw [integral_const_mul, integral_exp_mul_complex_Ioi (c := 0) (by
    simp
    nlinarith [ha j, ha k])]
  have harg : (-((a j + a k : ℝ) : ℂ) +
      Complex.I * ((gamma j - gamma k : ℝ) : ℂ)) =
      -((((a j + a k : ℝ) : ℂ) -
        Complex.I * ((gamma j - gamma k : ℝ) : ℂ))) := by ring
  have hquot : -Complex.exp
      ((-((a j + a k : ℝ) : ℂ) +
        Complex.I * ((gamma j - gamma k : ℝ) : ℂ)) * (0 : ℝ)) /
      (-((a j + a k : ℝ) : ℂ) +
        Complex.I * ((gamma j - gamma k : ℝ) : ℂ)) =
      ((((a j + a k : ℝ) : ℂ) -
        Complex.I * ((gamma j - gamma k : ℝ) : ℂ))⁻¹) := by
    simp only [mul_zero, Complex.ofReal_zero, Complex.exp_zero]
    rw [harg, div_eq_mul_inv, inv_neg]
    ring
  rw [hquot]

theorem re_integral_finiteOfflinePairIntegrand {n : ℕ}
    {a gamma : Fin n → ℝ} (m : Fin n → ℕ) (ha : ∀ j, 0 < a j) (j k : Fin n) :
    (∫ t in Ioi (0 : ℝ), finiteOfflinePairIntegrand a gamma m j k t).re =
      4 * (m j : ℝ) * (m k : ℝ) *
        transverseCauchyKernel (a j) (a k) (gamma j - gamma k) := by
  rw [integral_finiteOfflinePairIntegrand m ha j k]
  have hcoef : (4 * (m j : ℂ) * (m k : ℂ)) =
      ((4 * (m j : ℝ) * (m k : ℝ) : ℝ) : ℂ) := by norm_cast
  rw [hcoef]
  have hinvre :
      (((((a j + a k : ℝ) : ℂ) -
        Complex.I * ((gamma j - gamma k : ℝ) : ℂ))⁻¹).re) =
        transverseCauchyKernel (a j) (a k) (gamma j - gamma k) := by
    rw [Complex.inv_re, Complex.normSq_apply]
    simp [transverseCauchyKernel, pow_two]
    congr 1
    ring
  rw [Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [hinvre]

theorem finiteOfflineProfile_gramExpansion {n : ℕ}
    (a gamma : Fin n → ℝ) (m : Fin n → ℕ) (t : ℝ) :
    (starRingEnd ℂ) (finiteOfflineProfile a gamma m t) *
        finiteOfflineProfile a gamma m t =
      ∑ j, ∑ k, finiteOfflinePairIntegrand a gamma m j k t := by
  unfold finiteOfflineProfile
  calc
    (starRingEnd ℂ) (∑ j, finiteOfflineMode a gamma m j t) *
        (∑ k, finiteOfflineMode a gamma m k t) =
      (∑ j, (starRingEnd ℂ) (finiteOfflineMode a gamma m j t)) *
        (∑ k, finiteOfflineMode a gamma m k t) := by rw [map_sum]
    _ = ∑ j, ∑ k, (starRingEnd ℂ) (finiteOfflineMode a gamma m j t) *
        finiteOfflineMode a gamma m k t := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
    _ = ∑ j, ∑ k, finiteOfflinePairIntegrand a gamma m j k t := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      exact finiteOfflinePairIntegrand_eq a gamma m j k t

theorem finiteOfflineProfile_gramIntegrableOn {n : ℕ}
    {a gamma : Fin n → ℝ} (m : Fin n → ℕ) (ha : ∀ j, 0 < a j) :
    IntegrableOn (fun t =>
      (starRingEnd ℂ) (finiteOfflineProfile a gamma m t) *
        finiteOfflineProfile a gamma m t) (Ioi 0) := by
  rw [show (fun t =>
      (starRingEnd ℂ) (finiteOfflineProfile a gamma m t) *
        finiteOfflineProfile a gamma m t) =
      fun t => ∑ j, ∑ k, finiteOfflinePairIntegrand a gamma m j k t by
    funext t
    exact finiteOfflineProfile_gramExpansion a gamma m t]
  apply integrable_finsetSum
  intro j hj
  apply integrable_finsetSum
  intro k hk
  exact finiteOfflinePairIntegrand_integrableOn m ha j k

theorem integral_finiteOfflineProfile_gram {n : ℕ}
    {a gamma : Fin n → ℝ} (m : Fin n → ℕ) (ha : ∀ j, 0 < a j) :
    ∫ t in Ioi (0 : ℝ),
        (starRingEnd ℂ) (finiteOfflineProfile a gamma m t) *
          finiteOfflineProfile a gamma m t =
      ∑ j, ∑ k, ∫ t in Ioi (0 : ℝ),
        finiteOfflinePairIntegrand a gamma m j k t := by
  rw [show (fun t =>
      (starRingEnd ℂ) (finiteOfflineProfile a gamma m t) *
        finiteOfflineProfile a gamma m t) =
      fun t => ∑ j, ∑ k, finiteOfflinePairIntegrand a gamma m j k t by
    funext t
    exact finiteOfflineProfile_gramExpansion a gamma m t]
  rw [integral_finsetSum Finset.univ]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [integral_finsetSum Finset.univ]
    intro k hk
    exact finiteOfflinePairIntegrand_integrableOn m ha j k
  · intro j hj
    apply integrable_finsetSum
    intro k hk
    exact finiteOfflinePairIntegrand_integrableOn m ha j k

theorem integral_norm_sq_finiteOfflineProfile {n : ℕ}
    {a gamma : Fin n → ℝ} (m : Fin n → ℕ) (ha : ∀ j, 0 < a j) :
    ∫ t in Ioi (0 : ℝ), ‖finiteOfflineProfile a gamma m t‖ ^ (2 : ℕ) =
      finiteOfflineCauchyEnergy a gamma m := by
  have hpoint : (fun t : ℝ => ‖finiteOfflineProfile a gamma m t‖ ^ (2 : ℕ)) =
      fun t => ((starRingEnd ℂ) (finiteOfflineProfile a gamma m t) *
        finiteOfflineProfile a gamma m t).re := by
    funext t
    rw [← Complex.normSq_eq_norm_sq]
    have h := Complex.normSq_eq_conj_mul_self
      (z := finiteOfflineProfile a gamma m t)
    exact_mod_cast congrArg Complex.re h
  rw [hpoint]
  have hre :
      (∫ t in Ioi (0 : ℝ),
        ((starRingEnd ℂ) (finiteOfflineProfile a gamma m t) *
          finiteOfflineProfile a gamma m t).re) =
      (∫ t in Ioi (0 : ℝ),
        (starRingEnd ℂ) (finiteOfflineProfile a gamma m t) *
          finiteOfflineProfile a gamma m t).re :=
    integral_re (μ := volume.restrict (Ioi 0))
      (finiteOfflineProfile_gramIntegrableOn (a := a) (gamma := gamma) m ha)
  rw [hre]
  rw [integral_finiteOfflineProfile_gram m ha]
  rw [Complex.re_sum]
  unfold finiteOfflineCauchyEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Complex.re_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [re_integral_finiteOfflinePairIntegrand m ha]
  ring

end RHTower

