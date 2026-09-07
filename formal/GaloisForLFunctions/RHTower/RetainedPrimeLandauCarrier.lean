import GaloisForLFunctions.RHTower.RetainedPrimeSourceInterpolation
import GaloisForLFunctions.RHTower.LandauIntegralTransfer

/-!
# Positive integral carrier of a retained source functional

The absolute Mellin density of the actual retained primitive at four gives a
finite positive measure. Its logarithmic variable is nonnegative almost
everywhere and has all classical exponential moments. Under a one-sided
source functional, exact reality and interpolation identify its complex MGF
with the literal source Mellin transform, hence with the pole-filled
continuation near the MGF origin. No positivity or continuation is assumed
for the RH-bearing source outside this explicit implication.
-/

noncomputable section
open Complex MeasureTheory Filter Set ProbabilityTheory Topology
open scoped ENNReal NNReal
namespace RHTower

/-- The continuous primitive of a real functional on a finite retained prime field. -/
def retainedPrimeLandauPrimitive (Q : Finset Nat.Primes) (y : Finset ℕ → ℝ) : ℝ → ℂ :=
  squareRootSummatoryPrimitive
    (retainedPrimeDivisorConvolution (Q.image (fun p : Nat.Primes => (p : ℕ)))
      (fun R => (y R : ℂ)))

/-- Literal one-sided functional on every complete retained source cutoff. -/
def RetainedPrimeSourceNonnegative (Q : Finset Nat.Primes) (y : Finset ℕ → ℝ) : Prop :=
  ∀ M : ℕ, 0 ≤ (retainedPrimeSourceMean (Q.image (fun p : Nat.Primes => (p : ℕ)))
    (fun R => (y R : ℂ)) M).re

lemma retainedPrimeLandauPrimitive_eq_zero_of_le_one
    (Q : Finset Nat.Primes) (y : Finset ℕ → ℝ) {x : ℝ} (hx : x ≤ 1) :
    retainedPrimeLandauPrimitive Q y x = 0 := by
  rw [retainedPrimeLandauPrimitive, squareRootSummatoryPrimitive_eq_integral,
    Ioo_eq_empty_of_le hx]
  simp

lemma retainedPrimeLandauPrimitive_im_eq_zero
    (Q : Finset Nat.Primes) (y : Finset ℕ → ℝ) (x : ℝ) :
    (retainedPrimeLandauPrimitive Q y x).im = 0 := by
  by_cases hx : x ≤ 1
  · rw [retainedPrimeLandauPrimitive_eq_zero_of_le_one Q y hx]; rfl
  have hx1 : 1 ≤ x := (le_of_not_ge hx)
  let P := Q.image (fun p : Nat.Primes => (p : ℕ))
  let k : ℕ := ⌊x⌋₊
  have hk : 1 ≤ k := (Nat.le_floor_iff (by linarith : 0 ≤ x)).mpr (by simpa using hx1)
  have hkx : (k : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxk : x ≤ (k + 1 : ℕ) := by exact_mod_cast (Nat.lt_floor_add_one x).le
  have hsum : (∑ n ∈ Finset.Icc 1 k,
      retainedPrimeDivisorConvolution P (fun R => (y R : ℂ)) n).im = 0 := by
    rw [sum_retainedPrimeDivisorConvolution]
    simp [retainedPrimeMobiusCoefficient]
  have hnat : (retainedPrimeSourceMean P (fun R => (y R : ℂ)) k).im = 0 := by
    simp [retainedPrimeSourceMean]
  change (squareRootSummatoryPrimitive
    (retainedPrimeDivisorConvolution P (fun R => (y R : ℂ))) x).im = 0
  rw [squareRootSummatoryPrimitive_between _ hk hkx hxk,
    squareRootSummatoryPrimitive_retained_nat, Complex.add_im, hnat,
    Complex.mul_im, hsum]
  simp

lemma retainedPrimeLandauPrimitive_nonneg
    {Q : Finset Nat.Primes} {y : Finset ℕ → ℝ}
    (h : RetainedPrimeSourceNonnegative Q y) (x : ℝ) :
    0 ≤ (retainedPrimeLandauPrimitive Q y x).re := by
  by_cases hx : x ≤ 1
  · rw [retainedPrimeLandauPrimitive_eq_zero_of_le_one Q y hx]; exact le_rfl
  exact retainedPrimeSourceMean_re_nonneg_ray _ _ h (le_of_not_ge hx)

/-- Absolute center-four Mellin density. -/
def retainedPrimeLandauDensity (Q : Finset Nat.Primes) (y : Finset ℕ → ℝ) (x : ℝ) : ℝ :=
  ‖(x : ℂ) ^ (-5 : ℂ) * retainedPrimeLandauPrimitive Q y x‖

/-- Finite positive measure carried by the actual retained primitive. -/
def retainedPrimeLandauMeasure (Q : Finset Nat.Primes) (y : Finset ℕ → ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity fun x =>
    ENNReal.ofReal (retainedPrimeLandauDensity Q y x)

lemma integrable_retainedPrimeLandauDensity (Q : Finset Nat.Primes) (y : Finset ℕ → ℝ) :
    Integrable (retainedPrimeLandauDensity Q y) (volume.restrict (Ioi 0)) := by
  have h := (hasMellin_retainedPrimeSourcePrimitive Q (fun R => (y R : ℂ))
    (s := 4) (by norm_num)).1.norm
  change Integrable (fun x : ℝ => ‖(x : ℂ) ^ (-5 : ℂ) * retainedPrimeLandauPrimitive Q y x‖)
    (volume.restrict (Ioi 0))
  simpa only [MellinConvergent, smul_eq_mul, show (-4 - 1 : ℂ) = -5 by ring,
    retainedPrimeLandauPrimitive] using h

lemma retainedPrimeLandauMeasure_finite (Q : Finset Nat.Primes) (y : Finset ℕ → ℝ) :
    IsFiniteMeasure (retainedPrimeLandauMeasure Q y) :=
  isFiniteMeasure_withDensity_ofReal (integrable_retainedPrimeLandauDensity Q y).hasFiniteIntegral

lemma log_nonneg_ae_retainedPrimeLandauMeasure (Q : Finset Nat.Primes) (y : Finset ℕ → ℝ) :
    ∀ᵐ x ∂retainedPrimeLandauMeasure Q y, 0 ≤ Real.log x := by
  have hmeas := (integrable_retainedPrimeLandauDensity Q y).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  rw [retainedPrimeLandauMeasure, ae_withDensity_iff' hmeas]
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx hden
  have hx1 : 1 ≤ x := by
    by_contra hn
    have hz := retainedPrimeLandauPrimitive_eq_zero_of_le_one Q y (le_of_not_ge hn)
    simp [retainedPrimeLandauDensity, hz] at hden
  exact Real.log_nonneg hx1

lemma exp_mul_retainedPrimeLandauDensity_eq_norm
    (Q : Finset Nat.Primes) (y : Finset ℕ → ℝ) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    Real.exp (t * Real.log x) * retainedPrimeLandauDensity Q y x =
      ‖(x : ℂ) ^ ((t : ℂ) - 5) * retainedPrimeLandauPrimitive Q y x‖ := by
  simp only [retainedPrimeLandauDensity, norm_mul, norm_cpow_eq_rpow_re_of_pos hx,
    sub_re, ofReal_re]
  change Real.exp (t * Real.log x) *
    (x ^ (-5 : ℝ) * ‖retainedPrimeLandauPrimitive Q y x‖) =
    x ^ (t - 5) * ‖retainedPrimeLandauPrimitive Q y x‖
  rw [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hx, ← mul_assoc, ← Real.exp_add]
  congr 2
  ring

lemma integrable_exp_log_retainedPrimeLandauMeasure
    (Q : Finset Nat.Primes) (y : Finset ℕ → ℝ) {t : ℝ} (ht : t < 2) :
    Integrable (fun x => Real.exp (t * Real.log x)) (retainedPrimeLandauMeasure Q y) := by
  have hmeas := (integrable_retainedPrimeLandauDensity Q y).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  rw [retainedPrimeLandauMeasure, integrable_withDensity_iff_integrable_smul₀' hmeas
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hden0 (x : ℝ) : 0 ≤ retainedPrimeLandauDensity Q y x := norm_nonneg _
  simp_rw [ENNReal.toReal_ofReal (hden0 _), smul_eq_mul]
  have hconv := (hasMellin_retainedPrimeSourcePrimitive Q (fun R => (y R : ℂ))
    (s := ((4 - t : ℝ) : ℂ)) (by simp only [ofReal_re]; linarith)).1.norm
  refine hconv.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  change ‖(x : ℂ) ^ (-((4 - t : ℝ) : ℂ) - 1) * retainedPrimeLandauPrimitive Q y x‖ = _
  rw [show -((4 - t : ℝ) : ℂ) - 1 = (t : ℂ) - 5 by push_cast; ring]
  exact (exp_mul_retainedPrimeLandauDensity_eq_norm Q y t hx).symm.trans (mul_comm _ _)

lemma zero_mem_interior_integrableExpSet_retainedPrimeLandauMeasure
    (Q : Finset Nat.Primes) (y : Finset ℕ → ℝ) :
    0 ∈ interior (integrableExpSet Real.log (retainedPrimeLandauMeasure Q y)) := by
  rw [mem_interior_iff_mem_nhds]
  refine mem_of_superset (Iio_mem_nhds (by norm_num : (0 : ℝ) < 2)) ?_
  intro t ht
  exact integrable_exp_log_retainedPrimeLandauMeasure Q y ht

end RHTower

namespace RHTower

private lemma complex_exp_log_eq_cpow (z : ℂ) {x : ℝ} (hx : 0 < x) :
    Complex.exp (z * (Real.log x : ℂ)) = (x : ℂ) ^ z := by
  have hlog : Complex.log (x : ℂ) = (Real.log x : ℂ) := by
    apply Complex.ext
    · simp [Complex.log_re, Real.norm_of_nonneg hx.le]
    · simp [Complex.log_im, Complex.arg_ofReal_of_nonneg hx.le]
  rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx.ne'), hlog, mul_comm]

lemma ofReal_retainedPrimeLandauDensity_eq
    {Q : Finset Nat.Primes} {y : Finset ℕ → ℝ}
    (h : RetainedPrimeSourceNonnegative Q y) {x : ℝ} (hx : 0 < x) :
    (retainedPrimeLandauDensity Q y x : ℂ) =
      (x : ℂ) ^ (-5 : ℂ) * retainedPrimeLandauPrimitive Q y x := by
  let q : ℝ := x ^ (-5 : ℝ)
  have hq : 0 ≤ q := Real.rpow_nonneg hx.le _
  have hp : (x : ℂ) ^ (-5 : ℂ) = (q : ℂ) := by
    dsimp [q]
    rw [Complex.ofReal_cpow hx.le]
    norm_num
  let w : ℂ := (x : ℂ) ^ (-5 : ℂ) * retainedPrimeLandauPrimitive Q y x
  have hwim : w.im = 0 := by
    dsimp [w]
    rw [hp, mul_im, retainedPrimeLandauPrimitive_im_eq_zero]
    simp
  have hwre : 0 ≤ w.re := by
    dsimp [w]
    rw [hp, mul_re]
    simp only [ofReal_re, ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg hq (retainedPrimeLandauPrimitive_nonneg h x)
  have he : w = (w.re : ℂ) := by apply Complex.ext <;> simp [hwim]
  change ((‖w‖ : ℝ) : ℂ) = w
  rw [he, Complex.norm_real, Real.norm_of_nonneg hwre]

/-- Exact complex MGF of the positive retained carrier, at every argument where
its Bochner integral is defined, with no unproved continuation substitution. -/
lemma complexMGF_retainedPrimeLandauMeasure_eq_mellin
    {Q : Finset Nat.Primes} {y : Finset ℕ → ℝ}
    (h : RetainedPrimeSourceNonnegative Q y) (z : ℂ) :
    complexMGF Real.log (retainedPrimeLandauMeasure Q y) z =
      mellin (retainedPrimeLandauPrimitive Q y) (z - 4) := by
  have hmeas := (integrable_retainedPrimeLandauDensity Q y).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  rw [complexMGF, retainedPrimeLandauMeasure,
    integral_withDensity_eq_integral_toReal_smul₀ hmeas
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), mellin]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [ENNReal.toReal_ofReal (show 0 ≤ retainedPrimeLandauDensity Q y x from norm_nonneg _),
    Complex.real_smul, smul_eq_mul, ofReal_retainedPrimeLandauDensity_eq h hx,
    complex_exp_log_eq_cpow z hx]
  rw [mul_assoc, mul_comm (retainedPrimeLandauPrimitive Q y x), ← mul_assoc,
    ← Complex.cpow_add _ _ (ofReal_ne_zero.mpr hx.ne')]
  congr 2
  ring

/-- The actual pole-filled continuation in the center-four MGF variable. -/
def retainedPrimeLandauContinuation (Q : Finset Nat.Primes) (y : Finset ℕ → ℝ) (z : ℂ) : ℂ :=
  finiteDirichletDivisorMellin
    (retainedPrimeDirichletCoefficients (Q.image (fun p : Nat.Primes => (p : ℕ)))
      (fun R => (y R : ℂ))) Q (2 * Real.eulerMascheroniConstant : ℂ) (4 - z)

lemma retainedPrimeLandauContinuation_eq_complexMGF
    {Q : Finset Nat.Primes} {y : Finset ℕ → ℝ}
    (h : RetainedPrimeSourceNonnegative Q y) {z : ℂ} (hz : z.re < 2) :
    retainedPrimeLandauContinuation Q y z =
      complexMGF Real.log (retainedPrimeLandauMeasure Q y) z := by
  rw [complexMGF_retainedPrimeLandauMeasure_eq_mellin h]
  have hm := (hasMellin_retainedPrimeSourcePrimitive Q (fun R => (y R : ℂ))
    (s := 4 - z) (by simp only [sub_re]; norm_num; linarith)).2
  simpa only [neg_sub, retainedPrimeLandauPrimitive, retainedPrimeLandauContinuation] using hm.symm

lemma retainedPrimeLandauContinuation_eventuallyEq_complexMGF
    {Q : Finset Nat.Primes} {y : Finset ℕ → ℝ}
    (h : RetainedPrimeSourceNonnegative Q y) :
    retainedPrimeLandauContinuation Q y =ᶠ[𝓝 0]
      complexMGF Real.log (retainedPrimeLandauMeasure Q y) := by
  have hn : ∀ᶠ z : ℂ in 𝓝 0, z.re < 2 :=
    (isOpen_lt Complex.continuous_re continuous_const).mem_nhds (by norm_num)
  filter_upwards [hn] with z hz
  exact retainedPrimeLandauContinuation_eq_complexMGF h hz

end RHTower
