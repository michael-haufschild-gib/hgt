import GaloisForLFunctions.RHTower.CHMDPolarJumpForm
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspPrimeArchSourceEquation
import GaloisForLFunctions.RHTower.XiSliceHusimiHeatDictionary

/-!
# The pointwise harmonic identity of the theta kernel

Symmetrizing the one-sided complete theta source equation under `x ↦ −x` gives the exact
pointwise identity for the symmetric prime shift sum of Riemann's kernel `Θ`:

`Σ_n Λ(n) n^{−1/2} (Θ(x + log n) + Θ(x − log n))
  = cosh(x/2) − (γ + log π) Θ(x) + ∫_0^∞ [2ν(u) Θ(x) − ω(u)(Θ(x+u) + Θ(x−u))] du`,

with the archimedean Lévy density `ω(u) = e^{−u/2}/(1 − e^{−2u})` and the diagonal density
`ν(u) = e^{−2u}/(1 − e^{−2u})`. In the Doob picture this says that the total arithmetic jump rate
from `x` equals the polar rate `cosh(x/2)` up to the archimedean correction: `Θ` is harmonic for the
pole-free Weil operator with source `−cosh(x/2)`. The polar half-line integrals combine into the
full-line cosine moment of `Θ`, which is `cosh(x/2)/2` by evenness.
-/

open MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower.CHMDPolar
open CHMDDoobGraph ThetaSourceWard

/-- The diagonal archimedean density `ν(u) = e^{−2u}/(1 − e^{−2u})`. -/
def archDiagonalDensity (u : ℝ) : ℝ := Real.exp (-2 * u) / (1 - Real.exp (-2 * u))

/-- The symmetrized archimedean integrand of the theta kernel. -/
def symArchTerm (x u : ℝ) : ℝ :=
  2 * archDiagonalDensity u * riemannKernelReal x -
    archLevyDensity u * (riemannKernelReal (x + u) + riemannKernelReal (x - u))

/-- The archimedean constant `(γ + log π)/2`. -/
def archConstantReal : ℝ := (Real.eulerMascheroniConstant + Real.log Real.pi) / 2

/-- The symmetric prime shift sum of the theta kernel. -/
def primeKernelSum (x : ℝ) : ℝ :=
  ∑' n : ℕ, vonMangoldtAtom n * (riemannKernelReal (x + Real.log n) + riemannKernelReal (x - Real.log n))

theorem gammaSourceTerm_eq (x u : ℝ) :
    gammaSourceTerm x u =
      archDiagonalDensity u * riemannKernelReal x - archLevyDensity u * riemannKernelReal (x + u) := by
  unfold gammaSourceTerm archDiagonalDensity archLevyDensity
  rw [thetaCuspFullSource_eq_riemannKernelReal, thetaCuspFullSource_eq_riemannKernelReal]
  ring

theorem integrableOn_gammaSourceTerm_real (x : ℝ) : IntegrableOn (gammaSourceTerm x) (Ioi 0) := by
  have h := (gammaSourceTerm_integrable x).re
  exact h.congr (Eventually.of_forall fun u => by simp)

/-- Integrability of the symmetrized archimedean integrand. -/
theorem integrableOn_symArchTerm (x : ℝ) : IntegrableOn (symArchTerm x) (Ioi 0) := by
  have h1 := integrableOn_gammaSourceTerm_real x
  have h2 := integrableOn_gammaSourceTerm_real (-x)
  refine (h1.add h2).congr_fun (fun u _ => ?_) measurableSet_Ioi
  simp only [Pi.add_apply, gammaSourceTerm_eq, symArchTerm, WeilExcess.riemannKernelReal_neg]
  rw [show -x + u = -(x - u) by ring, WeilExcess.riemannKernelReal_neg]
  ring

theorem summable_primeKernelSum (x : ℝ) :
    Summable fun n : ℕ => vonMangoldtAtom n *
      (riemannKernelReal (x + Real.log n) + riemannKernelReal (x - Real.log n)) :=
  summable_weightTerm summable_vonMangoldt_abs_div_sq x

theorem summable_primeShift_right (x : ℝ) :
    Summable fun n : ℕ => vonMangoldtAtom n * riemannKernelReal (x + Real.log n) := by
  refine (summable_primeKernelSum x).of_nonneg_of_le (fun n => ?_) (fun n => ?_)
  · exact mul_nonneg (vonMangoldtAtom_nonneg n) (riemannKernelReal_pos _).le
  · exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (riemannKernelReal_pos _).le)
      (vonMangoldtAtom_nonneg n)

theorem summable_primeShift_left (x : ℝ) :
    Summable fun n : ℕ => vonMangoldtAtom n * riemannKernelReal (x - Real.log n) := by
  refine (summable_primeKernelSum x).of_nonneg_of_le (fun n => ?_) (fun n => ?_)
  · exact mul_nonneg (vonMangoldtAtom_nonneg n) (riemannKernelReal_pos _).le
  · exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (riemannKernelReal_pos _).le)
      (vonMangoldtAtom_nonneg n)

theorem cosh_mul_theta_shift_eq (x u : ℝ) :
    2 * Real.cosh (u / 2) * riemannKernelReal (x + u) =
      2 * Real.cosh (x / 2) * massDensity (u + x) - 2 * Real.sinh (x / 2) * sinhDensity (u + x) := by
  unfold massDensity sinhDensity
  rw [show (u + x) / 2 = x / 2 + u / 2 by ring, Real.cosh_add, Real.sinh_add, add_comm u x]
  have h := Real.cosh_sq_sub_sinh_sq (x / 2)
  linear_combination (-(2 * riemannKernelReal (x + u) * Real.cosh (u / 2))) * h

/-- The full-line polar moment of the translated kernel. -/
theorem integral_cosh_mul_theta_shift (x : ℝ) :
    (∫ u, 2 * Real.cosh (u / 2) * riemannKernelReal (x + u)) = Real.cosh (x / 2) := by
  simp_rw [cosh_mul_theta_shift_eq]
  have hshift := integral_add_right_eq_self (μ := volume)
    (fun y => 2 * Real.cosh (x / 2) * massDensity y - 2 * Real.sinh (x / 2) * sinhDensity y) x
  rw [hshift, integral_sub ((integrable_massDensity.const_mul _)) (integrable_sinhDensity.const_mul _),
    integral_const_mul, integral_const_mul, integral_massDensity, integral_sinhDensity]
  ring

theorem integrable_cosh_mul_theta_shift (x : ℝ) :
    Integrable fun u : ℝ => 2 * Real.cosh (u / 2) * riemannKernelReal (x + u) := by
  simp_rw [cosh_mul_theta_shift_eq]
  exact ((integrable_massDensity.const_mul _).sub (integrable_sinhDensity.const_mul _)).comp_add_right x

/-- The two polar half-line integrals combine into the polar rate. -/
theorem polar_halfLine_sum (x : ℝ) :
    (∫ u in Ioi (0 : ℝ), 2 * Real.cosh (u / 2) * riemannKernelReal (x + u)) +
      (∫ u in Ioi (0 : ℝ), 2 * Real.cosh (u / 2) * riemannKernelReal (x - u)) =
      Real.cosh (x / 2) := by
  have hneg : (∫ u in Ioi (0 : ℝ), 2 * Real.cosh (u / 2) * riemannKernelReal (x - u)) =
      ∫ u in Iic (0 : ℝ), 2 * Real.cosh (u / 2) * riemannKernelReal (x + u) := by
    have h := integral_comp_neg_Ioi (0 : ℝ)
      (fun u => 2 * Real.cosh (u / 2) * riemannKernelReal (x + u))
    rw [neg_zero] at h
    rw [← h]
    congr 1
    funext u
    rw [neg_div, Real.cosh_neg, show x + -u = x - u by ring]
  rw [hneg, add_comm, intervalIntegral.integral_Iic_add_Ioi (integrable_cosh_mul_theta_shift x).integrableOn
    (integrable_cosh_mul_theta_shift x).integrableOn, integral_cosh_mul_theta_shift]

/-- The real one-sided complete theta source equation. -/
theorem oneSided_source_equation (x : ℝ) :
    -archConstantReal * riemannKernelReal x + (∫ u in Ioi (0 : ℝ), gammaSourceTerm x u) +
      (∫ u in Ioi (0 : ℝ), 2 * Real.cosh (u / 2) * riemannKernelReal (x + u)) -
      (∑' n : ℕ, vonMangoldtAtom n * riemannKernelReal (x + Real.log n)) =
      x * riemannKernelReal x := by
  have h := literal_complete_theta_source_equation x
  have hg : (fun u : ℝ => (((Real.exp (-2 * u) * thetaCuspFullSource x -
      Real.exp (-u / 2) * thetaCuspFullSource (x + u)) / (1 - Real.exp (-2 * u)) : ℝ) : ℂ)) =
      fun u : ℝ => ((gammaSourceTerm x u : ℝ) : ℂ) := by
    funext u
    rfl
  have hp : (fun u : ℝ => ((2 * Real.cosh (u / 2) * thetaCuspFullSource (x + u) : ℝ) : ℂ)) =
      fun u : ℝ => ((2 * Real.cosh (u / 2) * riemannKernelReal (x + u) : ℝ) : ℂ) := by
    funext u
    rw [thetaCuspFullSource_eq_riemannKernelReal]
  have hsum : (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n / Real.sqrt n *
      thetaCuspFullSource (x + Real.log n) : ℝ) : ℂ)) =
      fun n : ℕ => ((vonMangoldtAtom n * riemannKernelReal (x + Real.log n) : ℝ) : ℂ) := by
    funext n
    rw [thetaCuspFullSource_eq_riemannKernelReal]
    unfold vonMangoldtAtom
    split_ifs with hn
    · rfl
    · have h2 : n < 2 := lt_of_not_ge hn
      interval_cases n <;> simp
  rw [hg, hp, hsum, integral_complex_ofReal, integral_complex_ofReal, ← Complex.ofReal_tsum,
    thetaCuspFullSource_eq_riemannKernelReal] at h
  have h2 : ((-archConstantReal * riemannKernelReal x + (∫ u in Ioi (0 : ℝ), gammaSourceTerm x u) +
      (∫ u in Ioi (0 : ℝ), 2 * Real.cosh (u / 2) * riemannKernelReal (x + u)) -
      (∑' n : ℕ, vonMangoldtAtom n * riemannKernelReal (x + Real.log n)) : ℝ) : ℂ) =
      ((x * riemannKernelReal x : ℝ) : ℂ) := by
    unfold archConstantReal
    simp only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_neg,
      Complex.ofReal_div, Complex.ofReal_ofNat] at h ⊢
    linear_combination h
  exact Complex.ofReal_injective h2

/-- **The pointwise harmonic identity of the theta kernel.** -/
theorem theta_harmonic_identity (x : ℝ) :
    primeKernelSum x = Real.cosh (x / 2) - 2 * archConstantReal * riemannKernelReal x +
      ∫ u in Ioi (0 : ℝ), symArchTerm x u := by
  have h1 := oneSided_source_equation x
  have h2 := oneSided_source_equation (-x)
  rw [WeilExcess.riemannKernelReal_neg] at h2
  have hgamma : (∫ u in Ioi (0 : ℝ), gammaSourceTerm x u) +
      (∫ u in Ioi (0 : ℝ), gammaSourceTerm (-x) u) = ∫ u in Ioi (0 : ℝ), symArchTerm x u := by
    rw [← integral_add (integrableOn_gammaSourceTerm_real x) (integrableOn_gammaSourceTerm_real (-x))]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u _
    simp only [gammaSourceTerm_eq, symArchTerm, WeilExcess.riemannKernelReal_neg]
    rw [show -x + u = -(x - u) by ring, WeilExcess.riemannKernelReal_neg]
    ring
  have hpolar := polar_halfLine_sum x
  have hpolar' : (∫ u in Ioi (0 : ℝ), 2 * Real.cosh (u / 2) * riemannKernelReal (-x + u)) =
      ∫ u in Ioi (0 : ℝ), 2 * Real.cosh (u / 2) * riemannKernelReal (x - u) := by
    congr 1
    funext u
    rw [show -x + u = -(x - u) by ring, WeilExcess.riemannKernelReal_neg]
  have hprime : (∑' n : ℕ, vonMangoldtAtom n * riemannKernelReal (x + Real.log n)) +
      (∑' n : ℕ, vonMangoldtAtom n * riemannKernelReal (-x + Real.log n)) = primeKernelSum x := by
    have hl : (fun n : ℕ => vonMangoldtAtom n * riemannKernelReal (-x + Real.log n)) =
        fun n : ℕ => vonMangoldtAtom n * riemannKernelReal (x - Real.log n) := by
      funext n
      rw [show -x + Real.log n = -(x - Real.log n) by ring, WeilExcess.riemannKernelReal_neg]
    rw [hl, ← (summable_primeShift_right x).tsum_add (summable_primeShift_left x)]
    unfold primeKernelSum
    apply tsum_congr
    intro n
    ring
  rw [hpolar'] at h2
  rw [← hprime, ← hgamma, ← hpolar]
  linarith

end RHTower.CHMDPolar
