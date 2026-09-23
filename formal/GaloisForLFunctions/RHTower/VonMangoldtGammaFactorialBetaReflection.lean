import GaloisForLFunctions.RHTower.VonMangoldtGammaFactorialNormalizationNoGo
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Factorial trace transport as a Beta-reflected source pairing

The raw von Mangoldt--Gamma moment matrices are ordinary positive Grams, whereas their odd
factorial trace normalization is not positivity preserving.  This file identifies the missing
geometry exactly.  The reciprocal factorial is the Beta pairing

`1 / (i + j + 1)! = 1 / (i! j!) * integral_0^(1 : ℕ) t^i (1-t)^j dt`.

Consequently every finite factorially normalized source entry is the average of a left Borel
feature at `t` paired with its reflected right feature at `1-t`.  This is a reflection form, not
an ordinary Gram form.  The existing cofinal two-by-two no-go therefore says precisely that raw
source positivity does not imply positivity for this reflection.

No Xi divisor, zero-location hypothesis, numerical certificate, or RH statement enters the
construction.
-/

open scoped BigOperators Matrix
open Complex Filter Topology

namespace RHTower

noncomputable section

/-- The Beta integral at positive integral parameters is the factorial ratio. -/
theorem betaIntegral_nat_add_one_eq_factorial_ratio (i j : ℕ) :
    Complex.betaIntegral ((i + 1 : ℕ) : ℂ) ((j + 1 : ℕ) : ℂ) =
      ((i.factorial : ℕ) : ℂ) * j.factorial / (i + j + 1).factorial := by
  rw [Complex.betaIntegral_eq_Gamma_mul_div]
  · rw [show (((i + 1 : ℕ) : ℂ)) = (i : ℂ) + 1 by push_cast; ring,
      show (((j + 1 : ℕ) : ℂ)) = (j : ℂ) + 1 by push_cast; ring,
      Complex.Gamma_nat_eq_factorial, Complex.Gamma_nat_eq_factorial]
    rw [show (i : ℂ) + 1 + ((j : ℂ) + 1) = ((i + j + 1 : ℕ) : ℂ) + 1 by
      push_cast; ring]
    rw [Complex.Gamma_nat_eq_factorial]
  · norm_num
    positivity
  · norm_num
    positivity

/-- Real monomial form of the integral Beta--factorial identity. -/
theorem integral_pow_mul_one_sub_pow_eq_factorial_ratio (i j : ℕ) :
    (∫ t : ℝ in 0..1, t ^ i * (1 - t) ^ j) =
      ((i.factorial : ℕ) : ℝ) * j.factorial / (i + j + 1).factorial := by
  rw [← Complex.ofReal_inj]
  calc
    (((∫ t : ℝ in 0..1, t ^ i * (1 - t) ^ j) : ℝ) : ℂ) =
        ∫ t : ℝ in 0..1, ((t ^ i * (1 - t) ^ j : ℝ) : ℂ) :=
      intervalIntegral.integral_ofReal.symm
    _ = Complex.betaIntegral ((i + 1 : ℕ) : ℂ) ((j + 1 : ℕ) : ℂ) := by
      rw [Complex.betaIntegral]
      congr 1
      funext t
      rw [show (((i + 1 : ℕ) : ℂ) - 1) = (i : ℂ) by push_cast; ring,
        show (((j + 1 : ℕ) : ℂ) - 1) = (j : ℂ) by push_cast; ring,
        Complex.cpow_natCast, Complex.cpow_natCast]
      push_cast
      rfl
    _ = _ := by
      rw [betaIntegral_nat_add_one_eq_factorial_ratio]
      push_cast
      rfl

/-- One exponential source atom after left/right Borel splitting and Beta reflection. -/
theorem integral_betaReflectedExponentialAtom
    (mass rate : ℝ) (i j : ℕ) :
    (∫ t : ℝ in 0..1,
      mass * rate * ((t * rate) ^ i / (i.factorial : ℝ)) *
        (((1 - t) * rate) ^ j / (j.factorial : ℝ))) =
      mass * rate ^ (i + j + 1) / ((i + j + 1).factorial : ℝ) := by
  have hfun : (fun t : ℝ =>
      mass * rate * ((t * rate) ^ i / (i.factorial : ℝ)) *
        (((1 - t) * rate) ^ j / (j.factorial : ℝ))) =
      fun t : ℝ =>
        (mass * rate ^ (i + j + 1) /
          ((i.factorial : ℝ) * (j.factorial : ℝ))) *
          (t ^ i * (1 - t) ^ j) := by
    funext t
    rw [mul_pow, mul_pow, pow_add]
    ring
  rw [hfun, intervalIntegral.integral_const_mul,
    integral_pow_mul_one_sub_pow_eq_factorial_ratio]
  have hi : (i.factorial : ℝ) ≠ 0 := by positivity
  have hj : (j.factorial : ℝ) ≠ 0 := by positivity
  have hij : ((i + j + 1).factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- Cross kernel of a finite exponential source between a left Borel feature at `t` and its
reflected right feature at `1-t`.  It is not asserted to be positive at fixed `t`. -/
def finiteExponentialGammaBetaReflectedKernel
    {P : Type*} [Fintype P] {n : ℕ}
    (weight rate : P → ℝ) (x : ℝ) (a : Fin n → ℕ) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ ∑ p : P,
    weight p * Real.exp (-x * rate p) * rate p *
      ((t * rate p) ^ a i / (a i).factorial) *
      (((1 - t) * rate p) ^ a j / (a j).factorial)

/-- Reflection exchanges the two matrix indices. -/
theorem finiteExponentialGammaBetaReflectedKernel_one_sub
    {P : Type*} [Fintype P] {n : ℕ}
    (weight rate : P → ℝ) (x : ℝ) (a : Fin n → ℕ) (t : ℝ) :
    finiteExponentialGammaBetaReflectedKernel weight rate x a (1 - t) =
      (finiteExponentialGammaBetaReflectedKernel weight rate x a t)ᵀ := by
  ext i j
  simp only [finiteExponentialGammaBetaReflectedKernel, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- The Beta average of the reflected kernel is exactly the odd factorially normalized raw
moment matrix. -/
theorem integral_finiteExponentialGammaBetaReflectedKernel
    {P : Type*} [Fintype P] {n : ℕ}
    (weight rate : P → ℝ) (x : ℝ) (a : Fin n → ℕ) (i j : Fin n) :
    (∫ t : ℝ in 0..1,
      finiteExponentialGammaBetaReflectedKernel weight rate x a t i j) =
      finiteExponentialGammaRawMoment weight rate x (a i + a j + 1) /
        ((a i + a j + 1).factorial : ℝ) := by
  simp only [finiteExponentialGammaBetaReflectedKernel]
  rw [intervalIntegral.integral_finsetSum]
  · rw [finiteExponentialGammaRawMoment, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro p hp
    rw [integral_betaReflectedExponentialAtom]
  · intro p hp
    apply Continuous.intervalIntegrable
    fun_prop

/-- The finite factorial trace matrix of the actual von Mangoldt source at arbitrary selected
raw orders. -/
def finiteVonMangoldtGammaFactorialTraceGram
    (M : ℕ) {n : ℕ} (x : ℝ) (a : Fin n → ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ finiteVonMangoldtGammaRawMoment M x (a i + a j + 1) /
    ((a i + a j + 1).factorial : ℝ)

/-- Actual von Mangoldt specialization of the reflected Beta kernel. -/
def finiteVonMangoldtGammaBetaReflectedKernel
    (M : ℕ) {n : ℕ} (x : ℝ) (a : Fin n → ℕ) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  finiteExponentialGammaBetaReflectedKernel
    (fun p : Fin M ↦
      ArithmeticFunction.vonMangoldt ((p : ℕ) + 2) / ((p : ℕ) + 2))
    (fun p : Fin M ↦ Real.log ((p : ℕ) + 2)) x a t

/-- **Finite source Beta-reflection identity.**  Every finite actual von Mangoldt factorial trace
entry is the Beta average of the canonically reflected source kernel. -/
theorem integral_finiteVonMangoldtGammaBetaReflectedKernel
    (M : ℕ) {n : ℕ} (x : ℝ) (a : Fin n → ℕ) (i j : Fin n) :
    (∫ t : ℝ in 0..1,
      finiteVonMangoldtGammaBetaReflectedKernel M x a t i j) =
      finiteVonMangoldtGammaFactorialTraceGram M x a i j := by
  exact integral_finiteExponentialGammaBetaReflectedKernel _ _ x a i j

/-- Cofinal factorial trace matrix at arbitrary selected raw orders. -/
def infiniteVonMangoldtGammaFactorialTraceGram
    {n : ℕ} (x : ℝ) (a : Fin n → ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ infiniteVonMangoldtGammaRawMoment x (a i + a j + 1) /
    ((a i + a j + 1).factorial : ℝ)

/-- The finite Beta-reflected factorial matrices converge entrywise to the cofinal factorial
reflection form. -/
theorem tendsto_finiteVonMangoldtGammaFactorialTraceGram_apply
    {x : ℝ} (hx : 0 < x) {n : ℕ} (a : Fin n → ℕ) (i j : Fin n) :
    Tendsto
      (fun M ↦ finiteVonMangoldtGammaFactorialTraceGram M x a i j)
      atTop
      (nhds (infiniteVonMangoldtGammaFactorialTraceGram x a i j)) := by
  exact (tendsto_finiteVonMangoldtGammaRawMoment hx (a i + a j + 1)).div_const _

/-- The first odd factorial block in the prior no-go is exactly the cofinal Beta-reflection form
at even Borel orders `0` and `2`. -/
theorem infiniteVonMangoldtGammaFactorialTraceGram_zero_two_eq_first
    (x : ℝ) :
    infiniteVonMangoldtGammaFactorialTraceGram x ![0, 2] =
      infiniteVonMangoldtGammaFirstFactorialTraceGram x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [infiniteVonMangoldtGammaFactorialTraceGram,
      infiniteVonMangoldtGammaFirstFactorialTraceGram]

/-- **Cofinal reflection obstruction.**  The canonical Beta reflection of the positive raw Euler
source is eventually indefinite already on Borel orders `0` and `2`.  Hence the RH-bearing
completion must orient this reflection using coupled Gamma/polar/Mellin data; ordinary source
Gram positivity cannot do so. -/
theorem infiniteVonMangoldtGammaFactorialBetaReflection_eventually_not_posSemidef :
    ∀ᶠ x : ℝ in atTop,
      ¬ (infiniteVonMangoldtGammaFactorialTraceGram x ![0, 2]).PosSemidef := by
  filter_upwards
    [infiniteVonMangoldtGammaFirstFactorialTraceGram_eventually_not_posSemidef]
      with x hx
  rw [infiniteVonMangoldtGammaFactorialTraceGram_zero_two_eq_first]
  exact hx

end

end RHTower
