import GaloisForLFunctions.RHTower.RoutePPrimitiveBaseBalancedReflectionCodiagonal
import GaloisForLFunctions.RHTower.XiWardCubicBurnolWindowConormalIncidence

/-!
# Route P primitive Burnol window Gram square

The primitive base Cauchy cube and Burnol's nested-window conormal were previously identified only
after separate source and divisor constructions.  This module constructs the missing source-side
square directly.  A primitive cell `(p,e)` with log frequency `lambda` and arbitrary ordinate
clock `kappa` is placed at the canonical right-half-plane node `1/2 + lambda + i*kappa`, and its
Burnol inverse-window feature is scaled by the positive square root of its resolved von Mangoldt
mass.

The complete Gram of these source-defined window features is exactly the P-G181 primitive base
Cauchy matrix, entry by entry.  This includes every off-diagonal ordinate interaction and the exact
prime-depth amplitudes.  Hence its positivity, balanced-source trace identity, and uniform `< 2`
budget require no Xi-zero expansion.  The remaining Route P seam is no longer construction of a
source-to-window square; it is the boundary-value restriction transporting this universal Burnol
Gram from canonical Euler nodes to the actual completed-Xi divisor.
-/

open Complex Matrix Set MeasureTheory
open scoped BigOperators ComplexOrder

namespace RHTower

noncomputable section

/-- Canonical right-half-plane spectral node carried by one primitive Euler cell. -/
def routePPrimitiveBurnolSpectralPoint
    (pe : Nat.Primes × ℕ) (kappa : ℝ) : ℂ :=
  ((1 / 2 + xiGammaEulerPrimitiveLogFrequency pe : ℝ) : ℂ) +
    I * (kappa : ℂ)

theorem routePPrimitiveBurnolSpectralPoint_re
    (pe : Nat.Primes × ℕ) (kappa : ℝ) :
    (routePPrimitiveBurnolSpectralPoint pe kappa).re =
      1 / 2 + xiGammaEulerPrimitiveLogFrequency pe := by
  simp [routePPrimitiveBurnolSpectralPoint]

theorem routePPrimitiveBurnolSpectralPoint_im
    (pe : Nat.Primes × ℕ) (kappa : ℝ) :
    (routePPrimitiveBurnolSpectralPoint pe kappa).im = kappa := by
  simp [routePPrimitiveBurnolSpectralPoint]

theorem routePPrimitiveBurnolSpectralPoint_right
    (pe : Nat.Primes × ℕ) (kappa : ℝ) :
    1 / 2 < (routePPrimitiveBurnolSpectralPoint pe kappa).re := by
  rw [routePPrimitiveBurnolSpectralPoint_re]
  linarith [xiGammaEulerPrimitiveLogFrequency_pos pe]

/-- Primitive Euler amplitude placed on the universal Burnol inverse-window conormal feature. -/
def routePPrimitiveBurnolWindowFeature
    (pe : Nat.Primes × ℕ) (kappa L : ℝ) : ℂ :=
  finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat pe) *
    xiWardCubicBurnolWindowConormalFeature L
      (routePPrimitiveBurnolSpectralPoint pe kappa)

/-- Full Gram matrix of the coefficient-weighted primitive Burnol window features. -/
def routePPrimitiveBurnolWindowGramMatrix {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j => ∫ L : ℝ in Ioi 0,
    star (routePPrimitiveBurnolWindowFeature (pe i) (kappa i) L) *
      routePPrimitiveBurnolWindowFeature (pe j) (kappa j) L

theorem integral_star_routePPrimitiveBurnolWindowFeature_mul
    (pe tau : Nat.Primes × ℕ) (kappa nu : ℝ) :
    (∫ L : ℝ in Ioi 0,
      star (routePPrimitiveBurnolWindowFeature pe kappa L) *
        routePPrimitiveBurnolWindowFeature tau nu L) =
      finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat pe) *
        routePBaseCauchyCubicKernel 1
          (xiGammaEulerPrimitiveLogFrequency pe)
          (xiGammaEulerPrimitiveLogFrequency tau) (nu - kappa) *
        star (finiteVonMangoldtDepthOneAmplitude
          (xiGammaEulerValuationNat tau)) := by
  let A : ℂ := finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat pe)
  let B : ℂ := finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat tau)
  let rho : ℂ := routePPrimitiveBurnolSpectralPoint pe kappa
  let sigma : ℂ := routePPrimitiveBurnolSpectralPoint tau nu
  have hrho : 1 / 2 < rho.re := routePPrimitiveBurnolSpectralPoint_right pe kappa
  have hsigma : 1 / 2 < sigma.re := routePPrimitiveBurnolSpectralPoint_right tau nu
  rw [show (fun L : ℝ =>
      star (routePPrimitiveBurnolWindowFeature pe kappa L) *
        routePPrimitiveBurnolWindowFeature tau nu L) =
      fun L : ℝ => (star A * B) *
        (star (routePXiBaseConormalResidueFeature rho L) *
          routePXiBaseConormalResidueFeature sigma L) by
    funext L
    simp only [routePPrimitiveBurnolWindowFeature,
      xiWardCubicBurnolWindowConormalFeature_eq]
    dsimp [A, B, rho, sigma]
    rw [map_mul]
    ring]
  rw [MeasureTheory.integral_const_mul,
    integral_star_routePXiBaseConormalResidueFeature_mul hrho hsigma]
  dsimp [A, B, rho, sigma]
  rw [routePPrimitiveBurnolSpectralPoint_re,
    routePPrimitiveBurnolSpectralPoint_re,
    routePPrimitiveBurnolSpectralPoint_im,
    routePPrimitiveBurnolSpectralPoint_im]
  simp [finiteVonMangoldtDepthOneAmplitude]
  ring

/-- **P-G186.** The entire primitive base Cauchy cube is the literal Burnol window Gram, including
all off-diagonal ordinate interactions and exact von Mangoldt amplitudes. -/
theorem routePPrimitiveBurnolWindowGramMatrix_eq_baseCauchy
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ) :
    routePPrimitiveBurnolWindowGramMatrix pe kappa =
      routePPrimitiveBaseCauchyCubicKernelMatrix 1 pe kappa := by
  ext i j
  rw [routePPrimitiveBurnolWindowGramMatrix,
    integral_star_routePPrimitiveBurnolWindowFeature_mul,
    routePPrimitiveBaseCauchyCubicKernelMatrix_apply]

/-- Source-window square gives positivity for arbitrary primitive packets and ordinate clocks. -/
theorem routePPrimitiveBurnolWindowGramMatrix_posSemidef
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ) :
    (routePPrimitiveBurnolWindowGramMatrix pe kappa).PosSemidef := by
  rw [routePPrimitiveBurnolWindowGramMatrix_eq_baseCauchy]
  exact routePPrimitiveBaseCauchyCubicKernelMatrix_posSemidef (by norm_num)

/-- Its trace is the already-identified balanced Euler source codiagonal, for every displacement. -/
theorem trace_routePPrimitiveBurnolWindowGramMatrix_eq_balanced_source
    {N : ℕ} (a : ℝ) (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ) :
    (routePPrimitiveBurnolWindowGramMatrix pe kappa).trace =
      ∑ i : Fin N, routePPrimitiveBaseBalancedReflectionCodiagonal a (pe i) := by
  rw [routePPrimitiveBurnolWindowGramMatrix_eq_baseCauchy]
  exact trace_routePPrimitiveBaseCauchyCubicKernelMatrix_eq_balanced_source a pe kappa

/-- Every injective finite primitive Burnol window packet lies below the same global `< 2` budget. -/
theorem re_trace_routePPrimitiveBurnolWindowGramMatrix_le_budget
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (hpe : Function.Injective pe)
    (kappa : Fin N → ℝ) :
    (routePPrimitiveBurnolWindowGramMatrix pe kappa).trace.re ≤
      routePPrimitiveBaseCauchyCubicTraceBudget := by
  rw [routePPrimitiveBurnolWindowGramMatrix_eq_baseCauchy]
  exact re_trace_routePPrimitiveBaseCauchyCubicKernelMatrix_le_budget
    (by norm_num) pe hpe kappa

end

end RHTower
