import GaloisForLFunctions.RHTower.RoutePPrimitiveBaseCauchyCapacityReduction
import GaloisForLFunctions.RHTower.CompletedPrimeFluxFittingAttachment
import GaloisForLFunctions.HTGeometry.BarnesMellinRepresentation

/-!
# Route P completed Xi conormal base residue

P-G181 reduces the remaining Route P landing to one positive base Cauchy cube.  This module
identifies that cube as an actual conormal residue Gram of a source-defined completed meromorphic
family.  Multiply the completed Xi logarithmic derivative by its radial Laplace column.  At every
Xi zero its multiplicity-normalized residue is exactly the base radial feature, and the finite Gram
on strict-right zeros is exactly P-G181's target matrix.

The raw logarithmic residue carries analytic multiplicity `m`, so its squared energy carries
`m^(2 : ℕ)`, whereas the multiplicity-exact divisor trace carries only `m`.  Raw residue Gram therefore
matches the divisor only at simple zeros.  The unique positive correction is the inverse
square-root multiplicity half-density.  The remaining producer is consequently a bounded
half-density conormal landing, not an unnormalized logarithmic-residue map.
-/

open Complex Set Filter Topology MeasureTheory
open scoped BigOperators ComplexOrder

namespace RHTower

noncomputable section

/-- Source-defined completed Xi logarithmic conormal column. -/
def routePCompletedXiConormalColumn (z : ℂ) (r : ℝ) : ℂ :=
  logDeriv xi z * (r : ℂ) * Complex.exp (-((z - 1 / 2) * (r : ℂ)))

/-- Base radial feature exposed by a normalized Xi conormal residue. -/
def routePXiBaseConormalResidueFeature (rho : ℂ) (r : ℝ) : ℂ :=
  (r : ℂ) * Complex.exp (-((rho - 1 / 2) * (r : ℂ)))

/-- The raw completed logarithmic conormal residue carries full analytic multiplicity. -/
theorem routePCompletedXiConormalColumn_residue
    (rho : ℂ) (r : ℝ) :
    Tendsto
      (fun z : ℂ => (z - rho) * routePCompletedXiConormalColumn z r)
      (nhdsWithin rho ({rho}ᶜ))
      (nhds (((analyticOrderAt xi rho).toNat : ℂ) *
        routePXiBaseConormalResidueFeature rho r)) := by
  have hres := xi_normalizedLogDeriv_tendsto_order rho
  have hfeature : Tendsto
      (fun z : ℂ => (r : ℂ) * Complex.exp (-((z - 1 / 2) * (r : ℂ))))
      (nhdsWithin rho ({rho}ᶜ))
      (nhds ((r : ℂ) * Complex.exp (-((rho - 1 / 2) * (r : ℂ))))) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    exact (by fun_prop : ContinuousAt
      (fun z : ℂ => (r : ℂ) * Complex.exp (-((z - 1 / 2) * (r : ℂ)))) rho)
  have h := hres.mul hfeature
  simpa [routePCompletedXiConormalColumn,
    routePXiBaseConormalResidueFeature, mul_assoc] using h

/-- Multiplicity normalization makes every Xi conormal residue exactly one base radial feature. -/
theorem routePCompletedXiConormalColumn_normalized_residue
    {rho : ℂ} (hzero : xi rho = 0) (r : ℝ) :
    Tendsto
      (fun z : ℂ =>
        ((z - rho) * routePCompletedXiConormalColumn z r) /
          ((analyticOrderAt xi rho).toNat : ℂ))
      (nhdsWithin rho ({rho}ᶜ))
      (nhds (routePXiBaseConormalResidueFeature rho r)) := by
  have hm : ((analyticOrderAt xi rho).toNat : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (xi_order_toNat_ne_zero hzero)
  have h := (routePCompletedXiConormalColumn_residue rho r).div_const
    ((analyticOrderAt xi rho).toNat : ℂ)
  convert h using 1
  field_simp [hm]

/-- The base conormal residue features have exactly P-G181's Cauchy-cube Gram. -/
theorem integral_star_routePXiBaseConormalResidueFeature_mul
    {rho tau : ℂ} (hrho : 1 / 2 < rho.re) (htau : 1 / 2 < tau.re) :
    (∫ r : ℝ in Ioi 0,
      star (routePXiBaseConormalResidueFeature rho r) *
        routePXiBaseConormalResidueFeature tau r) =
      routePBaseCauchyCubicKernel 1
        (rho - 1 / 2).re (tau - 1 / 2).re
        ((tau - 1 / 2).im - (rho - 1 / 2).im) := by
  let w : ℂ := star (rho - 1 / 2) + (tau - 1 / 2)
  have hw : 0 < w.re := by
    have hwre : w.re = (rho.re - 1 / 2) + (tau.re - 1 / 2) := by
      simp [w]
    rw [hwre]
    linarith
  have hgamma :=
    GaloisForLFunctions.HTGeometry.integral_cpow_mul_exp_neg_mul_Ioi
      (s := (3 : ℂ)) (w := w) (by norm_num) hw
  have hfun : (fun r : ℝ =>
      star (routePXiBaseConormalResidueFeature rho r) *
        routePXiBaseConormalResidueFeature tau r) =
      fun r : ℝ => (r : ℂ) ^ ((3 : ℂ) - 1) *
        Complex.exp (-(w * (r : ℂ))) := by
    funext r
    rw [routePXiBaseConormalResidueFeature,
      routePXiBaseConormalResidueFeature]
    have hstarExp :
        (starRingEnd ℂ) (Complex.exp (-((rho - 1 / 2) * (r : ℂ)))) =
          Complex.exp (-(star (rho - 1 / 2)) * (r : ℂ)) := by
      rw [← Complex.exp_conj]
      congr 1
      simp
      rw [map_ofNat (starRingEnd ℂ) 2]
      ring
    change (starRingEnd ℂ)
        ((r : ℂ) * Complex.exp (-((rho - 1 / 2) * (r : ℂ)))) *
          ((r : ℂ) * Complex.exp (-((tau - 1 / 2) * (r : ℂ)))) = _
    rw [map_mul, Complex.conj_ofReal, hstarExp]
    calc
      (r : ℂ) * Complex.exp (-(star (rho - 1 / 2)) * (r : ℂ)) *
          ((r : ℂ) * Complex.exp (-((tau - 1 / 2) * (r : ℂ)))) =
          (r : ℂ) ^ (2 : ℕ) *
            (Complex.exp (-(star (rho - 1 / 2)) * (r : ℂ)) *
              Complex.exp (-((tau - 1 / 2) * (r : ℂ)))) := by ring
      _ = (r : ℂ) ^ (2 : ℕ) * Complex.exp
          (-(star (rho - 1 / 2)) * (r : ℂ) +
            -((tau - 1 / 2) * (r : ℂ))) := by rw [Complex.exp_add]
      _ = (r : ℂ) ^ (2 : ℕ) * Complex.exp (-(w * (r : ℂ))) := by
        congr 2
        dsimp [w]
        ring
      _ = (r : ℂ) ^ ((3 : ℂ) - 1) *
          Complex.exp (-(w * (r : ℂ))) := by norm_num
  rw [hfun, hgamma]
  rw [show Complex.Gamma (3 : ℂ) = 2 by
    rw [show (3 : ℂ) = (2 : ℕ) + 1 by norm_num, Complex.Gamma_nat_eq_factorial]
    norm_num]
  rw [routePBaseCauchyCubicKernel, routePCollisionPairFrequency]
  norm_num
  have hden :
      (rho.re : ℂ) - 1 / 2 + ((tau.re : ℂ) - 1 / 2) +
          ((tau.im : ℂ) - (rho.im : ℂ)) * I = w := by
    apply Complex.ext
    · simp [w]
    · simp [w]
      ring
  rw [hden]
  rw [Complex.cpow_neg w 3]
  norm_num
  ring

/-- Gram matrix of the actual strict-right normalized conormal residue features. -/
def routePStrictRightZeroConormalResidueGramMatrix {N : ℕ}
    (q : Fin N → XiRightZeroCopy) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => ∫ r : ℝ in Ioi 0,
    star (routePXiBaseConormalResidueFeature ((q i).1.1 : ℂ) r) *
      routePXiBaseConormalResidueFeature ((q j).1.1 : ℂ) r

/-- P-G181's target matrix is exactly the Gram of normalized residues of the completed Xi
logarithmic conormal family. -/
theorem routePStrictRightZeroConormalResidueGramMatrix_eq
    {N : ℕ} (q : Fin N → XiRightZeroCopy) :
    routePStrictRightZeroConormalResidueGramMatrix q =
      routePStrictRightZeroBaseCauchyCubicKernelMatrix q := by
  ext i j
  have hi : 1 / 2 < (((q i).1.1 : XiDivisorSupport) : ℂ).re := by
    have hpos := xiRightCenteredZero_re_pos (q i)
    rw [xiRightCenteredZero_eq_support_sub_half] at hpos
    norm_num at hpos ⊢
    linarith
  have hj : 1 / 2 < (((q j).1.1 : XiDivisorSupport) : ℂ).re := by
    have hpos := xiRightCenteredZero_re_pos (q j)
    rw [xiRightCenteredZero_eq_support_sub_half] at hpos
    norm_num at hpos ⊢
    linarith
  rw [routePStrictRightZeroConormalResidueGramMatrix,
    integral_star_routePXiBaseConormalResidueFeature_mul hi hj]
  rw [routePStrictRightZeroBaseCauchyCubicKernelMatrix,
    routePBaseCauchyCubicKernelMatrix]
  rw [xiRightCenteredZero_eq_support_sub_half,
    xiRightCenteredZero_eq_support_sub_half]

/-- A raw logarithmic residue has quadratic multiplicity energy. -/
def routePRawXiConormalResidueCharge (m : ℕ) (a : ℝ) : ℝ :=
  (m : ℝ) ^ (2 : ℕ) * (1 / (4 * a ^ (3 : ℕ)))

/-- Multiplicity-exact divisor trace has linear multiplicity energy. -/
def routePXiDivisorMultiplicityCharge (m : ℕ) (a : ℝ) : ℝ :=
  (m : ℝ) * (1 / (4 * a ^ (3 : ℕ)))

/-- Raw residue Gram matches divisor multiplicity only for a simple zero. -/
theorem routePRawXiConormalResidueCharge_eq_divisor_iff
    {m : ℕ} (hm : 0 < m) {a : ℝ} (ha : 0 < a) :
    routePRawXiConormalResidueCharge m a =
        routePXiDivisorMultiplicityCharge m a ↔ m = 1 := by
  rw [routePRawXiConormalResidueCharge, routePXiDivisorMultiplicityCharge]
  have hcharge : 0 < 1 / (4 * a ^ (3 : ℕ)) := by positivity
  constructor
  · intro h
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have : (m : ℝ) ^ (2 : ℕ) = (m : ℝ) := by
      exact (mul_right_cancel₀ hcharge.ne' (by simpa [mul_assoc] using h))
    have hmOne : (m : ℝ) = 1 := by nlinarith
    exact_mod_cast hmOne
  · rintro rfl
    norm_num

/-- The unique positive scalar correcting a raw multiplicity residue to linear divisor energy is
the inverse square-root half-density. -/
theorem routePXiConormalMultiplicityHalfDensity_unique
    {m : ℕ} (hm : 0 < m) {c : ℝ} (hc : 0 < c)
    (henergy : (c * (m : ℝ)) ^ (2 : ℕ) = (m : ℝ)) :
    c = (Real.sqrt m)⁻¹ := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hsqrt : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hmR
  have hcm : 0 < c * (m : ℝ) := mul_pos hc hmR
  have hroot : c * (m : ℝ) = Real.sqrt (m : ℝ) := by
    apply (sq_eq_sq₀ hcm.le hsqrt.le).mp
    rw [henergy, Real.sq_sqrt hmR.le]
  calc
    c = Real.sqrt (m : ℝ) / (m : ℝ) := (eq_div_iff hmR.ne').2 hroot
    _ = Real.sqrt (m : ℝ) / (Real.sqrt (m : ℝ)) ^ (2 : ℕ) := by
      rw [Real.sq_sqrt hmR.le]
    _ = (Real.sqrt (m : ℝ))⁻¹ := by field_simp [hsqrt.ne']

end

end RHTower
