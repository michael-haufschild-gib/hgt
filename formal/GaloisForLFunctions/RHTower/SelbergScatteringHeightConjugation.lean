import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMAngularScalarEquation

/-!
# Height conjugation of the complete Eisenstein cusp source

The actual second product rule retains the vertical derivative of the full
Fourier–Bessel field. A quarter shift of its outgoing exponent has an explicit
inhomogeneous term; no spectral or modular-domain transport is inferred from
its scalar eigenvalue alone.
-/

open Complex Real Set Filter Topology
open scoped ContDiff
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open RHTower.D4BMAngularSeries
namespace RHTower.SelbergScatteringHeightConjugation
noncomputable section

/-- The actual hyperbolic product rule retains both coordinate cross terms. -/
theorem hyperbolicLaplacian_mul {f g : (Fin 2 → ℝ) → ℂ} {z : Fin 2 → ℝ}
    (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) :
    hyperbolicLaplacian (fun w => f w * g w) z =
      f z * hyperbolicLaplacian g z + hyperbolicLaplacian f z * g z +
        2 * (z 1 : ℂ)^(2 : ℕ) *
          (coordDeriv 0 f z * coordDeriv 0 g z + coordDeriv 1 f z * coordDeriv 1 g z) := by
  change (z 1 : ℂ)^(2 : ℕ) * ((ofField (fun w => f w * g w) z).second 0 0 +
    (ofField (fun w => f w * g w) z).second 1 1) = _
  rw [ofField_mul hf hg]
  simp only [ScalarTwoJet.mul, ofField, hyperbolicLaplacian]
  ring

/-- Exact conjugation by every complex height power on the positive-height chart. -/
theorem hyperbolicLaplacian_height_mul (a : ℂ) {f : (Fin 2 → ℝ) → ℂ}
    {z : Fin 2 → ℝ} (hz : 0 < z 1) (hf : ContDiffAt ℝ 2 f z) :
    hyperbolicLaplacian (fun w => (w 1 : ℂ)^a * f w) z =
      (z 1 : ℂ)^a * (hyperbolicLaplacian f z + a*(a-1)*f z +
        2*a*(z 1 : ℂ)*coordDeriv 1 f z) := by
  have hp := (height_cpow_contDiffOn a 2).contDiffAt
    ((isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz)
  have h0 : coordDeriv 0 (fun w : Fin 2 → ℝ => (w 1 : ℂ)^a) z = 0 := by
    rw [coordDeriv, (height_cpow_hasFDerivAt a z hz).fderiv]
    simp [RHTower.D4BMAngularSeries.gradient]
  have h1 : coordDeriv 1 (fun w : Fin 2 → ℝ => (w 1 : ℂ)^a) z =
      a * (z 1 : ℂ)^(a-1) := by
    rw [coordDeriv, (height_cpow_hasFDerivAt a z hz).fderiv]
    simp [RHTower.D4BMAngularSeries.gradient]
  have hpow : (z 1 : ℂ)^a = (z 1 : ℂ)^(a-1)*(z 1 : ℂ) := by
    calc
      (z 1 : ℂ)^a = (z 1 : ℂ)^((a-1)+1) := by congr 1; ring
      _ = (z 1 : ℂ)^(a-1) * (z 1 : ℂ)^(1:ℂ) :=
        Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hz.ne')
      _ = _ := by rw [Complex.cpow_one]
  rw [hyperbolicLaplacian_mul hp hf, height_cpow_hyperbolicLaplacian a z hz, h0, h1]
  rw [hpow]
  ring

/-- The original complete scalar Eisenstein cusp field, including both Weyl terms and all Fourier modes. -/
def scalarSource (u : ℂ) (z : Fin 2 → ℝ) : ℂ :=
  d4BMCompletedEisensteinCuspLeg .scalar u (z 0) (z 1)

/-- The full vertical derivative after subtracting the outgoing indicial derivative. -/
def outgoingDefect (u : ℂ) (z : Fin 2 → ℝ) : ℂ :=
  (z 1 : ℂ)*coordDeriv 1 (scalarSource u) z - (1/2-u)*scalarSource u z

/-- The literal height multiplier that shifts the outgoing exponent by minus one quarter. -/
def quarterShiftSource (u : ℂ) (z : Fin 2 → ℝ) : ℂ :=
  (z 1 : ℂ)^(-1/4 : ℂ)*scalarSource u z

/-- The complete quarter-shift equation with its exact retained first-order forcing. -/
theorem quarterShiftSource_equation (u : ℂ) (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    -hyperbolicLaplacian (quarterShiftSource u) z -
        (u+3/4)*(1/4-u)*quarterShiftSource u z =
      (1/2 : ℂ)*(z 1 : ℂ)^(-1/4 : ℂ)*outgoingDefect u z := by
  unfold quarterShiftSource
  have hf : ContDiffAt ℝ 2 (scalarSource u) z := cuspLeg_contDiffAt .scalar u 2 z hz
  rw [hyperbolicLaplacian_height_mul _ hz hf]
  have he := scalarCusp_hyperbolicLaplacian u z hz
  change hyperbolicLaplacian (scalarSource u) z = (u^(2 : ℕ)-1/4)*scalarSource u z at he
  rw [he]
  unfold outgoingDefect
  ring

end
end RHTower.SelbergScatteringHeightConjugation
