import GaloisForLFunctions.HTGeometry.CayleyUnitCircleReality
import GaloisForLFunctions.HTGeometry.ParaorthogonalBlaschkeRoot

/-!
# Carathéodory--Fejér finite real-zero bridge

Connes--van Suijlekom's 2025 real-zero theorem and Connes's 2026 RH survey use a
Carathéodory--Fejér mechanism at finite truncation: a positive Toeplitz section gives a
paraorthogonal polynomial with unit-circle roots, which become real spectral parameters under the
Cayley transform.

The two theorems below close that exact finite connector using the project's existing OPUC and
Cayley results.  They do not supply the continuous convolution-operator theorem or the locally
uniform convergence of the finite Weil ground-state transforms to `XiC`; those are the live
infinite-dimensional wall of the Connes route.
-/

open Complex Matrix Polynomial
open scoped ComplexOrder InnerProductSpace ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A stable paraorthogonal polynomial can vanish at a Cayley spectral parameter only when that
parameter is real. -/
theorem finiteParaorthogonal_lineCayley_root_im_eq_zero
    {p : Polynomial ℂ} {z τ : ℂ}
    (hp : p ≠ 0)
    (hroots : ∀ a ∈ p.roots, ‖a‖ < 1)
    (hτ : ‖τ‖ = 1)
    (hz : (finiteParaorthogonalPolynomial p τ).IsRoot (lineCayley z)) :
    z.im = 0 := by
  apply (norm_lineCayley_eq_one_iff_im_eq_zero z).mp
  exact finiteParaorthogonalPolynomial_isRoot_norm_eq_one hp hroots hτ hz

/-- **Finite Carathéodory--Fejér real-zero theorem in OPUC coordinates.**  Every Cayley spectral
root of the paraorthogonal terminal attached to a positive-definite Toeplitz section is real. -/
theorem finiteOPUCParaorthogonal_lineCayley_root_im_eq_zero
    {N : ℕ} (c : ℤ → ℂ) (hG : (circleToeplitzGram N c).PosDef)
    {τ z : ℂ} (hτ : ‖τ‖ = 1)
    (hz : (finiteParaorthogonalPolynomial (finiteOPUCPolynomial c hG) τ).IsRoot
      (lineCayley z)) :
    z.im = 0 := by
  apply (norm_lineCayley_eq_one_iff_im_eq_zero z).mp
  exact finiteOPUCParaorthogonalPolynomial_isRoot_norm_eq_one c hG hτ hz

end

end GaloisForLFunctions.HTGeometry
