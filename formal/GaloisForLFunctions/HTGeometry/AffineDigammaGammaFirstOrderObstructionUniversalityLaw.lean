import GaloisForLFunctions.HTGeometry.DigammaGammaFirstOrder
import GaloisForLFunctions.HTGeometry.ExactDifferentialOrderAffine

/-!
# Affine digamma-after-Gamma first-order obstruction

The reciprocal-Gamma pole clusters exclude every differential equation of order at most one for
`digamma ∘ Gamma`.  Fixed-order differential algebraicity is invariant under every invertible
affine change of the independent variable, so the obstruction is an affine-orbit law.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- **Affine digamma-after-Gamma first-order obstruction universality law.**  Every nondegenerate
affine reparametrization of `digamma ∘ Gamma` satisfies no algebraic differential equation of order
at most one with complex polynomial coefficients. -/
theorem not_differentiallyAlgebraicOfOrder_one_digamma_comp_Gamma_affine
    {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    ¬ DifferentiallyAlgebraicOfOrder
      (fun z : ℂ => Complex.digamma (Complex.Gamma (a * z + b))) 1 := by
  intro haffine
  have htranslated : DifferentiallyAlgebraicOfOrder
      (fun w : ℂ => Complex.digamma (Complex.Gamma (w + b))) 1 :=
    (differentiallyAlgebraicOfOrder_comp_const_mul_iff_uncond ha).mp haffine
  have hbase : DifferentiallyAlgebraicOfOrder
      (fun z : ℂ => Complex.digamma (Complex.Gamma z)) 1 :=
    (differentiallyAlgebraicOfOrder_comp_add_const_iff b).mp htranslated
  exact not_differentiallyAlgebraicOfOrder_one_digamma_comp_Gamma hbase

end

end GaloisForLFunctions.HTGeometry
