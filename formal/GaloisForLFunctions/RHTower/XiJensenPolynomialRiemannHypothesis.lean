import GaloisForLFunctions.RHTower.XiLaguerrePolyaRiemannHypothesis
import GaloisForLFunctions.HTGeometry.LaguerrePolyaJensenConverse
import GaloisForLFunctions.HTGeometry.RealTaylorCoefficients

/-!
# Hyperbolicity of every Jensen polynomial of the centred Xi implies RH

Jensen's converse turns splitting of all Jensen polynomials of a Schwarz-real entire function into
Laguerre--Pólya membership, and a Laguerre--Pólya function has only real zeros.  In the centred
supercharge coordinate that is exactly the Riemann hypothesis.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

theorem differentiable_XiC : Differentiable ℂ XiC := fun z =>
  (XiC_analytic z (Set.mem_univ z)).differentiableAt

/-- **RH from hyperbolicity of the Jensen polynomials of `XiC`.**  A single classical criterion in
place of the infinite ladder of leading Hankel determinants. -/
theorem riemannHypothesis_of_splits_jensenPoly_XiC
    (h : ∀ d, (jensenPoly (realTaylorCoeff XiC) d).Splits) :
    RiemannHypothesis :=
  riemannHypothesis_of_laguerrePolya_XiC
    (laguerrePolya_of_splits_jensenPoly
      (fun z => hasSum_realTaylorCoeff differentiable_XiC (fun w => XiC_conj w) z) h)

end

end RHTower
