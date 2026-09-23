import GaloisForLFunctions.HTGeometry.LaguerrePolyaClass
import GaloisForLFunctions.RHTower.XiSuperchargeHarnackDefect
import GaloisForLFunctions.RHTower.XiHadamardFactorization

/-!
# Laguerre--Pólya membership of the centred Xi is equivalent to RH

The corpus proves `RiemannHypothesis → LaguerrePolya Xi` for the real Laguerre--Pólya interface.
The converse direction is available for the complex class: a nonzero Laguerre--Pólya function has
only real zeros, and the centred supercharge coordinate turns that into the Riemann hypothesis.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- **Laguerre--Pólya membership of `XiC` implies RH.**  A single function-theoretic statement,
in place of the infinite ladder of leading Hankel determinants. -/
theorem riemannHypothesis_of_laguerrePolya_XiC
    (h : GaloisForLFunctions.HTGeometry.LaguerrePolya XiC) :
    RiemannHypothesis :=
  riemannHypothesis_iff_XiC_zeros_real.mpr fun _ ht =>
    im_eq_zero_of_laguerrePolya h XiC_zero_ne ht

end

end RHTower
