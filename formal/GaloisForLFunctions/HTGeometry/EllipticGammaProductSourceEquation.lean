import GaloisForLFunctions.HTGeometry.EllipticGammaProduct
import GaloisForLFunctions.HTGeometry.EllipticGammaAdditiveLogKernel

/-!
# Factorwise multiplicative source equations for the elliptic-gamma product

The period-one product identity is proved exactly.  For each structural period, every factor on
the zero face and successor face is identified with the corresponding one-dimensional boundary
factor or unshifted double-product factor.  These are the unconditional reindexing identities used
by the paper proof of the full infinite-product source equations.  The whole-product reindexing is
kept out of this module because fresh compilation of Mathlib's two-dimensional `tprod` Fubini
conversion is prohibitively expensive in the shared build.
-/

open Complex Set Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

/-! ## First structural period -/

def ellipticGammaForwardBoundaryFactor (tau : ℂ) (k : ℕ) (z : ℂ) : ℂ :=
  1 - ellipticNome tau ^ (k + 1) / ellipticThetaCoordinate tau z

theorem ellipticGammaForwardFactor_add_sigma_zero
    (sigma tau z : ℂ) (k : ℕ) :
    ellipticGammaForwardFactor sigma tau (0, k) (z + sigma) =
      ellipticGammaForwardBoundaryFactor tau k z := by
  rw [ellipticGammaForwardFactor, ellipticGammaForwardBoundaryFactor,
    ellipticThetaCoordinate_add]
  rw [ellipticGammaForwardArgument_mul_p_zero
    (ellipticNome_ne_zero sigma) (ellipticThetaCoordinate_ne_zero tau z)]

theorem ellipticGammaForwardFactor_add_sigma_succ
    (sigma tau z : ℂ) (j k : ℕ) :
    ellipticGammaForwardFactor sigma tau (j + 1, k) (z + sigma) =
      ellipticGammaForwardFactor sigma tau (j, k) z := by
  rw [ellipticGammaForwardFactor, ellipticGammaForwardFactor,
    ellipticThetaCoordinate_add]
  rw [ellipticGammaForwardArgument_mul_p_succ
    (ellipticNome_ne_zero sigma) (ellipticThetaCoordinate_ne_zero tau z)]

def ellipticGammaBackwardBoundaryFactor (tau : ℂ) (k : ℕ) (z : ℂ) : ℂ :=
  1 - ellipticNome tau ^ k * ellipticThetaCoordinate tau z

theorem ellipticGammaBackwardFactor_zero
    (sigma tau z : ℂ) (k : ℕ) :
    ellipticGammaBackwardFactor sigma tau (0, k) z =
      ellipticGammaBackwardBoundaryFactor tau k z := by
  simp [ellipticGammaBackwardFactor, ellipticGammaBackwardBoundaryFactor,
    ellipticGammaBackwardArgument]

theorem ellipticGammaBackwardFactor_add_sigma
    (sigma tau z : ℂ) (j k : ℕ) :
    ellipticGammaBackwardFactor sigma tau (j, k) (z + sigma) =
      ellipticGammaBackwardFactor sigma tau (j + 1, k) z := by
  rw [ellipticGammaBackwardFactor, ellipticGammaBackwardFactor,
    ellipticThetaCoordinate_add]
  rw [ellipticGammaBackwardArgument_mul_p]

def ellipticGammaMultiplicativeThetaBoundary (tau z : ℂ) : ℂ :=
  (∏' k : ℕ, ellipticGammaForwardBoundaryFactor tau k z) *
    ∏' k : ℕ, ellipticGammaBackwardBoundaryFactor tau k z

/-! ## Second structural period -/

def ellipticGammaTauForwardBoundaryFactor (sigma tau : ℂ) (j : ℕ) (z : ℂ) : ℂ :=
  1 - ellipticNome sigma ^ (j + 1) / ellipticThetaCoordinate tau z

def ellipticGammaTauBackwardBoundaryFactor (sigma tau : ℂ) (j : ℕ) (z : ℂ) : ℂ :=
  1 - ellipticNome sigma ^ j * ellipticThetaCoordinate tau z

theorem ellipticGammaForwardFactor_add_tau_zero
    (sigma tau z : ℂ) (j : ℕ) :
    ellipticGammaForwardFactor sigma tau (j, 0) (z + tau) =
      ellipticGammaTauForwardBoundaryFactor sigma tau j z := by
  rw [ellipticGammaForwardFactor, ellipticGammaTauForwardBoundaryFactor,
    ellipticThetaCoordinate_add]
  rw [ellipticGammaForwardArgument_mul_q_zero
    (ellipticNome_ne_zero tau) (ellipticThetaCoordinate_ne_zero tau z)]

theorem ellipticGammaForwardFactor_add_tau_succ
    (sigma tau z : ℂ) (j k : ℕ) :
    ellipticGammaForwardFactor sigma tau (j, k + 1) (z + tau) =
      ellipticGammaForwardFactor sigma tau (j, k) z := by
  rw [ellipticGammaForwardFactor, ellipticGammaForwardFactor,
    ellipticThetaCoordinate_add]
  rw [ellipticGammaForwardArgument_mul_q_succ
    (ellipticNome_ne_zero tau) (ellipticThetaCoordinate_ne_zero tau z)]

theorem ellipticGammaBackwardFactor_add_tau
    (sigma tau z : ℂ) (j k : ℕ) :
    ellipticGammaBackwardFactor sigma tau (j, k) (z + tau) =
      ellipticGammaBackwardFactor sigma tau (j, k + 1) z := by
  rw [ellipticGammaBackwardFactor, ellipticGammaBackwardFactor,
    ellipticThetaCoordinate_add]
  rw [ellipticGammaBackwardArgument_mul_q]

theorem ellipticGammaBackwardFactor_tau_zero
    (sigma tau z : ℂ) (j : ℕ) :
    ellipticGammaBackwardFactor sigma tau (j, 0) z =
      ellipticGammaTauBackwardBoundaryFactor sigma tau j z := by
  simp [ellipticGammaBackwardFactor, ellipticGammaTauBackwardBoundaryFactor,
    ellipticGammaBackwardArgument]

def ellipticGammaMultiplicativeThetaBoundaryTau (sigma tau z : ℂ) : ℂ :=
  (∏' j : ℕ, ellipticGammaTauForwardBoundaryFactor sigma tau j z) *
    ∏' j : ℕ, ellipticGammaTauBackwardBoundaryFactor sigma tau j z

/-! ## Exact period-one law -/

theorem ellipticGammaForwardProduct_add_one (sigma tau z : ℂ) :
    ellipticGammaForwardProduct sigma tau (z + 1) =
      ellipticGammaForwardProduct sigma tau z := by
  rw [ellipticGammaForwardProduct, ellipticGammaForwardProduct]
  apply tprod_congr
  intro jk
  rw [ellipticGammaForwardFactor, ellipticGammaForwardFactor,
    ellipticThetaCoordinate_add_one]

theorem ellipticGammaBackwardProduct_add_one (sigma tau z : ℂ) :
    ellipticGammaBackwardProduct sigma tau (z + 1) =
      ellipticGammaBackwardProduct sigma tau z := by
  rw [ellipticGammaBackwardProduct, ellipticGammaBackwardProduct]
  apply tprod_congr
  intro jk
  rw [ellipticGammaBackwardFactor, ellipticGammaBackwardFactor,
    ellipticThetaCoordinate_add_one]

theorem ellipticGammaProduct_add_one (sigma tau z : ℂ) :
    ellipticGammaProduct sigma tau (z + 1) =
      ellipticGammaProduct sigma tau z := by
  rw [ellipticGammaProduct, ellipticGammaProduct,
    ellipticGammaForwardProduct_add_one,
    ellipticGammaBackwardProduct_add_one]

end

end GaloisForLFunctions
