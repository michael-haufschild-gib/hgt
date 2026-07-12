import GaloisForLFunctions.RHTower.XiTaylorAnisotropicMesh
import GaloisForLFunctions.RHTower.CompletedPrimeFluxFittingAttachment

/-!
# Xi logarithmic residues on the anisotropic rational mesh

The explicit `1/n` by `1/n^2` mesh approaches every target through its punctured neighborhood.
Composing this fact with the normalized Xi logarithmic-residue theorem shows that the mesh reads
the full analytic multiplicity exactly.  Together with the mesh reciprocal amplifier, this is the
source-pole input for the sublinear finite-Taylor flux criterion.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- The normalized Xi logarithmic derivative along the anisotropic rational mesh converges to the
full analytic multiplicity at the target. -/
theorem xi_normalizedLogDeriv_anisotropicMesh_tendsto (sigma : ℂ) :
    Tendsto
      (fun n : ℕ =>
        (xiTaylorAnisotropicRightApprox sigma (n + 1) - sigma) *
          logDeriv xi (xiTaylorAnisotropicRightApprox sigma (n + 1)))
      atTop (nhds ((analyticOrderAt xi sigma).toNat : ℂ)) := by
  exact (xi_normalizedLogDeriv_tendsto_order sigma).comp
    (tendsto_xiTaylorAnisotropicRightApprox_succ sigma)

end

end RHTower
