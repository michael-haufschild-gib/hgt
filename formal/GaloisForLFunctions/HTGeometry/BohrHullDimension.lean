import GaloisForLFunctions.HTGeometry.CoveringDimensionEmbedding
import GaloisForLFunctions.HTGeometry.BohrTorusQuotientHom

/-!
# The dimension of the phase carrier

The Bohr hull is compact, so any continuous injection of it into a Hausdorff space is a
homeomorphism onto its image: a dimension bound for the image is a dimension bound for the carrier.

This is the interface through which the finite-phase law consumes a jet embedding — the carrier
inherits the covering dimension of the jet image, and the frequency rank is then read off the
carrier.
-/

open Set

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

noncomputable section

variable {f : ℝ →ᵇ ℂ}

/-- **A jet-type embedding bounds the covering dimension of the phase carrier.** -/
theorem hasCoverDimLE_bohrHull_of_injection (htb : HasTotallyBoundedOrbit (fun x => f x))
    {Y : Type} [TopologicalSpace Y] [T2Space Y] {n : ℕ} {φ : BohrHull f → Y}
    (hcont : Continuous φ) (hinj : Function.Injective φ)
    (hdim : HasCoverDimLE (Set.range φ) n) : HasCoverDimLE (BohrHull f) n := by
  haveI : CompactSpace (BohrHull f) := compactSpace_bohrHull htb
  intro ι _ U hU hcov
  exact hasCoverDimLE_of_continuous_injective hcont hinj hdim U hU hcov

end

end GaloisForLFunctions
