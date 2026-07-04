/-
# RHTower — the ξ-Kummer tower and the RH_{2^k} multiplicity-parity ladder

Umbrella for the MWM lane's Arc A (docs/drafts/rh-monodromy-weight-mismatch/):

* `KummerObstruction` — roots force order divisibility; root rigidity; convex ⟹ simply
  connected.
* `Peeling` — global single-zero factorisation `f = (·-ρ)^m · h`.
* `RootExistence` — `exists_root_iff_orders_dvd`: analytic `n`-th roots exist iff every
  vanishing order is divisible by `n` (convex exhaustion + gluing).
* `CoherentTower` — the ℤ₂-Kummer tower; existence ⟺ nonvanishing.
* `RiemannTower` — the entire completed `xi`, the ladder `RHLadder k`, and the capstones
  `rh_iff_xi_ne_zero_right`, `rhLadder_iff_root`, `rh_iff_tower`, `rh_iff_forall_ladder`
  against mathlib's `RiemannHypothesis`.
-/
import GaloisForLFunctions.RHTower.KummerObstruction
import GaloisForLFunctions.RHTower.Peeling
import GaloisForLFunctions.RHTower.RootExistence
import GaloisForLFunctions.RHTower.CoherentTower
import GaloisForLFunctions.RHTower.RiemannTower
import GaloisForLFunctions.RHTower.Reflection
import GaloisForLFunctions.RHTower.DirichletRigidity
import GaloisForLFunctions.RHTower.LogIndependence
import GaloisForLFunctions.RHTower.PerturbationZero
import GaloisForLFunctions.RHTower.DeckCocycle
import GaloisForLFunctions.RHTower.DeckMonomial
import GaloisForLFunctions.RHTower.DeckAssembly
import GaloisForLFunctions.RHTower.DeckMultiZero
import GaloisForLFunctions.RHTower.XiDeck
import GaloisForLFunctions.RHTower.DeckHomotopy
import GaloisForLFunctions.RHTower.FarFieldAnchor
import GaloisForLFunctions.RHTower.ReflectionParity
import GaloisForLFunctions.RHTower.UPlaneDescent
import GaloisForLFunctions.RHTower.LedgerJump
import GaloisForLFunctions.RHTower.SeamCocycle
import GaloisForLFunctions.RHTower.ModulusHolography
import GaloisForLFunctions.RHTower.MirrorPencil
import GaloisForLFunctions.RHTower.CountingSubstitute
import GaloisForLFunctions.RHTower.WindowRelation
import GaloisForLFunctions.RHTower.SquareLadder
import GaloisForLFunctions.RHTower.GermExtension
import GaloisForLFunctions.RHTower.SpurHermite
import GaloisForLFunctions.RHTower.SpurRescale
import GaloisForLFunctions.RHTower.PolynomialTruncation
import GaloisForLFunctions.RHTower.SpurCumulant
import GaloisForLFunctions.RHTower.SpurCumulantBounds
import GaloisForLFunctions.RHTower.SpurEnvelope
import GaloisForLFunctions.RHTower.SpurClearance
import GaloisForLFunctions.RHTower.SpurOperator
import GaloisForLFunctions.RHTower.SpurStability
import GaloisForLFunctions.RHTower.SpurNoGo
import GaloisForLFunctions.RHTower.SeamTransport
import GaloisForLFunctions.RHTower.SpurWeights
import GaloisForLFunctions.RHTower.SpurCounting
import GaloisForLFunctions.RHTower.DictionaryBase
import GaloisForLFunctions.RHTower.DictionarySign
import GaloisForLFunctions.RHTower.LedgerIdentity
import GaloisForLFunctions.RHTower.LedgerConvex
