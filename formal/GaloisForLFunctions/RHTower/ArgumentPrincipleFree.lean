/-
# The RH ladder is proved without contour integration — a machine-checked certificate

The classical route from "every off-line ξ-zero has order divisible by `2^k`" to
"ξ has an analytic `2^k`-th root" runs through the argument principle: one counts the
enclosed zeros by integrating the logarithmic derivative around a contour,
`(2πi)⁻¹ ∮ f'/f`, and reads the monodromy of the root off that count.  That count is a
*flow* — a quantity accumulated by transporting a phase around a loop.

The ladder developed here is proved from a *constraint* instead: the `2^k`-th-root
branches are fixed algebraically on two slit charts, and their monodromy `exp(2πi·m/n)`
is read off the explicit jump `log I − log(−I) = 2πi` of the principal logarithm across
the slit (`deckClass_monomial`), with no loop transported and no integral evaluated.
Divisibility of orders is forced locally by `analyticOrderAt_pow`
(`root_orders_dvd`), and roots are assembled by peeling `(z−ρ)^m`, taking the
nonvanishing branch on a simply connected chart, and gluing by rigidity
(`exists_root_iff_orders_dvd`).  Every step is a pointwise algebraic identity; none
integrates.

This file turns that claim into a build gate.  For a named declaration it walks the
whole transitive constant-dependency closure of its proof term (value and type) and
verifies:

* the closure contains **no** contour-integration constant — nothing whose name carries
  `circleIntegral`, `circleMap`, or `intervalIntegral`; a contour integral in mathlib is
  always one of these, so their joint absence certifies that no argument-principle
  mechanism enters;
* the closure introduces **no** axiom beyond the three mathlib always allows
  (`propext`, `Classical.choice`, `Quot.sound`) — in particular no `sorryAx`.

Both checks share one traversal.  A violation raises an elaboration error, so the check
is enforced whenever the file is built.  The certificate is self-validating: the two
`#assert_uses_integration` lines are positive controls on the spectral holonomy readings,
which *do* integrate; were the traversal blind to integration those lines would raise,
so their success witnesses that the traversal genuinely detects contour integration
where it is present.
-/
import GaloisForLFunctions.RHTower.DeckWindow
import GaloisForLFunctions.RHTower.SquareLadder
import GaloisForLFunctions.RHTower.XiDeck
import GaloisForLFunctions.RHTower.RHLadderTheory
import GaloisForLFunctions.RHTower.DictionarySign
import GaloisForLFunctions.RHTower.DeckMonomial
import GaloisForLFunctions.RHTower.RootTraceHolonomy

open Lean Elab Command Meta

namespace RHTower.ArgumentPrincipleFree

/-- Fuel-bounded transitive constant-dependency closure of a declaration, over both its
type and its value.  The fuel bound makes the traversal structurally terminating; it is
set far above the number of edges in any mathlib dependency graph reached here, so the
worklist empties long before the fuel does. -/
def collect (env : Environment) : Nat → Std.HashSet Name → List Name → Std.HashSet Name
  | 0, seen, _ => seen
  | _ + 1, seen, [] => seen
  | fuel + 1, seen, n :: rest =>
    if seen.contains n then
      collect env fuel seen rest
    else
      let seen := seen.insert n
      let more : List Name :=
        match env.find? n with
        | none => []
        | some ci =>
          ci.type.getUsedConstants.toList ++
            ((ci.value?.map fun e => e.getUsedConstants.toList).getD [])
      collect env fuel seen (more ++ rest)

/-- The transitive constant-dependency closure of `start`. -/
def transitiveDeps (env : Environment) (start : Name) : Std.HashSet Name :=
  collect env 20000000 {} [start]

/-- The name fragments that mark a contour integral in mathlib.  Every contour integral
unfolds to `intervalIntegral` of a function of `circleMap`; `circleIntegral` is the
packaged form.  The argument principle needs at least one of these. -/
def contourMarkers : List String := ["circleIntegral", "circleMap", "intervalIntegral"]

/-- The contour-integration constants appearing in a dependency closure. -/
def contourHits (deps : Std.HashSet Name) : List Name :=
  deps.toList.filter fun nm =>
    contourMarkers.any fun s => (nm.toString.splitOn s).length > 1

/-- The three axioms mathlib admits everywhere. -/
def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Any axiom in a dependency closure other than the three standard ones. -/
def extraAxioms (env : Environment) (deps : Std.HashSet Name) : List Name :=
  deps.toList.filter fun nm =>
    match env.find? nm with
    | some (.axiomInfo _) => !standardAxioms.contains nm
    | _ => false

/-- `#assert_integration_free foo` builds only if the proof term of `foo` contains no
contour-integration constant and introduces no non-standard axiom. -/
elab "#assert_integration_free" id:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverload id
  let env ← getEnv
  let deps := transitiveDeps env n
  let ax := extraAxioms env deps
  unless ax.isEmpty do
    throwError m!"{n} depends on non-standard axioms: {ax}"
  let hs := contourHits deps
  unless hs.isEmpty do
    throwError m!"{n} depends on contour-integration constants: {hs}"
  logInfo m!"{n}: contour-integration-free and axiom-clean ({deps.size} constants scanned)"

/-- `#assert_uses_integration foo` builds only if the proof term of `foo` *does* use a
contour integral — a positive control witnessing that the traversal is live. -/
elab "#assert_uses_integration" id:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverload id
  let env ← getEnv
  let deps := transitiveDeps env n
  let hs := contourHits deps
  if hs.isEmpty then
    throwError m!"control failed: {n} uses no contour integration, so the traversal is not live"
  else
    logInfo m!"control: {n} does use contour integration {hs}"

/-! ## The certified surface

Every equivalence Phase B rests on, certified free of contour integration and clean of
axioms.  The list spans the half-plane root ladder, its `u`-plane (slit) form, the
coherent Kummer tower, the deck-cocycle realization (local and windowed), and the
identifications of RH itself with each. -/

#assert_integration_free rh_iff_xi_ne_zero_right
#assert_integration_free rhLadder_iff_root
#assert_integration_free rhLadder_one_iff_sqrt_rightHalf
#assert_integration_free rh_iff_forall_ladder
#assert_integration_free rh_iff_tower
#assert_integration_free rh_iff_exists_roots_all_two_powers
#assert_integration_free rhLadder_iff_root_slitPlane
#assert_integration_free rh_iff_forall_root_slitPlane
#assert_integration_free rh_iff_xiDescent_coherentTower_slitPlane
#assert_integration_free xi_deckClass
#assert_integration_free xi_deckClass_eq_one_iff_ladder_dvd
#assert_integration_free deckClass_monomial
#assert_integration_free xi_deckClass_eq_sign_product
#assert_integration_free rhLadder_iff_forall_deck_trivial
#assert_integration_free rh_iff_forall_deck_trivial

/-! ## Positive controls

The spectral side of the root-trace holonomy reads the same invariant by pairing against
periodic probes on a circle; it integrates by design.  These lines must find that
integration, or the traversal above would be certifying vacuously. -/

#assert_uses_integration doubledTrace_pairing
#assert_uses_integration trace_parity_spectral_dichotomy

end RHTower.ArgumentPrincipleFree
