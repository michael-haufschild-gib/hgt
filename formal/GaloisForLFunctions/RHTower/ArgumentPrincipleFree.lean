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
  mechanism enters.  The target is contour integration specifically, not integration in
  general: ξ is built from `completedRiemannZeta₀`, whose definition is a Mellin integral
  over `(0, ∞)`, so the closure does contain `MeasureTheory.integral` — a real integral
  that defines the object, not a loop integral that counts its zeros.  The argument
  principle is exactly the loop integral, and that is what is absent;
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
import GaloisForLFunctions.RHTower.XiDeckCharge
import GaloisForLFunctions.RHTower.RHLadderTheory
import GaloisForLFunctions.RHTower.DictionarySign
import GaloisForLFunctions.RHTower.DeckMonomial
import GaloisForLFunctions.RHTower.DeckChargeBridge
import GaloisForLFunctions.RHTower.CarrierDeckCharge
import GaloisForLFunctions.RHTower.CarrierChargeSoftness
import GaloisForLFunctions.RHTower.HolonomyChargeBridge
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

/-- The markers of an actual loop integral, as opposed to a circle used only as a path
(`circleMap`).  A loop integral is `circleIntegral` or `intervalIntegral`. -/
def loopIntegralMarkers : List String := ["circleIntegral", "intervalIntegral"]

/-- The loop-integral constants in a dependency closure. -/
def loopIntegralHits (deps : Std.HashSet Name) : List Name :=
  deps.toList.filter fun nm =>
    loopIntegralMarkers.any fun s => (nm.toString.splitOn s).length > 1

/-- `#assert_no_loop_integral foo` builds only if `foo` evaluates no loop integral, even if
it uses the circle as a path (`circleMap` is permitted here). -/
elab "#assert_no_loop_integral" id:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverload id
  let env ← getEnv
  let deps := transitiveDeps env n
  let hs := loopIntegralHits deps
  unless hs.isEmpty do
    throwError m!"{n} depends on a loop integral: {hs}"
  logInfo m!"{n}: reads without a loop integral ({deps.size} constants scanned)"

/-- `#assert_uses_loop_integral foo` builds only if `foo` does evaluate a loop integral. -/
elab "#assert_uses_loop_integral" id:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverload id
  let env ← getEnv
  let deps := transitiveDeps env n
  if (loopIntegralHits deps).isEmpty then
    throwError m!"control failed: {n} evaluates no loop integral"
  else
    logInfo m!"control: {n} evaluates a loop integral"

/-! ## The engine

The base complex-analytic layer under every equivalence: divisibility is forced from a
root by local order arithmetic (`root_orders_dvd`), roots are unique and are assembled by
peeling and gluing (`pow_root_unique`, `exists_root_iff_orders_dvd`), the coherent tower
obstruction is the divisor (`coherentTower_iff_nonvanishing`), and the deck class glues iff
a global root exists (`deckClass_eq_one_iff_exists_root`).  None integrates. -/

#assert_integration_free root_orders_dvd
#assert_integration_free pow_root_unique
#assert_integration_free exists_root_iff_orders_dvd
#assert_integration_free coherentTower_iff_nonvanishing
#assert_integration_free nonvanishing_of_exists_roots_all_two_powers
#assert_integration_free deckClass_eq_one_iff_exists_root

/-! ## The certified surface

Every equivalence Phase B rests on, certified free of contour integration and clean of
axioms.  The list spans the half-plane root ladder, its `u`-plane (slit) form, the
coherent Kummer tower, the deck-cocycle realization (local and windowed), the deck-charge
observable, and the identifications of RH itself with each. -/

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
#assert_integration_free xiDeckCharge_eq_chart_deckClass
#assert_integration_free xiDeckCharge_pow
#assert_integration_free xiDeckCharge_succ_sq
#assert_integration_free rhLadder_iff_xiDeckCharge_one
#assert_integration_free rh_iff_xiDeckCharge
#assert_integration_free xiDeckCharge_one_eq_neg_one_pow
#assert_integration_free forall_xiDeckCharge_eq_one_iff_ne_zero
#assert_integration_free xiDeckCharge_eq_one_iff_ladderCharge_zero
#assert_integration_free carrierCharge_pow
#assert_integration_free carrierCharge_succ_sq
#assert_integration_free carrierCharge_quadruple
#assert_integration_free carrierCharge_one_eq_neg_one_pow
#assert_integration_free exists_root_iff_carrierCharge_trivial
#assert_integration_free xiDeckCharge_eq_carrierCharge
#assert_integration_free orbitQuartic_fe
#assert_integration_free orbitQuartic_conj
#assert_integration_free orbitQuartic_order_one
#assert_integration_free exists_feSchwarz_carrier_odd_charge
#assert_integration_free carrierCharge_one_eq_one_of_reflection
#assert_integration_free carrierCharge_xi_central
#assert_integration_free analyticOrderAt_dvd_of_rotation
#assert_integration_free carrierCharge_eq_one_of_rotation

/-! ## Positive controls

The spectral side of the root-trace holonomy reads the same invariant by pairing against
periodic probes on a circle; it integrates by design.  These lines must find that
integration, or the traversal above would be certifying vacuously. -/

#assert_uses_integration doubledTrace_pairing
#assert_uses_integration trace_parity_spectral_dichotomy

/-! ## The constraint → path → flow grading of the seam

The base charge, the circle-trace holonomy that reads it, and the spectral functional that
reads the same holonomy form a graded ascent, each rung machine-separated from the next:

* `carrierCharge_one_eq_neg_one_pow` — the pure-order charge: no circle path, no integral
  (certified above, contour-integration-free).
* `trace_holonomy_eq_carrierCharge_one` — the holonomy reads the charge using the circle only
  as a *path*: it is not integration-free in the strict sense (it carries `circleMap`), but it
  evaluates no loop integral.
* `doubledTrace_pairing` — the spectral reading of the same holonomy adds the loop integral.

So the charge sits at the constraint end, the loop integral at the flow end, and the holonomy
is the exact hinge between them. -/

#assert_no_loop_integral trace_holonomy_eq_carrierCharge_one
#assert_uses_loop_integral doubledTrace_pairing

end RHTower.ArgumentPrincipleFree
