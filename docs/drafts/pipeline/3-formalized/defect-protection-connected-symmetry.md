# Defect protection of the weld: the connected-symmetry verdict and the RH cut

- **ID:** defect-protection
- **Stage:** 3-formalized (moved 2026-07-12; §E conjecture live)
- **Type:** THEOREM (paper→Lean) for §A–§D; CONJECTURE for §E
- **Source:** connected-symmetry-of-the-weld conjecture (session 2026-07-08); GoldilocksTrichotomy / ChargeMotion residue ("the seam input conservation lacks")
- **Statement:** No connected symmetry of the weld can mix deck classes; the surviving invariant is π₀ of the constraint pair space, RH is the emptiness of its protected right-half defects, and the softness/rigidity boundary of the constraint lattice (the RH cut) lies strictly above every multiplication-stable constraint.

## Goal

Exhaust the conjecture: *"There is a connected symmetry of the weld — a continuous deformation of
the completed object fixing the constraint set — whose orbit map surjects onto the deck classes;
connectedness would be the conservation law the Goldilocks cell lacks."*

Verdict established here: **FALSE as a mechanism, and the failure is a theorem.** What survives is a
relocation (the pair-space π₀) and a new lattice invariant (the RH cut), both native to the branch:
constraint-side objects, no carrier, no flow, no spectrum.

## §A [PROVED HERE] Connected-symmetry collapse (the conjecture's refutation)

Let `G` be any preconnected topological space (in particular any connected topological group), and
let `Φ : G × ℝ → ℂ` be jointly continuous with each `Φ g` a nonvanishing loop — the value of the
`g`-deformed member on the `g`-transported window boundary. Then `g ↦ loopCharge k (Φ g)` is
**constant** on `G`.

Consequences:
- **No surjectivity.** An orbit map from a connected `G` cannot realize two distinct deck classes.
  The conjecture's two demands (connected + surjects onto classes) are jointly unsatisfiable —
  for every `G`, every action, every window transport. Unconditional.
- **Group elimination.** Any connected-symmetry mechanism factors through the components of the
  underlying pair space; the group contributes nothing beyond the topology of the constraint space
  itself. The conjecture's "conservation law" was never about a group.
- **Solenoid subtlety.** The natural symmetry of the 2-tower is the dyadic solenoid — connected but
  NOT path-connected. The proof must therefore be open–closed (local domination), not path-lifting;
  the theorem then covers exactly the solenoidal deformations the tower suggests. A path-only
  version would have left the tower's own symmetry outside the barrier.

Mechanism: on the compact angle interval, joint continuity gives a uniform domination neighbourhood
(`‖Φ g' − Φ g‖ < min ‖Φ g‖` on the loop); dominated nonvanishing loops are linearly homotopic
through nonvanishing loops, so the winding is locally constant; `ZMod 2^k` is discrete and `G`
preconnected, hence constant.

## §B [PROVED HERE] Moving-window conservation

The banked `boxCharge_conserved` deforms the member over a *fixed* circle. The pair version: along
any jointly continuous path `t ↦ (f_t, c_t, r_t)` with `f_t` nonvanishing on the moving circle
`∂B(c_t, r_t)`, the box charge is constant. (Corollary of `windingNumber_of_homotopic` applied to
`H(t,θ) = f_t(c_t + r_t e^{iθ})`.) This is the conservation law on the **pair space**
`𝒫 = {(f, window) : ∂-nonvanishing}` — the object §A relocates everything onto.

## §C [PROVED HERE] The π₀ relocation, the RH surface, and completeness

The level-`k` charge is a locally constant function on `𝒫`, hence a function on π₀(𝒫). A pair is
**vacuum** if its member is nonvanishing on the closed window. Then:

> **RH ⟺ no hypothetical right-half ξ-defect pair is joined in 𝒫 to a vacuum pair.**
> (`rh_iff_no_protected_defect` — the certificate is LEVEL-FREE: one deformation to vacuum kills
> every dyadic level at once, because the same path conserves the charge at all `k`.)

Forward direction is emptiness (RH leaves no right-half defect); backward is §B conservation plus
the isolating-window reading `boxCharge = ord mod 2^k` and all-`k` divisibility forcing `ord = 0`.

**Completeness (the h-principle half), also proven:** the charge is not merely conserved — it is a
COMPLETE deformation invariant. Two nonvanishing loops are joined through nonvanishing loops iff
their winding numbers agree (`windingNumber_eq_iff_joined`, via linear interpolation of canonical
logarithms; equal increments `2πi·w` keep every intermediate curve a loop). So π₀ of the
nonvanishing loop space IS ℤ, the level-`k` charge is its reduction mod `2^k`, and nothing finer
than the charge obstructs deformation. The conjecture's phrase "no π₀-obstruction" is now a fully
classified object: protection ⟺ nonzero winding, and RH ⟺ no protected right-half ξ-defect.
No carrier, no flow: 𝒫 is fixed by its defining constraint (boundary nonvanishing), and RH is
which of its components contain ξ.

## §D [PROVED HERE] Multiplicative softness and the lattice squeeze

Order the constraint classes `𝒞 ⊆ (ℂ → ℂ)` by inclusion; the realized-charge set is monotone.
The two Goldilocks endpoints become instances of one law:

> **Softness metatheorem.** Any class closed under multiplication by the V₄-orbit quartic
> `orbitQuartic ρ₀` that has a member analytic and nonvanishing at `ρ₀` carries nontrivial charge
> at `ρ₀`; if this holds at every off-line off-real point, the class is soft (`PlantsArbitrary`).

Corollaries: `FESchwarz` soft (recovers the banked witness); every polynomial-multiplication-stable
class containing ξ (Hadamard-type growth classes included — polynomial × order-1 is order-1) fails
`ForcesRHParity`. Hence:

> **The RH cut** — the softness/rigidity boundary in the constraint lattice — **lies strictly above
> every multiplication-stable constraint.** A constraint that decides parity must break stability
> under polynomial multiplication, i.e. must couple to the coefficient/arithmetic side. The banked
> `dirichlet_surgery_rigid` shows the Dirichlet-series constraint does exactly that: the cut is
> squeezed into (mult-stable, Dirichlet-series].

This answers the conjecture's motivating question ("the conservation law the Goldilocks cell
lacks") negatively for an entire lattice region at once: no conservation law readable below
multiplicativity-coupling can decide the parity — matching, from a new axis, the invariant-collision
barrier of `DeciderBarrier`.

**The two ends of the lattice meet (`forcesRHParity_xiScalarClass_iff_rhLadder_one`, proved):**
parity-forcing of the rigid endpoint — the ξ-scalar class `{c·ξ : c ∈ ℝ}` — is EXACTLY the base
rung `RHLadder 1`. Left-half points transport by the FE/reality order pairings; scalars do not
move orders.

**No class-level shortcut (`rhLadder_one_of_forcesRHParity`, proved):** ANY parity-forcing class
containing ξ certifies the base rung, because forcing instantiates at ξ itself.

**Ladder-uniform (`rhLadder_of_forces_charge_level`,
`exists_nontrivial_charge_level_of_orbitQuartic_stable`, proved):** the collapse is not a parity
accident — at EVERY positive level `k`, a class-level `2^k`-charge law containing ξ certifies rung
`k` directly, and one quartic multiplication defeats the law on any mult-stable class
(consecutive orders are never both `2^k`-divisible). The conjecture's "deck classes" are covered
at all dyadic levels simultaneously. So the class-level
parity-law spectrum is fully mapped by three theorems: below multiplication stability forcing is
impossible; wherever forcing holds around ξ it was the rung all along; and at the rigid endpoint
it is the rung exactly. **The conservation law the Goldilocks cell "lacks" does not exist as a
class property** — it can only be an ξ-specific mechanism producing even orders, i.e. a rung
mechanism. Hamburger rigidity `[KNOWN]` confirms the collapse already at "Dirichlet series + exact
ξ-FE + regularity": that class IS the completed `{c·ζ}`, so its parity-forcing is again the rung,
not a new law.

## §E [CONJECTURE / OPEN] The cut sits at the Euler product

Three independent planting engines are now on the table, each defeating a different constraint
family:
1. **bump surgery** (banked, `PerturbationZero`) — defeats FE + Schwarz at Weyl regularity;
2. **quartic multiplication** (§D, proven) — defeats every multiplication-stable class;
3. **pencil surgery** `[CONJECTURE]` — real combinations of two FE-sharing Dirichlet series vanish
   at any prescribed point (one linear condition), so even the FE + Dirichlet-series class (no
   Euler product) stays soft; `[KNOWN, paper register]` Davenport–Heilbronn exhibits exactly such
   off-line charge, so this class certainly carries charge and is not categorical.

The banked `dirichlet_surgery_rigid` blocks only engine 2 for the Dirichlet class — it does NOT
classify that class as parity-forcing, since engine 3 survives. The only known constraint dodging
all three engines at once is **coefficient multiplicativity — the Euler product**: a polynomial or
pencil combination of Euler products is no Euler product, and a bump is no Dirichlet series.

> `[CONJECTURE]` **The RH cut is pinned at the Euler product**: the minimal constraint (over the
> FE + Schwarz base) that empties the nontrivial right-half defect components is multiplicativity
> of the coefficients — the arithmetic pillar of the weld, exactly the constraint-side object the
> branch's founding metaphor points at. Every constraint below it is soft by one of the three
> engines.

**On `SignedReflectionParity`:** the seam conservation law named (but nowhere defined) by
`GoldilocksTrichotomy` and `ChargeMotion` as "what the Goldilocks cell still needs" is now
bounded by §D: if it is expressible on any multiplication-stable class, it cannot decide the
parity. The candidate must be anchored to the Euler side. Successor work: define it there or
retire the name.

## Gates
- [x] 0 → 1  in-progress: well-posed; refutation mechanism identified; Lean plan drawn
- [x] 1 → 2  fully-proven: §A–§D paper-complete, proofs carried by the Lean below
- [x] 2 → 3  formalized: `ConnectedSymmetryBarrier.lean`, `MultiplicativeSoftness.lean` compile
      green in the umbrella; all ten capstones axiom-clean (`propext, Classical.choice,
      Quot.sound` only): `windingNumber_eq_of_close`, `windingNumber_const_of_preconnected`,
      `loopCharge_const_of_preconnected`, `not_surjective_loopCharge_of_preconnected`,
      `boxCharge_const_of_preconnected`, `boxCharge_conserved_moving`,
      `boxCharge_eq_zero_of_vacuum`, `joined_of_windingNumber_eq`,
      `windingNumber_eq_iff_joined`, `rh_iff_no_protected_defect`; plus
      `analyticOrderAt_orbitQuartic_mul`, `carrierCharge_one_orbitQuartic_mul`,
      `carriesChargeAt_of_orbitQuartic_stable`, `isSoft_of_orbitQuartic_stable`,
      `not_forcesRHParity_of_orbitQuartic_stable`,
      `not_forcesRHParity_of_xi_orbitQuartic_stable`, `carriesChargeAt_mono`,
      `forcesRHParity_anti`, `forcesRHParity_xiScalarClass_iff_rhLadder_one`,
      `rhLadder_one_of_forcesRHParity`
- [ ] 3 → 4  publication-ready

## Approach
Reuse, never rebuild: `boxCharge`, `loopCharge`, `windingNumber_of_homotopic` (WindingHomotopy),
`orbitQuartic_*` (CarrierChargeSoftness), Goldilocks predicates, `xi` factorization lemmas.
New Lean: dominated-loop winding equality; moving-pair conservation; preconnected-parameter
constancy; no-surjectivity corollary; RH surface; softness metatheorem + instances + squeeze.

## Log
- 2026-07-08 — created directly in 1-in-progress; conjecture refuted on paper (§A), relocation and
  cut identified; Lean formalization started. Session seed 305775574337410514; rng move: monotone
  (→ the lattice ordering of §D).

## 2026-07-12 Stage move

Axiom audit re-confirmed on this toolchain: `rh_iff_no_protected_defect` depends only on
`propext, Classical.choice, Quot.sound`. All gates through 2 → 3 are checked (see above); the
card moves to `3-formalized`. The §E successor (`[CONJECTURE]` the RH cut is pinned at the Euler
product) stays live inside this card; its resolution — defining `SignedReflectionParity` on the
Euler side or retiring the name — is the named forward move.
