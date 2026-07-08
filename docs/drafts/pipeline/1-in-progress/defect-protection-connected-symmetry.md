# Defect protection of the weld: the connected-symmetry verdict and the RH cut

- **ID:** defect-protection
- **Stage:** 1-in-progress
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

## §A [THEOREM] Connected-symmetry collapse (the conjecture's refutation)

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

## §B [THEOREM] Moving-window conservation

The banked `boxCharge_conserved` deforms the member over a *fixed* circle. The pair version: along
any jointly continuous path `t ↦ (f_t, c_t, r_t)` with `f_t` nonvanishing on the moving circle
`∂B(c_t, r_t)`, the box charge is constant. (Corollary of `windingNumber_of_homotopic` applied to
`H(t,θ) = f_t(c_t + r_t e^{iθ})`.) This is the conservation law on the **pair space**
`𝒫 = {(f, window) : ∂-nonvanishing}` — the object §A relocates everything onto.

## §C [THEOREM] The π₀ relocation and the RH surface

The level-`k` charge is a locally constant function on `𝒫`, hence a function on π₀(𝒫). A pair is
**vacuum** if its member is nonvanishing on the closed window. Then:

> **RH ⟺ for every k, no hypothetical right-half ξ-defect pair is joined in 𝒫 to a vacuum pair
> — equivalently, every right-half ξ-window pair of every level is unprotected-or-absent.**

Forward direction is emptiness (RH leaves no right-half defect); backward is §B conservation plus
the isolating-window reading `boxCharge = ord mod 2^k` and all-`k` divisibility forcing `ord = 0`.
The conjecture's corrected form — "no π₀-obstruction" — is thus **provably equivalent to RH**, and
the open content is relocated onto a topological emptiness statement about one constraint space.
No carrier, no flow: 𝒫 is fixed by its defining constraint (boundary nonvanishing), and RH is
which of its components contain ξ.

## §D [THEOREM] Multiplicative softness and the lattice squeeze

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

## §E [CONJECTURE / OPEN] The completed-weld class sits at the cut

`[KNOWN, paper register]` The Davenport–Heilbronn function (completed, FE-symmetric, Dirichlet
series) has off-line zeros: the completed-Dirichlet class with *general* FE carries off-line charge,
so it is not categorical. With §D it cannot be soft if its surgery rigidity extends from polynomial
factors to continuous planting. `[CONJECTURE]` The completed-Dirichlet class (FE + Schwarz +
Dirichlet-series shape) is Goldilocks, and the ξ-pinned constraint (its specific FE) empties the
odd right-half components — that emptiness IS the cut crossing, and it is exactly what §C makes RH.
Open sub-question (the generative next move): exhibit ANY constraint strictly between
"multiplication-stable" and "Dirichlet-series" with a provable, non-tautological planting no-go.

## Gates
- [x] 0 → 1  in-progress: well-posed; refutation mechanism identified; Lean plan drawn
- [ ] 1 → 2  fully-proven: §A–§D paper-complete (this card §A–§D carries the proofs' mechanisms)
- [ ] 2 → 3  formalized: `ConnectedSymmetryBarrier.lean`, `MultiplicativeSoftness.lean` green
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
