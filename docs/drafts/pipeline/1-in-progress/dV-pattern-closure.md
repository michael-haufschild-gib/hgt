# ∂𝒱 = closure of the pattern region: a parameter-space disk-avoidance analog of M

- **ID:** dV-pattern-closure
- **Stage:** 1-in-progress (formal objects banked; conjecture is a named Prop; verdict: PARTIAL —
  the clean half reduces to a classical density fact, one sub-case is genuinely open)
- **Type:** [CONJECTURE] + formal objects (Lean) - grade **partial BRIDGE**
- **Statement (`U0ParameterSpace.ObstructedEqClosurePattern`):**
  `Obstructed = closure PatternRegion`, where `Obstructed = {b | K_b ∩ D̄(0,1) ≠ ∅}` and
  `PatternRegion = {b | K_b contains a PREPERIODIC point in D̄(0,1)}`.

## Banked (Lean, axiom-clean)

- `Obstructed`, `Viable` as formal `Set ℂ`; `isClosed_obstructed` (compact-witness sequential
  closedness), `isOpen_viable`.
- `patternRegion_subset_obstructed`, `cassini_subset_obstructed`; the easy half
  `closure_pattern_subset_obstructed : closure PatternRegion ⊆ Obstructed`.
- `ObstructedEqClosurePattern : Prop` — the conjecture as a named object (not an axiom).
- `exists_frontier_obstructed_on_ray` — first certified point of `∂Obstructed = ρ`, on the ray
  `arg b ≈ 126.9°` in `[11/5, 22/5]`.
- File `formal/GaloisForLFunctions/U0/U0ParameterSpace.lean`; card `obstructed_frontier_card`.

## Novelty-gate interrogation (the reduces-to-known audit)

Reformulation: `Obstructed = {b | K_b meets D̄(0,1)}`, `PatternRegion = {b | K_b meets D̄(0,1) at a
preperiodic point}` (the entry `x₀ = √(y−b) ∈ D̄(0,1) ∩ K_b` IS a preperiodic point of `K_b`).

**The half that reduces to known.**  Preperiodic points are DENSE in the Julia set `J_b` (classical
Fatou–Julia / Montel).  If `b ∈ Obstructed` with a witness `z₀ ∈ J_b ∩ (open D(0,1))`, density
gives a preperiodic point `p` near `z₀` still inside the open disk, so `b ∈ PatternRegion`
DIRECTLY (not merely in the closure).  So on the set of parameters whose disk-witness can be taken
on `J_b` in the OPEN disk, the conjecture is a consequence of a classical theorem — search, not a
moonshot.

**The genuinely open sub-case (the surviving content).**  A witness may exist ONLY in the INTERIOR
of `K_b` (a Fatou/bounded component — possible exactly for `b ∈ M`, where `K_b` has interior), or
ONLY on the boundary circle `‖z₀‖ = 1` exactly.  Density-in-`J` does not reach an interior witness.
So the real question narrows to:

> [OPEN CORE] For `b ∈ Obstructed ∩ M` whose disk-intersection is realized ONLY through the
> interior of `K_b` (no `J_b`-witness in the open disk), is `b ∈ closure PatternRegion`?

This is a statement about how the Fatou-interior touching set is approximated by preperiodic-witness
parameters — NOT a corollary of `J`-density, and the load-bearing piece of the conjecture.

## Pre-registered probe (anti-theatre: theory settles the main case, so no heavy sweep)

Prediction, registered before any compute:
- **P1 (settled by reasoning):** on the Cantor locus `b ∉ M` (`K_b` = Cantor set, NO interior,
  `K_b = J_b`), EVERY `Obstructed` witness is a `J_b`-point, so `b ∈ PatternRegion` directly and
  `Obstructed ∖ M ⊆ PatternRegion` (stronger than closure).  No numerical test needed — it is the
  density theorem.  [This also matches the recon: in the Cantor regime the only finite certificates
  are preperiodic.]
- **P2 (the only genuine test):** the interior/boundary sub-case above lives in `M`.  A worthwhile
  numerical probe is narrow — sample `∂Obstructed ∩ ∂M`-type parameters and test approximation by
  preperiodic-witness parameters — NOT a 12-ray brute sweep.  Deferred until the sub-case is
  sharpened into a decidable predicate; a blind sweep would be theatre.

## Route decision

survives(BRIDGE) PARTIAL.  The conjecture as stated is a mixture: the Cantor / `J`-witness half is
`reduces-to-known` (density of preperiodic points), the Fatou-interior half is a genuine open
sub-question.  **Action:** keep `ObstructedEqClosurePattern` as the formal target; the novel,
non-reducing content to pursue is the narrowed OPEN CORE (interior-witness approximation for
`b ∈ Obstructed ∩ M`).  Do NOT claim the full conjecture as a moonshot — its clean half is search.

## Next generative move

- Prove `Obstructed ∖ M ⊆ PatternRegion` in Lean (the reduces-to-known half, made rigorous via
  a `J_b`-density input) — turns the "search" half into a banked theorem and isolates the open core.
- Sharpen the interior-witness predicate into a decidable/testable form, THEN a targeted probe.

## Log
- 2026-07-02 — formal objects + closedness + frontier point + conjecture-Prop banked (#54–#56);
  interrogated: partial reduction (density-in-J), open core narrowed to the Fatou-interior case.
