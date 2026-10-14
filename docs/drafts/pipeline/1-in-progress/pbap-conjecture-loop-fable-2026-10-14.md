# PBAP conjecture loop (archimedean value function, blind cone geometry)

- **ID:** pbap-loop-fable-2026-10-14
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (loop) with THEOREM (Lean) rows
- **Source:** docs/reports/rh-current-frontier-map.md (route HF, "Needs: prove PBAP"); STATUS MUST-1431/1437/1439
- **Statement:** PBAP (pole + archimedean energy ≥ 0 on every nonnegative blind combination of autocorrelations) is RH; this card runs a conjecture → Lean → learn loop on its structure.

## Goal
Find the mechanism by which the archimedean place (symbol `A(r) = Re ψ(¼+ir/2) − log π`, pole `k̂(±i/2)`) and the
positions `log n` force positivity on the blind cone. Every row is either a Lean theorem (unconditional) or a
recorded failure with the exact obstruction.

## Gates
- [x] 0 → 1  in-progress: well-posed (RH ⟺ PBAP is [L]); attack = structure of the blind cone and its dual
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized
- [ ] 3 → 4  publication-ready

## Approach
Reading of the corpus (frontier map + STATUS only): PBAP is a sharp LP with unique dual `Λ`, infinite-dimensional
equality face (Ξ²-divisible tests), node-critical at every prime power, pole-critical (β = 1, depth ½), trivial on
the nonnegative and support-blind sectors. A direct proof must be primal (no certificate other than `Λ` exists).

## Log
- 2026-10-14 — created. Mission: contribute to PBAP.
- 2026-10-14 — **Row 1 [L]. The archimedean node value function is linear with gradient `Λ`.**
  Module `RHTower/ArchimedeanNodeValueFunction` (standard axioms, `lake env lean` clean, wired).
  For a finitely supported node vector `v` let `nodeFibre v` = energies `A(c)` of nonnegative combinations `c`
  with node vector `L(c) = v`, and `nodeValue v = inf nodeFibre v`.
  * `nodeFibre_nonempty`: every `v` is attained.
  * `nodeValue_eq_vonMangoldtPairing`: under RH, `nodeValue v = Σ_n Λ(n) v_n` for every `v`
    (Hahn–Banach `exists_extension_of_le_sublinear` on the sublinear `V`, then full-cone uniqueness
    `eq_vonMangoldt_of_weilPositiveFull`). So `V` is linear and `∇V = Λ`.
  * `nodeValue_single`: mass `t` at one node `m` costs `t Λ(m)` (both signs).
  * `not_bddBelow_nodeFibre`, `riemannHypothesis_iff_bddBelow_nodeFibre`: without RH every fibre is unbounded
    below; RH ⟺ one fibre bounded below.
  * `riemannHypothesis_iff_nodeFibre_add_neg_nonneg`, `riemannHypothesis_iff_unitNode_two_sided`:
    RH ⟺ `A(c₊) + A(c₋) ≥ 0` for all `c₊` with `L(c₊) = v` and `c₋` with `L(c₋) = −v` (any single `v`,
    e.g. `v = e_m`): the least energy carrying mass `+1` at `m` and the least energy carrying mass `−1` at `m`
    add to zero.
  Reading: MUST-1439 (single node, positive mass) is the restriction of a linear law. The convex value function
  of the archimedean LP has no kinks; its gradient is the von Mangoldt function. Composite nodes are free in both
  directions, prime powers cost `log p` one way and refund `log p` the other way.
