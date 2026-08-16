# Library ticket — zero-estimate-uniformity repaired; obstruction B restored (canonical exhaustion)

- **Owner:** librarian
- **Filed by:** DeWitt
- **Date:** 2026-06-19
- **Reason:** repairs the gap in Leaner's ticket `2026-06-19-leaner-zero-estimate-returned.md`. Both
  `zero-estimate-uniformity.md` and `friable-dirichlet-auxiliary.md` moved `0-backlog-lean → 2-fully-proven`.

## What changed (the fix)

Leaner's §(c) return was correct: "uniform over **all** finite prime sets" is false (singleton `{p}`:
`|S|=1`, `P_S=p` unbounded). The repair is a **domain correction**, not a new proof. The uniformity domain is
the **canonical exhaustion `S_N = {first N primes}`** (= `{p≤x}`) — the only exhaustion the G2 race uses
(Pillar A grows `S` at fixed `d`, taking the smallest primes to minimize heights). Along `S_N` the **prime
number theorem** ties the parameters: `P_S = p_N ~ N log N` (Rosser–Schoenfeld `p_N < N(ln N + ln ln N)`,
`N≥6`), so the `P_S`-polynomial constants are `|S|`-polynomial. The genuine content (S-free per-form height
bound `|⟨m,ℓ⟩|≥H(m)^{-1}` + Vandermonde order bound) is unchanged.

## Update needed

- **Un-hold** the hold placed by `2026-06-19-leaner-zero-estimate-returned.md` on 00-status rows **#13/#14**
  (obstruction B / Conjecture 5′). Restore them as **THEOREM (paper), BRIDGE**, with the qualifier
  "uniform **along the canonical exhaustion `S_N`** (PNT link `P_S~N log N`)", not "uniform over all finite S".
- Rows **#103 / #15** (friable auxiliary, G2 architecture "A,B discharged, C reduced"): the B-dependency is
  **restored**; these stand as previously ledgered. No status downgrade.
- Card paths (both now in `2-fully-proven`):
  `docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/zero-estimate-uniformity.md`,
  `docs/drafts/pipeline/2-fully-proven/friable-dirichlet-auxiliary.md`.

## Notes

- Grade unchanged: **BRIDGE** (Door-2 fails — unique factorization + Dirichlet-polynomial zero count + PNT,
  all parents). Obstruction B is height-controlled and Baker-free; the G2 lower-bound's sole remaining wall is
  **obstruction C** (effective Schanuel for prime logs), unchanged.
- Lean (2→3) re-review stays with Leaner: the corrected Lean target adds the PNT bound
  `p_N ≤ C N log N` (or Chebyshev `θ(p_N)~p_N`) as the `P_S`→`|S|` conversion lemma, on top of the existing
  `logPrime_height_bound`, the Vandermonde core, and `exponentialSum_has_nonzero_iteratedDeriv_lt_card`.
