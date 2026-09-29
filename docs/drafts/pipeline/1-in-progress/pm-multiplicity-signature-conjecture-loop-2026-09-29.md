# PM multiplicity signature conjecture loop

- **ID:** pm-multiplicity-signature-2026-09-29
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `docs/reports/rh-current-frontier-map.md` §PM; `pm-physical-model-clock-reduction.md` PM-18/19a/19b
- **Statement:** The physical alternating Nyman witness form detects zero multiplicity, not only distinct zero locations.

## Goal

Advance recorded PM-19b without assuming RH, a zero-free region, simplicity, a source positivity law, or any new axiom. No numerical computations. Literal source identities and finite-dimensional algebra must supply every claimed direction.

## Plan

- [x] Read PM frontier, source modules, relevant memories, and current instructions.
- [ ] Exhaust corpus search for logarithmic witnesses, confluent coupling, and signature count.
- [ ] Dependency-closed paper proof and public-literature novelty audit.
- [ ] Formalize exact surviving theorem in narrowly imported leaf modules.
- [ ] Direct `lake env lean` audit, axiom audit in `/tmp`, lint, umbrella wiring, cleanup.

## Conjectures and failures

1. Reverse dyadic Haar closure: technically open in local Lean, but card already derives it from bounded equivalent Nyman weight. Classical closure theory found in public sources. Rejected as contribution satisfying requested novelty; retain as infrastructure only if necessary.
2. Multiplicity-sensitive negative index: recorded PM-19b. Candidate: a zero of order `m` gives `m` literal logarithmic witnesses, whose coupling to `m` distinct spurious witnesses is confluent Cauchy and invertible. Their neutral completions produce exact physical Gram matrix `-I_m`. Stronger survivor to investigate: simultaneous hyperbolic signature `(m,m)`.

## Evidence and limitations

- `FermiNymanWitnessNegativeIndex.lean` constructs `-I_n` for distinct right-strip zeros via `B_lj=(2^(-rho_j)-1/2)/(rho_j-d_l)`; spurious span is neutral.
- `FermiNymanWitnessSelfSimilarityCriterion.lean` localizes non-self-similar witness defects at meromorphic poles unconditionally (PM-19a).
- `MellinIteratedDerivative.lean` identifies all logarithmic source moments with Mellin derivatives for `MellinRapid` densities.
- First broad corpus search returned no lexical AND matches; available hybrid hits had complete source inventory but substantial stale/pending compiler coverage. Narrowed searches underway; applicability requires direct Lean verification.
- No finite search certifies absence from all public literature or training data. Novelty status remains provisional until scoped searches and comparison of exact statements.

## Working log

- 2026-09-29: initialized. Existing dirty files recorded and reserved; no commits/push, no dev server, no full/umbrella build.
- Tool availability: Serena available; `update_plan` and `multi_tool_use.parallel` absent from exposed tools. Plan tracked here; independent reads batched via `Promise.allSettled`.

## Next checkpoint

Read narrow search results; verify reusable Mellin and confluent algebra APIs in `/tmp`; first close all-order literal witness admission. Do not count this ingredient alone as significant final contribution.

## Paper mechanism (candidate, not yet audited)

Write `c(z)=2^(-z)-1/2`, nonzero for `Re z<1`. For a right-strip zero `rho` of order `m`, the functions `conj(d^j/dz^j[t^(z-1)/c(z)] at rho)`, `0<=j<m`, are finite combinations of literal log-power witnesses. Their coupling to spurious witness `g_k` is

`q(g_k,h_(rho,j))=(-1)^j j!/(rho-d_k)^(j+1)`.

Reason: logarithmic Mellin differentiation identifies all source moments; the order of the nonzero eta/source unit times zeta equals the order of zeta; dividing the coupling by `c` removes its triangular jet multiplier. Distinct zero nodes and injective imaginary spurious nodes permit the corpus's complex Cauchy-jet controllability theorem. Thus finite combinations `g_s` of spurious witnesses can satisfy `q(g_s,h_t)=delta_st`, while `q(g_s,g_t)=0`.

For `Q_st=q(h_s,h_t)`, set `v_s^- = h_s - (1/2) sum_t (Q_st+delta_st) g_t` and `v_s^+ = h_s - (1/2) sum_t (Q_st-delta_st) g_t`. Sesquilinearity gives `q(v_s^-,v_t^-)=-delta_st`, `q(v_s^+,v_t^+)=delta_st`, and `q(v_s^-,v_t^+)=0`. This supplies the exact hyperbolic block, hence negative index at least the sum of zero multiplicities in every finite packet.

Audit obligations: all-order L2 log admission; analytic source order; exact conjugation convention; normalized-jet coupling; spurious controllability; no omitted zero or simplicity condition; no computation-backed axiom.

- First ingredient passed scratch Lean: `isFermiNymanWitness_logPower_of_order` admits every log-power jet strictly below zeta analytic order. Source leaf `FermiNymanLogarithmicWitness.lean` created; targeted `lake --old build` underway. No numerical experiments or evaluator-backed proofs used.
- Public comparison: Burnol, *On Fourier and Zeta(s)* (2001), Theorem 7.1, already uses zero multiplicity to characterize jet-vector orthogonality. Logarithmic admission alone is therefore not claimed novel. Exact dyadic-form hyperbolic completion is the candidate distinction.
- A duplicate scratch Lean process was accidentally launched while previous check remained active; older owned process was terminated and its exit verified. Subsequent Lean checks are strictly sequential.

- Narrow PM-jet search returned existing PM-18/19a only, with partial method coverage; exact source searches found no log-power witness or multiplicity-index bridge.
- Serena symbol lookup reports Lean path ignored by configured Python project. Source reads and new-file edits use standard tools.
