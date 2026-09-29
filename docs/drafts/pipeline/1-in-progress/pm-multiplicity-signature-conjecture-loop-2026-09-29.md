# PM multiplicity signature conjecture loop

- **ID:** pm-multiplicity-signature-2026-09-29
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `docs/reports/rh-current-frontier-map.md` §PM; `pm-physical-model-clock-reduction.md` PM-18/19a/19b
- **Statement:** The physical alternating Nyman witness form detects zero multiplicity, not only distinct zero locations.

## Goal

Advance recorded PM-19b without assuming RH, a zero-free region, simplicity, a source positivity law, or any new axiom. No numerical computations. Literal source identities and finite-dimensional algebra must supply every claimed direction.

User updated overarching goal: continue contributing significant PM knowledge until RH is proved or falsified unconditionally in Lean. Completing the multiplicity milestone does not complete that goal; continue the conjecture loop through exact index equality and then the source-side obstruction.

## Plan

- [x] Read PM frontier, source modules, relevant memories, and current instructions.
- [ ] Exhaust corpus search for logarithmic witnesses, confluent coupling, and signature count.
- [ ] Dependency-closed paper proof and public-literature novelty audit.
- [ ] Formalize exact surviving theorem in narrowly imported leaf modules.
- [ ] Direct `lake env lean` audit, axiom audit in `/tmp`, lint, umbrella wiring, cleanup.

## Conjectures and failures

1. Reverse dyadic Haar closure: technically open in local Lean, but card already derives it from bounded equivalent Nyman weight. Classical closure theory found in public sources. Rejected as contribution satisfying requested novelty; retain as infrastructure only if necessary.
2. Multiplicity-sensitive negative index: recorded PM-19b. Candidate: a zero of order `m` gives `m` literal logarithmic witnesses, whose coupling to `m` distinct spurious witnesses is confluent Cauchy and invertible. Their neutral completions produce exact physical Gram matrix `-I_m`. Stronger survivor to investigate: simultaneous hyperbolic signature `(m,m)`.
3. Exact multiplicity index: `witnessNegIndex = rightStripMultiplicityCount`. Lower side is now reduced to the audited literal hyperbolic construction. Upper-side candidate uses correlation-Mellin jets; their common kernel cancels every possible pole of the left dyadic defect, hence is self-similar and neutral. A negative orthonormal family maps injectively into those jets. Finite-dimensional rank bounds its size by total multiplicity; infinite total multiplicity makes the extended upper bound automatic.

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

- All-order admission leaf targeted build passed. Normalized-coupling scratch under audit: compactly supported spurious cuts are MellinRapid; their logarithmic Mellin derivatives compute the literal dyadic pairing. Normalize by the reciprocal of `2^(-s)-1/2` before applying confluent controllability.
- Refined construction avoids choosing an arbitrary finite square confluent matrix: the existing infinite-node complex control map is surjective, yielding finite spurious combinations dual to every finite multiplicity packet. Candidate strengthened to two mutually orthogonal signed families with exact Gram matrices `-I` and `+I`.
- Next capstone is unconditional `rightStripMultiplicityCount ≤ witnessNegIndex`, where the count is the supremum of finite sums over the actual right-strip-zero subtype. Analytic order finiteness will be discharged through the existing xi/zeta order bridge, not assumed.

- Exact normalized-jet/spurious coupling passed scratch Lean without warnings. `FermiNymanConfluentCoupling.lean` created and targeted dependency build started. Reciprocal differentiation uses the toolchain's proved iterated-derivative formula; no numerical computation, evaluator tactic, new premise, or heartbeat increase.
- Import refinement: the multiplicity capstone can prove zeta order finiteness directly by analytic continuation on the punctured complex plane and nonvanishing at `2`. This avoids importing the much broader completed-prime-flux module solely for its xi/zeta bridge.
- Public exact-statement searches (`Nyman-Beurling` with `negative index`, `inertia`, `indefinite`, `dyadic`, `multiplicity`) found no matching physical dyadic theorem. The public 2026 Weil-form inertia framework concerns a different form and compression mechanism; it does not by itself supply the literal Fermi witness construction. Absence from all public literature/training data remains uncertifiable.

## Upper-bound paper mechanism (new conjecture)

For each right-strip zero `rho` of multiplicity `m`, attach the `m` coordinates
`J_(rho,j)(w) = conj(iteratedDeriv j (correlationMellin (conj ∘ w)) rho)`, `j<m`.
The map is complex-linear on finite sums of witnesses: correlation integrates the real alternating generator against `conj(w)`; its bounded compact support makes every Mellin derivative legitimate.

If all coordinates vanish, the analytic order of the correlation Mellin transform at `rho` is at least `m`. The prefactor in the left dyadic defect is analytic, while the entire zeta denominator has order exactly `m`. Thus the quotient has no pole there. Every possible left-half-plane pole corresponds to a right-strip zero: nonvanishing on `Re s >= 1` excludes the rest. Existing unconditional removability then gives self-similarity of `w`, and its dyadic quadratic form is zero.

On a negative orthonormal family, a nonzero coefficient vector gives quadratic form `-sum |c_i|^2 < 0`. Therefore the jet-coordinate map on its span is injective. If total multiplicity is finite, the target has exactly that dimension, proving the upper index bound. If total multiplicity is infinite, the extended-natural upper bound is immediate. This is a dependency-closed paper mechanism; formal obligations remain all-order coordinate linearity, local order cancellation, and finite/infinite counting glue.
