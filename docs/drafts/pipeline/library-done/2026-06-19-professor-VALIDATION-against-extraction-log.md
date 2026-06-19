# Library / strategic update — Professor — VALIDATION against support-extraction-log.md

**For:** librarian + all. **Date:** 2026-06-19. **Author:** Professor. Did not touch ledger files.
**Trigger:** user asked to validate that recent work is not already in `docs/support-extraction-log.md`.

## Finding: much recent (2026-06-19) work RE-DERIVES existing log content
The log (1502 lines, the mining of the 37 denied docs) already contains, as conjecture/seed, most of
today's "results." Provenance map (cite when annotating 00-status rows / buckets):

| Recent card / result | Already in the log |
|---|---|
| `compute-omega-h2-gl.md` §R — ω purely archimedean | **#90 / Attack 6** (L1423): ω = additivity of the archimedean place = missing Frobenius at ∞; trace defect = Γ-factor = Kurokawa abs. zeta |
| `faces-orthogonality.md` — Face A⊥B, positivity≠genuineness | **#75 / B29** (L575–581): the (E)/(A)/(P) cuts; "(P) does NOT imply (A)"; fakes pass positivity |
| `stieltjes-log-weld.md` — joint `{log p}∪{γ_n}`, Schanuel | **#72/#74/#128** (L128, 459–466, 524–556): Stieltjes block = genuinely-new no-motive object; DSS = joint indep; "trdeg=dim OPEN, Schanuel-type"; height vacuum |
| `c5-jensen-prime-kernel.md` — `K_d(p)`, finite-free | **SEED-AB** (L1410–1421): `K_d(p)` "the prime kernel"; RH = finite-free CLT fixed-point stability |
| `finite-free-convolution-flow.md` §7 / Selberg-extremes | **#87 §12** (L978–983): Selberg CLT, FHK extremes, "zeros = degenerations" |
| all no-margin work (`λ_d↓0`, two-rate) | **#89 / Part XI** (L665, 1081, 1435) |
| `combination-mode-baker-reducibility` Pólya–Schur framing | **Attack 5** (L1396–1408): each σ_p a Pólya–Schur multiplier; RH = ξ is an LP-limit |

## The decisive item — the log already audited the positivity route as a dead-end
Honest novelty audit, **L1430–1438**:
> "The RH positivity attack COLLAPSES to dBN: A1=A2=A5 = the heat flow Λ≤0. No new mechanism to force Λ≤0
> (honestly not faked)."
⟹ The single-orbit-positivity C5★ thread (`finite-free-convolution-flow.md`, and my kernel/divergence
feeding it) sits on this collapsed axis. `λ_min(S_d)≥−1` is a clean RH⟺ but per the audit yields **no new
mechanism** — it will not earn C5.

## What the log flags as genuinely NEW (L1433–1438)
B7 (Bogomolov height geometry, #89); **B29 = the (E)(A)(P) cuts** (= faces-orthogonality, on the new axis);
the no-margin welds; **ζ(½) as a non-motivic period** (#69 §23); and **the transcendence reframe — RH as a
COROLLARY of DSS, not positivity** (the corank/Stieltjes axis).

## Recommended ledger actions
1. Annotate rows #90/#71 (ω), #75 (faces), #18/#19 (Stieltjes), #104 (finite-free), #59/#110 (Selberg) with
   "re-derives / proves log §… ; not a new conclusion."
2. Add a scorecard note: **the positivity axis is a known dead-end (log L1430); C5 should be sought on the
   transcendence/DSS/corank axis.**
3. Genuinely-new *proofs* this session (legitimate, = proofs of log conjectures, NOT new discoveries):
   DeWitt's G2-over-F_q (#22); the (★) Cauchy identity in Lean (Leaner); the corank↔transcendence exact
   identity; the explicit first-order kernel form. Keep these; reclassify the rest as re-derivations.

## Process fix
Validate against `support-extraction-log.md` BEFORE opening a card, so re-derivations are recognized as
proofs-of-existing-conjectures, not discoveries.
</content>
