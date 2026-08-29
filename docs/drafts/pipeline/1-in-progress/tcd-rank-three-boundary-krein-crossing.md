# TCD rank-three boundary Krein crossing

- **ID:** TCD-KCF
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `scripts/formal_tools.py research` results for `theta cusp projective drift source positive D1 ninth jet`, `finite Hankel boundary Krein crossing adjugate null direction determinant first zero`, and `theta cusp reflected sixth rank two minors positive full source`; `docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md` (read-only TCD/S6F ledger)
- **Statement:** On `0 < x < 137/2000`, if the completed-theta rank-three reflected D1 vanishes, then its projective first variation is strictly positive.

## Goal
Exclude the first zero of rank-three reflected D1 by an oriented null-line crossing theorem rather than a global monotonicity or coefficient-bound proof. Corpus seam positivity, global strict rank-two reflected minors, and the existing `x >= 137/2000` D1 theorem then give global rank-three D1. The intended RH chain is: rank-three boundary crossing → global D1 → an all-order version of the same Krein-crossing induction for the cofinal singular Hardy/RKHS or completed Bezoutian cone → Weil positivity → RH. Global D1 alone is not RH; cofinal extension remains explicit.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, exact leaf build green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach
Let `M(x)` be the `3 x 3` signed even-jet Hankel matrix. Corpus proves its order-one and order-two leading faces are strictly positive. Hence at `det M = 0`, `M` is positive semidefinite of rank two and `adj(M)` is a positive rank-one projector onto the canonical null polynomial. Derive the projective connection cancellation exactly: normalized source jets obey `L f_n = f_(n+1) - (B/2) f_n`, while `det M` has source weight six, so

`Q L(det M) - 6 det(M) L(Q) = Q * shiftVariation(det M) - 6 f_1 det(M)`.

On the zero face, the second term vanishes. Jacobi's formula then identifies the remaining sign with the pure shifted crossing form on the null line. Prove that source-specific crossing form is positive using the physical modular orbit, not an arbitrary positive orthant or a numerical coefficient certificate.

Novelty audit through 2026-08-29 found generic Toda/Hankel determinant variation and generic total-positivity results, but no theorem for this completed-theta reflected D1 boundary flux. Corpus search found generic finite Hankel Krein crossing and the theta rank-two faces, but no connector between them.

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** pending
- **Strongest positive survivor:** pending exact gauge-cancellation/null-line classification
- **New insight:** pending
- **Status:** open

## Log
- 2026-08-29 — created directly in 1-in-progress after corpus and literature audit; frontier map left unchanged.
- 2026-08-29 — **Conjecture admission rule.** Every further conjecture on this card must cite a
  `scripts/formal_tools.py research` corpus result and state its complete implication chain to one
  of: (i) global D1, (ii) a rigorous TCD no-go, or (iii) the cofinal Hardy/Bezoutian landing and
  Weil positivity.  Local identities which do not remove one of those burdens are not research
  targets.
- 2026-08-29 — Lean-closed Jacobi--Krein reduction identifies the singular-face projective drift
  with the canonical null-line crossing form.  Exact chain now under attack:
  `source crossing > 0 at every D1 zero` -> `no first zero` -> `global rank-three D1` ->
  `all-order Krein crossing/cofinal Hardy or completed Bezoutian cone` -> `Weil positivity` -> RH.
- 2026-08-29 — killed the apparent center-mixed three-node shortcut after corpus audit.  Existing
  unconditional PSD concerns the *integrated* Hedenmalm center-mixed density; D1 is the
  pointwise-center determinant, and determinant formation does not commute with that integral.
  It therefore supplies no source-pointwise crossing sign or global D1 theorem.
