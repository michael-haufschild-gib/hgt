# CCM canonical-head completed-error producer

- **ID:** CCM-O-HEAD-D
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** Route O canonical exact-ground Gamma--Slepian heads; CCM-FU/UR completed current
- **Statement:** For every positive aperture and every canonical actual Gamma--Slepian ground head, the complete archimedean energy plus the signed completed-error pairing of its literal aperture autocorrelation is nonnegative.

## Goal

Construct the missing source-side producer, not another receiver: prove the literal finite
von-Mangoldt compression cannot exceed identity, scalar Gamma, and polar energy on canonical
actual ground heads.  Via the established canonical-head convergence and nested-floor theorem,
this yields nonnegative restricted-Weil floors and RH.  Common-clock, reporter-only, and
separately-positive prime/polar replacements are inadmissible.

## Gates

- [x] 0 -> 1 in-progress: exact source-pure claim; canonical heads and completed current are literal
- [ ] 1 -> 2 fully-proven: dependency-closed paper proof, `[PAPER-PROVED]`, no open implication
- [ ] 2 -> 3 formalized: exact unconditional Lean theorem, targeted leaf build and axiom audit
- [ ] 3 -> 4 publication-ready: standalone theorem/proof/Lean certificate/priority audit

## Exact notation

For aperture `a`, let `h_(a,n)` be the corpus's canonical projection of the exact restricted-Weil
ground onto a finite peripheral Gamma--Slepian head and let `v_(a,n)` be its physical zero-extended
aperture vector.  Put

```text
C_(a,n)(t) = integral_R v_(a,n)(x+t) conjugate(v_(a,n)(x)) dx,
D(t)       = 4 sinh(t/2) - sum_(2 <= m <= exp t) Lambda(m)/sqrt(m).
```

On differentiable heads the established Stieltjes law identifies polar minus prime with
`-2 Re integral_(0,2a] D(t) C'_(a,n)(t) dt`; without differentiability use the original signed
Stieltjes pairing.  Exact producer target is the corresponding signed pairing plus complete
archimedean quadratic energy `>= 0`, equivalently
`CCMRestrictedWeilCanonicalGroundHeadReversePrimeBound a n`.

## Approach

Audit only source-faithful mechanisms acting on `C_(a,n)`: completed-error Stieltjes integration,
the exact Gamma--Slepian ground equation, head/tail shifted-defect identity, and possible
prime--polar square/Schur decompositions.  Hostile tests must reject any law valid only for a
reporter, a common clock, separate absolute estimates, fixed positive margin, or an assumed RH
continuation.

## Live claim

- `[OPEN CORE]` Produce a non-circular signed order or square law for the completed-error pairing
  on `C_(a,n)` that pays the complete Gamma energy and is stable under the canonical head limit.

## No-go closure

- **Exact killing theorem/mechanism:** pending conjecture loop.
- **Strongest positive survivor:** pending.
- **New insight:** pending.
- **Status:** Stage 1; no paper proof and no Lean theorem yet.

## Log

- 2026-08-17 -- created after corpus search isolated the actual-head completed-error pairing as the
  only lawful Route O / CCM-FU interface; fixed positive head margin already closed negatively.
