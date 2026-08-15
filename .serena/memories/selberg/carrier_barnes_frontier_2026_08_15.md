# Selberg carrier and Barnes frontier (2026-08-15)

## Honest status
- General Selberg C1/C2 remain open; no Lean proof/disproof exists or is claimed.
- External audit: Kaczorowski–Perelli arXiv:2603.13885 (2026-03-14) gives multiple-standard-twist meromorphic continuation/polar geometry, not Rankin–Selberg prime covariance. Liu–Wang–Ye proves scoped automorphic orthogonality via Rankin–Selberg, not arbitrary Selberg class.
- Exact missing primitive: a prime-local tensor/Hadamard object with Euler-log prime coefficient `a_F(p) * star a_G(p)`, analytic continuation, and a positive trace/PNT theorem. Ordinary convolution/product and coefficientwise conjugation are first-order and cannot supply it.

## Verified Lean modules now wired in `formal/GaloisForLFunctions/RHTower/SelbergClass.lean`
- `FullProduct.lean`: `SelbergClass.mul`, full ordinary product closure.
- `FullConjugate.lean`: `SelbergClass.conjugate`, full coefficientwise conjugation closure.
- `FullEulerLogPrime.lean`: `SelbergClass.coeff_prime_eq_eulerLogCoeff`.
- `DirichletCharacterC1.lean`, `DirichletCharacterC2.lean`: exact degree-one finite reductions; C2 still needs ordered Mertens/AP boundary estimate.
- Barnes chain: `BarnesTwoGammaLineIntegrable.lean`, `BarnesFiniteRectangleIntegral.lean`, `BarnesFiniteRectangleExplicitSum.lean`, `BarnesHorizontalEdges.lean`, `BarnesVerticalShift.lean`.
- `BarnesVerticalShift.verticalIntegral'_barnesJ_sub_left_eq_range_sum`: for `0<c<Re ξ`, `η≠0`, `|arg η|<π`, exact `V'_c(J)-V'_{-(m+1/2)}(J)=Σ_{n=0}^m (-1)^n Γ(ξ+n)η^n/n!`. Negative line integrability is independently proved; no positive-line misuse.

## Barnes next open core
Pass `m→∞`, identify binomial branch on full sector, then only afterward apply to K–P transformed remainder. Do not call fixed finite shift Barnes Lemma 6 or K–P continuation.

## Docs
- `docs/drafts/pipeline/1-in-progress/selberg-orthogonality-working-log.md`, sections 251–255.
- `docs/drafts/pipeline/1-in-progress/kaczorowski-perelli-multiple-standard-twist-continuation.md`, later verification update.
