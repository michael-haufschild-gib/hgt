# Suzuki Cauchy-wall lower Hardy evaluation

## Status

Formalized in Lean 4.  Route map remains read-only.  Result identifies exact RH-bearing Hardy mode
inside completed Suzuki/CCM wall carrier; it does not prove required uniform bound.

## Corpus-first frontier audit

Before conjecturing, exact `scripts/formal_tools.py research` searches covered completed Cauchy wall
symbols, lower imaginary evaluations, Hardy/Cauchy decompositions, critical Mellin resolvents,
unit-Riesz outgoing charge, and Suzuki wall continuation.  Corpus already contained:

- `unitRieszCoherentCompletedOutgoingCharge_eq_resolvent_half`;
- exact CCM-HG pole domination / RH classification;
- generic Hardy and Cauchy evaluation machinery;
- completed unit-Riesz physical-space barycenter energy.

It did not contain a complex-height continuation of the literal completed Suzuki wall symbol, its
evaluation at `-I`, or a point-evaluation RH classification for that source-faithful wall object.

## Theorem

Let

\[
 \Phi_N(z)=\sum_{2\le k\le N}{\Lambda(k)\over\sqrt N}
 \left(1-\exp\left(-{i z\over2}(\log N-\log k)\right)\right)
 -\sqrt N\,{iz/2\over1+iz/2}.
\]

This is the complex-height continuation of the real Suzuki Cauchy-wall symbol.  At the lower Hardy
point `z=-i`,

\[
 \Phi_N(-i)=Q_N={1\over2}
   \operatorname{criticalMellinChebyshevResolventSource}(\log N),
\]

where `Q_N` is the literal completed outgoing unit-Riesz coherent charge.  Therefore

\[
 \mathrm{RH}\quad\Longleftrightarrow\quad
 \forall n\in\mathbb N,\ |\Phi_{n+2}(-i)|^2\le4.
\]

Indexing by `n+2` makes the public theorem closed and premise-free.

## New scientific content

This identifies the scalar RH-bearing outgoing charge as one distinguished complex evaluation of
the full prime-minus-polar Suzuki wall carrier.  Route O/CCM-HG endpoint control and Suzuki
reflected-wall assembly are therefore not separate scalar targets: both must control the same
lower-Hardy wall value.  Gamma/polar completion is retained exactly through the rational term.

## Hostile audit

- Classification is RH-equivalent; no proof of the four-unit bound is claimed.
- Analytic continuation alone supplies no boundary-norm estimate.
- Real-height zero-mode cancellation does not control the value at `-I`.
- No zero-free region, RH premise, computation, or added axiom enters any declaration.

## Lean certificate

- **Module:** `GaloisForLFunctions.RHTower.Suzuki.SuzukiCauchyWallHardyEvaluation`
- **Exact outgoing evaluation:**
  `suzukiUnitRieszCompletedCauchyWallSymbolComplex_neg_I_eq_outgoingCharge`
- **Closed resolvent evaluation:**
  `suzukiUnitRieszCompletedCauchyWallSymbolComplex_add_two_neg_I_eq_resolvent_half`
- **Closed classification:**
  `riemannHypothesis_iff_suzukiCompletedCauchyWall_neg_I_sq_le_four`

## Log

- 2026-08-16 — exact corpus-first collision audit completed.
- 2026-08-16 — paper theorem and unconditional Lean formalization completed; umbrella wired.
