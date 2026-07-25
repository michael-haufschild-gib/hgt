# Rational archimedean CCM Schwartz reflection

- **Status:** Formalized in Lean
- **Claim type:** THEOREM
- **Date:** 2026-07-25
- **Role:** First concrete analytic factor of the CCM Real-Brauer lift

## Statement

On the Schwartz space \(\mathcal S(\mathbb R,\mathbb C)\), define
\[
  (Rf)(x)=\overline{f(-x)}.
\]
Then \(R\) is a continuous conjugate-linear involution. Hence it defines an even
\(K_{\mathbb R}\)-structure on the rational archimedean Schwartz factor.

## Proof

Negation is a real-linear isometric equivalence of \(\mathbb R\). Precomposition by such an
equivalence is continuous on Schwartz space. Complex conjugation is a real-linear isometric
equivalence of \(\mathbb C\), and postcomposition by a continuous real-linear map is continuous
on Schwartz space. Their composite is therefore continuous.

For \(z\in\mathbb C\),
\[
 R(zf)(x)=\overline{z f(-x)}=\overline z\,Rf(x),
\]
so \(R\) is conjugate-linear. Finally,
\[
 R^2f(x)=\overline{\overline{f(-(-x))}}=f(x).
\]

## Hostile checks

- Exact Schwartz topology is used, not a pointwise function surrogate.
- Continuity is inherited from continuous-linear pre- and postcomposition maps.
- This covers only the archimedean factor; finite Bruhat--Schwartz factors remain separate.
- No numerical, trace, positivity, spectrum, or RH premise occurs.

## Gates

- [x] Dependency-closed proof
- [x] Formalized in Lean; cached leaf build and axiom audit passed
- [ ] Combined with finite adele Bruhat--Schwartz factor

## Log

- 2026-07-25 — extracted as the first concrete analytic leaf after mathlib audit found
  `SchwartzMap.compCLMOfContinuousLinearEquiv` and `SchwartzMap.postcompCLM`.
- 2026-07-25 — formalized in `CCMRationalArchimedeanSchwartzReal.lean`. Axiom audit contains
  only `propext`, `Classical.choice`, and `Quot.sound`.
