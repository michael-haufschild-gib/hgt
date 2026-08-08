# Finite-prime Gibbs modular phase realization

- **ID:** `finite-prime-gibbs-modular-phase-realization`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / OPERATOR REALIZATION / PRIME PHASE CLOCK
- **Status:** `[PAPER PROOF COMPLETE] [UNCONDITIONAL] [BRIDGE] [NO RH CLAIM]`
  `[NO LEAN WRITTEN] [NO PHYSICS CLAIM]`
- **Arithmetic parent:** `phase-subdiscriminant-kahler-smith-stratification-law.md`.

## Theorem

Let `p_1,...,p_N` be distinct primes, `beta>0`, and let `E_ij` be matrix units of
`M_(N+1)(C)` indexed by `0,1,...,N`. Define faithful Gibbs state

\[
 \rho_\beta
 =Z^{-1}\operatorname{diag}(1,p_1^{-\beta},\ldots,p_N^{-\beta}),
 \tag{1}
\]

where `Z=1+sum_i p_i^(-beta)`.

with modular flow

\[
 \sigma_s(Y)=\rho_\beta^{is}Y\rho_\beta^{-is}.
 \tag{2}
\]

Put

\[
 X=\sum_{i=1}^N(\log p_i)E_{i0},
 \qquad
 X(t)=\sigma_{-t/\beta}(X).
 \tag{3}
\]

Then

\[
 \boxed{
 X(t)=\sum_{i=1}^N(\log p_i)e^{it\log p_i}E_{i0}.}
 \tag{4}
\]

For framed coordinate functionals

\[
 \epsilon_i(Y)=\langle i|Y|0\rangle
 \tag{5}
\]

define quadratic two-copy polynomial

\[
 Q_N(Y)=N\sum_i\epsilon_i(Y)^2-\left(\sum_i\epsilon_i(Y)\right)^2.
 \tag{6}
\]

If `z_i(t)=(log p_i)e^(it log p_i)`, then

\[
 \boxed{Q_N(X(t))=H_2(z(t)),}
 \tag{7}
\]

where

\[
 H_2(z)
 =\det\begin{pmatrix}N&\sum_i z_i\\\sum_i z_i&\sum_i z_i^2\end{pmatrix}
 =N\sum_i z_i^2-(\sum_i z_i)^2.
 \tag{8}
\]

For prime triple `(101,103,107)`,

\[
 \boxed{\inf_{t\in\mathbb R}|Q_3(X(t))|=0.}
 \tag{9}
\]

No exact finite-time zero is claimed.

## Proof

Ratio of Gibbs eigenvalues at indices `i` and `0` is `p_i^(-beta)`. Hence

\[
 \sigma_s(E_{i0})
 =(p_i^{-\beta})^{is}E_{i0}
 =e^{-is\beta\log p_i}E_{i0}.
 \tag{10}
\]

Set `s=-t/beta` and sum with coefficients `log p_i` to obtain `(4)`. Applying `(5)` gives
`epsilon_i(X(t))=z_i(t)`, and substitution in `(6)` is exactly determinant `(8)`, proving `(7)`.

Existing fixed-radius theorem proves independent phase torus with radii
`(log101,log103,log107)` meets `H_2=0`. Prime logarithms are rationally independent by unique
factorization, so Kronecker flow `t mapsto (e^(it log p_i))` is dense. Continuity gives `(9)`.
QED.

## Exact boundary

This theorem realizes arithmetic phase clock and scalar subdiscriminant reader inside ordinary
finite matrix modular flow. It does **not** realize DVR source order, Kähler Smith wall, or nontrivial
extension phase. Matrix category is semisimple and every exact sequence of finite complex vector
spaces splits.

Thus modular recurrence can approximate scalar shadow of law wall while operator algebra remains
in one fixed isomorphism chart. A comparison functor

\[
 \text{framed modular coherence}
 \longrightarrow
 \text{nonsemisimple source order}
 \tag{11}
\]

is required before arithmetic wall crossing can be inferred.

## Predictions and falsifiers

1. Framed two-copy polynomial measured along Gibbs modular clock approaches zero for explicit prime
   triple.
2. Any finite model claiming actual Kähler Smith jump from `(9)` alone is false: no valuation or
   module specialization occurs in `M_(N+1)(C)`.
3. Exact finite-time zero remains exponential-polynomial question; density is insufficient.
4. Removing frame `(E_i0)` destroys arithmetic coefficient meaning; unitary-invariant spectrum of
   `rho_beta` alone does not specify `Q_N`.

## Novelty boundary

Finite-dimensional modular automorphisms, Gibbs states, prime-log frequencies, Kronecker density,
and quadratic coherence readers are classical or already present in corpus. New-to-corpus bridge is
exact identity `(7)` joining prime modular clock to phase-subdiscriminant observable. No priority or
physical novelty claim.

Relevant parent: https://arxiv.org/abs/2604.02213.

## Lean-return note

No Lean work authorized. Later formal proof uses diagonal matrix powers, matrix-unit conjugation,
finite sums, and previously paper-proved Kronecker wall closure. Search existing KMS/prime-log Lean
corpus first.

## Gates

- [x] dependency-closed paper proof
- [x] explicit operator realization
- [x] exact arithmetic scalar reader
- [x] semisimple non-transfer boundary
- [ ] independent hostile audit
- [ ] Lean formalization

## Log

- 2026-08-08 -- realized prime phase flow as Gibbs modular orbit and `H_2` as framed two-copy
  coherence polynomial.
