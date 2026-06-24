# Positive Source Weights Require Pointwise Hankel Kernels

- **ID:** positive-source-weights-require-pointwise-hankel-kernels
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / source-transfer guardrail
- **Source:** `axis-positivity-does-not-imply-hankel-positivity.md`,
  `source-selector-repair-obligation-ledger.md`,
  `seam-log-markov-pick-rh-equivalence.md`
- **Statement:** A linear proof that turns positive source weights into Hankel
  positivity works for every positive weighting only when each source atom
  already contributes a positive semidefinite Hankel kernel. Otherwise the
  proof must use more than weight positivity.

## Setup

Let `X` be a set, and let

`phi_n : X -> R`, `n >= 0`,

be a family of real functions.

For a finitely supported nonnegative weight function `w:X -> R_{>=0}`, define
moments

`m_n(w)=sum_{x in X} w(x) phi_n(x)`.

For each degree `d`, define the Hankel matrix

`H_d(w)=[m_{i+j}(w)]_{0<=i,j<=d}`.

Also define the pointwise source kernel

`K_d(x)=[phi_{i+j}(x)]_{0<=i,j<=d}`.

## Theorem

For a fixed `d`, the following are equivalent:

1. `H_d(w) >= 0` for every finitely supported nonnegative weight `w`.
2. `K_d(x) >= 0` for every `x in X`.

Therefore positive source weights imply degree-`d` Hankel positivity uniformly
over all positive weights if and only if every point source already has a
positive semidefinite degree-`d` Hankel kernel.

## Proof

For every finitely supported `w`,

`H_d(w)=sum_x w(x) K_d(x)`.

If every `K_d(x)` is positive semidefinite and every `w(x)>=0`, then `H_d(w)` is
a nonnegative linear combination of positive semidefinite matrices. Hence
`H_d(w)>=0`.

Conversely, assume `H_d(w)>=0` for every finitely supported nonnegative `w`.
Fix `x_0 in X` and take the point mass weight

`w=delta_{x_0}`.

Then

`H_d(delta_{x_0})=K_d(x_0)`.

Thus `K_d(x_0)>=0`. Since `x_0` was arbitrary, every pointwise source kernel is
positive semidefinite.

## Measure Version

The same statement holds for positive measures whenever the entries are
integrable:

`H_d(mu)=int_X K_d(x) dmu(x)`.

If the implication is required for every positive measure `mu`, then point masses
again force `K_d(x)>=0` at each source point.

## Consequence for the Euler-Product Transfer

Suppose a proposed source proof writes the repair moments or a Schur/Hankel block
linearly as

`m_n=sum_x w_x phi_n(x)`

with `w_x>=0` coming from Euler/local-factor orientation.

If the proof uses only `w_x>=0`, then this theorem says exactly what it must
show:

`[phi_{i+j}(x)]_{i,j<=d} >= 0` for every source atom `x` and every degree `d`.

If those pointwise kernels are not positive semidefinite, positive source weights
alone cannot prove the Hankel or Schur sign. The argument must then use extra
structure: the exact arithmetic values of the weights, multiplicativity,
archimedean cancellation, a completed explicit-formula identity, or another
source constraint beyond positivity.

## Theatre Test

For any claimed Euler/local-factor positivity transfer:

1. Write the target Hankel or Schur matrix as a linear combination of source
   kernels.
2. Ask whether the theorem is meant to hold for all positive source weights.
3. If yes, prove each pointwise source kernel is positive semidefinite.
4. If no, name the additional source structure beyond positivity that selects
   the actual weights and prevents negative pointwise kernels from contributing
   a bad direction.

## Route Impact

This theorem does not prove RH. It narrows the live source theorem:

`Euler positivity => semilocal Schur/index sign`

is viable only through either

1. a pointwise positive-kernel representation, or
2. a non-pointwise source theorem using arithmetic structure beyond
   coefficient positivity.

Thus a proof cannot stop at positive Euler coefficients unless it also supplies
the pointwise Hankel-kernel positivity that makes positive coefficients relevant.

## Gates

- [x] 0 -> 1 in-progress: positive-weight transfer criterion isolated.
- [x] 1 -> 2 fully-proven: finite point-mass proof completed.
- [ ] 2 -> 3 formalized: finite matrix-cone lemma.

## Log

- 2026-06-24 -- Codex: created to sharpen the axis-to-combination transfer
  obligation after the coefficient-positivity guardrail.

## 2026-06-24 Loewner budget is a stronger demand

`positive-source-weights-do-not-bound-loewner-budget.md` gives the budget analogue of this positivity criterion. Pointwise PSD kernels can make a positive-weighted sum PSD, but they do not place that sum under a fixed Loewner budget. If arbitrary positive scaling is allowed, a nonzero PSD kernel already breaks any fixed upper bound.

Thus the Euler/local-factor transfer has two separate gates: pointwise kernel sign, then scale-sensitive domination by the archimedean budget. The second gate requires exact weights, normalization, multiplicative structure, archimedean cancellation, or a completed source identity.

## 2026-06-24 Atom-motion kernels fail the pointwise test

`hankel-atom-displacement-tangent-indefinite.md` gives a concrete source-kernel failure in the Jensen/Hankel chart. A positive atom `m v(r)v(r)^T` is PSD, but the tangent created by moving it has square-test value `2m q(r)q'(r)`, which changes sign with the test polynomial.

Thus positive Euler amplitudes attached to root or atom displacement cannot satisfy this card's pointwise PSD-kernel criterion. A proof using that chart must use nonlinear full-matrix comparison, completed explicit-formula coupling, or a source-built index theorem beyond positive-weight summation.

## 2026-06-24 single even frequency fails the pointwise kernel test

`single-even-frequency-not-stieltjes.md` gives the seam-log pointwise failure. The FE-even source germ `B(cosh(lambda w)-1)` has shifted moments `T_k=B(-1)^(k+1)lambda^(2k)/(2k-1)!`, and its first shifted Hankel determinant is negative.

Therefore a positive-weight Euler proof cannot use termwise FE-even frequencies as pointwise PSD kernels. Any viable proof must use extra completed structure beyond positive frequency weights.

## 2026-06-24 positive FE-even cone fails before the kernel test

`positive-even-frequency-cone-not-markov.md` strengthens the single-point kernel failure. A positive mixture of FE-even frequency germs has alternating shifted seam moments and in particular `T_2<0`, so the positive frequency cone itself is outside the Markov/Stieltjes target.

Thus no pointwise-kernel repair can be obtained by first forming a positive FE-even frequency measure. The proof must use completed source structure outside that cone.
