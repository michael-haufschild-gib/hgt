# Two-prime real Euler-transition selector

- **ID:** `two-prime-real-euler-transition-selector`
- **Stage:** 3-formalized / not new scientific knowledge
- **Type:** EXACT RH CONSUMER REDUCTION / ELEMENTARY EXPONENTIAL RIGIDITY
- **Scientific status:** `[PAPER-PROVED]` `[BRIDGE]` `[NOT RH]`
  `[NO EXTERNAL NOVELTY CLAIM]`
- **Parents:**
  - `../../1-in-progress/adjoint-duality-cauchy-nerve-purity-law.md`;
  - `../../4-publication-ready/riemann-source-modular-superselection/main.tex`;
  - `../../4-publication-ready/riemann-divisor-prime-transfer-spectrum/main.tex`.
- **Statement:** For a nonreal complex coordinate, reality of the centered reflected-Euler
  transition at two multiplicatively independent positive bases forces critical real part.

## Theorem

For \(x>1\) and \(s=\beta+i\gamma\), define the centered reflected-Euler transition
\[
  q_x(s):=x+1-x^s-x^{1-s}.
  \tag{1}
\]
Let \(p,q>1\) satisfy
\[
  \frac{\log p}{\log q}\notin\mathbb Q.
  \tag{2}
\]
If \(\gamma\ne0\) and
\[
  q_p(s),q_q(s)\in\mathbb R,
  \tag{3}
\]
then
\[
  \boxed{\beta=\frac12.}
  \tag{4}
\]

Conversely, \(\beta=\tfrac12\) makes \(q_x(s)\) real for every \(x>1\).

For \(p=2,q=3\), condition `(2)` is unconditional: a rational relation between
\(\log2\) and \(\log3\) would give a nontrivial equality \(2^m=3^n\).

## Proof

Direct expansion gives
\[
\begin{aligned}
 \Im\!\left(x^s+x^{1-s}\right)
 &=x^\beta\sin(\gamma\log x)-x^{1-\beta}\sin(\gamma\log x)\\
 &=(x^\beta-x^{1-\beta})\sin(\gamma\log x).
\end{aligned}
\tag{5}
\]
Since \(x+1\) is real, reality of \(q_x(s)\) is equivalent to vanishing of `(5)`.

Assume \(\beta\ne\tfrac12\).  Then \(x^\beta-x^{1-\beta}\ne0\) for every \(x>1\), so `(3)` gives
\[
  \sin(\gamma\log p)=\sin(\gamma\log q)=0.
  \tag{6}
\]
There are integers \(m,n\) with
\[
  \gamma\log p=m\pi,\qquad \gamma\log q=n\pi.
  \tag{7}
\]
Because \(\gamma\ne0\) and \(\log p,\log q>0\), both \(m,n\) are nonzero.  Dividing `(7)` yields
\[
  \frac{\log p}{\log q}=\frac mn\in\mathbb Q,
\]
contradicting `(2)`.  Hence `(4)` holds.

If \(\beta=\tfrac12\), then
\[
  x^s+x^{1-s}
  =2\sqrt x\,\cos(\gamma\log x)\in\mathbb R,
\]
proving the converse.

## Riemann specialization

The exact finite-source prime-enlargement law in the corpus is
\[
  \Xi_{P\cup\{p\}}(s)
  =-q_p(s)\,\Xi_P(s).
  \tag{8}
\]
At a zero \(\rho\), the same scalar acts on the top conormal jet.  Nontrivial zeta zeros are
nonreal.  Therefore RH follows from the strictly weaker-looking source theorem
\[
  q_2(\rho)\in\mathbb R
  \quad\text{and}\quad
  q_3(\rho)\in\mathbb R
  \qquad
  \text{for every nontrivial Xi conormal.}
  \tag{9}
\]

No positivity, all-prime moderation, full unitary character, norm equality, or multiplicity
estimate is needed after `(9)`.

## What this changes

The previous consumers asked that every prime character
\[
  p^{\rho-1/2}
\]
be unitary.  The theorem shows that the final source comparison can be weakened to a rank-two
real-reduction problem:

```text
old target:
  construct a common positive/unitary all-prime conormal completion.

reduced target:
  construct one source-first real structure on the two literal conormal transitions q_2 and q_3.
```

This does not make `(9)` automatic.  A real self-adjoint source operator can have a complex
eigenvalue on a non-tempered analytic generalized eigenfunctional.  Thus the remaining theorem
is still a landing/real-reduction theorem, but it no longer requires an all-prime norm or a
distributional growth classification.

## Anti-theatre audit

1. The selector is elementary and carries no novelty claim.
2. Reality in `(9)` is RH-bearing; it must be derived before zero specialization.
3. Reality of the underlying Fourier or Poisson source does not imply `(9)`: complex evaluation
   of a real entire source can be nonreal.
4. Commutativity of the two prime transitions does not imply their scalar values are real.
5. A Hermitian metric placed on each zero fibre after reading \(\rho\) is circular.

## Gates

- [x] complete paper proof
- [x] isolate exact \(2,3\) specialization
- [x] identify source-transition formula already present in corpus
- [ ] derive two-prime real reduction from literal source before divisor specialization
- [x] formalize elementary selector in Lean — `GaloisForLFunctions.RHTower.EulerTransitionSelector`;
      axioms `[propext, Classical.choice, Quot.sound]`
- [ ] RH

## Log

- 2026-07-31 — proved exact two-prime real-transition selector and reduced the final consumer from
  all-prime unitarity to source-first reality at primes \(2\) and \(3\).

## Lean formalization — 2026-08-17

`formal/GaloisForLFunctions/RHTower/EulerTransitionSelector.lean`, unconditional
(`#print axioms` = `[propext, Classical.choice, Quot.sound]`).

| Paper step | Lean name |
|---|---|
| (1) the centered reflected-Euler transition `q_x(s)` | `eulerTransition` |
| the polar form of `x^s` for real `x>0` | `im_cpow_ofReal` |
| (5) `Im(x^s + x^(1-s)) = (x^beta - x^(1-beta)) sin(gamma log x)` | `im_eulerTransition` |
| reality of `q_x(s)` is `beta = 1/2` or `sin(gamma log x) = 0` | `im_eulerTransition_eq_zero_iff` |
| (6)-(7) and (4): two irrationally related bases force `beta = 1/2` | `re_eq_half_of_im_eulerTransition_eq_zero` |
| the converse at `beta = 1/2` | `im_eulerTransition_eq_zero_of_re_eq_half` |
| the closed form `x + 1 - 2 sqrt(x) cos(gamma log x)` on the critical line | `eulerTransition_re_eq_half` |
| the unconditional `p = 2`, `q = 3` specialization | `re_eq_half_of_two_three` |

Multiplicative independence of `2` and `3` is discharged inside `re_eq_half_of_two_three` from the
corpus lemma `RHTower.irrational_log_div_log` together with `2 ∤ 3`.

Not formalized, and not obligations of this card's theorem: gate "derive two-prime real reduction
from literal source before divisor specialization" and gate "RH".  Both are open research targets of
the surrounding programme — the card itself states that the selector "does not make (9) automatic"
and that the remaining reduction is a separate landing theorem.  The theorem stated on this card,
including its converse and its `2,3` specialization, is fully formalized.

## Log

- 2026-08-17 Formalized the elementary selector in Lean 4 and promoted to stage 3.  The two
  remaining gates are programme targets (source-side reality, RH), not parts of the proved theorem.
