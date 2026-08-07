# Dyadic Gaussian action-shell certificate

- **ID:** `dyadic-gaussian-action-shell-certificate`
- **Stage:** 2 — fully proven on paper
- **Type:** THEOREM (paper)
- **Status:** `[PAPER-PROVED] [LEAN PENDING] [FRONTIER BRIDGE] [NOVELTY UNVERIFIED]`
- **Parent:** `../1-in-progress/oriented-no-shortcut-without-return-law.md`
- **Role:** Replace positive near-action counting by a collision-free multiscale reporter.

## Conjecturing loop

### Conjecture 1 — one centered Gaussian reporter

For a finite signed spectral packet

\[
 H(T)=\sum_{a\in S}c_a e^{-T^2\omega_a^2/2},\qquad
 P=\sum_{\omega_a=0}c_a,
\]

subtracting total signed mass from `H(T)` was conjectured to remove the
replica-crowding floor.

**Hostile attack — `[FALSIFIED]`.**  The centered kernel
`exp(-x^2/2)-1` tends to `-1` at large action.  It suppresses collisions but
leaves the far-action signed sector unsuppressed.  No annular localization or
useful absolute estimate survives.

### Conjecture 2 — two-scale Gaussian wavelet

Replace centering by the dyadic difference

\[
 W(T)=H(T)-H(2T)
     =\sum_a c_a\left(e^{-T^2\omega_a^2/2}
                  -e^{-2T^2\omega_a^2}\right).
\]

The scalar kernel is zero at action zero, quadratic near zero, and
exponentially small at large action.  It therefore isolates an action shell
without charging the exact-recurrence channel.

**Hostile attack — survived with correction.**  Signed coefficients can
still cancel inside one shell; `W(T)` is not positive mass.  The valid inverse
statement must start from an observed excess `||H(T)-P||`, not from positive
mass in the shell.  Exact telescoping then forces at least one shell to carry
the excess.

## Theorem

Let `S` be finite, `c_a` complex, and `omega_a` real.  Define `H`, `P`, and
`W` as above.  For every real `T` and natural `L`,

\[
 \boxed{H(T)-P=\sum_{j=0}^{L-1}W(2^jT)+H(2^LT)-P.}       \tag{1}
\]

Every exact collision is absent from every wavelet:

\[
 \boxed{W(T)=\sum_{\omega_a\ne0}c_a
   \left(e^{-T^2\omega_a^2/2}-e^{-2T^2\omega_a^2}\right).} \tag{2}
\]

Assume `T>=0`, `delta>0`, and `|omega_a|>=delta` whenever
`omega_a!=0`.  With `A=sum_a |c_a|`,

\[
 \boxed{\|H(2^LT)-P\|\le
 A\exp\!\left[-{(2^LT\delta)^2\over2}\right].}           \tag{3}
\]

Consequently,

\[
 \boxed{\|H(T)-P\|\le
 \sum_{j<L}\|W(2^jT)\|+
 A\exp\!\left[-{(2^LT\delta)^2\over2}\right].}           \tag{4}
\]

If `L>0`, `||H(T)-P||>=eta`, and the final term in `(4)` is at most
`eta/2`, then some `j<L` satisfies

\[
 \boxed{\|W(2^jT)\|\ge {\eta\over2L}.}                    \tag{5}
\]

## Proof

Equation `(2)` follows termwise: when `omega_a=0`, both Gaussian kernels are
one and their difference is zero.  Set `F(j)=H(2^jT)`.  Since
`W(2^jT)=F(j)-F(j+1)`, the finite sum telescopes to
`H(T)-H(2^LT)`, proving `(1)`.

For `(3)`, subtract `P` termwise.  Only nonzero actions remain.  For each of
them, monotonicity of `x |-> exp(-x^2/2)` on absolute action and the gap give

\[
 \left|e^{-(2^LT\omega_a)^2/2}\right|
 \le e^{-(2^LT\delta)^2/2}.
\]

The triangle inequality yields `(3)`.  Taking norms in `(1)` and applying
`(3)` proves `(4)`.  Under the assumptions of `(5)`, `(4)` forces the sum of
the first `L` shell norms to be at least `eta/2`; one term is therefore at
least their average `eta/(2L)`.

## Why this advances the open recurrence proof

The positive near-action reporter had a universal `delta/sqrt(r)` crowding
floor and could not survive the circuit union.  Equations `(2)`–`(5)` remove
the common exact-recurrence mass once, suppress both smaller and larger action
scales, and reduce any shortcut excess to one of only `L` collision-free
dyadic shells.  The remaining quenched task is narrower: bound a fixed-depth
circuit dictionary on each action shell, paying a logarithmic scale union
instead of repeatedly charging scalar recurrence.

This theorem does **not** prove the quenched local-Hamiltonian estimate.  It
provides the deterministic inverse reduction that the estimate can act on.

## Hostile review

- The law is deterministic and unconditional for every finite signed packet.
- It contains no positivity claim for signed shell amplitudes.
- It does not infer shell mass from one pointwise shortcut; the required input
  is a Gaussian-window excess above the exact collision plateau.
- Finite spectra and a positive nonzero-action gap are essential for the
  explicit terminal remainder.  The exact telescope `(1)`–`(2)` needs neither.
- Priority and terminology remain unaudited.  Until external comparison, this
  is a frontier bridge, not a claimed standalone novelty result.

## Gates

- [x] 0 -> 1: conjecture frozen; first version falsified
- [x] 1 -> 2: survivor proof complete and hostile-audited
- [ ] 2 -> 3: Lean theorem and axiom audit
- [ ] 3 -> 4: use only after priority audit and integration with quenched shell bound

## Log

- 2026-08-07 — Replaced failed centered reporter by dyadic Gaussian wavelet;
  proved collision erasure, telescope, terminal gap bound, and inverse shell
  certificate.
