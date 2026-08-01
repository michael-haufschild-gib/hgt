# Static circuitwise temporal min-entropy

- **ID:** `static-circuitwise-temporal-min-entropy`
- **Stage:** 5-failed
- **Type:** NO-GO WITH POSITIVE SURVIVOR
- **Parent:** `../1-in-progress/static-local-complexity-law.md`
- **Status:** `[FALSE AT REQUIRED SCALE] [PAPER PROOF] [LEAN EXACT PERIODIC CENTER AND TUBE PROVED]`

## Retired claim

For a fixed finite local gate alphabet of size `M`, define

\[
Q_{\varepsilon,s}^{\rm short}(t)
=\sup_{C:\,|C|\leq s}
\Pr_H\{\Delta(\Phi_H(t),C\Phi_0)\leq\varepsilon\}.
\]

The proposed route required

\[
-\log Q_{\varepsilon,s}^{\rm short}(t)
\geq (s+1)\log M+\gamma_n(t)
\]

for `s` proportional to normalized physical time.  A union over circuit words
would then have proved ballistic robust complexity.  This estimate is false.

## Countermechanism

Write the `m`-parameter Pauli ensemble as
`H(J)=sum_(a=1)^m J_a P_a`, where every `P_a` has operator norm one, and fix a
nonidentity Pauli word `P_1`.  For large `t`, choose an integer `k` for which
`u_t=2 pi k/t` lies in a fixed compact interval bounded away from zero.  At

\[
J^{(0)}=(u_t,0,\ldots,0)
\]

the Hamiltonian has order-one energy scale and

\[
e^{-itH(J^{(0)})}=e^{-2\pi i kP_1}=I.
\]

If `||J-J^(0)||_infty <= epsilon/(2tm)`, then

\[
\|H(J)-H(J^{(0)})\|
\leq m\|J-J^{(0)}\|_\infty
\leq {\varepsilon\over2t}.
\]

Duhamel's inequality for self-adjoint generators gives

\[
\|e^{-itH(J)}-I\|
\leq t\|H(J)-H(J^{(0)})\|
\leq\varepsilon/2.
\]

`FiniteHorizonCStarPerturbationLaw.lean` proves this periodic-center shortcut
tube in arbitrary unital C-star algebras, without finite-dimensional,
commutativity, spectral or matrix assumptions.  It also proves an explicit
non-scalar two-level sign Hamiltonian with norm `|omega|`, exact identity
recurrence at every time `2 pi k / omega`, and the resulting fixed-shell
operator-norm error tube.  Thus periodicity, non-scalarity, fixed nonzero
energy and the `epsilon/|t|` stability scale are Lean-certified.  The
coefficient-box Gaussian mass lower bound is not yet formalized.

The coefficient box has volume `(epsilon/(tm))^m`.  A nondegenerate Gaussian
density has a positive lower bound on the fixed compact region containing
these boxes.  Hence

\[
Q_{\varepsilon,s}^{\rm short}(t)
\geq c_0^m\left({\varepsilon\over tm}\right)^m
\]

for every `s >= 0`, because the identity word is allowed.  Equivalently,

\[
-\log Q_{\varepsilon,s}^{\rm short}(t)
\leq m\log(tm/\varepsilon)+O(m).
\]

For exponential `t` and `s` proportional to `t/poly(n)`, this is
incompatible with the retired lower bound.  Conditioning on an order-one
energy scale does not remove the obstruction: the centers `J^(0)` already
have order-one norm.

## Positive survivor

Do not union-bound individual circuit words.  Study the complete shortcut
locus

\[
\mathcal B_{\varepsilon,s}(t)
=\{H:C_\varepsilon(\Phi_H(t))\leq s\}
\]

as one geometric subset of coefficient space.  The strongest failure bound
compatible with the countermechanism has power-law form in `t`, with exponent
proportional to `m`.  The live target is the aggregate word-escape estimate
`(O4.3)` in the parent card.  It would prove ballistic growth without paying
for the low-circuit dictionary one word at a time.

## No-go closure

Exact insight: low-complexity recurrence strata have polynomially small
tubular neighborhoods in a polynomial-parameter static ensemble.  Any method
requiring exponentially small capture probability for each fixed circuit is
therefore structurally impossible.  The positive replacement must exploit
global geometry or algebraic organization of all shortcut circuits at once.
