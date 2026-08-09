# Resolution and time do not commute for static-local complexity

- **ID:** `resolution-time-noncommutativity-static-local-complexity-law`
- **Stage:** 2 -- fully proved on paper
- **Type:** theorem / singular observer-resolution law / static-local complexity
- **Parents:** `algebraic-two-local-instant-exact-complexity.md`,
  `instant-exact-complexity-calibration-singularity-law.md`
- **Status:** `[PAPER-PROVED] [FRONTIER ADVANCE] [NOVELTY UNVERIFIED] [LEAN DEFERRED]`
- **Date:** 2026-08-09

## Public sentence

For one ordinary rational two-local Hamiltonian, an ideal observer demanding exact equality sees
exponential circuit complexity at arbitrarily early nonzero times, whereas every observer with any
fixed positive resolution sees a genuinely easy interval after time zero.  Taking perfect
resolution and taking early time are different limits.

## Setup

Fix `n>=2`, put `D=2^n`, and use the rational traceless two-local Hamiltonian `H_n` and product
state `Omega` supplied by `algebraic-two-local-instant-exact-complexity.md`.  Let

\[
 \psi_n(t)=e^{-itH_n}\Omega,\qquad
 k_n=\left\lceil{D-1\over16}\right\rceil.                        \tag{1}
\]

Let `C_epsilon` be ancilla-free state-preparation complexity using arbitrary two-qubit unitaries
on arbitrary pairs, measured in Hilbert-space norm.  Let `Z_s` be the compact set of states
preparable by at most `s` such gates.  Compactness follows because there are finitely many support
patterns and each parameter space `U(4)^s` is compact.

Define the threshold history

\[
 I_{n,\epsilon}(t)
 =\mathbf 1\{C_\epsilon(\psi_n(t))\ge k_n\}.                     \tag{2}
\]

## Theorem A -- noncommuting resolution--time limits

For every `epsilon>0`,

\[
 I_{n,\epsilon}(t)=0
 \qquad\text{whenever}\qquad
 |t|\le {\epsilon\over\|H_n\|_{\rm op}}.                        \tag{3}
\]

For every nonzero algebraic real `t`, there is a number `delta_(n,t)>0` such that

\[
 I_{n,\epsilon}(t)=1
 \qquad(0\le\epsilon<\delta_{n,t}).                              \tag{4}
\]

Consequently

\[
 \boxed{
 \lim_{\epsilon\downarrow0}\ \lim_{t\to0}I_{n,\epsilon}(t)=0,
 \qquad
 \lim_{\substack{t\to0\\t\in\overline{\mathbb Q}\setminus\{0\}}}
       \ \lim_{\epsilon\downarrow0}I_{n,\epsilon}(t)=1.}        \tag{5}
\]

The second limit is taken along real algebraic times.  Thus the two operations do not commute even
for a fixed finite system and one fixed time-independent two-local Hamiltonian.

### Proof

Duhamel's formula gives

\[
 \|\psi_n(t)-\Omega\|\le |t|\,\|H_n\|_{\rm op}.                 \tag{6}
\]

Under `(3)`, the zero-gate preparation `Omega` is within `epsilon`, so
`C_epsilon(psi_n(t))=0<k_n`.

At every nonzero algebraic time the parent theorem gives

\[
 C_0(\psi_n(t))\ge {D-1\over16},                                \tag{7}
\]

and integrality gives `C_0(psi_n(t))>=k_n`.  Hence
`psi_n(t) notin Z_(k_n-1)`.  Since that circuit layer is compact,

\[
 \delta_{n,t}
 =d(\psi_n(t),Z_{k_n-1})>0.                                    \tag{8}
\]

For every `epsilon<delta_(n,t)`, no circuit of length below `k_n` enters the epsilon-ball, proving
`(4)`.  Equation `(3)` gives the first iterated limit in `(5)`, while `(4)` and density of the
nonzero real algebraic numbers at zero give the second.

## Theorem B -- finite-window robust stratification

Fix `T>0` and define

\[
 E_{n,T}=\{t\in[-T,T]:C_0(\psi_n(t))<k_n\}.                     \tag{9}
\]

Then `E_(n,T)` is finite.  For every open set `U` containing `E_(n,T)`, there is a
`delta_(n,T,U)>0` such that

\[
 \boxed{
 C_\epsilon(\psi_n(t))\ge k_n
 \quad\text{for all }t\in[-T,T]\setminus U
 \text{ and }0\le\epsilon<\delta_{n,T,U}.}                     \tag{10}
\]

### Proof

Local finiteness of the exact low-complexity times is Theorem B of the first parent card, applied
with `s=k_n-1`; on a compact interval it gives finiteness of `(9)`.  The set

\[
 K=[-T,T]\setminus U                                             \tag{11}
\]

is compact and its continuous orbit image is disjoint from the compact set `Z_(k_n-1)`.  Their
distance

\[
 \delta_{n,T,U}=d(\psi_n(K),Z_{k_n-1})                           \tag{12}
\]

is therefore strictly positive.  Equation `(10)` follows directly from the definition of
approximate complexity.

## Meaning for the Brown--Susskind law

The theorem changes which quantity can carry a physical growth law.  Exact endpoint complexity
does not grow from zero for this ordinary static-local system: it is already exponentially large
at every nonzero algebraic instant and at all but finitely many times in each bounded interval.
Finite observational resolution restores an easy early-time interval and turns the problem into a
positive-radius rate--distortion question.

Therefore a Brown ramp, if proved, is necessarily a law of the ordered triple

\[
 (\text{Hamiltonian time},\ \text{circuit budget},\ \text{observer resolution}),               \tag{13}
\]

not a resolution-free property of the exact state.  This statement does not prove the ramp's
rate.  It proves that the resolution variable is mathematically load-bearing rather than an
experimental afterthought.

## Black-hole interpretation boundary

The theorem does not identify a black-hole interior or a gravitational observable.  It supplies a
sharp warning for complexity--volume proposals: exact boundary-state complexity and operationally
resolved complexity can have incompatible early-time histories even under one fixed local
Hamiltonian.  Any claim that interior growth is dual to circuit growth must state the boundary
resolution before the time law is meaningful.

## Conjecturing and falsification ledger

### C0 -- exact transcendence seeds the Brown ramp

`[FALSIFIED]`.  Exact complexity is discontinuous and jumps to the exponential scale at
arbitrarily early algebraic times.

### C1 -- the jump is only a measure-zero algebraic curiosity

`[FALSIFIED]`.  The low exact-complexity set is locally finite, so the exponential exact lower
bound holds away from finitely many times on every compact window.

### C2 -- positive resolution is a harmless technical regularization

`[FALSIFIED]`.  Equation `(5)` proves a literal order-of-limits failure.  Every fixed resolution
creates an easy interval that the exact history lacks.

### C3 -- observer resolution is the missing Brown variable

`[PAPER-PROVED AS A NECESSARY VARIABLE, NOT AS A RATE LAW]`.  Theorems A--B prove necessity.  The
quenched constant-resolution growth rate for the ordinary random local ensemble remains the exact
open core.

## Hostile audit

1. The result is finite-dimensional and does not invoke thermodynamic or gravitational limits.
2. It proves noncommuting limits and robust stratification, not monotone Brown growth.
3. The lower robustness radius in Theorem B depends on `n,T,U`; no dimension-uniform bound is
   claimed.
4. Candidate novelty lies in the static-local complexity synthesis.  Order-of-limits phenomena and
   compact-set separation are classical mechanisms, so external priority remains unverified.
5. The theorem inherits the unformalized rational-specialization and circuit-transcendence layers
   of its first parent and may not enter the final paper before exact Lean closure.

## Exact next move

Prove a dimension-uniform version of `(10)` on the Brown schedule for the fixed-shell ordinary
local ensemble: one constant `epsilon>0`, circuit depth
`s(t)=Theta(min(B_n|t|,D)/log M_n)`, one return filtration, and quenched probability tending to one.
This is precisely the positive-radius separation that neither algebraic independence nor the
exact Bellman value supplies.

