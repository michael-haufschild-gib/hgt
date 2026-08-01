# Universal static Choi complexity plateau

- **ID:** universal-static-choi-complexity-plateau
- **Stage:** 2-fully-proven
- **Type:** THEOREM
- **Status:** `[PROVED HERE]`; dependency-closed Lean formalization pending
- **Role:** closes the geometric and completed-time parts of O3 in
  `../1-in-progress/static-local-complexity-law.md`

## Result

Let `H` be a Hermitian operator on a complex Hilbert space of dimension
`D >= 2`, with orthonormal eigenbasis `(e_j)` and eigenvalues `(E_j)`.  Write

\[
  \Phi_H(t)=D^{-1/2}\sum_{j=1}^D e^{-itE_j}
       e_j\otimes\overline{e_j}.
\]

This is the Choi state of `e^{-itH}`.  More generally, for
`z in T^D`, set

\[
  \Phi(z)=D^{-1/2}\sum_{j=1}^D z_j
       e_j\otimes\overline{e_j}.
\]

Let `Delta` be pure-state trace distance.  Fix `0 < delta < 1/2` and put

\[
  \eta_\delta=1-\sqrt{1-4\delta^2},\qquad
  B_D(\delta)=D e^{D/2}
      \left({\pi\eta_\delta\over2}\right)^{(D-1)/2}.
\]

Then, for every normalized target state `psi`, independently of the
eigenbasis,

\[
  \mu_{\mathbb T^D}\{z:\Delta(\Phi(z),\psi)\leq\delta\}
  \leq B_D(\delta).                                      \tag{1}
\]

Consequently, for every finite target dictionary `A`,

\[
  \mu_{\mathbb T^D}\{z:\exists\psi\in A,\
       \Delta(\Phi(z),\psi)\leq\delta\}
  \leq |A|B_D(\delta).                                   \tag{2}
\]

Let a discrete local gate alphabet offer at most `M >= 2` labelled gate
choices at every circuit step.  Circuits of length at most `s` produce at
most `M^(s+1)` target states, so

\[
  \mu_{\mathbb T^D}\{z:C_\delta(\Phi(z))\leq s\}
  \leq M^{s+1}B_D(\delta).                                \tag{3}
\]

For every fixed `delta` satisfying

\[
  \kappa_\delta:=-{1\over2}
      -{1\over2}\log\!\left({\pi\eta_\delta\over2}\right)>0,
\]

the right-hand side of (3) is exponentially small in `D` whenever
`s <= c_delta D / log M`, apart from the explicit lower-order `log D` term.
For local gates on `2n` qubits, `log M=O(log n)`, hence completed-time
complexity is `Omega(2^n/log n)` for all but `exp(-Omega(2^n))` of phase
time.

If the projective gaps of `H` are rationally independent, the phase flow is
uniquely ergodic on the projective torus.  Since the finite-circuit target in
(3) is closed, Portmanteau gives

\[
  \limsup_{T\to\infty}{1\over2T}
   \operatorname{Leb}\{t\in[-T,T]:C_\delta(\Phi_H(t))\leq s\}
  \leq M^{s+1}B_D(\delta).                                \tag{4}
\]

For the full-density fixed-`q` Pauli Gaussian ensemble with `q >= 2`, the
projective-gap premise holds almost surely by
`generic-two-local-spectral-monodromy.md`.  Equation (4) is therefore an
unconditional almost-sure static-local plateau law once that spectral theorem
is formally closed.

## Proof

### 1. A target ball is contained in one translated coherence target

If the left-hand target of (1) is empty there is nothing to prove.  Otherwise
choose `y` in it.  For any other `z` in the target, the triangle inequality
for pure-state trace distance gives

\[
  \Delta(\Phi(z),\Phi(y))\leq 2\delta.
\]

For pure states,

\[
  \Delta(\Phi(z),\Phi(y))^2
   =1-|\langle\Phi(z),\Phi(y)\rangle|^2,
\]

and orthonormality gives

\[
  \langle\Phi(z),\Phi(y)\rangle
    ={1\over D}\sum_j z_j\overline{y_j}.
\]

Hence every `z` in the ball satisfies

\[
  1-\eta_\delta=\sqrt{1-4\delta^2}
  \leq\left|{1\over D}\sum_jz_j\overline{y_j}\right|.
\]

Coordinatewise multiplication by `conj(y)` preserves product Haar measure.
Thus the target ball has no more Haar mass than the equal-weight coherence
target at defect `eta_delta`.

### 2. Exact torus entropy bound

`UniversalPhaseCoherenceTargetMeasure.lean` proves for every finite index
type of cardinality `D` and every `eta > 0` that the equal-weight target has
Haar mass at most

\[
  D e^{D/2}\left({\pi\eta\over2}\right)^{(D-1)/2}.
\]

Applying it at `eta=eta_delta` proves (1).  Finite subadditivity proves (2).

### 3. Circuit union

A length-`ell` circuit is one word of length `ell` in at most `M` labelled
gate choices.  The number of words of length at most `s` is at most
`M^(s+1)` for `M >= 2`.  Apply (2) to the output states of those words to get
(3).  Taking logarithms gives the exact exponent

\[
  (s+1)\log M+\log D-\kappa_\delta(D-1)+{1\over2}.
\]

This has no hidden dimension-linear remainder.

### 4. Static completed time

Projective rational independence makes the deterministic phase flow converge
weakly to normalized Haar measure on the projective torus.  Fidelity and
circuit balls are global-phase invariant, so their projective Haar mass equals
their full-torus Haar mass.  A finite union of closed trace-distance balls is
closed.  The closed-set half of Portmanteau therefore turns (3) into (4).

## What this closes and what it does not

This theorem closes a robust maximal-complexity **occupation plateau** for the
static Choi/thermofield-double trajectory.  It needs no Haar-random eigenbasis,
unitary design, ETH, mixing, stochastic drive, or complexity-class separation.
It is compatible with an efficient all-time non-Haar locality witness.

It does **not** prove pointwise linear growth from time zero, an exponentially
late first cut, or a doubly exponential first low-complexity recurrence.
Those remain O4 and O5 of the master card.  Long-time density alone cannot be
silently promoted to a first-hitting theorem.

## Initial collision audit

- Oszmaniec--Kotowski--Horodecki--Hunter-Jones prove saturation and recurrence
  for random circuits and stochastic local Hamiltonians using approximate
  equidistribution on the ambient state/unitary spaces.  They explicitly state
  that a concrete time-independent Hamiltonian remains out of reach.
- Kotowski--Oszmaniec--Horodecki treat static random-matrix Hamiltonians; their
  ensemble is nonlocal and its eigenbasis randomness is load-bearing.
- Guo--Sasieta--Swingle already occupy the slogan that complexity need not be
  randomness.  Novelty here is the eigenbasis-free spectral-torus bound and
  its deterministic static-local completed-time consequence, not that slogan.

Exact-title and mechanism searches found no theorem giving (1)--(4) for every
eigenbasis and static Hamiltonian with full projective spectral rank.  This is
an initial clean audit, not the final citation-graph/expert audit.

## Formalization plan

1. Define the finite equal-weight phase-state embedding and prove its inner
   product identity.
2. Formalize pure-state trace distance and its triangle inequality, or reuse an
   existing projective metric with the identical fidelity formula.
3. Prove target-ball domination by a translated `torusCoherenceTarget`.
4. Reuse `measureReal_torusCoherenceTarget_le_optimized` for (1).
5. Formalize finite dictionary and word-count union bounds for (2)--(3).
6. Combine with `FiniteSpectralHaarRecurrenceLaw` and Portmanteau for (4).
7. Audit axioms and wire all modules into their umbrellas before stage 3.

