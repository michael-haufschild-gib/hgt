# Autonomous return complexity reflection law

- **ID:** `autonomous-return-complexity-reflection-law`
- **Stage:** 2 -- fully proved on paper
- **Type:** theorem / autonomous recurrence reduction / robust circuit complexity
- **Parent:** `../1-in-progress/static-local-complexity-law.md`
- **Status:** `[PAPER-PROVED] [BRIDGE] [EXTERNAL PRIORITY OPEN] [LEAN DEFERRED]`
- **Date:** 2026-08-13

## Exact claim

Let `D>=1`, let `H` be Hermitian on `C^D`, and put

\[
 U_t=e^{-itH}.
\]

Write

\[
 \Phi(U)=(U\otimes I)\Phi_D,
 \qquad
 d_{\rm Ch}(U,V)
 =\sqrt{1-\left|{\operatorname{tr}(U^*V)\over D}\right|^2},
 \tag{1}
\]

where `Phi_D` is the normalized maximally entangled vector.  Thus `d_Ch` is trace distance between
the two pure Choi states, with global phase removed.

Fix a finite gate dictionary `G` closed under inverses.  Let

\[
 C_\epsilon(U)
 =\min\{\,|w|:w\in G^*,\ d_{\rm Ch}(W_w,U)\le\epsilon\,\},
 \tag{2}
\]

with value `infinity` if the set is empty.  For a proposed return time `R`, define its projective
return defect

\[
 \delta_R=d_{\rm Ch}(U_R,I).
 \tag{3}
\]

### Theorem A -- robust recurrence reflection

For every real `R,t` and every `epsilon>=0` with `epsilon+delta_R<1`,

\[
 \boxed{
 C_{\epsilon+\delta_R}(U_t)
 \le C_\epsilon(U_{R-t}),
 \qquad
 C_{\epsilon+\delta_R}(U_{R-t})
 \le C_\epsilon(U_t).}
 \tag{4}
\]

If `U_R` is a projective exact return, so `delta_R=0`, then

\[
 \boxed{C_\epsilon(U_{R-t})=C_\epsilon(U_t)}
 \qquad(t\in\mathbb R).
 \tag{5}
\]

Hence the robust circuit-complexity history on every exact autonomous return cycle is a palindrome
about `R/2`.

### Corollary A.1 -- growth forces the recurrence decline

For any `T>=0`, any integer `s>=0`, and every `t in [0,T]`,

\[
 C_{\epsilon+\delta_R}(U_t)>s
 \quad\Longrightarrow\quad
 C_\epsilon(U_{R-t})>s,
 \tag{6}
\]

while

\[
 C_\epsilon(U_t)\le s
 \quad\Longrightarrow\quad
 C_{\epsilon+\delta_R}(U_{R-t})\le s.
 \tag{7}
\]

Thus every proved lower growth envelope on `[0,T]` reappears, in reverse, as a lower envelope on
`[R-T,R]`, with only the return defect added to resolution.  Every simulation upper envelope is
reflected the same way.  No independent probabilistic estimate is needed for the shape of the
pre-return decline.

Equivalently, with

\[
 E_{s,\epsilon}=\{t:C_\epsilon(U_t)\le s\},
\]

one has the two inclusions

\[
 R-E_{s,\epsilon}\subseteq E_{s,\epsilon+\delta_R},
 \qquad
 R-E_{s,\epsilon+\delta_R}^{\,c}\subseteq E_{s,\epsilon}^{\,c}.
 \tag{8}
\]

For an exact return, `E_(s,epsilon)` is invariant under `t mapsto R-t`.

### Theorem B -- every circuit-length shell is reflected

For `ell>=0`, define the normalized endpoint-incidence shell

\[
 I_{\ell,\epsilon}(U)
 ={1\over M^\ell}
 \left|\{w\in G^\ell:d_{\rm Ch}(W_w,U)\le\epsilon\}\right|.       \tag{B1}
\]

Then, for every `ell`,

\[
 \boxed{
 I_{\ell,\epsilon}(U_{R-t})
 \le I_{\ell,\epsilon+\delta_R}(U_t),
 \qquad
 I_{\ell,\epsilon}(U_t)
 \le I_{\ell,\epsilon+\delta_R}(U_{R-t}).}                         \tag{B2}
\]

Consequently, for every nonnegative length-weight sequence `b=(b_ell)` and the extended positive
partition function

\[
 Z_{b,\epsilon}(U)=\sum_{\ell\ge0}b_\ell I_{\ell,\epsilon}(U),     \tag{B3}
\]

one has

\[
 \boxed{
 Z_{b,\epsilon}(U_{R-t})
 \le Z_{b,\epsilon+\delta_R}(U_t),
 \qquad
 Z_{b,\epsilon}(U_t)
 \le Z_{b,\epsilon+\delta_R}(U_{R-t}).}                            \tag{B4}
\]

At an exact projective return, equality holds in (B2) at every word length and in (B4) for every
nonnegative weighting:

\[
 I_{\ell,\epsilon}(U_{R-t})=I_{\ell,\epsilon}(U_t),
 \qquad
 Z_{b,\epsilon}(U_{R-t})=Z_{b,\epsilon}(U_t).                       \tag{B5}
\]

The choice `b_ell=a^ell`, `0<a<1`, is the endpoint Abel/Green accessibility profile.  Theorem B
therefore reflects the complete finite-temperature circuit-incidence spectrum; Theorem A is its
zero-temperature shortest-word edge.

## Proof

The Choi metric is bi-invariant.  Indeed,

\[
 \left|\operatorname{tr}((UA)^*(VA))\right|
 =\left|\operatorname{tr}(A^*U^*VA)\right|
 =\left|\operatorname{tr}(U^*V)\right|,
\]

and left invariance is immediate.  It is also invariant under simultaneous inversion because

\[
 \left|\operatorname{tr}((U^{-1})^*V^{-1})\right|
 =\left|\operatorname{tr}(UV^*)\right|
 =\left|\operatorname{tr}(U^*V)\right|.
 \tag{9}
\]

Inverse closure of the dictionary sends every word to an inverse word of the same length and is a
bijection.  Equation (9) therefore gives

\[
 C_\eta(U^{-1})=C_\eta(U)
 \tag{10}
\]

for every resolution `eta`.

The autonomous group law gives

\[
 U_{R-t}=U_RU_{-t}.
\]

Right invariance of the metric yields

\[
 d_{\rm Ch}(U_{R-t},U_{-t})
 =d_{\rm Ch}(U_R,I)=\delta_R.                 \tag{11}
\]

If a word is within `epsilon` of either endpoint in (11), the triangle inequality puts the same
word within `epsilon+delta_R` of the other.  Consequently

\[
 C_{\epsilon+\delta_R}(U_{R-t})\le C_\epsilon(U_{-t})
 =C_\epsilon(U_t),
\]

where (10) proves the equality.  Reversing the roles of the two endpoints in (11), then applying
(10) at resolution `epsilon+delta_R`, gives the other inequality in (4).  Equations (5)--(8) are
immediate.  QED.

For Theorem B, inverse closure gives a length-preserving bijection

\[
 (g_1,\ldots,g_\ell)
 \longmapsto(g_\ell^{-1},\ldots,g_1^{-1})
\]

whose endpoint is `W_w^(-1)`.  Inversion invariance of the metric therefore proves

\[
 I_{\ell,\eta}(U^{-1})=I_{\ell,\eta}(U)                              \tag{B6}
\]

for every shell and radius.  Equation (11) and the triangle inequality inject every word counted
by the left side of the first inequality in (B2) into the radius-`epsilon+delta_R` shell about
`U_(-t)`.  Apply (B6) to identify that count with the shell about `U_t`.  Reverse the two endpoints
for the other inequality.  Nonnegative summation proves (B4); `delta_R=0` proves (B5).  QED.

## General form

The proof uses only:

1. an autonomous one-parameter subgroup;
2. a bi-invariant metric on its group;
3. a resource dictionary whose word cost is invariant under inversion.

Thus (4) holds verbatim for every reversible autonomous group evolution equipped with such a cost.
The quantum Choi statement is the operational specialization needed by the static-local complexity
programme.

## Conjecture loop and boundary

### C0 -- recurrence merely causes an isolated complexity collapse

Label: `[FALSIFIED]`.

An autonomous return does more than create one low-complexity point.  Equation (4) forces the whole
earlier complexity history to recur in reverse, up to the return defect.

### C1 -- the recurrence decline is an independent Brown--Susskind theorem obligation

Label: `[FALSIFIED]` for inverse-symmetric circuit cost.

Forward growth plus one return estimate already implies the matching decline by Corollary A.1.

### C2 -- recurrence reflection proves forward growth

Label: `[FALSIFIED]`.

Equation (4) is purely relational.  It cannot force either side to become complex.  Fast-forwardable
autonomous systems may remain easy throughout an exactly palindromic return cycle.

### C3 -- recurrence reflection locates the first return

Label: `[FALSIFIED]`.

The theorem is conditional on a chosen `R` only in the ordinary sense of evaluating its measured
defect `delta_R`; it gives no upper or lower bound on when a small defect first occurs.

### C4 -- shortest-word symmetry may hide asymmetric circuit multiplicity

Label: `[FALSIFIED FOR ENDPOINT INCIDENCE]` by Theorem B.

Every individual length shell and every positive endpoint partition function is reflected.  This
does **not** extend automatically to first-entrance path mass: inversion and word reversal exchange
prefix data with suffix data.  No first-hit palindrome is claimed.

## Hostile audit

1. **What is proved?** Exact radius-interlacing (4) for every finite autonomous quantum system and
   inverse-closed gate dictionary; shellwise endpoint-incidence reflection (B2); exact palindromes
   (5) and (B5) at a projective return.
2. **What part of the target moves?** Shape of the pre-return decline is removed as an independent
   problem.  Remaining hard inputs are forward growth/first cut, plateau duration, and a quantitative
   first-return scale.
3. **Is this the Brown--Susskind law?** No.
4. **Does it assert black-hole physics?** No.
5. **Is it novel?** Targeted searches found Brown--Susskind's qualitative rare complexity fall and
   rigorous recurrence results for stochastic dynamics, but no explicit robust reflection theorem.
   The proof is short group geometry, so this card is labeled `[BRIDGE]`; theorem-level priority and
   significance are not claimed.
6. **Why retain it?** It prevents duplicated effort on a recurrence-side ramp theorem and sharpens the
   full static-Hamiltonian target to a one-sided first-cut problem plus recurrence timing.
7. **Does Green reflection imply entrance reflection?** No.  Theorem B counts endpoint occupation at
   each word length.  First-entrance constraints are path-oriented and are not preserved by word
   reversal.

## External comparison

- Brown and Susskind, *The Second Law of Quantum Complexity*, Phys. Rev. D 97, 086015 (2018), draw
  and discuss a rare fall from maximal complexity near recurrence, but do not supply (4) as a robust
  circuit theorem.
- Oszmaniec, Kotowski, Horodecki, and Hunter-Jones, *Saturation and Recurrence of Quantum Complexity
  in Random Local Quantum Dynamics*, Phys. Rev. X 14, 041068 (2024), prove saturation and recurrence
  for random circuits and stochastic local Hamiltonian evolution, and explicitly leave ordinary
  fixed local Hamiltonians as the realistic next target.

## Formalization status

Lean is deliberately deferred during the shared corpus refactor.  No Lean process was started.  A
later formalization needs only finite-dimensional Choi trace distance, bi-invariance, inverse-word
bijection, the one-parameter group law, and the triangle inequality.
