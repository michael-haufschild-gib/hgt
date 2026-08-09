# Positive doctrine, additive intervention nondescendence, and response-coframe law

- **ID:** ULF-PIR-1
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** constitutive experimental mathematics
- **Statement:** Modulus-square positivity erases phase, but its first responses to two fixed additive interventions reconstruct the full complex law; no nonradial fixed intervention descends to the positive quotient.

## Goal

Construct one exact intervention--doctrine exchange theorem with a nonzero, jointly faithful response.
This is the first native CEM response square rather than a taxonomy.

## Gates

- [x] 0 → 1: fixed source law, doctrine, and interventions
- [x] 1 → 2: exact nondescendence, classification, and reconstruction proofs
- [ ] 2 → 3: no Lean formalization
- [ ] 3 → 4: no novelty/priority claim

## 1. Constitutive experiment

Let the source-law space be (\mathbb C^\times). The positive doctrine is

\[
P:\mathbb C^\times\longrightarrow\mathbb R_{>0},
\qquad P(z)=|z|^2.
\tag{1}
\]

For (h\in\mathbb C), define the local additive intervention

\[
I_{\varepsilon h}(z)=z+\varepsilon h
\tag{2}
\]

for real (\varepsilon) sufficiently close to zero. Its positive first response is

\[
\mathcal R_h(z)
=\left.\frac d{d\varepsilon}\right|_{\varepsilon=0}P(z+\varepsilon h)
=2\operatorname{Re}(\overline z h).
\tag{3}
\]

## Theorem 1 — fixed additive interventions do not descend through positivity

Let (h\ne0). There is no function (r_h:\mathbb R_{>0}\to\mathbb R) satisfying

\[
\mathcal R_h=r_h\circ P
\tag{4}
\]

on all of (\mathbb C^\times).

More generally, a vector field (V(z)) on (\mathbb C^\times) has positive first response
(2\operatorname{Re}(\overline zV(z))) descending through (P) exactly when this real scalar is
constant on every circle (|z|=r). Radial interventions (V(z)=a(|z|^2)z) with real (a) descend,
with response (2a(P(z))P(z)); fixed nonzero translations do not.

### Proof

The points (z) and (-z) have equal positive image, while

\[
\mathcal R_h(-z)=-\mathcal R_h(z).
\]

Choose (z=h), so (\mathcal R_h(z)=2|h|^2\ne0). Equation (4) is impossible. The general
classification is precisely the definition of factoring through the fibres of (P). The radial formula
is immediate from (3). ∎

## Theorem 2 — response coframe reconstructs erased law

The two fixed interventions (h=1) and (h=i) give

\[
\mathcal R_1(z)=2\operatorname{Re}z,
\qquad
\mathcal R_i(z)=2\operatorname{Im}z.
\tag{5}
\]

Hence the combined response map

\[
\mathcal R=(\mathcal R_1,\mathcal R_i):\mathbb C^\times\longrightarrow\mathbb R^2\setminus\{0\}
\tag{6}
\]

is exactly (\mathcal R(z)=2(\operatorname{Re}z,\operatorname{Im}z)), and therefore is injective.
The passive positive doctrine is phase-blind, but its marked two-intervention differential is
source-faithful.

### Proof

Write (z=x+iy). Then (\operatorname{Re}(\overline z)=x) and
(\operatorname{Re}(i\overline z)=y), proving (5)--(6). ∎

## Theorem 3 — constant positive observation, recurrent response, open phase history

For (z(t)=e^{it}),

\[
P(z(t))=1,
\qquad
\mathcal R(z(t))=2(\cos t,\sin t).
\tag{7}
\]

Thus the passive positive observation is constant, the intervention response is a recurrent circle,
and its basepoint phase lift (t\in\mathbb R) is open. After (N) response periods the passive
state and response return while the lift has advanced by (2\pi N).

### Proof

Equation (7) follows from (1) and Theorem 2. The final statement is the standard universal-cover lift
of (S^1). ∎

## 2. Constitutive meaning

This theorem separates three statements often conflated in route work:

1. positivity erases phase at endpoint level;
2. an individual fixed intervention fails to descend to that quotient;
3. a marked family of interventions reconstructs the erased phase from quotient response.

The missing datum is neither another endpoint invariant nor abstract curvature. It is the
**intervention response coframe**.

## 3. Exact prediction

For any proposed positive source doctrine, phase/orientation unselectability is not established merely
by showing endpoint blindness. One must also test the differential response to legal source
interventions. If a source-normal response coframe separates quotient fibres, phase is operationally
recoverable despite passive erasure. If every legal intervention is radial/equivariant, the phase
remains unidentifiable.

## 4. Hostile scope

This is elementary differential calculus and system identification. It does not construct legal
interventions for the arithmetic source, prove hypertranscendence, or imply RH. It passes a genuine
CEM gate because doctrine and intervention are fixed before response, the noncommuting/descent failure
is exact, and the full source state is reconstructed by a finite response family.

## Log

- 2026-08-09 — first nontrivial CEM intervention--doctrine response law proved on paper; no Lean.
