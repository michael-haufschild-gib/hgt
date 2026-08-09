# A2 positive wall and antisymmetric intervention-response selection law

- **ID:** ULF-A2R-1
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** constitutive experimental mathematics
- **Statement:** One fixed additive intervention response recovers the side of an A2 stability wall that the full passive modulus packet erases.

## Goal

Join three nonisomorphic organs in one finite constitutive experiment: exact-law stability, positive
observation, and intervention response.

## Gates

- [x] 0 → 1: source central charges and intervention fixed before response
- [x] 1 → 2: exact wall/response equivalence proved below
- [ ] 2 → 3: no Lean formalization
- [ ] 3 → 4: no novelty/priority claim

## Setup

Use the fixed quiver extension

\[
0\longrightarrow S_2\longrightarrow E\longrightarrow S_1\longrightarrow0
\tag{1}
\]

from `a2-law-stability-wall-positive-chamber-erasure-law.md`. For
(-\pi/2<\theta<\pi/2), define

\[
z_1(\theta)=e^{i(\pi/2+\theta)},
\qquad
z_2(\theta)=e^{i(\pi/2-\theta)}.
\tag{2}
\]

The passive positive doctrine records

\[
\mathcal P(\theta)=\bigl(|z_1|^2,|z_2|^2,|z_1+z_2|^2\bigr)
=\bigl(1,1,4\cos^2\theta\bigr).
\tag{3}
\]

Fix before observing the wall the real additive intervention (h=1) on each central charge. Its
component responses are

\[
r_j(\theta)=\left.\frac d{d\varepsilon}\right|_0|z_j(\theta)+\varepsilon|^2
=2\operatorname{Re}z_j(\theta).
\tag{4}
\]

Define the antisymmetric response (\Delta=r_2-r_1).

## Theorem — intervention response exactly selects the erased chamber

For every (-\pi/2<\theta<\pi/2):

1. (\mathcal P(\theta)=\mathcal P(-\theta)), so passive positive data do not determine the
   chamber.
2. The response is
   \[
   \Delta(\theta)=4\sin\theta.
   \tag{5}
   \]
3. The exact-law stability classification is
   \[
   E\text{ stable}\iff\Delta(\theta)>0,
   \tag{6}
   \]
   \[
   E\text{ strictly semistable}\iff\Delta(\theta)=0,
   \tag{7}
   \]
   \[
   E\text{ unstable}\iff\Delta(\theta)<0.
   \tag{8}
   \]

Thus one source-fixed intervention derivative restores precisely the orientation of the stability wall
that the complete passive modulus packet loses.

### Proof

Equation (3) is even in (\theta). From (2),

\[
\operatorname{Re}z_1=-\sin\theta,
\qquad
\operatorname{Re}z_2=\sin\theta,
\]

so (4) gives (\Delta=4\sin\theta). The earlier A2 classification gives stability exactly when
(\arg z_2<\arg z_1), which in this interval is (\theta>0). Equations (6)--(8) follow. ∎

## Exact field consequence

"Positivity erases phase" is only an endpoint statement. It does not imply operational
unselectability. The correct test is whether legal source interventions descend through the positive
quotient:

- if all responses factor through (\mathcal P), chamber remains hidden;
- if a marked response is transverse, its sign can select the chamber exactly.

This theorem also shows why non-equivariance is only a necessary hint, not a conclusion: the response
must be proven to coincide with the desired law orientation.

## Hostile scope

The central charge and intervention are supplied in this finite model. No arithmetic source currently
derives their analogue. The theorem is a dependency-closed CEM calibration, not an RH selector or a
claim that all positivity walls admit such an intervention.

## Log

- 2026-08-09 — three-organ positive/stability/intervention response theorem proved; no Lean.
