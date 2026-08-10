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
- [x] 2 → 3: Lean certified — `HTGeometry.ConstitutiveAntisymmetricWallResponse`
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

## Lean certification status (2026-08-09) — COMPLETE

Module: `GaloisForLFunctions.HTGeometry.ConstitutiveAntisymmetricWallResponse`
(wired into `HTGeometry.UniversalLawField`).

The extension, the charges `z₁, z₂` of (2), their phase order and the stability classification are
**reused** from `ConstitutiveStabilityWall` (the Lean certification of
`a2-law-stability-wall-positive-chamber-erasure-law.md`); the intervention response and the fact
that it is a genuine derivative are **reused** from `ConstitutivePositiveResponse`.  Nothing is
rebuilt.

Clause 1, equation (3): `wallPositivePacket θ = (1, 1, 4 cos²θ)` (`wallPositivePacket_eq`) and
`wallPositivePacket_even` proves `𝒫(−θ) = 𝒫(θ)`.  The two unit entries come from
`constitutivePositiveDoctrine_unit_phase` and the third from `wallCharge_sum`.

Clause 2, equations (4)–(5): `wallCharge₁_re θ = −sin θ` and `wallCharge₂_re θ = sin θ` are new.
`wallResponse₁_hasDerivAt` and `wallResponse₂_hasDerivAt` certify (4) in the strong sense — the
component responses really are `d/dε|₀ |z_j + ε|²`, via
`constitutivePositiveDoctrine_hasDerivAt_intervention` with the intervention `h = 1` fixed before
the wall is observed.  `antisymmetricWallResponse_eq` is (5): `Δ(θ) = 4 sin θ`.

Clause 3, equations (6)–(8): `wallFamily_unstable_iff_neg` and `wallFamily_semistable_iff_zero` are
new and complete the trichotomy that `ConstitutiveStabilityWall` had only on the stable side
(`wallFamily_stable_iff_pos`).  The instability half uses the swapped cross product
`im_mul_conj_swap` together with `wallCharge_cross`; the semistable half uses `arg_eq_of_arg_eq` at
`θ = 0`, where the two charges coincide.  `sin_pos_iff_of_abs_lt`, `sin_neg_iff_of_abs_lt` and
`sin_eq_zero_iff_of_abs_lt` convert the sign of `θ` into the sign of `Δ`, giving
`stable_iff_response_pos`, `semistable_iff_response_zero` and `unstable_iff_response_neg`.

`antisymmetric_response_selects_chamber` bundles all three clauses, and
`antisymmetric_response_not_factoring` certifies the exact field consequence: at `θ` and `−θ` the
complete passive packet agrees while `Δ` changes sign, so this response provably does not factor
through the positive quotient.

`#print axioms` on `wallPositivePacket_eq`, `wallPositivePacket_even`, `wallResponse₁_hasDerivAt`,
`antisymmetricWallResponse_eq`, `wallFamily_unstable_iff_neg`, `wallFamily_semistable_iff_zero`,
`stable_iff_response_pos`, `semistable_iff_response_zero`, `unstable_iff_response_neg`,
`antisymmetric_response_selects_chamber`, and `antisymmetric_response_not_factoring` reports only
`propext`, `Classical.choice`, and `Quot.sound`.
