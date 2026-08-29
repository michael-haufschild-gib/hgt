# Theta C5 center velocity: likelihood Bregman cone

Status: in progress  
Route: CLG/TTF, modular-center direct velocity (`C5-VP1`)  
Date: 2026-08-29

## RH proof chain

`likelihood Bregman cone + first-atom cone transfer`
`→ thetaCuspCenterFifthRootVelocityFirstAtomCurvatureCore ≥ 0`
`→ thetaCuspReflectedSourceFifthRootCurvatureVelocity 0 t > 0`
`→ modular-center C5 by seam anchoring and radial monotonicity`
`→ off-center fixed-action transport + higher packets + source-to-Weil no-escape`
`→ RH`.

## Corpus-derived conjecture C5-VP2

Write the completed center action and slope as

`A = Q - D`, `a = p - E`,

where `(Q,p)` is the first theta atom centered by the tangent of the exact higher-atom
log-partition at the modular seam. Then the higher atoms obey the strict Bregman cone

`0 < D < t E` for every `t > 0`.

The research target is not merely this decomposition: prove the resulting first-atom cone-transfer
inequality, or produce an exact counterexample and replace it by the strongest source-specific
survivor. Success removes the last actual full-source action and slope from `C5-VP1`; only explicit
first-atom Born--Witten geometry remains.

## Hostile falsifier

Generic convex Bregman data need not preserve an arbitrary cubic velocity polynomial. Therefore no
sign transfer may be assumed from `0 < D < tE`. Expand the exact C5 core along `(Q-sD,p-sE)` and
either prove its derivative has the required sign using theta first-atom identities, or formally
kill the generic cone transfer and retain the exact theta-specific residual condition.

## Novelty audit

Corpus search finds strict likelihood convexity, strict score monotonicity, center action convexity,
and the two likelihood-cumulant reserves, but no tangent-centered first-atom Bregman decomposition
of center C5 velocity. August 2026 literature search finds lower Laguerre/log-concavity results for
the Riemann Xi kernel, not this fifth-root velocity or Bregman cone law.

## 2026-08-29 closure of generic transfer branch

Status: generic cone transfer killed; source-specific survivor formalized.

- Exact killing theorem: `not_C5VelocityStrongTangentBregmanConeTransfer`.
- Mechanism: at positive curvature gap, C5 core remains negative for sufficiently small positive
  actual action, independently of third jet. Strict Bregman cone and tangent floors allow such
  abstract collapse.
- Strongest positive survivor:
  `c5VelocityActionCore_nonneg_iff_drive_pos_and_reserve`, exact positive-drive/action-reserve
  classification in curvature-dominant chamber.
- Theta-specific anti-collapse:
  `thetaCuspCenterLikelihoodBregmanSlope_lt_one` and
  `thetaCuspCenterLikelihoodBregmanAction_lt_self`; hence actual theta orbit cannot realize arbitrary
  generic collapse.
- Formal module:
  `GaloisForLFunctions.RHTower.ThetaCuspFifthRootCurvatureVelocityLikelihoodBregmanCone`.
- Surviving open core: prove theta source drive positivity and exact action-reserve barrier, with
  chamber split when slope square crosses first-atom curvature. This is precisely remaining
  `C5-VP1` center premise before velocity-to-C5 transport.

## 2026-08-29 conjecture C5-VP1-velocity

Status: frozen for paper attack; no Lean statement until dependency-closed proof.

For every `t > 0`,

`0 < thetaCuspReflectedSourceFifthRootCurvatureVelocity 0 t`.

This is stronger than stationary-locus C5 and is selected by the corpus normalization
`thetaCuspReflectedSourceFifthRootCurvatureVelocity_pos_iff_actionCore`. Its exact proof chain is

`strict center velocity`
`→ center C5 from the zero seam value by monotonicity`
`→ modular-center rank-four source sign`
`→ off-center fixed-action transport + higher packets + no escape`
`→ TTF/Weil positivity`
`→ RH`.

Hostile falsifier: one physical `t > 0` with nonpositive literal velocity. Generic Bregman or
positive-mixture cones cannot decide this sign: the formal saturated-channel and strong-tangent
cone no-go theorems already exclude those shortcuts. The attack must retain exact theta source
cooling or modular differential coupling.

Corpus inputs exposed for the first proof attempt:

- `thetaCuspLikelihoodSourceLogPartitionJetTwo_le_thirteen_tenths`;
- `strictAntiOn_expSix_mul_thetaCuspLikelihoodSourceLogPartitionJetTwo`;
- `six_mul_thetaCuspLikelihoodSourceLogPartitionJetTwo_lt_neg_jetThree`;
- `thetaCuspCenterFifthRootVelocityFirstAtomCurvatureCore_eq_bregmanCone`;
- the exact Born--Witten readout profiles for tangent slope, curvature, and third jet;
- the second--sixth Hankel seam certificate and cofinal first-atom limits.

First attempted transfer using only quadratic Bregman envelopes fails at the seam-leading order:
it destroys the exact even-source cancellations responsible for the eighth-order C5 opening.
Therefore the live proof attempt retains the differential coupling `D' = E`,
`E' = 2 likelihoodJetTwo`, and its strict support-gap cooling instead of replacing them by
independent bounds.

## 2026-08-29 closure of stripped first-atom-curvature branch

Status: sufficient branch killed; exact seam-essential likelihood survivor formalized.

The attempted premise

`∀ t > 0, 0 ≤ thetaCuspCenterFifthRootVelocityFirstAtomCurvatureCore t`

is false. Write

- `k = thetaCuspReflectedLogJetTwo 0 0`,
- `B = 2 * thetaCuspBornWittenLogCurvature 1 0`,
- `G = thetaCuspLikelihoodSourceLogPartitionJetTwo 0`.

The new seam identity is `k = B - 2G`, with `k > 0` and `G > 0`. The stripped core vanishes
through order two and has exact third seam jet

`15 * k * (k - B) = -30 * k * G < 0`.

Taylor transfer proves it is strictly negative throughout a punctured right neighborhood of the
modular seam. Hence the route

`global stripped-core nonnegativity → strict center velocity → C5-VP1`

is killed unconditionally, not merely left unsupported.

Strongest positive survivor: the exact second-likelihood correction discarded by the failed
reduction vanishes through order two, has third seam jet `30 * k * G > 0`, and its third jet sums
with the stripped core's third jet to exactly zero. The likelihood channel is therefore
seam-essential. A viable proof of `C5-VP1-velocity` must retain this cancellation and attack the
next surviving jet/full master-reserved core; it cannot prove the stripped core separately.

Lean module:
`GaloisForLFunctions.RHTower.ThetaCuspFifthRootCurvatureVelocityFirstAtomCurvatureSeamNoGo`.
Key route-kill theorem:
`not_forall_thetaCuspCenterFifthRootVelocityFirstAtomCurvatureCore_nonneg`.
Key survivor theorem:
`iteratedDeriv_three_thetaCuspCenterFirstAtomCore_add_secondLikelihoodCorrection_eq_zero`.

## 2026-08-29 conjecture C5-VP1-master-reserve-seam

Status: frozen for paper attack; intended outcome is a branch-level no-go.

Let

- `k = thetaCuspReflectedLogJetTwo 0 0`,
- `G₂ = thetaCuspLikelihoodSourceLogPartitionJetTwo 0`,
- `G₃ = thetaCuspLikelihoodSourceLogPartitionJetThree 0`.

Conjecture: the full master-reserved center-velocity core has exact fourth seam jet

`120 * k * (G₃ + 6 * G₂) < 0`,

and is therefore negative throughout a punctured right neighborhood of the modular seam. Hence
the sufficient premise

`∀ t > 0, 0 ≤ thetaCuspCenterFifthRootVelocityMasterReservedCore t`

is false.

Proof chain under test:

`global master-reserved-core nonnegativity`
`→ strict modular-center C5 velocity`
`→ center C5 by seam anchoring and radial monotonicity`
`→ fixed-action transport and higher-packet assembly`
`→ CLG/TTF or Weil polarization positivity`
`→ RH`.

The corpus forces the conjecture. On the positive ray,

`master = literal action + 10 * radius * t^2 * (G₃(t) + 6*G₂(t))`.

The literal center action core is odd, so its fourth seam jet vanishes. Radius has second seam jet
`k`; the product rule therefore gives the displayed coefficient. Strict support-gap cooling gives
`G₃ + 6*G₂ < 0`, while completed-source curvature gives `k > 0`.

Hostile falsifier: any missing fourth-order contribution from the literal action core, or failure
of smooth extension of the positive-ray identity to the seam. The proof must establish parity and
the right-germ extension explicitly; it may not infer derivatives from a one-sided equality.

Novelty audit: corpus search finds no master-reserved-core seam classification. It contains only
the newly proved cubic cancellation, the separate fixed-action adaptive-reserve fifth-order no-go,
and the literal eighth-order C5 seam opening. August 2026 primary-literature search finds the
Planat--Solé second-level Xi-kernel concavity theorem, but no fifth-root curvature velocity,
likelihood-reserve substitution, or fourth-order defect theorem.

## 2026-08-29 closure of master-reserved branch

Status: conjecture proved; sufficient branch killed; sharp defect survivor formalized.

The smooth seam proxy equal to `thetaCuspCenterFifthRootVelocityMasterReservedCore` for every
`t > 0` vanishes through order three and has exact fourth jet

`120 * k * (G₃ + 6 * G₂) < 0`.

The hostile falsifiers are discharged: the literal action core is proved odd and hence has zero
fourth jet, while the positive-ray master identity is transferred only after constructing a
two-sided smooth proxy. Taylor's theorem then gives punctured-right negativity. Therefore

`∀ t > 0, 0 ≤ thetaCuspCenterFifthRootVelocityMasterReservedCore t`

is false, killing the entire master-reserved sufficient route to `C5-VP1`.

Strongest positive survivor: the reserve error is now classified exactly. Replacing the literal
third likelihood jet by the uniform bound `-G₃ > 6G₂` preserves the cubic cancellation but creates
the first uncancelled seam term one order later. Thus a viable center-velocity proof must retain the
full third likelihood channel or use a correction whose fourth jet cancels
`120 * k * (G₃ + 6G₂)` exactly. No fixed uniform six-curvature reserve can close this gate.

Lean module:
`GaloisForLFunctions.RHTower.ThetaCuspFifthRootCurvatureVelocityMasterReservedSeamNoGo`.
Route-kill theorem:
`not_forall_thetaCuspCenterFifthRootVelocityMasterReservedCore_nonneg`.
Exact survivor theorem:
`thetaCuspCenterFifthRootVelocityMasterReservedSeamProxy_seamJetClassification`.

## 2026-08-29 conjecture C5-VP1-literal-velocity-far-tail

Status: frozen for paper and Lean attack; intended outcome is discharge of the full noncompact
literal-velocity premise.

Put `S(t) = thetaCuspSingleAtomReflectionScale 1 t`,
`r(t) = exp(thetaCuspReflectedLogAction 0 t) - 1`, and let `q₁,q₂,q₃` be the first three
literal reflected log jets at center. Conjecture:

`thetaCuspReflectedActionFifthRootVelocityCore r(t) t q₁(t) q₂(t) q₃(t)`
`  / (r(t) * t^2 * S(t)^3) -> 320` as `t -> +∞`.

Consequently the literal center velocity is strictly positive on a cofinal tail.

Proof chain being shortened:

`cofinal literal center-velocity positivity`
`→ confine C5-VP1 radial-monotonicity burden to one compact annulus`
`→ modular-center C5`
`→ fixed-action transport + higher packets + no escape`
`→ CLG/TTF or Weil polarization positivity`
`→ RH`.

Corpus mechanism: the exact first-atom likelihood factorization gives
`q₁/S -> 4`, while the already formalized far-tail jet laws give `q₂/S -> 8` and
`q₃/S -> 16`. The source action diverges, so `1/r -> 0`; also `1/t -> 0` and `1/S -> 0`.
After division by `r*t^2*S^3`, every term vanishes except the cubic term
`5*(q₁/S)^3 -> 5*4^3 = 320`.

Hostile falsifier: a higher-likelihood first jet surviving at scale `S`, failure of action-radius
divergence, or another action-core monomial surviving cubic normalization. Each is testable by an
exact limit, with no computation or numerical cutoff.

Novelty audit: corpus search finds the cofinal sign only for completed C5 seam orientation and for
the C5 numerator itself, not for literal center velocity. Planat--Solé (arXiv:2608.19160) proves
second-level concavity of the Xi kernel using a first-summand tail analysis, but does not state a
fifth-root divided-drop velocity law or the normalized coefficient `320`.
