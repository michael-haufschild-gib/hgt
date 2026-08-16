# Literal completed outgoing charge as an exact HG boundary trace

- **ID:** `ccm-unit-riesz-coherent-outgoing-charge-hankel`
- **Stage:** 3-formalized
- **Type:** LITERAL SOURCE WELD / RANK-ONE HG BLOCK / EXACT POLE-DOMINATION EQUIVALENCE
- **Scientific status:** `[UNCONDITIONALLY PROVED IN LEAN]`
  `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [EXTERNAL PRIORITY UNVERIFIED] [NOT AN RH PROOF]`
- **Formal module:**
  `formal/GaloisForLFunctions/RHTower/CCMUnitRieszCoherentOutgoingChargeHankel.lean`
- **Parents:** `ccm-unit-riesz-coherent-arithmetic-tail-charge`,
  `ccm-unit-riesz-coherent-finite-boundary-readout`

## Result

For integer aperture `N>=2`, define literal outgoing prime and polar charges by

```text
q_prime(N) = sum_(2<=k<=N) Lambda(k)/sqrt(N)
  * (1-exp(-(log N-log k)/2)),

q_polar(N) = sqrt(N) integral_(0,infinity)
  exp(-p)(1-exp(-p/2)) dp,

q_N = q_prime(N)-q_polar(N).
```

Lean evaluates actual continuum channel, rather than inserting its value as a constant:

```text
q_polar(N)=sqrt(N)/3,
q_N=R_1(log N)/2.
```

The source-defined outgoing profile

```text
ell_N(u)=q_N exp(-u/2)
```

is an HG `LeakProfile`. Its complete density, gap, and boundary trace are exact:

```text
leakDensity(ell_N,u)=q_N^2 exp(-u),
integral leakDensity=q_N^2,
hankelGapProfile(ell_N,u)=q_N^2 exp(-u),
boundaryRelativeTrace(ell_N,u)=q_N^2(1-exp(-u)).
```

Consequently its initial boundary slope is `R_1(log N)^2/4`, and all-aperture domination by the
canonical pole packet is equivalent to one arithmetic inequality:

```text
for every u>0,
  boundaryRelativeTrace(ell_N,u) <= boundaryRelativeTrace(polePacket,u)
iff
  R_1(log N)^2 <= 16.
```

## Scientific consequence

Completed unit-Riesz source has a canonical HG carrier without an infinite reconstruction or an
arbitrary profile choice: its literal outgoing base-state projection is the pure exponential HG
mode. Prime and polar source provenance survives in its coefficient before evaluation.

This also exposes a rigidity/no-go. Source and pole boundary traces are collinear copies of
`1-exp(-u)`. Therefore scalar HG aperture variation cannot create missing cancellation: checking
one positive aperture, the infinitesimal slope, or all apertures is exactly same arithmetic bound.
HG advances only if CCM geometry supplies independent contractivity of this outgoing coefficient,
or couples outgoing block to a nontrivial bulk/ground incidence. Recomputing scalar trace shape is
theatre.

## Claim-to-Lean closure

| Claim | Declaration |
|---|---|
| finite prime charge equals half coherent prime energy | `unitRieszCoherentPrimeOutgoingCharge_eq_energy_half` |
| literal polar continuum equals `sqrt N/3` | `unitRieszCoherentPolarOutgoingCharge_eq` |
| completed outgoing charge equals `R_1(log N)/2` | `unitRieszCoherentCompletedOutgoingCharge_eq_resolvent_half` |
| outgoing profile is exact resolvent exponential | `unitRieszCoherentCompletedOutgoingProfile_eq_resolvent` |
| profile continuity and HG admissibility | `continuous_unitRieszCoherentCompletedOutgoingProfile`, `leakProfile_unitRieszCoherentCompletedOutgoingProfile` |
| density and total energy | `leakDensity_unitRieszCoherentCompletedOutgoingProfile`, `integral_leakDensity_unitRieszCoherentCompletedOutgoingProfile` |
| exact Hankel gap and boundary trace | `hankelGapProfile_unitRieszCoherentCompletedOutgoingProfile`, `boundaryRelativeTrace_unitRieszCoherentCompletedOutgoingProfile` |
| exact initial slope | `tendsto_boundaryRelativeTrace_div_unitRieszCoherentCompletedOutgoingProfile` |
| slope-four equivalence | `unitRieszCoherentCompletedOutgoingProfile_density_le_four_iff` |
| all-aperture pole-domination equivalence | `unitRieszCoherentCompletedOutgoingProfile_le_pole_iff` |

All 13 theorem declarations have `#print axioms` output exactly
`[propext, Classical.choice, Quot.sound]`. Direct module check and exact leaf build pass. Module is
wired into `GaloisForLFunctions.RHTower`; umbrella itself was not built.

## Theatre and novelty audit

Pure-exponential integration is classical and not novel. Candidate novelty is exact composition

```text
literal finite von-Mangoldt outgoing charge
  - literal continuum polar outgoing charge
  = completed critical-Mellin aperture resolvent / 2
  = coefficient of canonical HG rank-one boundary block,
```

followed by exact all-aperture equivalence with pole domination. This is a source-specific theorem,
not generic profile calculus. It removes profile-construction ambiguity and proves scalar HG has no
extra aperture leverage. External priority remains unverified.

## New open core

Prove one non-circular CCM source/ground theorem forcing outgoing coefficient contractivity
`|q_N|<=2`, or any uniform integer-log bound sufficient for the now-formalized UR/FU endpoint.
The proof must use bulk-ground coupling, operator-valued completed covariance, or source-derived
restricted-Weil order; it cannot follow from scalar HG trace identities alone.

The receiver is no longer open. `CCMUnitRieszLogLatticeHandoff.lean` proves that a uniform bound on
`R_1(log N)` loses only an explicit additive constant between consecutive integer apertures.
`CCMUnitRieszResolventRHCriterion.lean` constructs a holomorphic defect extension from the bounded
resolvent, proves its equality with the regularized critical-Mellin defect by an
absolutely-continuous Abel identity across prime-power jumps and the identity theorem, and invokes
the divisor-tomography endpoint. In particular, pole domination of every literal outgoing block
implies RH in Lean. Therefore further lattice, Landau, or scalar-HG receiver work is theatre; the
sole open theorem is the non-circular producer of the integer-aperture bound.

## Gates

- [x] literal finite prime outgoing charge
- [x] literal continuum polar outgoing charge
- [x] completed-source coefficient weld
- [x] HG admissibility
- [x] exact gap, density, energy, and boundary trace
- [x] all-aperture pole-domination equivalence
- [x] unconditional Lean proof
- [x] exact leaf build and umbrella wiring
- [x] integer-log lattice-to-continuous handoff in Lean
- [x] bounded-resolvent-to-RH analytic endpoint in Lean
- [x] all-integer outgoing pole-domination-to-RH theorem in Lean
- [ ] independent mathematical audit
- [ ] external priority audit
- [ ] non-circular CCM contractivity/source-to-ground theorem
- [ ] RH

## Log

- 2026-08-16 -- Identified outgoing base-state projection of literal completed coherent source.
- 2026-08-16 -- Evaluated polar continuum and welded coefficient to half critical resolvent.
- 2026-08-16 -- Proved exact HG density, gap, energy, boundary trace, and initial slope.
- 2026-08-16 -- Proved all-aperture pole domination is exactly `R_1(log N)^2<=16`.
- 2026-08-16 -- Audited axioms, built exact leaf, and wired umbrella.
- 2026-08-16 -- Closed integer-log interpolation and bounded-resolvent analytic continuation to RH.
- 2026-08-16 -- Proved all-integer literal outgoing pole domination implies RH; only producer remains.
