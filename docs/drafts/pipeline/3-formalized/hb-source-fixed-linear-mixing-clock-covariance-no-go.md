# HB source-fixed linear mixing clock-covariance no-go

- **ID:** hb-source-fixed-linear-mixing-clock-covariance-no-go
- **Stage:** 3-formalized
- **Type:** PROVED / ROUTE-CLASS NO-GO
- **Source:** HB live core; survivors isolated by
  `ThetaCuspHawkingBMClockPreservingGaugeConjugacyNoGo` and
  `ThetaCuspHawkingBMFinitePhysicalClockStepCovarianceRigidity`
- **Statement:** No arbitrary invertible static complex-linear packet mixing can make conjugated
  source-FE transport commute with one fixed nonzero physical clock while retaining every literal
  source packet, except under RH.

## Goal and exact RH chain

Kill strongest static linear-mixing survivor left after diagonal and clock-preserving gauge no-gos:

```text
source-fixed arbitrary linear packet mixing
  -> conjugated source-FE covariance at one predeclared nonzero clock step
  -> complete HB causal-orbit extinction
  -> source-FE unit clock gain
  -> shared HB/FZZ-P/PW-B/RBH Ward cancellation
  -> RH.
```

## Gates

- [x] 0 -> 1: corpus-derived conjecture and exact RH chain frozen
- [x] 1 -> 2: dependency-closed paper proof and hostile audit
- [x] 2 -> 3: premise-free Lean certificate, umbrella wiring, targeted build, axiom audit
- [ ] 3 -> 4: publication-ready exposition and independent priority review

## Internal frontier

- `[CORPUS]` Full literal finite-clock covariance at nonzero time is already exactly RH.
- `[CORPUS]` Arbitrary clock-preserving conjugacies cannot alter covariance.
- `[CORPUS]` Diagonal source-fixed gauges are already rigid.
- `[CORPUS]` Source amplitudes vanish exactly on the critical wall, so every tilted orbit supplies
  two nonzero source anchors.
- Exact corpus search on 2026-08-31 found no arbitrary non-clock-preserving `LinearEquiv`
  classification retaining literal source packets.

## External frontier

Moving-mirror literature treats intrinsically time-dependent evolution, backreaction, radiation,
noise, and dissipation; examples include Weinstein, *Moving Mirrors, Black Holes, Hawking
Radiation and All That* (arXiv:gr-qc/0111027), and Butera, *Noise and dissipation on a moving
mirror induced by the dynamical Casimir emission* (arXiv:2306.03813). Generic linear fixed-vector
arguments and operator commutators are classical. Targeted primary-source search through
2026-08-31 found no source-fixed HB packet-mixing/physical-clock classification or local
source-displacement survivor law. Novelty is claimed only for this exact route classification,
pending independent priority review.

## Conjecture C-HB.2 — proved

Let `V` be finite-support Xi packets, `T` literal anti-linear source-FE transport, `U_t` the fixed
centered Birmingham--Mokhtari physical clock, and `G : V ≃ₗ[ℂ] V` arbitrary. Assume `G` fixes the
literal source packet at every Xi copy, with no diagonality, locality, topology, clock, pairing,
support, reflection, norm, or basis-preservation hypothesis. Put `T_G = G⁻¹ T G`. Then

```text
there exists such G with T_G U_t = U_t T_G
  iff t = 0 or RH.
```

At unit time, existence is exactly RH.

## Complete paper proof

At an off-wall Xi copy `q`, literal source amplitude `a_q` is nonzero. If complex-linear `G` fixes
`single(q,a_q)`, then cancellation of `a_q` shows that `G` fixes `single(q,1)`, hence the entire
coordinate line. Reflection sends `q` to another off-wall copy `Rq`; fixing its literal source
likewise makes `G⁻¹` fix the whole `Rq` line. Therefore `G⁻¹ T G` equals literal `T` on every
packet supported at `q`.

If `T_G` commutes with `U_t`, specialize covariance to `single(q,1)`. The preceding orbit rigidity
turns it into literal `T U_t = U_t T` at `q`. Existing single-orbit clock classification gives
`t = 0` or `Re(q)=1/2`. At nonzero time every Xi zero copy lies on the wall, which is RH.
Conversely, identity equivalence witnesses zero time; under RH literal covariance holds, so identity
also witnesses arbitrary time.

## No-go closure

- **Exact killing theorem:**
  `hbXiPeierlsExistsUnitSourceFixedLinearGaugePhysicalClockStepCovariant_iff`.
- **Unit-clock endpoint:**
  `hbXiPeierlsExistsUnitSourceFixedLinearGaugeUnitPhysicalClockStepCovariant_iff_rh`.
- **Strongest positive survivor:**
  `hbXiPeierlsLinearGaugeClockCovariant_sourceDisplacement_of_offLine`: at nonzero time, any
  clock-covariant linear mixing on a tilted FE orbit must displace at least one of its two literal
  source packets.
- **New insight:** arbitrary global eigenspace mixing buys nothing while literal source incidence
  is retained. Remaining HB producer must be source-changing, nonlinear, or time-dependent.
- **Status:** `[LEAN-PROVED]`; static source-fixed complex-linear mixing route killed.

## Lean formalization

Module:
`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceFixedLinearMixingClockCovarianceNoGo`

Closed certificate:
`d4HBSourceFixedLinearMixingClockCovarianceRouteKilled`.

Audit on 2026-08-31: direct `lake env lean` passed; targeted module build passed; all main
declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`, with no project axiom,
premise, hypothesis, `sorry`, `admit`, `opaque`, or `unsafe` declaration. Global lint's only
reported error was an unrelated concurrently-created unwired HTGeometry module; re-audit pending
shared-tree settlement.

## Log

- 2026-08-31 — C-HB.2 frozen from corpus endpoint and exact source-to-clock RH chain.
- 2026-08-31 — arbitrary source-fixed linear mixing route killed; exact source-displacement
  survivor formalized; module wired, built, and axiom-audited.

