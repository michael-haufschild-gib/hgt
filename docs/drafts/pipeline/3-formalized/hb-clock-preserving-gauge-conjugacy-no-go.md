# HB clock-preserving gauge conjugacy no-go

- **ID:** HB-CLOCK-GAUGE-NOGO-001
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / ROUTE CLASSIFICATION
- **Source:** `rh-current-frontier-map.md` · HB finite physical-clock producer
- **Statement:** Conjugating literal anti-linear source-FE transport by any invertible packet automorphism that commutes with the source-predeclared centered-QNM clock cannot change finite-clock covariance; in particular the Hilbert-90 amplitude gauge trivializes the FE cocycle but leaves unit-clock covariance equivalent to RH.

## Goal

Kill the complete clock-preserving gauge/normalization escape from the hardest live HB premise.
Exact RH chain under test:

`literal mixed-Casimir Einstein--Teukolsky source`
`→ source-FE packet transport, possibly after invertible packet-coordinate normalization`
`→ covariance with one source-predeclared nonzero centered-QNM physical clock step`
`→ universal complete-cokernel extinction`
`→ RH`.

The theorem shows that every invertible normalization preserving the physical clock has zero
producer power: it can re-present or even trivialize the source cocycle, but it cannot manufacture
the missing covariance identity. It forces any surviving producer to alter the physical
clock, mix clock eigenspaces nonlocally, or arise from genuine Einstein--Teukolsky dynamics rather
than a packet gauge.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: Lean theorem, targeted `lake build` green, axiom audit and lint PASS
- [ ] 3 → 4 publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Corpus-derived conjecture and proof route

Let `T` be literal anti-linear source-FE packet transport and `U_t` the fixed centered-QNM
physical clock step. Let `G,H` be packet maps satisfying `H ∘ G = id`, `G ∘ H = id`, and
`G U_t = U_t G`. Define the conjugated transport `T^G = H ∘ T ∘ G`.

**Conjecture HB-CG2.** Full packet covariance `T^G U_t = U_t T^G` is equivalent to literal
covariance `T U_t = U_t T`. Therefore, for every real `t`, gauged covariance is equivalent to
`t=0 or RH`; at unit time it is equivalent to RH.

Attack: transport the commutation identity across `G` and `H`. The reverse direction applies `G`
to the gauged identity at `H x`; the forward direction expands `T^G`, commutes `G` through `U_t`,
and derives commutation of `H` with `U_t` from inverse identities. No linearity, topology, norm,
or basis decomposition should be needed.

Then instantiate with the explicit diagonal Hilbert-90 amplitude gauge. Existing corpus theorems
give a nowhere-zero gauge `b_src`, an inverse diagonal weight, and
`T^b_src(c e_q)=conjugate(c)e_Rq`. Diagonal weights commute with `U_t` coefficientwise. Hence even
this pure reflection/conjugation presentation is unit-clock covariant iff RH.

## Conjecture loop and hostile checks

1. **HB-CG0 failed — cocycle realification as producer.** Corpus theorem
   `hbXiPeierlsUnitSourceAmplitudeGauge_conjugatedTransport_apply` trivializes the anti-linear FE
   cocycle to one unconditionally, while the finite-clock endpoint remains RH-strength. Cocycle
   phase is not the spectral obstruction.
2. **HB-CG1 too narrow — diagonal gauges only.** Direct coefficient cancellation would prove
   invariance for nowhere-zero diagonal weights, but leave arbitrary physical packet-coordinate
   normalizations open.
3. **HB-CG2 surviving — all invertible clock-preserving automorphisms.** Conjugacy algebra covers
   every packet map preserving the fixed physical clock, including diagonal Hilbert-90 gauges.

Failure criteria:

- semilinearity of `T` invalidates the conjugacy transport argument;
- one-sided inverse data are insufficient;
- clock commutation of `G` fails to force clock commutation of `H`;
- explicit amplitude gauge is not a genuine inverse packet automorphism;
- corpus already contains the exact source-FE/QNM classification.

All five checks must be discharged before promotion.

## Paper proof `[PROVED HERE]`

Write `U=U_t`. First derive clock preservation for the inverse gauge. For every packet `x`,

`H(Ux) = H(U(G(Hx))) = H(G(U(Hx))) = U(Hx)`.

The first and last equalities use `G H=id` and `H G=id`; the middle equality uses `G U=U G`.
Thus `H U=U H`.

Assume literal covariance `T U=U T`. Then

`T^G U = H T G U = H T U G = H U T G = U H T G = U T^G`.

Conversely assume `T^G U=U T^G`. Evaluate it on `H x`:

`H T G U Hx = U H T G Hx`.

Using `G U=U G` and `G H=id` gives `H T Ux=U H Tx`. Apply `G`; use `G H=id` and
`G U=U G` again to obtain `T Ux=U Tx`. Hence the two covariance laws are equivalent. This proof
uses no linearity of `T`, so anti-linearity creates no exception.

For a nowhere-zero diagonal weight `b`, take

`G_b(x)(q)=b(q)x(q)`, `H_b(x)(q)=b(q)^(-1)x(q)`.

Pointwise cancellation gives both inverse laws. Because the physical clock is diagonal,
`G_b U_t=U_t G_b`. Therefore the general theorem applies to the corpus definition
`hbXiPeierlsDiagonalGaugeConjugatedUnitSourceFETransport b`. Existing finite-clock rigidity gives

`T^b U_t=U_t T^b  <->  t=0 or RH`.

Finally the explicit amplitude gauge is nowhere zero and existing Hilbert-90 transport proves
`T^b_src(x)(r)=conjugate(x(Rr))`: its cocycle is identically one. At `t=1`, the displayed
classification nevertheless gives covariance iff RH. Thus cocycle triviality and physical-clock
covariance are independent obstructions in the exact claimed sense.

All dependencies are existing closed corpus theorems and elementary function composition. No
analytic, PDE, divisor-placement, or RH premise enters the proof.

## Novelty and significance audit

Corpus searches:

- `scripts/formal_tools.py research "clock preserving gauge conjugated transport covariance"`
- `scripts/formal_tools.py research "Hilbert 90 amplitude gauge physical clock step covariance"`
- `scripts/formal_tools.py research "diagonal gauge conjugated unit source FE transport"`
- `scripts/formal_tools.py research "centered QNM physical clock covariant iff RH"`

These found generic gauge covariance elsewhere, the explicit source-amplitude Hilbert-90 gauge,
and the literal finite-clock RH endpoint, but no theorem separating unconditional cocycle
trivialization from the gauge-invariant physical-clock obstruction.

Primary-literature audit through 2026-08-31 found standard similarity transformations and
antilinear-symmetry classifications (Mostafazadeh, arXiv:math-ph/0203005), non-Hermitian symmetry
commutators (Simon Martinez--Buendia--Muga, arXiv:1805.04968), and Kerr Teukolsky reflection
currents (Green--Hollands--Sberna--Toomani--Zimmerman, arXiv:2210.15935). Generic conjugacy algebra
is therefore not novel. Search found no Xi/source-FE theorem, no Hilbert-90 versus physical-clock
separation, and no classification of clock-preserving source normalizations as an RH-terminal
route. Novelty claim is restricted to that exact source-native no-go and its survivor.

## No-go closure

- **Exact killing theorem/mechanism:** conjugating source-FE transport by any invertible packet map
  in the commutant of the predeclared clock preserves and reflects the missing covariance identity.
  Hence no clock-preserving normalization can be its producer.
- **Strongest positive survivor:** fixed-clock covariance is a
  conjugacy invariant under every invertible clock-preserving packet gauge, even when FE cocycle
  itself is globally gauge-trivial.
- **New insight:** source-cocycle cohomology separates from physical-clock defect;
  surviving producer must change dynamics rather than coordinates.
- **Status:** dependency-closed paper proof and closed Lean formalization in
  `ThetaCuspHawkingBMClockPreservingGaugeConjugacyNoGo`.

## Lean certificate

Module:
`GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMClockPreservingGaugeConjugacyNoGo`.

Principal declarations:

- `HBXiPeierlsClockPreservingGauge.backward_clock`;
- `hbXiPeierlsClockGaugeConjugatedUnitSourceFEPhysicalClockStepCovariant_iff`;
- `hbXiPeierlsDiagonalGaugeConjugatedUnitSourceFEPhysicalClockStepCovariant_iff`;
- `hbXiPeierlsUnitSourceAmplitudeGaugeTrivializationClockObstruction`;
- `d4HBClockPreservingGaugeConjugacyRouteKilled`.

Audit, 2026-08-31:

- direct `lake env lean` check: PASS;
- targeted module `lake build`: PASS (`12027/12027`);
- axiom audit: only `propext`, `Classical.choice`, `Quot.sound`;
- imported by `GaloisForLFunctions.RHTower` umbrella;
- corpus research index resolves capstone and Hilbert-90 specialization;
- global formal lint: PASS after concurrent owners finished two imports and the sole remaining
  already-closed `SelbergGeneralSineRecurrence` module was wired into `RHTower`.

## Log

- 2026-08-31 — created in 1-in-progress after corpus and primary-literature audits; HB-CG0 killed,
  HB-CG1 strengthened, HB-CG2 frozen for paper and Lean proof.
- 2026-08-31 — HB-CG2 and Hilbert-90 specialization proved on paper; all hostile failure criteria
  discharged; promoted to 2-fully-proven.
- 2026-08-31 — Lean module, stronger joint trivialization/clock-obstruction theorem, unconditional
  capstone, direct check, targeted build, axiom audit, umbrella import, and corpus indexing closed;
  Stage 3 promotion waits only for unrelated shared-worktree lint reachability.
- 2026-08-31 — global formal lint passed; promoted to 3-formalized.
