# HB unit moving-horizon/AIME cancellation no-go

- **ID:** C-HB.1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Exact moving-horizon third-mass/AIME susceptibility is (>54) on every Xi copy; their unit-normalized reflection-defect sum vanishes iff the copy is critical.

## Goal
Kill HB subroute where physical moving-event-horizon third-mass response alone supplies the unit AIME/radiative `++` counterterm. Universal extinction of the literal unit sum is proved equivalent to RH.

## Gates
- [x] 0 → 1  corpus-derived exact conjecture and hostile test
- [x] 1 → 2  dependency-closed paper proof
- [x] 2 → 3  Lean certificate, targeted build, axioms audit
- [ ] 3 → 4  publication-ready

## Proof
Set `a=Re ρ`, `A=a(3-a)`, `B=(1-a)(2+a)`, and
`N=A²(2-B)+B²(2-A)+2AB`. Corpus identities give
`S=54 N (2-a)(a+1)/(A²B²)`. Since `0<a<1` and `0<A,B<2`,
`N>2AB`, `(2-a)(a+1)>2`, and `AB<4`; hence `S>54`. Off line, corpus uniqueness says cancellation by coefficient `c` holds iff `c=S`; therefore `c=1` is impossible. On line both defects vanish. Thus the unit sum vanishes pointwise iff `Re ρ=1/2`, and universally iff RH.

## Novelty audit
Corpus search found only positivity and uniqueness of `S`, not its magnitude gap or unit no-go. Primary literature through 2026-08 supplies massless topological-black-hole modes, AIME, QNM bilinear projection, and second-order Teukolsky sources, but no equivalent susceptibility theorem or RH consequence.

## Lean
- Module: `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingHBUnitMovingHorizonAIMECancellationNoGo`
- Capstone: `d4HBUnitMovingHorizonAIMECancellationRouteKilled`
- Direct `lake env lean`: PASS
- Targeted build: `11892/11892` PASS
- Axioms: `propext`, `Classical.choice`, `Quot.sound`
- Umbrella: wired into `GaloisForLFunctions.RHTower`
- Global lint: new module clean; existing unrelated umbrella-reachability failures remain

## No-go closure
- **Exact killing mechanism:** unique required coefficient is (S(q)>54), never unit.
- **Strongest positive survivor:** a successful moving-horizon completion must derive an amplified fibre-adaptive coefficient, or a non-AIME third-order cokernel channel.
- **New insight:** anti-alignment/passivity was too weak; magnitude normalization already excludes the literal physical unit sum.
- **Status:** paper- and Lean-proved; candidate novelty pending external expert review.
