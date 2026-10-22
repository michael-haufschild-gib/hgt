# Hedenmalm theta anomaly--Burnol canonical synthesis

- **ID:** `hedenmalm-theta-anomaly-burnol-canonical-synthesis`
- **Stage:** 1-in-progress
- **Label:** `P-G113`
- **Type:** `[THEOREM (LEAN)] [SINGULAR CONNECTOR] [EXACT MINIMALITY] [NO-GO CLOSURE]`
- **Parents:** `P-G111`, `P-G112`

## Frozen conjecture

Replace arbitrary entire Bezout choices by source-canonical pointwise synthesis. For completed
Burnol frame `a=(a2,a3)`, define

```text
E(z)=|a2(z)|^2+|a3(z)|^2,
b*(z)=(conj(a2(z))/E(z), conj(a3(z))/E(z)).
```

Prove frame is nowhere zero on all `C`, `b* dot a=1`, and `b*` is unique minimum-energy synthesis.
Derive exact excess square for every other synthesis. Then test reflection: if canonical energy is
even, close finite-prime least-energy orientation route and preserve connector as positive survivor.

## Complete paper proof `[PROVED HERE]`

At zero, prime-two completed cell is nonzero. Off zero, simultaneous vanishing would give a common
zero of centered prime-two/three multipliers, impossible by irrationality of `log(2)/log(3)`.
Hence `E(z)>0` everywhere and `b*` is defined.

For arbitrary complex `b2,b3,a2,a3`, direct expansion gives Lagrange identity

```text
(|b2|^2+|b3|^2)(|a2|^2+|a3|^2)
 = |b2 a2+b3 a3|^2
   + |b2 conj(a3)-b3 conj(a2)|^2.
```

Under synthesis constraint `b2 a2+b3 a3=1`, divide by positive `E`:

```text
||b||^2 - 1/E
 = |b2 conj(a3)-b3 conj(a2)|^2/E >= 0.
```

Canonical row has zero determinant, energy exactly `1/E`, and is unique at equality by solving the
two linear equations. P-G112's universal escape gives
`max(||b2*(t)||,||b3*(t)||)>=t/4` for every `t>0`.

Real structure of entire cells gives `a(conj z)=conj(a(z))`; therefore `E(conj z)=E(z)` and
`b*(conj z)=conj(b*(z))`. On each Xi multiplicity copy, canonical row reconstructs divisor quotient
one exactly, while minimum synthesis energy is unchanged by critical-line reflection.

## Scientific delta

P-G113 constructs previously missing finite-prime singular connector rather than postulating a
rigging. It is canonical, globally defined, quantitatively singular, and uniquely characterized by
an exact excess-square law. This closes connector-existence/minimality portion of Route P.

Hostile test also gives exact no-go closure: least-energy finite-prime synthesis is reflection-even
and cannot orient forward versus reflected translation. Orientation must be a non-minimal
source-order coupling (the transverse determinant term), or genuinely nonlocal/all-prime transport,
before final positive scalar reduction. Merely changing norm or choosing another Bezout row adds
the explicit nonnegative transverse square and supplies no canonical sign.

## External novelty audit

Targeted primary-source search checked Burnol's co-Poisson/Sonine papers and searches for a
co-Poisson two-cell Moore--Penrose/corona construction. Located literature develops co-Poisson
intertwining, Sonine spaces, Hilbert evaluators, and zeta-zero complete/minimal systems. No located
source identifies Hedenmalm's completed prime anomaly cells with a nowhere-zero two-prime frame,
constructs this canonical singular inverse, or states its exact transverse excess law and
reflection-even Xi specialization. General finite-frame pseudoinverse/Lagrange algebra is standard;
novelty claim is restricted to source-exact Burnol/Hedenmalm/Xi specialization and resulting Route-P
topology/orientation classification.

## Falsifiers

- Completed two-prime Burnol frame has a common zero.
- Moore--Penrose row fails to reconstruct one.
- Another synthesis has lower or equal energy without being canonical.
- Excess is not exact transverse determinant square divided by frame energy.
- Canonical row or energy fails critical-line reflection covariance.

## Gates

- [x] conjecture frozen with connector and hostile reflection test
- [x] completed frame nowhere-zero theorem formalized
- [x] canonical synthesis identity formalized
- [x] Lagrange excess-square/minimality theorem formalized
- [x] unique minimizer theorem formalized
- [x] order-one boundary escape transported to canonical row
- [x] Xi quotient reconstruction formalized
- [x] reflection-even energy no-go formalized
- [x] direct `lake env lean` passes
- [x] exact module `lake build` passes (`12935` jobs)
- [x] module wired into `RHTower.lean`
- [x] external novelty audit
- [x] capstone axiom audit contains only standard Lean foundations
- [x] full `GaloisForLFunctions.RHTower` umbrella build passes (`19790` jobs)
- [ ] repository lint passes (blocked by 41 pre-existing unrelated unreachable modules)

## Lean status

Umbrella-wired module
`formal/GaloisForLFunctions/RHTower/HedenmalmThetaAnomalyBurnolCanonicalSynthesis.lean` contains
complete result. Direct `lake env lean` and exact module build pass.

## Log

- 2026-08-13 — P-G113 frozen after P-G112 proved algebraic corona with forced linear escape.
- 2026-08-13 — Canonical singular connector, exact excess square, unique minimality, Xi quotient
  reconstruction, and reflection-even no-go proved in Lean; exact build and external novelty audit
  passed.
- 2026-08-13 — Capstone axiom audit passed (`propext`, `Classical.choice`, `Quot.sound` only) and
  full RHTower umbrella build passed; repository lint reached unrelated pre-existing reachability debt.
