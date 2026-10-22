# Hedenmalm theta anomaly--Burnol affine-gauge classification

- **ID:** `hedenmalm-theta-anomaly-burnol-affine-gauge-classification`
- **Stage:** 1-in-progress
- **Label:** `P-G114`
- **Type:** `[THEOREM (LEAN)] [UNIVERSAL CLASSIFICATION] [NO-GO CLOSURE] [POSITIVE SURVIVOR]`
- **Parents:** `P-G113`

## Frozen conjecture

Classify every right inverse of completed two-prime Burnol frame, not only minimum-energy inverse.
Conjecture synthesis fibre is affine line

```text
b(c;z) = b*(z) + c(z) (a3(z), -a2(z)),
```

with unique gauge obtained from transverse determinant. Prove exact energy splitting. Then test every
reflection-real gauge: if positive energy remains even, retire all finite-prime positive-norm
orientation and preserve unsquared gauge phase as sole survivor.

## Complete paper proof `[PROVED HERE]`

Let `a=(a2,a3)`, `E=|a2|^2+|a3|^2>0`, and let `b` satisfy `b2 a2+b3 a3=1`. Define

```text
c = (b2 conj(a3)-b3 conj(a2))/E.
```

Multiplying synthesis identity by `conj(a2)` and `conj(a3)` gives

```text
b2 E = conj(a2) + c E a3,
b3 E = conj(a3) - c E a2.
```

Division by `E` proves affine classification. Conversely every affine row synthesizes one, and its
transverse determinant is exactly `cE`, so gauge is unique. P-G113's Lagrange excess law becomes

```text
||b(c;z)||^2 = 1/E(z) + |c(z)|^2 E(z).
```

Under critical-line conjugation, source-real frame has `a(conj z)=conj(a(z))`. Any source-real gauge
obeys `c(conj z)=conj(c(z))`. Therefore both terms in energy formula are reflection-even. But
`Im(c(conj z))=-Im(c(z))`: unsquared imaginary gauge is reflection-odd and positive scalarization
is exactly operation erasing it.

## Scientific delta

P-G113's minimal no-go is upgraded to exhaustive classification of every finite-prime right inverse.
Changing Bezout row, choosing nonminimal synthesis, or changing positive coefficient norm cannot
orient Route P while respecting source real structure: all such energies are canonical even term
plus nonnegative even gauge term.

Higher universal principle: repeated Route-P stalls are shadows of **positive scalarization after
reflection-real synthesis**. Reflection orientation lives in symplectic/transverse gauge phase;
Hermitian squaring sends it to modulus and destroys sign. Surviving producer must couple unsquared
gauge to a source-ordered boundary current before positive reduction. If no source-canonical gauge
has faithful sign, finite-prime synthesis must yield to all-prime nonlocal transport.

## External novelty audit

Targeted primary-source search covered Burnol's co-Poisson intertwining and Sonine-space papers,
plus searches for co-Poisson two-cell corona/Moore--Penrose classifications. Located literature
develops co-Poisson harmonic/Hilbert structure and zeta-zero evaluators, but no located source states
this completed Hedenmalm anomaly-frame affine classification, exact gauge-energy law, or Xi
reflection-even/odd split. Affine kernel parameterization and finite-dimensional Lagrange identity
are standard; novelty claim is limited to source-exact Burnol/Hedenmalm specialization and exhaustive
Route-P consequence.

## Falsifiers

- A synthesis row is not in claimed affine family.
- Gauge fails uniqueness or fails exact determinant formula.
- Energy has cross term not captured by `1/E+|c|^2 E`.
- Reflection-real affine energy is not even.
- Unsquared imaginary gauge fails reflection oddness.

## Gates

- [x] conjecture frozen with exhaustive quantifier and hostile reflection test
- [x] affine synthesis and gauge inverse identities formalized
- [x] every synthesis classified formalized
- [x] exact all-synthesis energy law formalized
- [x] reflection-real energy-even theorem formalized
- [x] unsquared imaginary-gauge odd survivor formalized
- [x] Xi multiplicity-copy capstone formalized
- [x] direct `lake env lean` passes
- [x] exact module `lake build` passes (`12936` jobs)
- [x] module wired into `RHTower.lean`
- [x] external novelty audit
- [x] capstone axiom audit contains only standard Lean foundations
- [x] full `GaloisForLFunctions.RHTower` umbrella build passes (`19790` jobs)
- [ ] repository lint passes (blocked by 41 pre-existing unrelated unreachable modules)

## Lean status

Umbrella-wired module
`formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaAnomalyBurnolAffineGaugeClassification.lean`
contains complete result. Direct `lake env lean` and exact module build pass.

## Log

- 2026-08-13 — P-G114 frozen after P-G113 showed canonical connector is reflection-even.
- 2026-08-13 — All-synthesis affine classification, exact energy split, exhaustive reflection-even
  no-go, and odd gauge-phase survivor proved in Lean; exact build and external novelty audit passed.
- 2026-08-13 — Capstone axiom audit passed (`propext`, `Classical.choice`, `Quot.sound` only) and
  full RHTower umbrella build passed; repository lint reached unrelated pre-existing reachability debt.
