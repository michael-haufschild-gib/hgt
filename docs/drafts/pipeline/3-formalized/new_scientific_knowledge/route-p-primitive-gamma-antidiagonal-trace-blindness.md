# Route P primitive Gamma antidiagonal trace blindness

- **ID:** `route-p-primitive-gamma-antidiagonal-trace-blindness`
- **Stage:** 3-formalized
- **Label:** `P-G192`
- **Source:** P-G191 forced antidiagonal, P-G190 double-Green flux, W-H184 matrix-complete endpoint
- **Statement:** The physical Gamma reporter has an exact visible/hidden Pythagorean energy split.
  Its canonical P-G191 antidiagonal Wold current has zero report but strictly positive, globally
  summable Gram trace. Therefore antidiagonal shorting cannot provide Route P's Loewner trace
  transport; the hidden channel must be retained inside a matrix-complete colligation.

## Conjecture loop and falsification

`C192-A` proposed mapping the full quadratic source current coefficientwise into P-G191's forced
antidiagonal and using physical codiagonal cancellation as the missing completed shorting. This is
formally definable but fails the no-theatre audit. Route P needs Loewner domination of the complete
zero Gram, not vanishing of one coherent scalar observation. A nonzero antidiagonal vector is
precisely a counterexample to that inference.

The pivot was to measure exactly how much energy the physical reporter forgets and test P-G190's
literal source current against W-H184's matrix criterion.

## Exact visible/hidden law

For a fixed pair of primitive cells let

```text
E = physical cooriented Gamma exterior,
R_E(x,y) = xE+yE,
H(x,y) = x-y.
```

Lean proves the division-free identity

```text
2 E^2 (x^2+y^2) = R_E(x,y)^2 + E^2 H(x,y)^2.                (1)
```

The first term is visible codiagonal energy. The second is the exact antidiagonal energy discarded
by the reporter. Equation `(1)` remains valid at the balanced section and introduces no inverse
Gamma factor.

Let `Q_i` be the positive P-G190 double-Green flux and

```text
A_ij = sqrt(Q_i Q_j),
W_ij = (A_ij,-A_ij).
```

Then

```text
R_E(W_ij)=0,
energy(W_ij)=2 Q_i Q_j>0.                                    (2)
```

Consequently no scalar `C` can satisfy

```text
energy(z) <= C R_E(z)^2                                      (3)
```

for all resolved currents, and every linear observer applied after `R_E` is nonconservative on
the one-dimensional Wold sector.

## Matrix-complete obstruction

Complexify the same current as the two-column packet

```text
v_ij=(A_ij,-A_ij).
```

Its Gram is positive semidefinite and Lean proves

```text
sum_k v_ij(k)=0,
Re Tr Gram(v_ij)=2 Q_i Q_j>0.                                (4)
```

The trace family in `(4)` is globally summable over all ordered primitive cell pairs. Nevertheless
the Gram is not Loewner-dominated by zero, and its trace is not bounded by the squared norm of its
coherent sum. This is the literal source-derived version of the earlier abstract two-column
cancellation warning in `FrankensteinMatrixCompleteBoundaryRestriction.lean`.

Thus a coefficientwise antidiagonal lift of the full quadratic current would preserve, not remove,
positive Gram trace. Its codiagonal vanishing cannot yield W-H184.

## Higher universal principle

P-G191 and P-G192 expose two inequivalent notions of conservation:

```text
charge conservation: codiagonal = 0,
energy conservation: ||visible||^2 + ||hidden||^2 = source budget.
```

Physical Gamma coorientation observes charge. Route P's RH endpoint observes matrix energy.
Antidiagonal shorting kills the first while concentrating the second. The repeated obstruction
behind scalar passivity, reflection pairing, and resolved codiagonal cancellation is therefore
one principle: a quotient that enforces charge conservation is never energy conservative on its
kernel.

## Positive survivor and next producer

The antidiagonal is still useful, but only as a retained defect output of a contractive or lossless
colligation. A viable continuation of Route P must:

1. construct a source-defined matrix-complete boundary operator at the P-G185 wall;
2. carry both physical codiagonal and antidiagonal Wold output through the energy identity;
3. bound the hidden trace inside P-G184's fixed `<2` source budget;
4. land coefficient-faithfully on the raw completed-Xi conormal matrix before divisor expansion.

Simply proving that the completed quadratic current lies in an antidiagonal kernel is retired.
P-G192 does not construct W-H184 and does not prove RH.

## Hostile novelty audit

The corpus already proved abstract codiagonal blindness and exhibited a constant packet `(1,-1)`
with zero coherent sum and trace two. P-G192 does not claim those general facts as new. Its new
content is the exact coupling to the actual physical Gamma reporter and canonical P-G190 current:

- division-free visible/hidden identity `(1)`;
- failure of every reporter-energy coercive bound `(3)`;
- nonconservativity of all post-reporter observers on the source-derived Wold sector;
- exact double-Green Gram trace `(4)` and global trace summability;
- direct failure of zero Loewner domination for that literal Route P packet.

## Lean certificate

Module:

```text
formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaAntidiagonalTraceBlindness.lean
```

Capstones:

- `routePPrimitiveGammaResolvedReporter_pythagorean`;
- `not_exists_routePPrimitiveGammaResolvedEnergy_le_reporter_sq`;
- `routePPrimitiveGammaResolvedWoldSector_no_postReporter_conservativity`;
- `re_trace_routePPrimitiveGammaResolvedWoldPacket_gram`;
- `summable_re_trace_routePPrimitiveGammaResolvedWoldPacket_gram`;
- `not_routePPrimitiveGammaResolvedWoldPacket_gram_le_zero`;
- `routePPrimitiveGammaResolvedWoldPacket_not_trace_le_coherentNormSq`.

Verification:

- `/tmp/pg192.lean`: `lake env lean /tmp/pg192.lean` passed cleanly;
- exact leaf build passed; no umbrella build run;
- `/tmp/pg192_audit.lean`: capstones depend only on `propext`, `Classical.choice`, `Quot.sound`;
- targeted forbidden-declaration scan clean;
- umbrella import wired without building umbrella.

## Gates

- [x] antidiagonal-lift conjecture tested against actual Route P endpoint
- [x] coherent-shorting transport falsified
- [x] strongest positive survivor extracted
- [x] visible/hidden Pythagorean identity proved
- [x] source-native noncoercivity and nonconservativity proved
- [x] exact positive Gram trace and global summability proved
- [x] Loewner-zero and coherent-norm implications refuted
- [x] scratch verification
- [x] exact leaf build only
- [x] axiom and forbidden-declaration audit
- [x] umbrella wired without umbrella build
- [ ] construct energy-retaining matrix-complete pole--Gamma colligation
- [ ] prove W-H184 unconditionally
- [ ] unconditional RH
