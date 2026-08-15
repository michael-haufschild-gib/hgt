# Route P primitive Burnol matrix-complete colligation

- **ID:** `route-p-primitive-burnol-matrix-complete-colligation`
- **Stage:** 3-formalized
- **Label:** `P-G194`
- **Source:** P-G186 Burnol source Gram, P-G187 aperture shift, P-G188 scalar defect colligation
- **Statement:** The literal transported-tail, hard-boundary, and tail-cocycle channels preserve the
  full complex half-line pairing. Therefore every finite primitive Burnol packet satisfies an exact
  three-channel Gram conservation law, and its transported Gram is Loewner-dominated by P-G186's
  source Gram with two explicit positive defect Grams as remainder.

## Conjecture loop

P-G193 showed that a canonical finite-aperture antidiagonal envelope can fit inside the scalar
source budget, but did not couple that envelope to P-G188's actual transported packet. `C194-A`
asked whether P-G188's scalar norm identity already polarizes before divisor landing.

The answer is yes. For square-integrable continuous half-line data define

```text
T_c f = weighted forward aperture shift,
B_c f = deleted hard-boundary interval,
D_c f = square-root tail cocycle defect.
```

Direct source-side integration proves the complex identity

```text
<T_c f,T_c g> + <B_c f,B_c g> + <D_c f,D_c g> = <f,g>.  (1)
```

No polarization premise is added: `(1)` follows from the exact pointwise partition

```text
((u-c)/u)^2 + [1-((u-c)/u)^2] = 1
```

on the translated tail, plus the disjoint hard-boundary interval.

## Matrix-complete conservation

All four literal functions are constructed as elements of `L²((0,infinity),C)`. The three outputs
form one Hilbert direct-sum vector. For every finite primitive packet `f_i`, Lean proves

```text
Gram(f_i) = Gram((T_c f_i,B_c f_i,D_c f_i))
          = Gram(T_c f_i) + Gram(B_c f_i) + Gram(D_c f_i).  (2)
```

P-G186 identifies the left side of `(2)` with the complete primitive base Cauchy cube, including
all off-diagonal ordinate interactions. Every matrix on the right is a literal Gram and hence
positive semidefinite. Consequently

```text
Gram(T_c f_i) <=_Loewner Gram(f_i),                        (3)
```

with exact positive remainder `Gram(B_c f_i)+Gram(D_c f_i)`.

## Higher universal principle

The repeated Route P failures came from scalarizing before completion. P-G194 shows completion and
matrix amplification commute because the aperture loss is a pointwise partition of unity. The
correct universal principle is:

```text
source-local partition of energy => completely positive Gram conservation.
```

No separate all-pairs energy estimate is needed for the actual colligation. P-G193 remains a valid
finite-aperture hidden-envelope theorem, but P-G194 identifies the canonical matrix-complete defect
as the two literal L2 outputs of P-G188.

## Hostile novelty audit

The corpus contained scalar P-G188 conservation and unrelated projection/dyadic Loewner laws. It
did not contain the complex cross-pairing identity `(1)`, the literal half-line L2 direct-sum
realization, P-G186's exact three-Gram decomposition `(2)`, or the Route P transported Loewner law
`(3)`. This still does not identify an actual completed-Xi residue packet as one output channel.

## Lean certificate

Module:

```text
formal/GaloisForLFunctions/RHTower/RoutePPrimitiveBurnolMatrixCompleteColligation.lean
```

Capstones:

- `routePBurnolApertureDamping_pairing_colligation`;
- `inner_routePBurnolApertureColligationVector_eq_source`;
- `routePPrimitiveBurnolWindowGramMatrix_eq_colligation_gram`;
- `routePPrimitiveBurnolWindowGramMatrix_eq_sum_channelGrams`;
- `routePPrimitiveBurnolApertureTransportedGram_loewnerLE_source`.

Verification:

- `/tmp/pg194.lean`: `lake env lean /tmp/pg194.lean` passed cleanly;
- exact leaf build passed; no umbrella build run;
- `/tmp/pg194_audit.lean`: capstones depend only on `propext`, `Classical.choice`, `Quot.sound`;
- targeted forbidden-declaration scan and diff check clean;
- umbrella import wired without building umbrella.

## Gates

- [x] scalar P-G188 law polarized unconditionally
- [x] literal channel functions lifted to half-line L2
- [x] matrix-complete three-channel Gram conservation proved
- [x] exact positive defect remainder proved
- [x] transported Loewner domination proved
- [x] scratch verification
- [x] exact leaf build only
- [x] axiom and forbidden-declaration audit
- [x] umbrella wired without umbrella build
- [ ] identify completed-Xi residue columns with a contractive P-G194 output/restriction
- [ ] construct W-H184 witnesses from that coefficient-faithful boundary map
- [ ] unconditional RH
