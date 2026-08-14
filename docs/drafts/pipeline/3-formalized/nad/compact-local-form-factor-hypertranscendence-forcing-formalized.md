# Compact-local form-factor hypertranscendence forcing — formalized

- **ID:** `compact-local-form-factor-hypertranscendence-forcing-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `compact-local-form-factor-hypertranscendence-forcing.md`
- **Umbrella import:** `GaloisForLFunctions.HTGeometry`

## Lean modules

| Module | Content |
|---|---|
| `HTGeometry/KolchinExchangeGaugeObstruction.lean` | the exchange-law forcing `(4)`–`(7)`: a nonzero section of an HT exchange law is HT |
| `HTGeometry/DifferentialAdjoinFiniteTrdeg.lean` | descent of differential algebraicity across a derivation-closed finite-transcendence extension — step 3 of the forcing proof |
| `HTGeometry/KolchinSlopeDichotomy.lean` | the finite relative-jet rank `(8)` |
| `HTGeometry/KolchinLocalityFloor.lean` | the operator-independent local floor and the locality inequality `(11)`–`(13)` |

## Audited declarations

Each resolves and `#print axioms` reports exactly `propext`, `Classical.choice`, `Quot.sound`.

- `(4)`, `(6)`, `(7)` `DifferentialAlgEquiv`, `differentialAlgebraicOver_exchangeLaw_of_section`,
  `section_hypertranscendental_of_exchangeLaw` — reflection is an actual derivation-preserving field
  automorphism whose preservation of DA is proved, and a nonzero section of `reflection(F) = S·F` is
  hypertranscendental whenever `S` is.  This is the Watson-forcing step in the canonical coordinate;
- step 3 of the forcing proof: `differentialAlgebraicOver_of_intermediate_trdeg_lt_aleph0` — the
  constant extension `C(t) → C(u,t)` is derivation-closed with `D u = 0` and has transcendence degree
  one, so differential algebraicity over it descends to `C(t)`;
- `(8)` `kolchinJetRank_eq_of_hypertranscendentalOver` — every finite relative-jet packet of the
  hypertranscendental form factor has rank exactly `r + 1`;
- `(11)` `kolchinLocalFloor` — the infimum of the two-valued one-reporter slope over a nonempty
  family of local reporters, which removes the choice of local operator;
- `(12)` `kolchinSlopeValue_le_kolchinLocalFloor` — **the Kolchin locality inequality**: if
  hypertranscendence of the exchange reporter forces the whole family, the local floor is at least
  the exchange slope;
- `(13)` `kolchinLocalFloor_eq_one` — saturation on the hypertranscendental branch;
- `tendsto_kolchinSlope_kolchinSlopeValue` — the two-valued slope is the actual limit of the
  normalized jet rank, so `(11)`–`(13)` are statements about the genuine Kolchin slope, not about a
  surrogate.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/KolchinLocalityFloor.lean
lake build GaloisForLFunctions.HTGeometry.KolchinLocalityFloor
```

## What closed last

The locality inequality.  The card's `(11)` takes an infimum of Kolchin slopes over all compact-local
observables with nonzero two-particle component, and there was no Lean object for a Kolchin slope at
all until `KolchinSlopeDichotomy.lean`.  With the slope proved two-valued and equal to the limit of
the normalized jet rank, the infimum is well defined and bounded below, and the forcing theorem makes
every member of the family equal to one on the HT branch — so `(12)` and `(13)` follow without any
appeal to the operator algebra.

## Boundary

The physical inputs are cited published theorems, as the card states: the Lechner tube theorem for
analyticity of the two-particle form factor, the `S₂`-symmetric Fock sector structure behind the
Watson identity `(2)`, modular nuclearity, existence of compact-local intersections, and
Reeh–Schlieder density behind the abundance statement `(9)`.  The remaining paper gates — a
formula-level novelty audit across the form-factor literature, an intrinsic local form-factor profile
with operator-change invariance, a connected-correlator transfer or locality inequality, and an
independent operator-algebraic and differential-algebra review — are onward targets and external
obligations, not formalization gates for the forcing chain certified above.
