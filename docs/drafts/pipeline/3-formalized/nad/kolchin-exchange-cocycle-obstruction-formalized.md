# Kolchin exchange-cocycle obstruction — formalized

- **ID:** `kolchin-exchange-cocycle-obstruction-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `kolchin-exchange-cocycle-obstruction.md`
- **Umbrella import:** `GaloisForLFunctions.HTGeometry`

## Lean modules

| Module | Content |
|---|---|
| `HTGeometry/KolchinExchangeGaugeObstruction.lean` | the exchange-gauge relation, the ratio obstruction, the constant no-go, and the HT half-phase law `(7)`–`(10)` |
| `HTGeometry/LechnerPairMultiplier.lean` | the pair multiplier `(5)` and the creation recursion `(10a)` |
| `HTGeometry/LechnerFockIntertwiner.lean` | the Fock-space intertwiner `Y = ⊕ₙ Yₙ`, the conversion of the `S`-exchange law into the constant `ε` law, and the conjugated creation-operator formula `(10b)` |

## Audited declarations

Each resolves and `#print axioms` reports exactly `propext`, `Classical.choice`, `Quot.sound`.

- `DifferentialAlgEquiv` and `DifferentialAlgEquiv.differentialAlgebraicOver_map_iff` — reflection is
  an actual coefficient-fixing, derivation-preserving field automorphism, and its preservation of
  differential algebraicity is **proved**, not assumed;
- `differentialAlgebraicOver_ratio_of_daExchangeGaugeEquivalent` — a DA multiplier relating `S` and
  `T` forces the ratio `T/S` to be DA;
- `not_daExchangeGaugeEquivalent_of_ratio_hypertranscendental` — an HT ratio forbids **every** DA
  exchange gauge: the obstruction is a genuine differential-Galois invariant;
- `differentialAlgebraicOver_exchangeLaw_of_section` and `section_hypertranscendental_of_exchangeLaw`
  — a nonzero DA section of `reflection(f) = S·f` forces `S` DA, hence every nonzero section of an
  HT exchange law is HT;
- `no_daExchangeGauge_trivialization_of_hypertranscendental` — an HT law cannot be DA-gauged to a
  nonzero constant;
- `halfPhase_hypertranscendental_of_exchangeLaw` — every half-phase `y` with `S = c·y/reflection(y)`
  is HT whenever `S` is;
- `pairMultiplier`, `pairMultiplier_zero`, `pairMultiplier_one`, `pairMultiplier_two`,
  `pairMultiplier_succ`, `pairMultiplier_shift` — equation `(5)` and the first-particle string
  recursion `(10a)`;
- `lechnerFockIntertwiner`, `intertwine_swapAt`, `conjugated_creation_multiplier` — Lechner's
  analytic/Hilbert intertwiner as a linear isometry of the rapidity Fock space, its conversion of the
  `S`-exchange law into the constant `ε` law, and the conjugated creation-operator formula `(10b)`.

## Verification

```text
lake build GaloisForLFunctions.HTGeometry.KolchinExchangeGaugeObstruction
lake build GaloisForLFunctions.HTGeometry.LechnerFockIntertwiner
```

## What closed last

The QFT realization side.  The algebraic obstruction had been formalized first; the remaining
question was whether the abstract exchange law is the one Lechner's polarization-free construction
actually produces.  `LechnerPairMultiplier.lean` computes the multiplier
`prod_{k<l<n} y(θ_k − θ_l)` and proves that adjoining a new *first* particle multiplies it by the
string `prod_{j<n} y(θ_0 − θ_{j+1})`, which is exactly the recursion the conjugated creation operator
must satisfy; `LechnerFockIntertwiner.lean` then assembles the graded intertwiner and derives `(10b)`.
With those in place every `[x]` gate on the card has a Lean witness.

## Boundary

Open on the paper card: a physical admissibility theorem for DA exchange gauges, a
localization/OPE/profile invariant of the Kolchin exchange class, a wide novelty audit against twists
and differential Tannakian theory, and an independent operator-algebraic and differential-algebra
review.  The first two are onward theorem targets stated as such on the card; the last two are
external literature obligations.  None is a formalization gate for the theorems certified above.
