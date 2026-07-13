# Single Even Frequency Determinant

- **ID:** single-even-frequency-determinant
- **Stage:** 3-formalized
- **Lean module:** `formal/GaloisForLFunctions/HTGeometry/SingleEvenFrequency.lean`
- **Paper parent:** `../2-fully-proven/single-even-frequency-not-stieltjes.md`
- **Statement formalized:** For real `B` and `lambda`,

`(B lambda^2)(B lambda^6/120)-(-B lambda^4/6)^2 = -7 B^2 lambda^8/360`.

If `B>0` and `lambda>0`, this determinant is strictly negative.

## Lean Theorems

- `GaloisForLFunctions.singleEvenFrequency_det_identity`
- `GaloisForLFunctions.singleEvenFrequency_det_neg`
- `GaloisForLFunctions.positiveEvenFrequencyCone_T2_neg`

## Verification

Commands run from `formal/`:

```text
lake build GaloisForLFunctions.SingleEvenFrequency
lake env lean GaloisForLFunctions.lean
```

Both succeeded on 2026-06-24.

Scratch axiom check:

```text
lake env lean /tmp/single_even_frequency_axioms.lean
```

Output:

```text
'GaloisForLFunctions.singleEvenFrequency_det_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'GaloisForLFunctions.singleEvenFrequency_det_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
'GaloisForLFunctions.positiveEvenFrequencyCone_T2_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Scope

This formalizes only the finite arithmetic determinant calculation and the
finite positive-mixture `T_2<0` sign. It does not formalize the analytic
coefficient extraction from `cosh(lambda sqrt(z))`, the measure/integral version,
the Euler-product interpretation, or any RH statement.

## 2026-06-24 two-frequency dominance core

The same Lean module now also contains the two-frequency dominance sublemmas used as a formal core for `../2-fully-proven/finite-signed-even-frequency-atoms-not-markov.md`:

- `GaloisForLFunctions.twoFrequency_dominant_positive_eventually`
- `GaloisForLFunctions.twoFrequency_dominant_negative_eventually`

These formalize only the two-frequency top-coefficient tail sign. The full finite signed atom theorem remains paper-level.

Verification run from `formal/` on 2026-06-24:

```text
lake build GaloisForLFunctions.SingleEvenFrequency
lake env lean /tmp/single_even_frequency_axioms.lean
```

Axiom output for the two new dominance lemmas:

```text
'GaloisForLFunctions.twoFrequency_dominant_positive_eventually' depends on axioms: [propext, Classical.choice, Quot.sound]
'GaloisForLFunctions.twoFrequency_dominant_negative_eventually' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 2026-06-24 half-turn repaired determinant

The same Lean module now also contains the half-turn repaired one-frequency determinant:

- `GaloisForLFunctions.singleEvenFrequency_halfTurn_det_identity`
- `GaloisForLFunctions.singleEvenFrequency_halfTurn_det_neg`

These formalize the determinant used in `../2-fully-proven/half-turn-repaired-frequency-not-markov.md`: changing `-B lambda^4/6` to `+B lambda^4/6` does not change the squared middle term, so the first shifted Hankel determinant remains `-7 B^2 lambda^8/360`.

Verification run from `formal/` on 2026-06-24:

```text
lake build GaloisForLFunctions.SingleEvenFrequency
lake env lean /tmp/single_even_frequency_axioms.lean
lake env lean GaloisForLFunctions.lean
```

Axiom output for the two repaired determinant lemmas:

```text
'GaloisForLFunctions.singleEvenFrequency_halfTurn_det_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'GaloisForLFunctions.singleEvenFrequency_halfTurn_det_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 2026-06-24 half-turn repaired two-frequency cross-term

The same Lean module now contains the algebraic core for the bounded repaired-packet obstruction:

- `GaloisForLFunctions.twoFrequency_halfTurn_pairNumerator_identity`
- `GaloisForLFunctions.twoFrequency_halfTurn_det_neg_of_cross_nonpos`
- `GaloisForLFunctions.halfTurn_det_neg_of_moment_ratio_lt`
- `GaloisForLFunctions.twoFrequency_halfTurn_det_neg_of_ratio_quad_lt`

These formalize the two-frequency numerator expansion and optimized moment-ratio gate behind `../2-fully-proven/bounded-half-turn-frequency-packets-fail-hankel.md`. If the repaired two-frequency cross coefficient

`3 x^2 - 20 x y + 3 y^2`

is nonpositive, then the first shifted Hankel determinant of the repaired positive two-frequency packet is strictly negative. The optimized quadratic criterion proves the same determinant negativity under `3(x^2+y^2)<34xy`, the two-frequency form of the `(17+2 sqrt(70))/3` spread gate.

Verification run from `formal/` on 2026-06-24:

```text
lake build GaloisForLFunctions.SingleEvenFrequency
```

Build output:

```text
Build completed successfully (8476 jobs).
```

## 2026-06-24 sharp first-gate repaired threshold

The same Lean module now contains the explicit balanced two-frequency certificate showing that the first-gate spread threshold is sharp:

- `GaloisForLFunctions.twoFrequency_halfTurn_balanced_det_identity`
- `GaloisForLFunctions.twoFrequency_halfTurn_balanced_det_pos`

These formalize `../2-fully-proven/half-turn-first-gate-threshold-sharp.md`. For the balanced endpoint packet with weights `c_x=y^2`, `c_y=x^2`, the first shifted Hankel determinant is

`x^3 y^3 (3 x^2 - 34 x y + 3 y^2)/360`.

Thus above the quadratic threshold `34xy < 3(x^2+y^2)`, a positive repaired two-frequency packet passes the first Hankel gate. This is only a first-gate statement, not a Markov/Stieltjes all-order result.

Verification run from `formal/` on 2026-06-24:

```text
lake build GaloisForLFunctions.SingleEvenFrequency
```

Build output:

```text
Build completed successfully (8476 jobs).
```
