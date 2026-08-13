# Deninger--Hazewinkel additive multiplication stage bound

- **Stage:** 5-failed
- **Date:** 2026-08-13
- **Source:** Christopher Deninger, *Rational Witt vectors and associated sheaves*,
  arXiv:2508.05329v1, equation (15), Lemma 2.6, and Theorem 2.8.
- **Lean module:**
  `formal/GaloisForLFunctions/RHTower/DeningerHazewinkelStageBoundCounterexample.lean`
- **Status:** PUBLISHED QUANTITATIVE CLAIM REFUTED; POSITIVE SURVIVOR FORMALIZED

## Failed claim

The source assigns the same stage target to Witt addition and Witt multiplication:

```text
W_J^{<=n} (+ or Witt-mul) W_J^{<=m}  subset  W_J^{<=n+m}.
```

The Witt-multiplication clause is false.  Consequently the corresponding comultiplication
containment with `J_(n+m)` in Lemma 2.6 and the multiplication factorization through
`W_J^{<=n+m}` in Theorem 2.8 cannot be formalized as stated.  This does not refute the qualitative
claim that `W_J` is an ind-subring; it refutes the published quantitative stage index used there.

## Closed counterexample

Over `ℤ`, let

```text
E_r = [1] + ... + [1]  (r Witt-additive summands),
```

so its literal power series is `(1-T)^r`.  Lean proves for every `r`:

```text
rank H(E_r) = r+1,
E_r Witt-mul E_s = E_(r*s).
```

In project notation the exact-rank statement is

```text
rank H(E_r) < r+2,
not (rank H(E_r) < r+1).
```

Take `r=2`, `s=4`.  Then `E_2` lies in stage `3`, `E_4` lies in stage `5`, but their Witt product
is `E_8`, whose exact stage is `9`.  It therefore does not lie in claimed target stage
`3+5=8`.  The closed Lean theorem is
`deningerHazewinkel_wittMul_stage_add_counterexample`.

No numerical evaluation proves nonvanishing.  Coefficients above degree `r` vanish symbolically;
after reversing rows, the top Hankel minor is triangular with diagonal `(-1)^r`, hence nonzero.

## Strongest positive survivor

The exact packet law is the useful survivor:

```text
stage(E_r) = r+1,
stage(E_r Witt-mul E_s) = r*s+1.
```

Thus any corrected universal stage function must allow multiplicative growth.  For normalized
rational fractions with numerator/denominator stage bounds `(n,m)`, root-incidence bookkeeping
suggests the general safe candidate `2*n*m-n-m+2`; proving the sharp universal containment for
all Hazewinkel points, including non-rational points over nonreduced rings, remains open.

## Audit

- Direct foreground `lake env lean` passes.
- Exact module build passes; no full build was run.
- `#print axioms` for packet multiplication, exact stage, nonzero minor, and final counterexample
  reports only `propext`, `Classical.choice`, and `Quot.sound`.
- No `sorry`, `admit`, new axiom, `opaque`, `unsafe`, computation, reducedness premise, or
  RH-equivalent assumption is used.
