# Route T: strict-sub-half Borel sector classification

Status: `LEAN-PROVED`

Module:
`formal/GaloisForLFunctions/RHTower/XiHeatCassiniWoldResidualBorelSubhalfClassification.lean`

## Result

Corpus generalized von Koch estimates under RH were transported through the exact theta-error
Abel formula, canonical Mertens constant, and Wold/Euler decomposition. For every `eps` with
`0 < eps < 1/2`, RH gives

```text
|R_N| <= B_eps exp(-(1/2-eps) h_N)
```

eventually. Therefore every Borel terminal `|R_N| exp(y h_N)` vanishes for `0 <= y < 1/2`, and
the raw and Abel-renormalized finite positive-ray prescriptions asymptotically agree.

Under critical prime-gap energy:

```text
RH iff the raw residual edge current is absolutely summable
       at every strict height 0 < y < 1/2.
```

## Route consequence

Whole-strip raw absolute convergence is full RH burden, not a preliminary lemma. Remaining viable
work is cancellation-first lateral landing or another source-faithful regularity mechanism that
does not presuppose this classified condition.

## Audit

- `lake env lean` passed.
- Targeted module build passed.
- Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`.

