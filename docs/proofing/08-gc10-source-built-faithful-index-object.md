# G-C10 Proof Attempt: Source-Built Faithful-Index Object

Source: `docs/consolidated/08-conjectures-required.md` appendix.

Claim status: `[CONJECTURE]`.

## Target Claim

Euler/PNT/Gamma/FE data source-build a Jacobi/Loewner/Krein or Hodge/F1 object
whose faithful negative-square index is exactly the off-line zero count.

## Attempt

If such an object `C_xi` is constructed with

```text
index_-(C_xi) = # off-line zero pairs,
```

then RH is equivalent to `index_-(C_xi)=0`. This part is formal. The hard part
is source-building `C_xi` without feeding in the zeros.

## Weakened Theorem

Any source-built object with faithful index equal to the off-line zero count
reduces RH to proving index vanishing for that object.

## Obstruction

Finite gates and fitted recurrences can encode zeros indirectly. The object
must be audited for zero-feeding and fake-family separation.

## Missing

Canonical construction from source data, index equality, and proof of
dust-proof faithfulness.
