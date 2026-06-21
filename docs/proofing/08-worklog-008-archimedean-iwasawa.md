# C-2026-06-18-008 Proof Attempt: Archimedean Iwasawa Via Takesaki

Source: `docs/consolidated/08-conjectures-required.md` §4.

Claim status: `[CONJECTURE]`.

## Target Claim

An archimedean crossed product `M rtimes_sigma R` of type `II_infty` has a
Fuglede-Kadison determinant whose characteristic ideal is conjecturally `(xi)`;
the failure point is the absence of an archimedean Euler system.

## Attempt

The formal analogy is:

```text
Iwasawa module + characteristic ideal -> p-adic L-function.
archimedean crossed product + FK determinant -> xi.
```

If one constructs a Hilbert-module operator `T` affiliated to the crossed
product such that

```text
det_FK(1 - sT) = xi(s)
```

and the corresponding module has a positivity or torsion theorem forcing the
faithful index to vanish, then RH could follow.

## Weakened Theorem

If an affiliated self-adjoint operator has FK determinant `xi` and its spectral
measure is supported on the critical-line parameter, then RH follows. This is
only spectral reformulation, not construction.

## Obstruction

The missing archimedean Euler system is not cosmetic; it is the mechanism that
would supply the characteristic ideal and its positivity. Without it, the
crossed product is a host, not a proof.

## Missing

An actual module, Euler-system replacement, determinant computation, and a
faithful-index theorem inside the crossed-product category.
