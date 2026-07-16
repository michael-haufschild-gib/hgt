# Mahler collider signal constraint and nonrationality

- **ID:** `mahler-collider-signal-constraint`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / COSMOLOGICAL-SIGNAL ALGEBRAIC CORE
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/MahlerColliderSignal.lean`
- **Parent program:** `../../1-in-progress/mahler-cosmological-collider-tower.md`
- **Statement:** The geometric-frequency formal signal is the unique normalized solution of its
  one-shell Mahler constraint and is not rational.

## Exact theorem

For every integer `p>=2`, Lean constructs

```text
M_p(X)=sum_(k>=0) X^(p^k)                                 (1)
```

coefficientwise and proves

```text
M_p(X)=X+M_p(X^p).                                         (2)
```

It also proves normalized uniqueness: if `Y(0)=0` and `Y(X)=X+Y(X^p)`, then `Y=M_p`.

Finally, the support `{p^k}` has arbitrarily long zero windows before later nonzero coefficients.
The formal support-gap theorem therefore proves that no nonzero polynomials `P,Q` satisfy

```text
Q(X) M_p(X)=P(X).                                          (3)
```

Thus `M_p` is not rational.

## Exact boundary

The module does not formalize the external rational-or-hypertranscendental theorem for Mahler
equations.  Combining `(2)`--`(3)` with that published theorem is a paper argument, not a Lean
claim.  The module also does not construct a cosmological particle tower, compute an inflationary
wavefunction, or prove observational transfer.

All ingredients here are formal power-series algebra and a standard rational-series gap
obstruction.  Their cosmological use is new project architecture, not new mathematics.

## Lean surface

- `mahlerColliderCoefficient`
- `mahlerColliderSignal`
- `exists_eq_pow_iff`
- `mahlerColliderCoefficient_recursion`
- `mahlerColliderSignal_constraint`
- `mahlerInvariant_eq_zero`
- `mahlerColliderSignal_unique`
- `mahlerColliderSignal_not_rational`

## Verification

- [x] direct touched-file Lean check passed
- [x] exact cached module build passed in one foreground process
- [x] axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`
- [x] no numerical computation used
- [x] imported by the HTGeometry umbrella
