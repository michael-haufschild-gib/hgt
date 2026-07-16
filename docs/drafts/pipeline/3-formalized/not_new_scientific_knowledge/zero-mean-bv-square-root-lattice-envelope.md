# Zero-mean BV sources have a square-root lattice envelope

- **ID:** `zero-mean-bv-square-root-lattice-envelope`
- **Stage:** 3-formalized
- **Type:** THEOREM / ANALYTIC BRIDGE
- **Scientific status:** `[FULLY PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Formal source:** `formal/GaloisForLFunctions/HTGeometry/ZeroMeanBVLatticeEnvelope.lean`

## Theorem

Let `g : R -> C` be interval-integrable and of bounded variation on `[0,L]`, with

```text
integral_0^L g(x)dx=0,   g(L)=0.
```

For `k>0`, choose `n` so that

```text
n/k<=L<=(n+1)/k.
```

Then the positive right-endpoint lattice quadrature obeys

```text
|1/k sum_(j=1)^n g(j/k)|
 <=2 Var_[0,L](g)/k.                                           (1)
```

After the radial square-root normalization,

```text
|sqrt(k)/k sum_(j=1)^n g(j/k)|
 <=2 Var_[0,L](g)/sqrt(k).                                     (2)
```

The support endpoint need not lie on the lattice. The proof controls the covered uniform mesh by
the complex BV Riemann-sum theorem and the final partial cell by the same total variation.

## Connes-route use

On the source side of the one-sided Poisson--Muntz identity, `(2)` gives the exact
`a^(-1/2)` envelope for a compact zero-mean source. Applied with `a=lambda*exp(t)`, it replaces a
far-field radial-PSWF phase summation by compact-source variation:

```text
|b_lambda(t)|
 <=2 Var(g_lambda^+)/sqrt(lambda)*exp(-t/2).
```

The Poisson specialization and the concrete fixed-mode prolate variation bound are separate
gates; they are not asserted by this bridge theorem.

## Verification

The two headline theorems were checked in the project toolchain. Their axiom audit contains only
the standard logical axioms `propext`, `Classical.choice`, and `Quot.sound`; there are no project
axioms, `sorry`, or conditional analytic hypotheses hidden in the proof.
