# Library ticket: Xi unit-Euler-pole affine section and translated Bezoutian

- **Source card:**
  `docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/xi-unit-euler-pole-affine-section-translated-bezoutian.md`
- **Umbrella wiring:**
  `docs/drafts/pipeline/1-in-progress/rh-complete-corpus-dependency-closure.md`
- **Requested library action:** index this under RH value relations, projective-horizon affine
  marking, Euler normalization, and Hermitian kernel criteria.

## Index summary

For

```text
A(s) = s(s-1)/2 * Gamma_R(s),
Z_c(s) = (xi(s)-c)/A(s),
```

the exact punctured value relation is

```text
lim_(s->1) (s-1) Z_c(s) = 1-2c.
```

Hence the canonical unit zeta residue selects `c=0` inside the constant-translation orbit that
positive jet-horizon fields cannot distinguish. For real `c`, the translated centered function
`X_c(w)=xi(1/2+w)-c` has all zeros on the imaginary axis exactly when its Hermitian Bezoutian

```text
B_c(w,v) =
  (X_c'(w) conj(X_c(v)) + X_c(w) conj(X_c'(v))) / (w+conj(v))
```

is positive semidefinite on the right half-plane. The residue marks the value fibre; the kernel
orients it.

## Status language

Use:

```text
[PROVED ON PAPER] [TOP-DOWN INTERFACE DISCHARGE]
[CLASSICAL-KERNEL BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]
```

The unresolved assertion is source positivity of `B_0`. Do not report the affine marking or the
kernel equivalence as a proof of that sign.

