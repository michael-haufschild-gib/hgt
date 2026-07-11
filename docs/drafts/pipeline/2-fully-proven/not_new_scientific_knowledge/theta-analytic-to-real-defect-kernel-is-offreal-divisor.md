# The analytic-to-real theta-defect comparison has exactly the off-real divisor as kernel

- **ID:** `theta-analytic-to-real-defect-kernel-is-offreal-divisor`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper); terminal Route-A reduction
- **Scientific status:** `[BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** the theta analytic cokernel and the Xi logarithmic-derivative real-boundary measure
- **Statement:** On the algebraic semisimplification of the Xi analytic defect, the canonical map to
  the positive real-boundary defect is projection onto the real zero fibers.  Its kernel is exactly
  the sum of the nonreal zero fibers.  Hence faithfulness of this comparison is equivalent to RH.

## Analytic semisimple defect

Let `Z_Xi` be the distinct complex zero set of

```text
XiC(z)=xi(1/2+i z).
```

The semisimplification of the analytic cokernel of multiplication by `XiC` has algebraic
finite-support core

```text
D_an^alg=direct_sum_(rho in Z_Xi) C e_rho.              (1)
```

The logarithmic-derivative boundary theorem constructs the real defect core

```text
D_real^alg
  =direct_sum_(gamma in Z_Xi intersect R) C e_gamma,    (2)
```

with positive weights equal to the analytic multiplicities.

## Canonical comparison

The comparison from analytic support to the real boundary is restriction to the real spectral
axis:

```text
r(e_rho)=e_rho if rho is real,
r(e_rho)=0     if rho is nonreal.                       (3)
```

Therefore

```text
ker r
  =direct_sum_(rho in Z_Xi, Im(rho)!=0) C e_rho,        (4)

range r=D_real^alg.                                    (5)
```

Both identities follow immediately on the basis and remain valid for any completion on which the
coordinate maps are faithful.

## RH equivalence

By (4), `r` is injective exactly when every Xi zero is real.  Under

```text
s=1/2+i rho,
```

reality of `rho` is exactly `Re(s)=1/2`.  Hence

```text
r is faithful on the analytic semisimple defect
  iff RiemannHypothesis.                                (6)
```

This theorem does not prove injectivity.  It proves that the proposed real-boundary exhaustion is
the RH statement itself after the source and target defects have been constructed.

## Consequence

The positive real-boundary measure is a genuine source object, and the analytic theta cokernel is a
genuine source-first divisor object.  Their comparison supplies no intermediate localization law:
its missing injectivity is exactly the absence of off-line zeros.

Any successful pro-geometric continuation must therefore introduce additional pre-divisor prime
geometry that proves injectivity.  Rephrasing (3) as a faithful functor or purity axiom is circular.

## Gates

- [x] analytic and real semisimple cores identified
- [x] canonical comparison and kernel computed
- [x] faithfulness proved equivalent to RH
- [ ] no Lean formalization planned for a tautological divisor projection
