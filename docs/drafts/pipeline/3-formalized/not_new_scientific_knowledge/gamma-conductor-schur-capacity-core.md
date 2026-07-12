# Gamma-conductor Schur-capacity core

- **ID:** `gamma-conductor-schur-capacity-core`
- **Stage:** 3-formalized
- **Type:** LEAN THEOREM PACKAGE
- **Scientific status:** FORMAL CORE / NOVELTY CLASSIFICATION DEFERRED TO PAPER CARD
- **Lean file:** `formal/GaloisForLFunctions/RHTower/GammaConductorSchurCapacity.lean`
- **Paper card:** `docs/drafts/pipeline/1-in-progress/ccm-gamma-conductor-schur-capacity-law.md`

## Formalized result

For the explicit normalized Gamma characteristic

```text
phi(t)=(cosh t)^(-1/2)
```

and its centered second-moment covariance kernel, the prime-log scalar Schur cost is

```text
R_p
 = (9/8) p(p-1)^2(p+1)^4/(p^2+1)^4
 >= 9/(512p).
```

The module proves that `p |-> R_p` is not summable and, equivalently in cofinal finite-packet
form, that every real `B` is exceeded by `sum_(p in F) R_p` for some finite prime set `F`.

It also proves the exact damping law

```text
(d C_p)^2/(d^2 A_p)=R_p,       d!=0,
```

and the finite scalar Schur theorem: if

```text
sum_i A_i x_i^2 + 2 y sum_i c_i x_i + B y^2 >= 0
```

for every `x,y`, with all `A_i>0`, then

```text
sum_i c_i^2/A_i <= B.
```

Specializing this theorem to positively damped prime--Gamma channels proves that every positive
finite independently resolved block allocates at least `sum_i R_(p_i)` scalar conductor capacity.

The same module formalizes the positive complementary law. If the normalized prime covariance
`K` has diagonal one and the full prime--conductor quadratic block is nonnegative with conductor
capacity `B>0`, then, for `u_i^2=R_(p_i)` and `S=sum_i R_(p_i)`,

```text
sum_(i,j) K_ij u_i u_j >= S^2/B,
sum_(i!=j) K_ij u_i u_j >= S^2/B-S.
```

Accordingly fixed conductor capacity forces coherent off-diagonal covariance rather than merely
permitting it.

## Formal status

- The exact module builds with the repository toolchain.
- The RHTower aggregate imports the module and builds.
- The declarations contain no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` proof shortcut.
- The result is not RH and does not formalize the analytic identification of the finite block with
  the full CCM semilocal operator. In particular, the canonical Gamma-measure Gram realization and
  its moment value `B=3/2` remain paper-level classical analysis. Lean formalizes the unconditional
  arithmetic and quadratic-form capacity law used by that route.

The scientific novelty audit remains in the paper card because the proof combines classical
Gamma identities, a classical Schur-complement test, and Euler's reciprocal-prime divergence in a
route-specific way whose exact literature status still requires independent verification.
