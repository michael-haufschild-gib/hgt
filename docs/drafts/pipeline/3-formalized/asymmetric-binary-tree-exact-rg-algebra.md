# Asymmetric binary-tree exact RG algebra

- **ID:** `asymmetric-binary-tree-exact-rg-algebra`
- **Stage:** 3-formalized
- **Type:** THEOREM PACKAGE (Lean 4) / EXACT TRANSFER-CHANNEL ALGEBRA
- **Scientific status:** `[FORMALIZED] [UNCONDITIONAL] [ASYMMETRIC BINARY CHANNEL]`
  `[DOES NOT FORMALIZE EXTERNAL COMPLEX-DYNAMICAL CLASSIFICATION]`
- **Paper theorem:**
  `../2-fully-proven/needs-audit/asymmetric-binary-tree-channel-rg-clock-hypertranscendence.md`
- **Lean module:**
  `formal/GaloisForLFunctions/HTGeometry/AsymmetricBinaryTreeRG.lean`

## Formalized object

For natural branching `p` and rational binary-channel parameters `alpha,gamma`, the module derives
the exact rescaled one-child likelihoods

```text
1+(2 alpha-1)y,             1+(2 gamma-1)y
```

and their homogeneous `p`-branch projective belief-propagation update.  In independent affine
parameters `u,v`, it defines the rational map

```text
R_(p;u,v)(y)=((1+uy)^p-(1+vy)^p)/((1+uy)^p+(1+vy)^p).
```

## Unconditional theorem surface

The module proves:

- exact asymmetric-channel likelihood identities;
- exact homogeneous BP sum/difference formula;
- specialization `v=-u` to the formalized Bethe holographic Ising family;
- primitive numerator/normalization sum and difference factors;
- zero-message fixed anchor and normalization value two;
- primitive numerator derivative `p(u-v)` and normalization derivative `p(u+v)`;
- exact rational multiplier `p(u-v)/2`, equivalently `p(alpha-gamma)`;
- the polynomial derivative cross-numerator factorization

  ```text
  N' D - N D'
    = 2 p (u-v) (1+uX)^(p-1) (1+vX)^(p-1);
  ```

- absence of any common complex zero of numerator and normalization when `u!=v`.

The derivative factorization is the unconditional algebraic substrate for strict real monotonicity
on the positive channel interval.  No real-analysis or HT premise occurs in the theorem interface.

## Verification

The smallest touched-file check passed:

```text
lake env lean GaloisForLFunctions/HTGeometry/AsymmetricBinaryTreeRG.lean
```

The exact-module cached build passed:

```text
lake build +GaloisForLFunctions.HTGeometry.AsymmetricBinaryTreeRG
```

An external scratch-file `#print axioms` audit of the BP formula, symmetric specialization,
channel multiplier, derivative cross-numerator, and noncancellation theorem reported only:

```text
propext, Classical.choice, Quot.sound
```

No aggregate build or repository-wide lint was run in the shared active tree.

## Formal boundary

The following remain paper-level:

- strict interval positivity from `-1<v<u<1`;
- first-crossing existence of a non-super nonrepelling fixed point;
- Leau--Fatou sector construction;
- Ritt--Becker--Bergweiler exclusion and HT beta/clock conclusion;
- stochastic reconstruction and quantum-channel interpretation.

None is inserted as an assumption.  The formal package is unconditional exact channel algebra.

## Gates

- [x] Existing HTGeometry declarations checked before implementation.
- [x] Exact asymmetric branch likelihoods formalized.
- [x] Exact two-parameter rational family formalized.
- [x] Symmetric Bethe slice identified formally.
- [x] Projective factors and fixed anchor formalized.
- [x] Exact channel multiplier formalized.
- [x] Derivative cross-numerator factorized.
- [x] Primitive noncancellation formalized.
- [x] Touched-file check passed.
- [x] Exact-module build passed.
- [x] Axiom audit passed.
- [ ] Real interval first-crossing theorem formalized.
- [ ] External analytic HT classification internalized in Lean.
