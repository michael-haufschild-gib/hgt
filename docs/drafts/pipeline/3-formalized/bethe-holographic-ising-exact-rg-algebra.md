# Bethe holographic Ising exact RG algebra

- **ID:** `bethe-holographic-ising-exact-rg-algebra`
- **Stage:** 3-formalized
- **Type:** THEOREM PACKAGE (Lean 4) / EXACT PHYSICAL RG ALGEBRA
- **Scientific status:** `[FORMALIZED] [UNCONDITIONAL] [PARENT PHYSICS ALGEBRA]`
  `[DOES NOT FORMALIZE THE EXTERNAL HT CLASSIFICATION]`
- **Paper theorem:**
  `../2-fully-proven/needs-audit/bethe-padic-holographic-rg-clock-hypertranscendence.md`
- **Lean module:**
  `formal/GaloisForLFunctions/HTGeometry/BetheHolographicIsingRG.lean`

## Formalized object

For arbitrary natural branching `p` and rational edge transmissivity `a`, the module defines the
exact boundary-magnetization rational map

```text
F_(p,a)(y)=((1+ay)^p-(1-ay)^p)/((1+ay)^p+(1-ay)^p)
```

together with its primitive numerator, exact descendant block-normalization denominator, and
cross-multiplied displacement from the identity.

## Unconditional theorem surface

The module proves:

- exact positive/negative binary-symmetric one-edge likelihood identities and their homogeneous
  `p`-branch belief-propagation sum/difference update;
- exact numerator/denominator sum and difference factors;
- zero-field fixed anchor and normalization value two;
- exact numerator derivative `2pa` and vanishing denominator derivative at zero;
- exact projective fixed-point multiplier `pa`;
- critical multiplier one at `a=1/p` for positive `p`;
- critical displacement from the identity for every physical `p>=2`;
- the exact third derivative of that cross-multiplied critical displacement,
  `-4(p^2-1)/p^2`, anchoring the nonzero cubic parabolic term;
- noiseless positive-anchor numerator and normalization values `2^p`;
- collapse of the rational recursion at zero transfer;
- absence of any common complex zero of primitive numerator and normalization, hence no pointwise
  cancellation.

All statements are unconditional.  The module contains no Ritt, Becker--Bergweiler, holographic,
or continuum-QFT assumption.

## Verification

The smallest touched-file check passed:

```text
lake env lean GaloisForLFunctions/HTGeometry/BetheHolographicIsingRG.lean
```

The exact-module cached build passed:

```text
lake build +GaloisForLFunctions.HTGeometry.BetheHolographicIsingRG
```

An external scratch-file `#print axioms` audit of the critical multiplier, critical nonidentity,
critical cubic defect, and no-common-zero theorem reported only:

```text
propext, Classical.choice, Quot.sound
```

No aggregate build or repository-wide lint was run in the shared active tree.

## Formal boundary

The following remain external to this module:

- real attracting/repelling fixed-point analysis across temperature;
- Leau--Fatou petal construction at the Bethe transition;
- Becker--Bergweiler differential-algebraic classification;
- the resulting beta/clock hypertranscendence theorem;
- explicit Möbius conjugacy of the zero-temperature endpoint to the power map.

These are not represented by hypotheses.  The formal result is the exact algebraic substrate on
which the paper proof operates.

## Gates

- [x] Existing HTGeometry declarations checked before implementation.
- [x] Exact BSC transfer weights and homogeneous belief-propagation update formalized.
- [x] Exact two-parameter rational family defined.
- [x] Projective normalization factors formalized.
- [x] All-temperature linear multiplier anchor formalized.
- [x] Critical multiplier and nonzero cubic defect formalized.
- [x] Primitive numerator/denominator noncancellation formalized.
- [x] Infinite- and zero-temperature algebraic endpoint anchors formalized.
- [x] Touched-file check passed.
- [x] Exact-module build passed.
- [x] Axiom audit passed.
- [ ] Zero-temperature Möbius conjugacy formalized.
- [ ] External analytic HT classification internalized in Lean.
