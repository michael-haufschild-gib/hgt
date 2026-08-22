# Generalized-amplitude-damping tree population exact RG algebra

- **ID:** `gadc-tree-population-exact-rg-algebra`
- **Stage:** 3-formalized
- **Type:** THEOREM PACKAGE (Lean 4) / QUANTUM-CHANNEL POPULATION ALGEBRA
- **Scientific status:** `[FORMALIZED] [UNCONDITIONAL] [DIAGONAL CPTP-CHANNEL SECTOR]`
  `[DOES NOT FORMALIZE COMPLETE POSITIVITY OR EXTERNAL HT CLASSIFICATION]`
- **Paper theorem:**
  `../2-fully-proven/not_new_scientific_knowledge/04-rg-stochastic-quantum-fields/gadc-tree-population-rg-clock-hypertranscendence.md`
- **Lean module:**
  `formal/GaloisForLFunctions/HTGeometry/GADCTreePopulationRG.lean`

## Formalized object

For rational damping `d`, rational bath population `N`, and rational diagonal Bloch coordinate `z`,
the module defines the affine population action

```text
z |-> (1-d)z+d(1-2N).
```

It derives the positive-output probabilities from the two computational-basis inputs,

```text
alpha=1-dN,                 gamma=d(1-N),
```

and the affine likelihood parameters

```text
u=1-2dN,                   v=2d(1-N)-1.
```

For natural branching `p`, it specializes the existing asymmetric binary-tree rational family to

```text
R_(p;d,N)(y)=((1+uy)^p-(1+vy)^p)/((1+uy)^p+(1+vy)^p).
```

## Unconditional theorem surface

The module proves:

- exact positive- and negative-input Bloch endpoints;
- exact recovery of both transition probabilities from those endpoints;
- the thermal population `1-2N` is the fixed point of sequential affine damping;
- the signal parameters are `2 alpha-1` and `2 gamma-1`;
- probability gap `alpha-gamma=1-d`;
- affine signal gap `u-v=2(1-d)`;
- exact homogeneous population-BP rational formula;
- balanced bath `N=1/2` is exactly the symmetric Bethe/BSC family with signal `a=1-d`;
- exact zero-message multiplier `p(1-d)`, independent of `N`;
- zero damping is the noiseless symmetric family;
- full damping makes the affine parameters equal and collapses the tree update to zero.

All theorem statements are unconditional equalities.  Physical interval assumptions are absent
because none is required for the algebra.

## Verification

The smallest touched-file check passed:

```text
lake env lean GaloisForLFunctions/HTGeometry/GADCTreePopulationRG.lean
```

The exact-module cached build passed:

```text
lake build +GaloisForLFunctions.HTGeometry.GADCTreePopulationRG
```

An external scratch-file `#print axioms` audit of the Bloch endpoint, probability gap, homogeneous
BP formula, balanced-bath specialization, multiplier, and full-damping endpoint reported only:

```text
propext, Classical.choice, Quot.sound
```

No aggregate build or repository-wide lint was run in the shared active tree.

## Formal boundary

The module does not formalize the Kraus operators or prove complete positivity.  Those are source
properties identifying the physical domain of the exact diagonal formulas.  It also does not
formalize:

- strict stochastic inequalities on the physical interior;
- real attracting, parabolic, or repelling basin dynamics;
- the external Becker--Bergweiler hypertranscendence classification;
- transverse quantum coherences or noncommutative operator-valued messages;
- continuum QFT inheritance.

None of these is inserted as an assumption.  The formal package is unconditional exact population
algebra.

## Gates

- [x] Existing HTGeometry declarations and generated research index checked first.
- [x] Sequential GADC population action formalized.
- [x] Induced binary transition probabilities formalized.
- [x] Exact branch-likelihood parameter gap formalized.
- [x] Exact homogeneous population rational family formalized.
- [x] Balanced thermal bath specialization formalized.
- [x] Bath-independent multiplier formalized.
- [x] Identity and full-reset damping endpoints formalized.
- [x] Touched-file check passed.
- [x] Exact-module build passed.
- [x] Axiom audit passed.
- [ ] Physical complete positivity internalized in a matrix channel model.
- [ ] Operator-valued noncommutative branch recursion formalized.
- [ ] External analytic HT classification internalized in Lean.
