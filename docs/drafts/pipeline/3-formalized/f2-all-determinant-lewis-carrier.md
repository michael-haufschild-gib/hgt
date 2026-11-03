# F2 — every source Hecke correspondence preserves the completed Lewis carrier

- **Stage:** 3-formalized
- **Result:** For every integer determinant `n>0` and every complex parameter `s`, the literal finite-cone Hecke operator preserves the inversion-fixed, three-term Lewis carrier on `(0,∞)`.
- **Scope:** No regularity, resonance, spectral-strip, eigenfunction, or positivity assumption.

## Literal homogeneous source

For a physical function `g`, set

`F_s(x,y)=y^(−2s)g(x/y)`, `x,y>0`.

Positive scaling gives `F_s(cx,cy)=c^(−2s)F_s(x,y)`. The physical Lewis equation is exactly

`F_s(x,y)=F_s(x+y,y)+F_s(x,x+y)`.

For `A=[[a,b],[c,d]]`, put `H(A)=F_s(a x+b y,c x+d y)`. Positive determinant and nonnegative entries make both arguments positive. The source equation gives `H(A)=H(LA)+H(RA)`.

The [audited finite harmonic identity](f2-hecke-word-harmonic-transport.md) therefore yields

`Σ_B H(B)=Σ_B [H(BL)+H(BR)]`.

At `(x,y)=(a,1)`, the sum on the left is the literal source operator `T_(n,s)g(a)`. Right multiplication by `L` gives the translation branch at `a+1`; right multiplication by `R` gives the homogeneous parabolic branch at `a/(a+1)`. Hence `T_(n,s)g` satisfies the same Lewis equation. The finite matrix set is identified exactly with `heckeSet n`.

## Inversion

Physical inversion invariance is equivalent to `F_s(x,y)=F_s(y,x)`. The map

`[[a,b],[c,d]] ↦ [[d,c],[b,a]]`

is an involution of the actual Hecke basis set. Positive homogeneity and this symmetry identify each inversion-transformed branch with the corresponding reversed basis. Reindexing the finite sum proves inversion invariance of `T_(n,s)g`.

Thus every positive-determinant source operator preserves `mayerCompletedLewisCarrier s`. In particular every prime operator does so, without assuming an eigenfunction equation for general carrier elements.

## Remaining bridge

The prime boundary evaluation law on arbitrary carrier elements is a separate target. It is needed to identify the actual corrected Hecke formula with transport through retained-boundary restoration. Carrier invariance alone supplies no Krein positivity, physical signed-form descent, analytic completion, or full Mayer-family reflection.

## Lean

`RenormalizedIntersectionTheory/MayerScattering/AllPrimeLewisCarrier`:

- `lewisHeckeOperator_eq_matrixSum`
- `lewisFarey_heckeOperator_of_fixed`
- `lewisModularInversion_heckeOperator_of_fixed`
- `mayerCompletedLewisCarrier_heckeOperator`
- `lewisHomogeneousValue_scale`
- `lewisHomogeneousValue_farey`

Individual final `lake --old env lean` audit passed without warnings. All six declarations have only `propext`, `Classical.choice`, and `Quot.sound` as transitive axioms. Umbrella import wired.
