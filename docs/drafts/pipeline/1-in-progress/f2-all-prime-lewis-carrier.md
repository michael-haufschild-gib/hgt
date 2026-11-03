# F2 — source Hecke transport on the complete Lewis carrier

- **Stage:** 1-in-progress
- **Conjecture:** Every actual prime Hecke correspondence preserves the inversion-fixed, three-term Lewis carrier and acts on evaluation at `1` by `1+p^(1−2s)`.
- **Purpose:** Extend the retained-boundary source intertwining from the first prime to the full arithmetic family.

## Exact target

Let `W_s` be the functions fixed on `(0,∞)` by actual modular inversion and the Lewis three-term operator. Prove, for every prime `p`,

`T_(p,s) W_s ⊆ W_s`,

`(T_(p,s)g)(1)=(1+p^(1−2s))g(1)` for every `g∈W_s`.

The first-prime case follows from existing inversion commutation and Farey-defect transport: the source equations give `2g(2)=g(1)`, and direct evaluation gives its boundary eigenvalue. The [retained-boundary carrier](f2-boundary-restoration-carrier.md) uses precisely these two facts.

## Available and missing

The actual all-prime finite-cone operator, positive branches, and completed Eisenstein eigenlaw are audited. The [corrected actual-core eigenlaw](../3-formalized/f2-global-core-hecke-correction.md) is also audited. These special-family identities do not establish invariance of the whole source carrier.

The cone involution `(a,b,c,d)↦(d,c,b,a)` should supply universal inversion commutation. The remaining task is an exact finite-cone relation transporting the three-term defect and the boundary evaluation functional. It must be proved for arbitrary carrier elements; assuming a Hecke eigenfunction equation would miss the target.

No positivity, Hilbert-space boundedness, full Mayer-family reflection, or mixed-parameter synthesis claim follows from carrier invariance alone.
