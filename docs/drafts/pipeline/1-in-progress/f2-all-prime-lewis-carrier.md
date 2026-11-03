# F2 — source Hecke transport on the complete Lewis carrier

- **Stage:** 1-in-progress
- **Status:** Carrier invariance is audited for every positive determinant and every complex parameter. The prime boundary eigenfunctional and corrected retained-boundary transport remain open.
- **Purpose:** Extend the retained-boundary source intertwining from the first prime to the full arithmetic family.

## Exact target

Let `W_s` be the functions fixed on `(0,∞)` by actual modular inversion and the Lewis three-term operator. Prove, for every prime `p`,

`T_(p,s) W_s ⊆ W_s`,

`(T_(p,s)g)(1)=(1+p^(1−2s))g(1)` for every `g∈W_s`.

The first-prime case follows from existing inversion commutation and Farey-defect transport: the source equations give `2g(2)=g(1)`, and direct evaluation gives its boundary eigenvalue. The [retained-boundary carrier](../3-formalized/f2-boundary-restoration-carrier.md) uses precisely these two facts.

## Available and missing

The actual all-prime finite-cone operator, positive branches, and completed Eisenstein eigenlaw are audited. The [corrected actual-core eigenlaw](../3-formalized/f2-global-core-hecke-correction.md) is also audited. These special-family identities do not establish invariance of the whole source carrier.

The cone involution `(a,b,c,d)↦(d,c,b,a)` should supply universal inversion commutation. The remaining task is an exact finite-cone relation transporting the three-term defect and the boundary evaluation functional. It must be proved for arbitrary carrier elements; assuming a Hecke eigenfunction equation would miss the target.

No positivity, Hilbert-space boundedness, full Mayer-family reflection, or mixed-parameter synthesis claim follows from carrier invariance alone.

## Finite reduction and remaining summation

[Unique positive-word reduction and the exact finite suffix partition](../3-formalized/f2-hecke-positive-word-reduction.md) are audited, including identification with the actual `heckeSet n`. [Finite harmonic summation](../3-formalized/f2-hecke-word-harmonic-transport.md) is also audited: summing over actual Hecke bases converts left-generator harmonicity into right-generator harmonicity. [The literal weighted source operator preserves the complete carrier](../3-formalized/f2-all-determinant-lewis-carrier.md), also audited. For prime determinant, primitive basis row sums form a second suffix partition; the remaining `p` bases have row sums `(p,p)`, giving the boundary factor `1+p^(1−2s)`. Formalization must identify these partitions with the actual finite-cone operator.

## Stronger boundary conjecture

The prime evaluation law should require only the Lewis three-term equation, without inversion symmetry. Its proposed proof uses the homogeneous binary splitting law throughout: primitive basis row sums form the suffix partition, and the `p` equal-row-sum bases contribute `p·p^(−2s)g(1)`. The first-prime check already follows directly from the three-term equation at `1`. The all-prime statement remains unformalized.

The primitive partition proof is now drafted for every determinant `n>0`: coprime row sums with total greater than `n` admit a unique nonnegative determinant-`n` matrix. Matrix reduction then gives the complete suffix partition. At prime determinant, row sums are either coprime or `(p,p)`; the latter bases are indexed by `1≤k≤p`. This finite classification remains under Lean verification.
