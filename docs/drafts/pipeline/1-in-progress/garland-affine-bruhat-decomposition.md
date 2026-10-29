# Iwahori double cosets for the actual Laurent SL₂ group

- **Stage:** 1-in-progress
- **Type:** BRIDGE / known mathematics
- **Parent:** [Garland loop Eisenstein series](garland-loop-eisenstein-over-q.md)
- **Target:** Prove the affine Bruhat decomposition of the full Laurent
  matrix group, then lift it through the actual central extension.

## Dependency and novelty audit

Corpus searches found finite real Iwasawa decomposition and a DVR Smith
normal form, but no loop Iwahori–Bruhat theorem. The direct rank-two proof
below uses the already constructed Iwahori and elementary matrix identities.
It avoids deriving a finer alcove decomposition from Smith normal form.
This is classical affine Bruhat decomposition, with no novelty claim.

Required local facts are the actual Laurent valuation, its power-series
valuation ring and residue map, and factorization of every nonzero Laurent
series as `X^n` times a power-series unit. Existing statements must be checked
before reuse; none is to be supplied as an extra theorem premise.

## Elementary existence proof

Let `g=[[a,b],[c,d]]` have determinant one, let `v(0)=infinity`, and let
`I` consist of power-series matrices with `c(0)=0`. Its allowed elementary
operations are upper shears with parameter in `F[[X]]` and lower shears
with parameter in `X F[[X]]`.

At least one of the following pivot choices is available:

1. `c != 0`, `v(c)<=v(a),v(d)`. Left upper shear `-a/c` and right upper
   shear `-d/c` reduce `g` to `W(c)=[[0,-c^-1],[c,0]]`.
2. `b != 0`, `v(b)<v(a),v(d)`. Left lower shear `-d/b` and right lower
   shear `-a/b` reduce `g` to `W(-b^-1)`.
3. `a != 0`, `v(a)<=v(b)`, `v(a)<v(c)`. Left lower shear `-c/a` and
   right upper shear `-b/a` reduce `g` to `D(a)`.
4. `d != 0`, `v(d)<=v(b)`, `v(d)<v(c)`. Left upper shear `-b/d` and
   right lower shear `-c/d` reduce `g` to `D(d^-1)`.

To see exhaustiveness, compare `v(c)` with `min(v(a),v(d))`. If the first
case fails, compare `v(b)` with that minimum. A strict inequality gives
the second case; otherwise choose whichever of `a,d` attains the minimum.
The only infinite minimum has `a=d=0`, in which case the determinant forces
both off-diagonal entries to be nonzero and the first case applies.

Each displayed reduction follows by multiplication and `ad-bc=1`.
For a pivot `s=X^n u`, with `u` a power-series unit, the diagonal `D(u)`
belongs to `I`. Hence every double coset has a representative `D(X^n)` or
`W(X^n)`, with integer `n`.

## Uniqueness from lattice-chain invariants

For an invertible Laurent matrix `M`, let `mu(M)` be the minimum valuation
of its four entries. It is unchanged by left or right multiplication by
an invertible power-series matrix: integrality gives one inequality, and
the integral inverse gives the reverse inequality.

Put `J=diag(1,X)`. Every `i` in `I` and `J^-1 i J` is an invertible
power-series matrix. Thus the triple

`(mu(g), mu(J^-1 g), mu(J^-1 g J))`

is invariant under both Iwahori factors. For the proposed representatives:

| Representative | First entry | Second entry | Third entry |
| --- | --- | --- | --- |
| `D(X^n)` | `-|n|` | `min(n,-n-1)` | `-|n|` |
| `W(X^k)` | `-|k|` | `min(-k,k-1)` | `-|k-1|` |

For diagonal representatives the first and third entries coincide. For
antidiagonal representatives they differ by one, so the two families are
disjoint. In the diagonal family the second entry distinguishes `n>=0`
from `n<0`; the first then recovers `n`. In the antidiagonal family the
third minus the first distinguishes `k>=1` from `k<=0`; the first then
recovers `k`. Therefore all representatives are distinct double cosets.

## Central lift and scope

The positive Borel has projection exactly `I` and contains the full central
kernel. Lift both Iwahori factors using the proved positive splitting and
absorb the remaining central discrepancy into either Borel factor.
Projection gives uniqueness of the lifted double-coset representative.
With `N_m=D(X^-m)` and the canonical finite Weyl lift, these are precisely
the two families of the actual infinite dihedral affine Weyl group.

Paper proof recorded; Lean implementation and local dependency verification
pending. This supplies no compact subgroup, archimedean Iwasawa theorem,
arithmetic lattice, measure, or Eisenstein convergence by itself.

## Implementation checkpoint

`LaurentIwahoriCriteria` contains the valuation criterion, integral matrix
recovery, both permitted shear families, and actual monomial/unit splitting.
Its first check exposed an implicit matrix coercion at the determinant; that
step is now explicit, with the finite matrix simplification corrected.
Recheck pending. `SL2PivotReduction` contains all four elimination identities;
its first check requires expanding the residual vector-matrix multiplication
before the field identities. `IwahoriBruhatExistence` contains the double-coset
relation, monomial normalization, and exhaustive valuation pivot cases; it is
not yet checked and its final existence theorem remains to be added.
