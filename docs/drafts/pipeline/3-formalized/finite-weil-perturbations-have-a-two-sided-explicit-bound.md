# Two-sided explicit Weil perturbation bound

- **ID:** finite-weil-perturbations-have-a-two-sided-explicit-bound
- **Stage:** 3-formalized
- **Statement:** Every compact `C²` perturbation with sup bound `e`, support
  `[-R,R]`, and Lipschitz bound `L` has an explicit two-sided Weil error.

## Proof

Put `V=synthLevy(R,e,L,k)` for `k≥1`. The existing perturbation estimate gives
`√∫D²≤√(2R)e`, `Levy(D)≤V`, and `∫|D|≤2Re`.
Triangle inequalities bound the norms of `F+D` by

`a=√∫F²+√(2R)e`, `l=√Levy(F)+√V`,
`c=|coshMoment(F)|+|sinhMoment(F)|+4R cosh(R/2)e`.

The proved upper Weil estimate, first from `F` with perturbation `D` and then
from `F+D` with perturbation `−D`, gives

`|Q(F+D)−Q(F)|≤weilErrBound(a,l,c,R,e,V)`.

Both one-sided inputs are proved source estimates; no continuity radius or
external analytic bound appears in the conclusion.

Polarizing `F_i±F_j` with perturbations `D_i±D_j` gives the entry error
`(B(F_i+F_j,R,2e,4V)+B(F_i−F_j,R,2e,4V))/4`.
Thus one finite scalar bound controls every entry of the actual Weil Gram matrix.

## Lean

`EffectiveArithmeticHodgeTheory/FiniteWeilPerturbationsHaveExplicitBounds.lean`:
`abs_weilQuad_add_sub_le_explicit` and `norm_weilGram_add_sub_le_explicit`
passed direct `lake --old env lean` checking. Both transitive axiom audits
contain only `propext`, `Classical.choice`, and `Quot.sound`.
Umbrella import added.
