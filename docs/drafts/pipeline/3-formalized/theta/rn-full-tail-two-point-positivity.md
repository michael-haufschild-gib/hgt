# RN: complete theta tail positivity on every two-node family

Status: formalized and audited.
Date: 2026-10-02.
Route: RN, full source-form positivity.

## Exact new result

For the literal `thetaCuspFullSource` and complete
`thetaTailFirstMomentKernel H`, every pair of real nodes gives a positive
semidefinite matrix. Every distinct pair has strictly positive determinant:

    H(x,y)^2 < H(x,x) H(y,y)  (x != y).

There is no large-translation, separation, positive-node, RH, or additional
source hypothesis. Repeated nodes are included in the unconditional PSD
capstone. This removes the domain restrictions of the earlier separated
packet and fixed-pattern far-tail results at rank two.

Lean file: `formal/GaloisForLFunctions/RHTower/ThetaTailTwoPointPositivity.lean`.
Namespace: `RHTower.ThetaTailTwoPoint`.
Public results:

- `strictMonoOn_decaySlope_div`.
- `diagonal_tail_lt_source_square`.
- `strictMonoOn_normalizedSource`.
- `kernel_two_point_strict`, `kernel_two_point_det_pos`.
- `kernel_two_point_quadratic_nonneg`.
- `twoNodeMatrix_posSemidef`.

## Dependency-closed paper proof

Write `k=thetaCuspFullSource`, `f=log k`, `p=-f'`, and
`J=thetaPrimeGammaCutEnergy`. The corpus proves `f''''<0` everywhere,
smoothness and evenness of `f`, positivity and evenness of `J`, and

    J'= -2x k(x)^2,  J(+infinity)=0,  H(x,x)=J(x).

Evenness gives `f'(0)=f'''(0)=0`. Hence `f'''(x)<0` for `x>0`, and
`(x f''-f')'=x f'''<0`. It follows that `p(x)/x` is strictly increasing
on the positive ray. Integrating its strict comparison against
`2t k(t)^2` and using the exact integral of `k k'` gives

    (p(x)/x) J(x) < k(x)^2.

Consequently `R(x)=k(x)/sqrt(J(x))` is strictly increasing on `[0,infinity)`.
It is positive and even on the whole real line.

For `x<y`, `x+y>=0`, let

    F(s)=sqrt(J(x+s))*sqrt(J(y+s))-H(x+s,y+s).

The corpus's common-translation derivative gives exactly

    F'(s)= -sqrt(J(x+s))*sqrt(J(y+s))
           *(R(y+s)-R(x+s))
           *((y+s)R(y+s)-(x+s)R(x+s)).

For `s>0`, `|x+s|<y+s`; evenness and strict monotonicity of `R` make both
last factors positive, including seam-crossing pairs. Thus `F` strictly
decreases on `[0,infinity)`. Its limit is zero, so `F(0)>0`.
For `x+y<0`, use simultaneous reflection and symmetry of `H` on `(-y,-x)`.
Nonnegativity of `H` allows squaring. Completing the square establishes
the quadratic inequality; repeated nodes reduce to `H(x,x)(a+b)^2`.

## Frontier and next hard obligation

This proves a full literal-source sign result, not RH. Pairwise positivity
does not establish arbitrary-rank PSD. The continuation is RN-P-7 in
`docs/drafts/pipeline/1-in-progress/rn-singular-weight-conjecture-loop-2026-10-01.md`:
prove a source-specific sign law for the source and coordinate-source
residuals under successive Schur projections. Their product controls the
derivative of each Schur-complement energy. RN-P-6 supplies its first step;
preservation at all later steps is unproved.

## Validation

- Direct leaf `lake env lean` passed, including the unconditional matrix theorem.
- Wired into `formal/GaloisForLFunctions/RHTower.lean`.
- Targeted `lake --old build GaloisForLFunctions.RHTower.ThetaTailTwoPointPositivity`
  passed, including the required fourth-log-derivative source dependencies.
- A `/tmp` axiom audit of all seven listed public results passed: only
  `propext`, `Classical.choice`, and `Quot.sound`. No added axioms or premises.
- Final `lake env lean GaloisForLFunctions/RHTower/ThetaTailTwoPointPositivity.lean`
  passed without warnings after the targeted build and axiom audit.
- `scripts/formal_tools.py lint` failed on thirteen unrelated unreachable
  modules, listed in the working log. It reported no error in this leaf.
