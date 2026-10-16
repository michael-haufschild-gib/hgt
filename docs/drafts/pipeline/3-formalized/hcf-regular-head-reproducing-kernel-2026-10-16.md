# HCF: exact inverse moment kernel across singular gaps

Status: formalized and directly audited. Scope: one unconditional structural contribution.

## Corpus evidence

The canonical regular-head transfer and source divided-difference companion are audited in
`XiGaussianHeatRegularTransfer` and `XiGaussianHeatRegularPade`. Existing
`ChristoffelKernel` and `ChristoffelDarboux` require positive moment forms.
The HCF normal blocks can have arbitrary singular gaps and indefinite forms.
Deep corpus searches for normal-block inverse kernels and source Padé Bezoutians completed
with full file inventory; applicability is being checked against source and Lean.

## Theorem and paper proof

Write `n_j` for regular heads, `P_j` for their admissions, `mu_j` for the first
surviving coupling and `A_j=P_(j+1) /ₘ P_j`. Define

`K_j(x,Y) = (P_j(x) D_x P_(j+1)(Y) - P_(j+1)(x) D_x P_j(Y))/mu_j`.

This is the exact inverse Hankel reproducing kernel through degree
`n_(j+1)-1`, and equals the finite block sum

`sum_(i<=j) P_i(x) P_i(Y) D_x A_i(Y)/mu_i`.

The source companion identity and Casoratian give `L(K_j)=1`.
Multiplication by `Y-x` gives a linear combination of the two admissions.
Both vanish on moment rows below `n_(j+1)-1`, so induction gives
`L(Y^r K_j)=x^r` for every `r<n_(j+1)`. The degree bound and regular
Hankel solve identify the coefficient vector with `H^(-1)(1,x,...)`.
The polynomial recurrence telescopes the kernel one complete gap at a time.

## Structural contribution

Recovered the full inverse moment kernel from the canonical source transfer data at
every positive heat time, without a positive-form or nonzero-intermediate-pivot
premise. This replaces scalar positive orthogonal-kernel machinery by an
exact block kernel retaining the singular gaps. It does not assert source positivity.

## Conjecture loop

1. Scalar rank-one kernel terms do not follow through a gap: the quotient has degree
   greater than one. Survivor: replace each scalar term by its polynomial divided
   difference, retaining the entire gap.
2. Candidate inverse-kernel identity above: dependency-closed paper mechanism;
   proved for the actual heat source in Lean.
3. Stronger survivor: the individual gap kernels are mutually orthogonal
   projections for the signed source form. Write the section kernel at head
   `n_j` as `S_j`, with `S_0=0`. Then `B_j=S_(j+1)-S_j`.
   Reproduction on nested degree spaces proves `L(p B_j)=0` below `n_j`;
   applying this to lower block kernels proves off-diagonal orthogonality.
   Reproducing `B_j` against `S_(j+1)` and subtracting the vanished `S_j`
   pairing gives `L(B_j(x,.) B_j(y,.))=B_j(x,y)`. No positive form is used.
   This stronger theorem is also proved for every positive time and all block indices.

## Formalized modules and capstones

- `HTGeometry/MomentInverseKernel`: inverse-kernel uniqueness and reproduction
  from a normalized moment displacement.
- `RHTower/XiGaussianHeatRegularKernel`: `hcf_regular_kernel_inverse`,
  `hcf_regular_kernel_reproduces`, exact pairing and symmetry.
- `RHTower/XiGaussianHeatRegularKernelBlocks`:
  `hcf_regular_inverse_kernel_blocks`, exact block Christoffel--Darboux identity.
- `RHTower/XiGaussianHeatRegularKernelProjections`:
  `hcf_regular_block_kernel_orthogonal`, including block idempotence.

The actual-source capstones take only positive heat time, block indices,
evaluation variables and, for reproduction, a finite coefficient vector.
No positivity, total-mass, genericity or regular-time premise remains.

## Completed validation

- Focused `lake --old build +Module:olean` passed for all four modules.
- Final direct `lake env lean <source>` passed for each of the four files,
  without warnings. No source changed after its direct audit.
- `/tmp` API audit passed for 28 names. A separate `/tmp` audit checked all
  28 public theorem dependency closures and printed actual capstone signatures.
  Every axiom list was exactly `[propext, Classical.choice, Quot.sound]`.
- All four modules wired into their area umbrellas; no umbrella or full build.
- `scripts/formal_tools.py index` passed, refreshing 25 changed files in the
  shared workspace. `git diff --check` passed.
- Global `scripts/formal_tools.py lint` exited 1 with 16 unrelated umbrella
  reachability errors: eleven CHMD modules, four `PaperThetaNative*` modules,
  and `WeilCutEvenMeanZeroDeficit`. No new HCF module was reported. Those
  concurrent research files were preserved.
- No numerical experiments, added axioms, placeholders, or heartbeat increases.

The complete prime--Gamma source sign remains open. The new result is an exact
source decomposition and projection law, not an RH equivalence or receiver.
