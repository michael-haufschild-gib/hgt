# HCF: exact inverse moment kernel across singular gaps

Status: in progress. Scope: one unconditional structural contribution.

## Corpus evidence

The canonical regular-head transfer and source divided-difference companion are audited in
`XiGaussianHeatRegularTransfer` and `XiGaussianHeatRegularPade`. Existing
`ChristoffelKernel` and `ChristoffelDarboux` require positive moment forms.
The HCF normal blocks can have arbitrary singular gaps and indefinite forms.
Deep corpus searches for normal-block inverse kernels and source Padé Bezoutians completed
with full file inventory; applicability is being checked against source and Lean.

## Conjecture and paper mechanism

Write `n_j` for regular heads, `P_j` for their admissions, `mu_j` for the first
surviving coupling and `A_j=P_(j+1) /ₘ P_j`. Define

`K_j(x,Y) = (P_j(x) D_x P_(j+1)(Y) - P_(j+1)(x) D_x P_j(Y))/mu_j`.

Conjecture: this is the exact inverse Hankel reproducing kernel through degree
`n_(j+1)-1`, and equals the finite block sum

`sum_(i<=j) P_i(x) P_i(Y) D_x A_i(Y)/mu_i`.

The source companion identity and Casoratian give `L(K_j)=1`.
Multiplication by `Y-x` gives a linear combination of the two admissions.
Both vanish on moment rows below `n_(j+1)-1`, so induction gives
`L(Y^r K_j)=x^r` for every `r<n_(j+1)`. The degree bound and regular
Hankel solve identify the coefficient vector with `H^(-1)(1,x,...)`.
The polynomial recurrence telescopes the kernel one complete gap at a time.

## Structural target

Recover the full inverse moment form from the canonical source transfer data at
every positive heat time, without a positive-form or nonzero-intermediate-pivot
premise. This should replace scalar positive orthogonal-kernel machinery by an
exact block kernel retaining the singular gaps. It does not assert source positivity.

## Conjecture loop

1. Scalar rank-one kernel terms do not follow through a gap: the quotient has degree
   greater than one. Survivor: replace each scalar term by its polynomial divided
   difference, retaining the entire gap.
2. Candidate inverse-kernel identity above: dependency-closed paper mechanism;
   generic reproduction/uniqueness foundation passes its focused Lean build.
3. Stronger survivor: the individual gap kernels are mutually orthogonal
   projections for the signed source form. Write the section kernel at head
   `n_j` as `S_j`, with `S_0=0`. Then `B_j=S_(j+1)-S_j`.
   Reproduction on nested degree spaces proves `L(p B_j)=0` below `n_j`;
   applying this to lower block kernels proves off-diagonal orthogonality.
   Reproducing `B_j` against `S_(j+1)` and subtracting the vanished `S_j`
   pairing gives `L(B_j(x,.) B_j(y,.))=B_j(x,y)`. No positive form is used.

## Audit plan

Focused `lake --old build +Module:olean`; direct `lake env lean` for every new
source; `/tmp` signatures and axiom audit; area umbrella wiring, index and lint.
No full builds, numerical computation, extra axioms, or heartbeat increases.
