# Exact counterterm semidefinite shortcut: retired

Date: 2026-10-09
Scope: only a coefficient-independent matrix-sign or quadratic-size argument for the exact renormalized square source. The signed Möbius route and RH remain open.

## Exact object

Write Q(N) = sum_{s<N} s^2 and K(N,q) = mobiusSquareShortBilinearKernel N q. Define

R_N(a,b) = K(N,ab) - 1_{a=b=1} Q(N)
           - 1_{a=1} Q(N) log(b)/b - 1_{b=1} Q(N) log(a)/a.

For N >= 1, the quadratic form at the actual Möbius vector equals mobiusShortBilinearSquareSource N. The generic identity subtracts Q(N) f(1)^2 and 2 Q(N) f(1) sum_{b<=N} f(b) log(b)/b.

## Obstruction and strongest positive survivor

For N >= 2, the determinant of the (2,N) principal block is negative exactly when N >= 4. The whole two-coordinate quadratic form is nonnegative for every real pair exactly when N <= 3. Its terminal diagonal is zero, and its (2,2) diagonal is positive for N >= 3. For N >= 4, an explicit direction attains -1: put A = R_N(2,2), B = R_N(2,N) > 0, and y = -(A+1)/(2B); then A + 2yB + y^2 R_N(N,N) = -1.

For N >= 8, R_N(2,2) >= (log 2)/32 * N^3. Consequently, for every real constant B there exists N >= 8 with B N^2 < R_N(2,2).

The obstruction persists under every correction supported only on the first row and column, since the (2,N) block remains unchanged. The positive survivor is the sharp sign classification, exact negative direction, and cubic positive direction. The bounded unit vector e_2 disproves a universal O(N^2) upper bound over arbitrary bounded coefficient vectors. It has first coordinate zero; this is not a counterexample at the actual Möbius vector and does not impose its arithmetic identities.

## Dependency-closed paper proof

Counterterm expansion gives the exact source identity. Away from index 1 the correction vanishes. Kernel support and strict positivity give K(N,N^2)=0 and, for N >= 4, K(N,2N)>0, yielding the negative determinant. For N=2 or 3 the cross term is zero; diagonal nonnegativity gives the converse classification. Completing the linear cross term gives the explicit -1 direction.

For the cubic bound, 6Q(N)=N(N-1)(2N-1), Q(N)>=N^3/8 for N>=8, and V(N,4)+4F(N,4)=Q(N), with V(N,4)<=4N. Thus F(N,4)>=N^3/64. Retaining the k=1 nonnegative summand in K(N,4), and log 4 = 2 log 2, gives the stated bound. Archimedean growth gives failure of any universal quadratic coefficient bound.

Paper status: proved, with exact boundary and positive survivor.
Lean status: all 12 public theorems compiled in formal/GaloisForLFunctions/RHTower/MobiusSquareRenormalizedKernel.lean. A separate scratch audit reported only propext, Classical.choice, Quot.sound for every theorem. API scratch checks passed. The module is imported by RHTower.lean; direct .olean and .ilean are fresh. Owned scratch files removed.

Whitespace checks passed. Global formal lint failed because the unrelated module GaloisForLFunctions.HTGeometry.DiscreteCrossedProductCStar is unreachable from the HTGeometry umbrella. No out-of-scope changes made to repair that shared-worktree issue.

## Prior-research audit and limits

Research reads used only Lean-corpus output from scripts/formal_tools.py research. Ramaré results retain a bilinear integral premise; twist bounds retain a uniform twist premise. Pointwise divisor estimates did not supply the required signed global estimate. Targeted counterterm searches returned partial coverage, so no corpus-wide novelty or absence claim is made. A final lexical search indexed the new module.

Next live target: exploit actual Möbius identities to bound the signed renormalized quadratic form from above by O(N^2), or find an unconditional falsification of that equivalent criterion. The present obstruction neither proves nor falsifies RH.
