# Continuous affine dilations classify subgroup-indicator successors

- **ID:** AFFINE-CONTINUOUS-SUBGROUP-SUCCESSORS
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Parent:** [Cyclic Haar obstruction](../1-in-progress/cyclic-haar-averages-force-infinite-index-at-continuous-dilations.md)
- **Statement:** For an additive subgroup `H≤ℚ`, a Hermitian kernel on `Aff(ℚ)` with translation reading `1_H`, finite negative index, and positive-dilation reading continuous at one exists exactly when `H={0}` or `H=ℚ`.

## Positive boundary

For `H=ℚ`, the constant kernel `1` is positive definite. For `H={0}`, the indicator of the dilation subgroup, `k(g)=1[shift(g)=0]`, is positive definite by extension from a subgroup. Both have constant dilation reading `1` and index zero.

The proposed obstruction would therefore classify all subgroup indicators, including the single-prime successor `1_{ℤ_(p)}`. It would locate the discontinuity obstruction at any one finite place with bounded denominator depth.

## Proposed argument for the remaining subgroups

Conjugating the affine kernel by dilation by a nonzero element of `H` rescales the successor subgroup to contain `ℤ`, while preserving dilation readings and negative index. If `H≠ℚ`, some prime `p` has finite height `h`, meaning `1/p^h∈H` but `1/p^(h+1)∉H`. Otherwise Bézout combinations of prime-power reciprocals would generate every rational. For `q∈H`, Bézout applied to its reduced numerator and denominator first gives `1/den(q)∈H`; integer multiplication then gives each reciprocal prime-power factor. Thus membership forces `v_p(q)≥−h`.

Let `d_H(q)` be the order of `q+H` in `ℚ/H`. It divides the ordinary denominator, and satisfies `d_H(q)≥p^max(0,−v_p(q)−h)`. After the existing zero-axis polynomial correction, integer translations are invariant. Use the full ordinary-denominator period `m=den(b/a)` in the cyclic projection. Each class in the cyclic quotient of size `d_H(b/a)` occurs `m/d_H(b/a)` times, so its projection norm should equal `1/d_H(b/a)` without requiring invariance under all of `H`. The first `d_H(c/a)` orbit vectors are orthonormal; the moving-column estimate should therefore have squared bound `1/d_H(c/a)` whenever `c` is a natural multiple of `b`.

For finitely many indices and `N≥1`, choose `a_(N,i)=p^(N(i+1))/(p^(N(i+1))+1)`. These positive slopes tend to one, with pairwise valuation differences `N(i−j)`. A common step

`b_N=1/(p^N ∏_i (p^(N(i+1))+1))`

makes every `a_(N,i)/b_N` a positive integer. Fixed diagonal norms tend to zero. For each off-diagonal pair, choose the orientation with negative valuation ratio; its moving pairing tends to zero. Continuity then gives the same projected Gram limit `J−I`, contradicting finite index.

## Novelty and verification boundary

The corpus supplies the integer-Haar obstruction, zero-axis polynomial correction, locally periodic projections, and the local Hecke index wall. The latter treats a specified Hecke kernel; it does not classify arbitrary finite-index carriers with a prescribed subgroup indicator.

The finite-height lemma, quotient-order projection formula, and generalized moving estimate remain to be proved and formalized. The positive endpoint examples also need explicit Lean statements. No complete proof is claimed.

## Gates

- [ ] Complete paper proof, including the two positive branches and every quotient-order input.
- [ ] Exact Lean classification in the existing topic subfolders.
- [ ] Direct `lake --old env lean` audit and standard transitive axiom closure.
