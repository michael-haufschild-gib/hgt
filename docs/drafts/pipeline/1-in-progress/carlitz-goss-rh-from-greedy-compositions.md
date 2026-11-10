# Carlitz–Goss RH from greedy compositions

- **Stage:** 1-in-progress
- **Source:** review-0911 §11.4.

## Exact target

For every prime power `q=p^s`, `s>0`, and every `y∈ℤ_p`, the zeros in `x`
of the Goss zeta function of `𝔽_q[T]` are simple and belong to
`𝔽_p((T⁻¹))`. The domain for `x` is the nonzero elements of the completed
algebraic closure of `𝔽_q((T⁻¹))`.

## Proof dependencies

[Sheats, Theorems 1.1–1.4 and §2](https://arxiv.org/pdf/math/9801158):

1. Among carry-free compositions of `N`, with all but the final part
   positive and divisible by `q−1`, the reversed-lexicographic maximum
   uniquely maximizes the weighted sum of the parts.
2. Finite-field power sums and Lucas's theorem identify the leading
   coefficient of each monic-polynomial power sum. The unique maximum
   prevents cancellation.
3. Greedy-composition inequalities give strictly increasing consecutive
   coefficient valuations. For general `y∈ℤ_p`, digit truncations stabilize
   those valuations.
4. Every Newton-polygon segment has horizontal length one. Its root is
   simple and belongs to the coefficient field.

`SignFreePurityMechanisms/SeparationForcesRationality.lean` supplies a
polynomial Galois-invariance principle. The same owner's
`TheUltrametricNewtonPolygonSeparatesTheRoots.lean` proves simplicity,
separation and splitting of polynomials with strictly log-concave
coefficient norms (`HasSimpleSlopes.derivative_eval_ne_zero`,
`splits_of_strict_logConcave`). The composition theorem, actual Goss
coefficients and passage to the entire series remain necessary.

## Lean status

The actual Goss-zeta theorem and its composition input remain unformalized.
The target includes every prime power, not only prime `q` or integer `y`.

## Combinatorial mechanism

Write `Γ(N)_h` for the number of base-`p` digits of `N`, counted with
multiplicity, whose exponents are `h mod s`. Put
`(Ea)_h=p a_{h+1}−a_h`, with cyclic indices. The entries of `E⁻¹` are
positive; its rows are the cyclic rotations of `(1,p,…,p^(s−1))/(p^s−1)`.
Thus `Γ(N)` is the content of a positive `(q−1)`-multiple precisely when
`E⁻¹Γ(N)` has positive integral coordinates. A carry-free composition
into `m` positive parts, the first `m−1` divisible by `q−1`, exists
precisely when `min(E⁻¹Γ(N))>m−1` (Sheats, Proposition 4.3).

For a fixed content matrix, increasing allocation of the digit powers
within each residue class uniquely maximizes the weight. The difficult
step compares different content matrices. A minimal nongreedy optimum
has last part `p^k`; after a cyclic rotation, the first `m−1` parts have
zeroth inverse-content coordinate one. If `β=k mod s`, a greedy last
part has a larger digit and content supported below `β`, but the same
weighted residue sum as `p^k` (Proposition 5.1).

For prefix contents `θ_j` and `w_j=E⁻¹θ_j`, choose `α<β` with
`w_{α,m−1}=m−1` and `w_{h,m−1}>m−1` for `α<h≤β`.
Keep the coordinates outside `(α,β]`. Within it, descending recursion
`d_{h,m−1}=min(w_{h,m−1}−1,p d_{h+1,m−1})` and
`d_{h,j}=min(d_{h,j+1}−1,p d_{h+1,j})` gives admissible prefix contents
`δ_j=Ed_j`. Their increasing digit allocation defines another composition
`Z`. Successive nonzero prefix contents in each affected class differ
by at least `p−1` digits (Lemma 6.2).

If `τ_{h,r}` is the `r`th digit power in class `h`, set
`S=Σ_{α≤h<β}τ_{h,δ_{h,m−1}}`. The prefix cost is at most `p^k+S`,
whereas `deg_p Z_m>k` and, when `S>0`, `deg_p Z_m>deg_p S+1`.
These imply `Z_m>2p^k+S` for `p≥3`. For `p=2`, the only possible equal
degree case forces `β=s−1`, `α=0`, and at least two retained digits in
class zero; its second digit makes the inequality strict as well
(Lemmas 7.1–7.3 and Proposition 7.4). Hence `wt Z>wt O`, contradicting
optimality. This is the missing composition theorem, not a hypothesis
to attach to the Goss-zeta statement.
