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

`CarlitzGoss/DigitContents.lean` proves
`exists_positive_cyclicDifference_content_iff`: a positive integer is
divisible by `p^s−1` exactly when its digit content is `Ea` for a positive
integral vector `a`. The inverse, integrality propagation, and digit
congruence are proved; direct and transitive axiom audits passed, using
only the three standard axioms.

`CarlitzGoss/ContentRounding.lean` proves `exists_integral_content_layer`:
if every inverse-content coordinate exceeds `m≥1`, a proper positive
integral layer with inverse coordinates at least `m` can be extracted.
Direct and transitive axiom audits passed, using only the standard axioms.
`CarlitzGoss/ContentPartitions.lean` proves `hasContentPrefix_iff`:
a nonnegative content vector admits `k` positive divisible parts and
one unrestricted positive last part iff every inverse-content coordinate
exceeds `k`. Direct and transitive axiom audits passed, using only the
standard axioms.

`CarlitzGoss/DigitAllocations.lean` proves `tokenPrefix_iff_inverseContent`:
the same criterion partitions the individual finite digit occurrences,
not only their count vectors. Direct and transitive axiom audits passed,
using only the standard axioms.
`CarlitzGoss/DigitValues.lean` identifies divisible content with divisibility
of a block's actual integer value and proves `digitTokenPrefix_iff` for the
canonical base-`p` digits of every `N`. Direct and transitive axiom audits
passed, using only the standard axioms. All five modules are wired into the umbrella.

The actual Goss-zeta theorem and its optimal-composition input remain unformalized.
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

The rounding step has a closed form. For `u=Ec≥0` integral and
`c_h>m≥1`, put `b_h=⌈c_h⌉−1` and
`d_h=min_{0≤k<s} p^k b_{h+k}`. Then `m≤d_h<c_h` and
`d_h=min(b_h,p d_{h+1})`. If `d_h=p d_{h+1}`, then `(Ed)_h=0`;
otherwise `d_h=b_h` and `(Ed)_h<u_h+1`, hence `(Ed)_h≤u_h` by
integrality. Thus `0≤Ed≤u`, with both `Ed` and `u−Ed` nonzero by
invertibility of `E`. This supplies the recursive decomposition into
positive divisible parts without choosing a coordinate of minimum `c`.

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

For the optimality proof, a carry-free digit collection can be represented
by a finite subset of `ℕ×Fin(p−1)`: `(e,r)` has value `p^e` and colour
`e mod s`. Each exponent occurs at most `p−1` times. An admissible
composition partitions this set into nonempty parts, all but the last
having value divisible by `p^s−1`. Its weight is the sum of part values
times their one-based positions. Deletion and exponent shifts preserve
this model, so minimality can use `(number of parts, number of digits)`.
