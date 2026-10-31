# Bi-integer-invariant Haar kernels split into positive and slope parts

- **ID:** HAAR-BIINTEGER-POSITIVE-SLOPE-SPLITTING
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [Relative Haar splitting](finite-index-haar-carriers-split-modulo-polynomial-kernels.md)
- **Statement:** Every Hermitian finite-index affine kernel `k` with integer Haar successor and invariance under integer translations on both sides admits a unique decomposition `k=p+ψ∘slope`, with `p` positive definite and having the same successor, and `ψ` Hermitian. The existing exact index law then gives `κ(k)=κ(ψ)`.

## Positivity of the moving subspaces

In the column representation, `v_1` is fixed by `T_1`; therefore `v_g` is fixed by `T_(slope g)`. Every rational translation acts periodically on each vector, since each vector is a finite sum of columns.

Take `x=(T_b−1)y` and choose `m>0` with `T_b^m y=y`. Then `T_b^m x=x` and `Σ_(j<m)T_b^j x=0`. Set `U=D_(1/m)`, so `T_b U=U T_b^m`. Every `U^j x`, `j>0`, is fixed by `T_b` and hence orthogonal to `x`. Invariance makes all distinct `U^i x` mutually orthogonal with the same norm. A negative norm would contradict finite negative index. Consequently `range(T_b−1)` is nonnegative, without spectral decomposition.

## Finite cyclic averages

Local periodicity gives the algebraic orthogonal projection `P_b` onto `ker(T_b−1)`, with kernel `range(T_b−1)`: averaging a finite orbit gives the direct-sum decomposition. The intersection is zero because a fixed vector `(T_b−1)y` makes `y` both periodic and unipotent, so the verified periodic-unipotent lemma forces `(T_b−1)y=0`. Orthogonality follows directly from invariance of `B`. The complementary form

`A_b(x,y)=B((1−P_b)x,(1−P_b)y)`

is positive semidefinite. If `a` is an integer multiple of `b`, then `P_bP_a=P_b` and `A_a≤A_b`. Conjugating by an affine map of slope `u` replaces `P_b` by `P_(ub)`.

Take `b_n=1/n!`. For every column `v_g`, Haar orthogonality on its finite translation orbit gives `B(P_(b_n)v_g,P_(b_n)v_g)=1/d_n`, where `d_n=den(b_n/slope(g))`. Hence `0≤A_(b_n)(v_g,v_g)≤1`. Cauchy–Schwarz bounds the forms on every finite linear combination of columns. Their increasing diagonal values and polarization therefore define a pointwise positive semidefinite limit `A`.

## Invariant limit and slope remainder

The lattices `(1/n!)ℤ` are cofinal among rational cyclic subgroups. After any fixed nonzero rational rescaling they remain cofinal. The order comparison above therefore makes `A` invariant under the entire affine group.

Every rational translation fixes `range(P_(b_n))` for all sufficiently large `n`. Thus `B−A`, the limit of `B(P_(b_n)·,P_(b_n)·)`, kills translation differences in either argument. Its coefficient factors through slope. The coefficient `p` of `A` is positive definite. On translation columns, the discarded pairing is eventually `B(P_(b_n)v_1,P_(b_n)v_1)=1/n!→0`, so `p` retains the Haar successor.

The exact slope-index law gives `κ(k)=κ(ψ)`. If two such decompositions agree, that law makes the difference of their slope parts positive definite. Its identity value is zero, so the positive-kernel norm bound makes it zero. Both parts are therefore unique.

## Lean realization

In `AdelicKreinGeometry/Haar/PositiveSlopeSplit.lean`:

- `exists_unique_positive_haar_slope_split` constructs the unique pair; right integer invariance suffices.
- `haarPositivePart_add_slope` gives the pointwise decomposition.
- `negIndex_haarSlopePart` gives the exact equality `κ(ψ)=κ(k)`.

`MovingLimit.lean` proves convergence, nonnegativity, affine invariance, and translation invariance of the discarded form. `PositivePart.lean` proves positivity and preservation of the entire Haar successor. These use the cyclic projection and finite-sum bounds described above.

Direct `lake --old env lean` audits passed. The three splitting declarations have transitive axioms exactly `propext`, `Classical.choice`, and `Quot.sound`.
