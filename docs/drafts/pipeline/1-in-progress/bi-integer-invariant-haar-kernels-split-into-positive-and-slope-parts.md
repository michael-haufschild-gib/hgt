# Bi-integer-invariant Haar kernels split into positive and slope parts

- **ID:** HAAR-BIINTEGER-POSITIVE-SLOPE-SPLITTING
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Parent:** [Relative Haar splitting](finite-index-haar-carriers-split-modulo-polynomial-kernels.md)
- **Statement:** Every Hermitian finite-index affine kernel `k` with integer Haar successor and invariance under integer translations on both sides admits `k=p+ψ∘slope`, with `p` positive definite and having the same successor, and `ψ` Hermitian. The existing exact index law then gives `κ(k)=κ(ψ)`.

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

## Verification boundary

Local periodicity, the orthogonal cyclic projections, and moving-subspace positivity are formalized in `BiarithmeticGeometry/Affine/PeriodicTranslations.lean`, `HeckeKreinToeplitz/Index/ColumnProjections.lean`, and `AdelicKreinGeometry/Haar/TranslationMovingPositivity.lean`, with direct audits and standard axiom closures.

`HeckeKreinToeplitz/Index/HermitianFiniteSums.lean` gives the squared `ℓ¹` bound for finite combinations of unit-bounded generators. `MonotoneHermitianForms.lean` gives pointwise convergence and nonnegativity of bounded monotone Hermitian forms by polarization. Both passed direct audits with standard axiom closures.

`HeckeKreinToeplitz/Index/ProjectionFunctoriality.lean` and `ProjectionOrder.lean` formalize intertwining, nested powers, and the resulting order of nonnegative moving forms. `AdelicKreinGeometry/Haar/TranslationProjections.lean` gives affine covariance, step reversal, and invariance under integer multiples of the step. All passed direct audits with standard axiom closures.

`AdelicKreinGeometry/Haar/GeneralOrbits.lean` proves the reciprocal-denominator projection norm for every affine column, with a direct audit and standard axiom closure.

`BiarithmeticGeometry/Affine/FactorialTranslations.lean` proves cofinal cyclic exhaustion and convergence of the factorial steps to zero. `AdelicKreinGeometry/Haar/SplittingUniqueness.lean` proves uniqueness whenever a positive Haar and Hermitian slope split exists. Both passed direct audits with standard axiom closures.

`AdelicKreinGeometry/Haar/TranslationForms.lean` proves Hermitian symmetry, nonnegativity, uniform boundedness, affine covariance, and monotonicity under enlargement of cyclic subgroups. It passed a direct audit with standard axiom closure.

Affine invariance of the limit and slope factorization remain to be formalized. Combined with the formalized [zero-axis polynomial correction](../3-formalized/finite-index-periodic-affine-kernels-have-a-zero-axis-polynomial-correction.md), these would supply the full relative splitting; it is not yet a proved decomposition.
