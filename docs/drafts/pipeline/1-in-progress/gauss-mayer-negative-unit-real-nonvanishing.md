# Real-source nonvanishing at the negative unit spectral parameter

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Parent:** [negative-unit cancellation](../3-formalized/gauss-mayer-negative-unit-pole-cancellation.md).
- **Target:** For every real `w>0`, `D(w,−1)=A(w,−1)≠0`, including `w=1`.

## Stronger source target

Prove that every actual derivative eigenfunction satisfying
`(R(w)f)'=−f'` on `[0,1]` is `f=c f_w`, without assuming `f(0)=0`.
The constant-response derivative and extrema must first force that value
to vanish. The actual operator equation `Rf=−f` then forces `c=0`.
This is a source rigidity statement, not an assumed positive-kernel interface.

## Source mechanism

The checked cancellation theorem proves equality and holomorphy, not
nonvanishing. The checked derivative cone supplies positive functionals
`L_x(g)=−(R(w)g)'(x)/h_w(x)` for `g(0)=0`, with `L_x(f_w)=1`.
The residual functional `L_x(g)−g(1/2)` has mass
`τ_w=(3/2)^(-w)<1`.

Suppose `Rf=−f`. Write `a=f(0)` and `g=f−a`. The actual branch series
should give `(R1)'(x)=−w Σ_{n≥1}(n+x)^(-w−1)<0`.
For `q=Re(g'/h_w)`, the eigen-equation then reads
`q−Re L_x(g)=−Re(a)(R1)'/h_w`.
The minimum and maximum of `q`, together with positivity and unit mass,
force `Re(a)=0`. Repeating for `if` forces `a=0`.

The residual-mass bound now contracts the oscillation of both components
of `f'/h_w` by `τ_w<1`; hence `f=c f_w`. The exact identity
`Rf_w=1−f_w` forces `c=0`. Transport this source exclusion through the
actual remainder's Hilbert factorization and Fredholm determinant.

## Certified source input

`GaussMayerNegativeUnitRigidity.lean` proves the strict negative real
constant-response derivative, unit-mass source bounds, and forced vanishing
at zero. `MayerNegativePole.negative_derivative_eigen_response` proves the
stronger response classification above; `remainder_negative_eigen_eq_zero`
excludes a nonzero `−1` eigenfunction of the actual remainder. Direct
production check and all five transitive axiom audits pass with only
`propext`, `Classical.choice`, and `Quot.sound`.

## Open obligations

Complete the actual remainder determinant/eigenvector transport. The
source rigidity is certified, but `D(w,−1)≠0` is not yet certified.
No complex-source or scattering exclusion is claimed.
