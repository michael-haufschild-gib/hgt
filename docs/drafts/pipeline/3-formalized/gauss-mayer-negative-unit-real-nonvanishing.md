# Real-source nonvanishing at the negative unit spectral parameter

- **Stage:** 3-formalized
- **Type:** Theorem
- **Parent:** [negative-unit cancellation](gauss-mayer-negative-unit-pole-cancellation.md).
- **Input:** [actual source derivative cone](gauss-mayer-positive-real-pole-coefficient.md).

## Theorem

For every real `w>0` and every complex `t`,

`det(I+R(w)+tP)=det(I+R(w))≠0`.

In particular, the actual source determinant `D(w,−1)=A(w,−1)` is
nonzero on the entire positive real axis, including its analytic value
at `w=1`.

A stronger source rigidity holds: every disc-algebra function satisfying
`(R(w)f)'=−f'` on `[0,1]` is a scalar multiple of the exact response
`r_w(z)=1−(1+z)^(-w)`. No initial condition at zero is assumed. The
actual operator equation `Rf=−f` then forces `f=0`.

## Proof

1. Bounded interior derivative evaluation realizes the actual branch
   derivative series. For the constant input, every negative branch
   derivative is the positive real quantity `w(n+x)^(-w−1)`.
   The first term is strictly positive, so `(R1)'(x)<0` is real.
2. Let `h_w=r_w'>0` and `L_x(g)=−(Rg)'(x)/h_w(x)`. On centered
   functions this is positive on the real derivative cone, with exact
   mass `L_x(r_w)=1`. Thus `m≤Re(g'/h_w)≤M` implies
   `m≤Re L_x(g)≤M`.
3. Given `(Rf)'=−f'`, write `a=f(0)` and `g=f−a`. Then
   `Re L_x(g)=Re(g'/h_w)−Re(a)L_x(1)`, with `L_x(1)>0` real.
   Evaluating at the minimum and maximum of the normalized real jet
   forces `Re(a)=0`. Repeating for `if` forces `a=0`.
4. The residual functional `L_x(f)−f(1/2)` has common mass
   `τ_w=(3/2)^(-w)<1`. Its bounds at the extrema force the normalized
   real jet constant. Applying the same argument to `if` handles the
   imaginary part. Zero initial value and the analytic identity principle
   recover `f=c r_w` on the original disc algebra. Since
   `Rr_w=1−r_w`, the actual equation `Rf=−f` gives `c=0` at zero.
5. Remove the zeta constant mode from the actual synthesis map:
   `J_R=J−ζ(w)[x↦e(x)1]`. Exact Cauchy evaluation gives
   `J_R analysis=R` and `analysis J_R=R_H`, the existing Hilbert
   remainder. Its matrix is exactly the actual remainder Cauchy matrix.
   The geometric Carleman identity turns a zero of `A(w,−1)` into a
   Hilbert `−1` eigenvector. Synthesis produces a nonzero source
   eigenfunction, contradicting step 4.
6. The certified scalar-mode cancellation identifies every perturbed
   negative-unit determinant, and the actual source determinant, with `A`.

## Lean certificate

Modules in `RenormalizedIntersectionTheory`, namespace `MayerNegativePole`:

- `GaussMayerNegativeUnitRigidity.lean`: `remainder_constant_derivative`,
  `averagedDerivative_bounds`, `evaluation_zero_of_negative_derivative_eigen`,
  `negative_derivative_eigen_response`, `remainder_negative_eigen_eq_zero`.
- `GaussMayerNegativeUnitNonvanishing.lean`: `remainderSynthesis_analysis`,
  `analysis_remainderSynthesis`, `remainder_eigenvector_transfer`,
  `regularPart_negative_one_ne_zero`,
  `perturbedDeterminant_negative_one_ne_zero`,
  `sourceDeterminant_negative_one_ne_zero`.

Both direct production checks pass without diagnostics. All five source
and six determinant-bridge transitive axiom audits contain only `propext`,
`Classical.choice`, and `Quot.sound`. Umbrella imports wired.

## Scope

The [exact inverse formula and nonzero rank-one source residue](gauss-mayer-negative-unit-resolvent-pole.md) are also certified. The nonvanishing theorem concerns real source parameters. Complex-source
resonance exclusion, primitive modular coding, and Selberg/scattering
comparison remain open. No RH conclusion or literature-priority claim follows.
