# Positive real nonvanishing of the Mayer pole coefficient

- **Stage:** 3-formalized
- **Type:** Theorem
- **Parent:** [exact determinant finite part](gauss-mayer-raw-determinant-finite-part.md).

## Theorem

For the actual source determinant `D(w,λ)=A(w,λ)+ζ(w)B(w,λ)`,

`w>0`, `0<λ<(3/2)^w` imply `B(w,λ)≠0`, for real `w,λ`.

This interval includes every `0<λ≤1`. In particular, `B(1,1)≠0`, so
`w↦D(w,1)` has meromorphic order exactly `−1` at one. The previously
certified negative-unit cancellation has `B(w,−1)=0` throughout `Re w>0`.

## Proof

Let `Q=I−P`, `K=QR(w)Q`, and `r_w(z)=1−(1+z)^(-w)`.
The exact response satisfies `r_w(0)=0` and `Rr_w=1−r_w`.
Its derivative `h_w(x)=w(1+x)^(-w−1)` is positive on `[0,1]`.

1. Bounded Cauchy derivative evaluation maps the actual normally
   convergent remainder series to its derivative series. For `f(0)=0`
   with `Re f'≥0`, every negative branch derivative has nonnegative real
   part. The first inverse branch is at least `1/2`, and its normalized
   value coefficient is one. Monotonicity therefore gives
   `Re[-(Rf)'/h_w−f(1/2)]≥0`.
2. This constructed residual functional takes `r_w` to the constant
   `τ_w=(3/2)^(-w)`. If `m≤Re(f'/h_w)≤M`, applying positivity to
   `f−m r_w` and `M r_w−f` bounds its real value between `mτ_w` and
   `Mτ_w`. Compact extrema show that a real derivative eigenvalue
   `μ>τ_w` forces the normalized real jet constant. The response identity
   then forces that constant to vanish. Applying the same argument to
   `if` kills the imaginary part. The analytic identity principle gives
   `f=0` on the original disc algebra.
3. A `K` eigenfunction with nonzero eigenvalue vanishes at zero, and
   differentiation removes its output centering. Thus `K` has no nonzero
   eigenfunction with real eigenvalue `μ>τ_w`.
4. Compress the actual synthesis map on both sides, using the checked
   Hilbert evaluation projection. The resulting `J_K` satisfies
   `J_K analysis=K`; its reverse product has precisely the actual Cauchy
   matrix of `K`. Geometric decay identifies the Hilbert kernel and
   bounded operator. Synthesis transports every nonzero Hilbert eigenvalue
   back to a nonzero source eigenfunction.
5. The constant column of this matrix is zero. Finite determinant
   expansion removes it, and passage to Fredholm limits identifies the
   full determinant with the complementary determinant `C`. The exact
   identity is `B(w,λ)=−λ det(I−λC)`. The geometric Carleman identity
   detects determinant zeros as Hilbert eigenvectors. A zero of `B` in
   the stated interval would give `μ=λ⁻¹>τ_w`, contradicting step 3.
6. At `w=λ=1`, nonvanishing of the exact residue gives meromorphic order
   `−1` by the certified source pole theorem.

## Lean certificate

Modules in `RenormalizedIntersectionTheory`:

- `GaussMayerDerivativeCone.lean`: actual derivative series, source
  minorization, exact residual mass, compact-extremum contraction, and
  `MayerPositive.derivative_eigen_eq_zero`.
- `GaussMayerPositivePoleCoefficient.lean`, namespace `MayerPositivePole`:
  `compressed_eigen_eq_zero`, `compressedSynthesis_analysis`,
  `matrixOf_compressedHilbert`, `toOperator_compressed`,
  `fdet_compressed_eq_complement`, `compressed_eigenvector_transfer`,
  `polePart_ne_zero`, `polePart_one_one_ne_zero`, and
  `sourceDeterminant_one_simple_pole`.

Both direct production checks pass without diagnostics. All 19 source
and 10 determinant-bridge transitive axiom audits contain only `propext`,
`Classical.choice`, and `Quot.sound`. Umbrella imports wired.

## Scope

This is nonvanishing of the exact pole coefficient for real source
parameters. The interval endpoint, complex source exclusion, primitive
modular coding, and Selberg/scattering comparison remain open. No RH
conclusion or literature-priority claim follows.
