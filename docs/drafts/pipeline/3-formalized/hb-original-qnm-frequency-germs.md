# HB: original radial Green germs at every Xi QNM

- **Stage:** formalized in Lean 4.
- **RH:** unproved; endpoint continuation, joint left pairing, and extinction remain open.
- **Scope:** the existing BM horizon/normalizable functions, full connection coefficient,
  and original native source profile with its fixed smooth-onset transform.
- **Frontier map:** read-only for this work.

## Exact closed statements

`sourceGreenIntegrands_allXi_qnm_meromorphic` proves that, for every Xi multiplicity
copy and every overtone, both original source-weighted radial Green integrands have
meromorphic frequency germs at both physical QNM frequencies. The radial point
lies strictly between the horizon and outer boundary. Fixed source amplitudes and
angular coefficients remain arbitrary. No RH, continuation, nonresonance, or
nonvanishing-numerator premise is supplied.

The underlying statements establish:

- `hypergeometric_family_differentiableAt`: frequency holomorphy of the original Gauss
  sum under proved local bounds and denominator separation, including terminating
  numerator parameters.
- `horizon_frequency_analyticAt`: the original dressed horizon solution is analytic
  off the real Laplace-frequency axis.
- `normalizable_frequency_entire`: the original dressed outer solution is entire
  in frequency at every physical interior radial point.
- `connection_frequency_analyticAt`: the full connection coefficient is analytic
  off the real frequency axis, including its QNM zeros.
- `greenKernel_frequency_meromorphicAt`: the actual expression
  `H(w,min(z,t))*N(w,max(z,t))/(-connection(w))` has a meromorphic frequency germ.
- `continuedSourceProfile_eq`: the continued source agrees with the original
  smooth-onset source transform in its convergence chamber.

These are pointwise radial germs. Meromorphy does not assert a pole, a nonzero
residue, or vanishing of a physical source coefficient.

## Proof

Write the Gauss coefficient as

`d_n(a,b,c) = (a)_n (b)_n / (n! (c)_n)`.

On a frequency neighborhood choose positive `B,delta` such that all three
parameter norms are at most `B` and `|c+j| >= delta` for every nonnegative integer
`j`. Choose a natural `N >= B+1`. The actual Pochhammer product splits into a
prefix and tail. Since `Re(c+N) >= 1`,

`|(c)_(N+m)| >= delta^N m!`.

The numerator products are bounded by the positive real products with parameter
`B`. Therefore

`|d_(N+m)(a,b,c)| <= ((B)_N)^2 / delta^N * ((B+N)_m)^2/(m!)^2`.

The finite prefix has an explicit finite bound. The remaining positive Gauss
series has radius one, so this yields one summable majorant on every strictly
smaller radial disk. Each coefficient is holomorphic in frequency. The corpus's
dominated holomorphic summation theorem applies to the original sum. No numerator
is divided out, so terminating parameters remain admissible.

For the physical horizon parameters, a ball of radius
`min(1, |Im(w)|/2)` keeps every `1+u+j` at distance at least `|Im(w)|/2` from zero.
The normalizable denominator is fixed at `3/2`, so its series is entire in the
frequency parameter. Positive radial bases make the physical complex-power
dressing entire in its exponent. The connection is the product of an off-pole
Gamma factor and two entire reciprocal Gamma factors; its zeros are retained.

The source profile retains the factor

`1/(w-2*s) + onsetCorrection(2*s,w)`.

Its correction is the existing entire transform of the fixed smooth transition.
The existing transform identity gives equality in the actual source convergence
chamber. All remaining source factors are entire at each positive interior
radial point. Multiplication and division now give the original source-weighted
Green germs. Finally, the proved nonzero real part of each Xi spectral point
places both corresponding Laplace QNM frequencies off the real axis.

## Files and audit

General leaves in `formal/GaloisForLFunctions/HTGeometry/`:

- `HypergeometricParameterBounds.lean`
- `HypergeometricParameterMajorant.lean`
- `HypergeometricParameterHolomorphy.lean`

Physical leaves in `formal/GaloisForLFunctions/RHTower/`:

- `ThetaCuspHawkingBMLaplaceParameterHolomorphy.lean`
- `ThetaCuspHawkingBMLaplaceFrequencyContinuation.lean`
- `ThetaCuspHawkingBMLaplaceSourceContinuation.lean`

Six individual canonical `lake build <module>` audits passed without warnings.
All 25 new public theorems passed scratch `#print axioms`, with only `propext`,
`Classical.choice`, and `Quot.sound`. Sources total 493 lines. Twelve installed
olean/ilean artifacts are byte-identical to the canonical audits. Each new leaf
is wired once into its theorem-area umbrella. No full or umbrella build ran;
only the six new oleans were produced in the isolated audit package. Development
used foreground `lake env lean` checks with one owned process at a time.
No numerical experiment or computational proof certificate was used.

Repository-wide `formal_tools.py lint --check-generated` reported no errors in
these leaves. Its global gate remains unclean: concurrent unwired
`SelbergMaassAugmentedDirection` and `SelbergWeightedPathEnergy`, plus concurrent
`LEAN_API.md`/`LEAN_OVERVIEW.md` generated-index drift, were reported outside this
work. Those concurrent sources were preserved.

## Remaining physical obligation

Continue the actual endpoint Green moments, including source tails and all
normalizations; pointwise meromorphy cannot be interchanged with improper
integration without proof. Identify the resulting continuation with the original
complete-source joint causal response, including its cutoff commutators and
angular cusp domain. Then prove the physical advanced/adjoint left pairing,
retained spin-two/AIME identification, and an independent Hawking-clock extinction
law. None of these remaining obligations is discharged by the present theorem.
