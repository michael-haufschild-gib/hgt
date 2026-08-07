# Hedenmalm--Burnol completed divided-energy identification

## Status

Stage 2: dependency-closed paper proof; Lean formalisation in progress.

## Conjecture cycle

### C26a — individual dipole neutrality from theta symmetry — FALSE

For an actual theta-source zero `z`, write

`c_z = integral_(0,1) (t - 1/2) rootG(z,t)`.

Even-source reflection and real-source conjugation can force only the quartet covariance

`c_(-z) = -c_z`, `c_(-conj z) = conj(c_z)`, and
`c_(conj z) = -conj(c_z)`.

An arbitrary non-pure-imaginary complex number assigned to `c_z` and extended by these three
rules satisfies every covariance.  Therefore symmetry alone does not force `Re c_z = 0`.

Positive survivor: the full normalized root modes, not only their zeros, transform covariantly
under the quartet.  This remains useful for orbit bookkeeping but cannot close RH.

### C27a — completed divided energy is quantile root energy — PROVED ON PAPER

For `rho : XiDivisorSupport`, put

`a = xiSpectralPointSupport rho`, `alpha = -a`, and

`U_alpha(x) = sourceModeU thetaSource alpha x`.

Then

`integral_xi ||completedXiFirstDividedFunction rho xi||^2`

`= 2*pi*thetaSource.mass^2*thetaRootEnergy alpha`.                 `(1)`

Equivalently,

`||completedXiFirstDividedL2 rho||^2`

`= 2*pi*thetaSource.mass^2*thetaRootEnergy (-xiSpectralPointSupport rho)`. `(2)`

This is an unconditional identity at every actual Xi divisor, including multiple and off-line
divisors.

## Dependency-closed paper proof

1. `XiC a = 0`; evenness gives `XiC alpha = XiC (-a) = 0`.  Both points lie in the open
   Hedenmalm strip because every Xi divisor lies in the critical strip.
2. Unfolding the two Volterra definitions gives

   `U_alpha = hedenmalmCausalVolterra alpha`.

   Both are `-i exp(-i alpha x)` times the left primitive of
   `thetaCuspFullSource(y) exp(i alpha y)`.
3. Define the Plancherel-scaled time vector

   `V_alpha(x) = 2*pi*U_alpha(2*pi*x)`.

   Exponential two-ended decay makes `V_alpha` both integrable and square-integrable.
4. A dilation change of variables in the classical Fourier integral gives, for real `xi`,

   `Fourier(V_alpha)(xi) = hedenmalmThetaEigenTransform alpha xi`.
5. Away from the singleton `xi = -alpha = a`, the existing transform theorem and multiplicity
   bridge give

   `Fourier(V_alpha)(xi)`

   `= i*xiThetaEigenFourier a xi`

   `= i*(i*xiThetaDividedChain a 1 xi)`

   `= -completedXiFirstDividedFunction rho xi`.

   The exceptional singleton is null, so this equality is sufficient for energy integrals.  No
   simplicity assumption is used: the divided chain is the removable quotient at arbitrary
   multiplicity.
6. Classical Plancherel and dilation yield

   `integral ||completedXiFirstDividedFunction rho||^2`

   `= integral ||Fourier(V_alpha)||^2`

   `= integral ||V_alpha||^2`

   `= 2*pi*integral ||U_alpha||^2`.                                `(3)`
7. Quantile change of variables, together with

   `rootH(thetaSource,alpha,t) = (-i/M) U_alpha(Q(t))`

   and `q(t)=M/k(Q(t))`, gives

   `thetaRootEnergy alpha = M^(-2)*integral ||U_alpha||^2`.         `(4)`

8. Substituting `(4)` into `(3)` proves `(1)`; the definition of
   `completedXiFirstDividedL2` and the `L2` norm-as-integral theorem prove `(2)`.

## C27b — source-leakage reinterpretation — paper consequence

The completed quotient belongs to the maximal domain of real-coordinate multiplication and
satisfies

`M_x Q_rho = a Q_rho + XiC`.

Since `M_x` is formally self-adjoint, the imaginary part of the diagonal pairing gives

`Im <Q_rho, XiC> = -Im(a) ||Q_rho||^2`

with sign adjusted to the corpus's inner-product convention.  Combining this with `(2)` and the
C25 law

`Re c_alpha = -Im(alpha) thetaRootEnergy alpha`, `alpha=-a`,

identifies the quantile dipole with the normalized imaginary completed-source leakage.  Lean must
verify the exact convention before this consequence is promoted.

## Hostile audit

- This does not prove the source leakage is zero.  Formal self-adjointness alone permits the
  nonzero inhomogeneous defect `XiC` to carry exactly the nonreal spectral charge.
- It does not assume root simplicity; all statements use the first removable divided chain.
- It does not put `rootG` in unweighted `L2(0,1)`.  The proof uses the already-proved weighted root
  energy and the time-side `L2` mode, avoiding the false C25a upgrade.
- It is not a numerical identity and introduces no computation.

## Novelty audit

- Corpus search found separate quantile energy/flux, time-to-entire transform, multiplicity-chain,
  Plancherel, and Burnol--Hedenmalm completion-domain theorems, but no theorem identifying their
  exact energies.
- Hedenmalm's 2026 spectral-interpretation paper supplies the two-ended eigenfunction viewpoint;
  this exact quantile-mass-normalized, multiplicity-safe completed-divided energy identity was not
  located there.  External priority remains subject to expert review.

## Lean target

New module should prove, unconditionally:

1. `sourceModeU thetaSource alpha = hedenmalmCausalVolterra alpha`;
2. Fourier transform of the `2*pi`-scaled time mode;
3. exact quantile/time energy change of variables;
4. `(1)` and `(2)`;
5. if convention audit succeeds, C27b's exact dipole/source-leakage identity.

## Open core after C27

Prove that the completed source leakage pairing is real (or otherwise neutral) from a genuinely
independent Euler--Gamma--prime law.  By C27 this is exactly the missing individual dipole
neutrality and hence exactly the RH obstruction, not a stronger hidden assumption.
