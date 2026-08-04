# Mass-dispersion radiation-corona universality

**Stage:** 3 — formalized in Lean 4  
**Date frozen:** 2026-08-04  
**Label:** `[BRIDGE] [LEAN-PROVED] [NOVELTY UNVERIFIED]`

## 1. Exact theorem

Let `0\le\lambda\le a` and define the principal gauged mass dispersion

\[
 \omega_{a,\lambda}(\xi)
 :=\sqrt{(\xi-i\lambda)^2+a^2},\qquad \xi\in\mathbb R.
\]

Then the two frequency ends have exact limits

\[
 \lim_{\xi\to+\infty}
   \left(\omega_{a,\lambda}(\xi)-\xi\right)=-i\lambda,
 \qquad
 \lim_{\xi\to-\infty}
   \left(\omega_{a,\lambda}(\xi)+\xi\right)=i\lambda.
\]

Consequently, for any `a,b\ge\lambda\ge0`,

\[
 \omega_{a,\lambda}(\xi)-\omega_{b,\lambda}(\xi)\longrightarrow0
 \quad(\xi\to\pm\infty).
\]

Equivalently, all masses have the same class in the two-ended corona algebra
`C_b(\mathbb R)/C_0(\mathbb R)` after subtracting the ungauged symbols
`|\xi|`; their boundary values are `-i\lambda` at `+\infty` and `i\lambda` at
`-\infty`.

## 2. Proof at the positive end

Put `w=\xi-i\lambda`.  For `\xi\to+\infty`, `w` remains in the fourth
quadrant and `w/\xi\to1`.  The principal square root satisfies

\[
 \omega_{a,\lambda}(\xi)^2=w^2+a^2,
 \qquad \Re\omega_{a,\lambda}(\xi)>0.
\]

Rationalization gives

\[
 \omega_{a,\lambda}(\xi)-w
 =\frac{a^2}{\omega_{a,\lambda}(\xi)+w}.
\]

The explicit principal-root formula shows
`\Re\omega_{a,\lambda}(\xi)\sim\xi`; hence the denominator has modulus
asymptotic to `2\xi`, and the right side tends to zero.  Therefore

\[
 \omega_{a,\lambda}(\xi)-\xi
 =\left(\omega_{a,\lambda}(\xi)-w\right)-i\lambda
 \longrightarrow-i\lambda.
\]

## 3. Proof at the negative end

For `\xi\to-\infty`, the principal root is asymptotic to `-w`, because its
real part remains positive.  Rationalizing against `-w` gives

\[
 \omega_{a,\lambda}(\xi)+w
 =\frac{a^2}{\omega_{a,\lambda}(\xi)-w}\longrightarrow0,
\]

since the denominator has modulus asymptotic to `2|\xi|`.  Thus

\[
 \omega_{a,\lambda}(\xi)+\xi
 =\left(\omega_{a,\lambda}(\xi)+w\right)+i\lambda
 \longrightarrow i\lambda.
\]

Subtracting the endpoint laws for masses `a` and `b` proves the mass-difference
limits.

## 4. Dependency ledger

- explicit principal-square-root formula and branch selection;
- elementary rationalization;
- real/complex limit algebra.

No spectral, number-theoretic, or RH hypothesis enters.

## 5. Scientific interpretation

Mass is a corona-trivial deformation.  It changes finite-frequency dispersion,
real-time decay, and every lower radiation coefficient, but it cannot change
the two asymptotic growth characters imposed by exponential gauge.

This unifies four independent observations:

| Observation | Corona shadow |
|---|---|
| Mass preserves spectral charge | finite mass perturbation does not move frequency ends |
| Exact weighted growth `e^{\lambda|u|}` | imaginary corona values are `\mp\lambda` |
| No nonzero two-sided bounded state | each corona end is unstable in one time direction |
| Every finite radiation jet fails | changing lower asymptotic coefficients never changes the corona class |

The result rules out tuning `a` as a source-side cure.  Every strict mass
`a>1/2` has the same critical radiation corona at `\lambda=1/2`.

## 6. Universal prediction

Any even strip-analytic dispersion whose two analytic ends satisfy

\[
 \omega(\xi-i\lambda)=\pm(\xi-i\lambda)+o(1)
 \quad(\xi\to\pm\infty)
\]

has the same vertical exponential type `\lambda`, regardless of its
finite-frequency gap.  Thus no asymptotically relativistic carrier can improve
the zeta exponent without a new arithmetic cancellation law.

This general prediction is not claimed proved here; it is the next exact
corona-universality target.

## 7. Novelty and significance audit

The endpoint expansion is routine symbol calculus.  Exact use as a unifier of
the mass-charge, nonnormal-growth, bounded-orbit, and finite-jet obstructions
was not found in the route corpus or targeted external search.  It is a
`[BRIDGE]`, not yet candidate new science.

## 8. Lean proof

Formalization pressure strengthens the statement from strict `a>\lambda` to
the closed chamber `0\le\lambda\le a`; the same proof works at `a=\lambda`,
including the massless corner `a=\lambda=0`.

Module:

`formal/GaloisForLFunctions/HTGeometry/MassDispersionRadiationCorona.lean`

Exact capstones:

- `tendsto_massGaugeDispersion_sub_atTop`;
- `tendsto_massGaugeDispersion_add_atBot`;
- `tendsto_massGaugeDispersion_sub_mass_atTop`;
- `tendsto_massGaugeDispersion_sub_mass_atBot`;
- `tendsto_massGaugeDispersion_im_atTop`;
- `tendsto_massGaugeDispersion_im_atBot`;
- `abs_massGaugeDispersion_im_lt`;
- `massGaugeHalfWaveSymbol_bound_iff`.

The module proves the principal-root square law, real-part lower bound,
rationalized endpoint remainders, two complex endpoint limits, mass-difference
limits, imaginary growth characters, strict finite-frequency radiation
interval, and optimal pointwise half-wave envelope.  The separate
`MassGaugeHalfWaveL2` module lifts this envelope to the exact `L²` operator norm
and nonzero-orbit rigidity.  No `K_1`, PNT, or number-theoretic hypothesis
enters.

Verification:

- `lake env lean GaloisForLFunctions/HTGeometry/MassDispersionRadiationCorona.lean`;
- `lake build GaloisForLFunctions.HTGeometry.MassDispersionRadiationCorona`;
- `scripts/formal_tools.py lint --check-generated`;
- `#print axioms` on all six capstones: only `propext`, `Classical.choice`,
  `Quot.sound`.

Status: `[LEAN-PROVED]`.
