# Hedenmalm local-normality times numerical-sector criterion

- **ID:** `hedenmalm-numerical-sector-product-criterion`
- **Stage:** 3-formalized
- **Type:** TOP-DOWN CONSTRAINT × ORIENTATION PRODUCT / NUMERICAL RANGE
- **Scientific status:** `[BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean module:** `formal/GaloisForLFunctions/RHTower/XiHedenmalmNumericalSectorCollision.lean`

## Statement

For an Xi divisor copy `q`, let `theta_q` be the canonical evaluated Hedenmalm mode and let
`R_Xi` be the reciprocal centered-Xi operator.  Define the numerical value

\[
\nu_q=\langle\theta_q,R_\Xi\theta_q\rangle.
\]

Lean proves the exact complementary factorization

\[
RH\quad\Longleftrightarrow\quad
\left(
\begin{array}{c}
\text{every local Hedenmalm Jordan block at an existing}\\
\text{right-half Xi divisor point is normal}
\end{array}
\right)
\qquad\wedge\qquad
\left(\operatorname{Im}\nu_q\ge0\text{ for every divisor copy }q\right).
\]

At a locally simple zero with centered spectral coordinate `alpha_q`, the mode is nonzero and

\[
R_\Xi\theta_q=\alpha_q^{-1}\theta_q,
\qquad
\operatorname{Im}\nu_q
=\operatorname{Im}(\alpha_q^{-1})\,\|\theta_q\|^2.
\]

Functional-equation reflection sends `alpha_q` to `-alpha_q`.  Applying the same upper-sector
inequality to both reflected modes squeezes `Im(alpha_q^{-1})` to zero, hence forces `alpha_q` to
be real.  Right-half local Jordan normality supplies the missing local simplicity, so no right-half
divisor point can exist.

The formal chain is

```text
right-half local Jordan normality
  -> every hypothetical right-half Xi zero is simple

upper numerical sector on theta_q and its reflected mode
  -> every simple centered Xi spectral point is real

simple + real + strictly right-half
  -> contradiction
  -> RH.
```

## Anti-redressing attack

Neither factor is RH in altered notation.

- A simple off-critical zero gives a one-dimensional scalar Jordan block, which is normal even
  when its eigenvalue is nonreal.  Local normality therefore contains multiplicity information but
  no critical-line orientation.
- At a multiple zero the first evaluated Hedenmalm mode is exactly zero.  Consequently `nu_q=0`,
  so the numerical-sector condition holds automatically on precisely those fibers.  It contains
  orientation information only where the multiplicity obstruction has already been removed.

The theorem is therefore a genuine constraint-times-orientation collision.  Its two premises have
complementary blind spots rather than being two individually RH-equivalent criteria.

## Source-side corollary

The existing source-to-source closure condition

\[
\overline{\operatorname{span}(\text{continued Cauchy sources})}
\supseteq
\overline{\operatorname{span}(\text{Hedenmalm theta evaluations})}
\]

implies global Xi simplicity.  Lean consequently proves that this closure condition together with
the upper numerical sector already implies RH.  The closure input is only one sufficient provider;
the exact capstone needs normality solely at right-half divisor points.

## Open core

`[OPEN CORE]` Prove the Hedenmalm upper numerical-sector condition directly from the prime--Gamma
source form, without assuming self-adjointness of `R_Xi`, zero locations, or a positivity statement
already equivalent to RH.  Independently provide right-half local Jordan normality, or use the
stronger already isolated continued-Cauchy-to-Hedenmalm closure condition.

The preferred target is a source identity or positive kernel whose specialization is

\[
\operatorname{Im}\langle\theta_q,R_\Xi\theta_q\rangle\ge0
\]

for both members of each functional-equation reflection pair.  A construction that first assumes
the reciprocal operator is self-adjoint would merely import RH and does not discharge the open core.

## Formal verification

Lean proves:

- `xiReciprocalOperator_thetaEigen_of_deriv_ne_zero`;
- `xiThetaReciprocalNumericalValue_im_eq_of_deriv_ne_zero`;
- `xiThetaReciprocalNumericalValue_eq_zero_of_deriv_eq_zero`;
- `xiSpectralPoint_real_of_numericalUpperSector_of_deriv_ne_zero`;
- `riemannHypothesis_of_rightHalfLocalJordanNormal_of_numericalUpperSector`;
- `riemannHypothesis_iff_rightHalfLocalJordanNormal_and_numericalUpperSector`;
- `riemannHypothesis_of_xiContinuedCauchyToHedenmalmClosure_of_numericalUpperSector`.

The named module build passes in the repository toolchain.
