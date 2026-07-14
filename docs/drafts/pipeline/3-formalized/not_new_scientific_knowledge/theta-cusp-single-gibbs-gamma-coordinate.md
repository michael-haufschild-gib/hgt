# Theta-cusp single-Gibbs incomplete-Gamma coordinate

- **ID:** `theta-cusp-single-gibbs-gamma-coordinate`
- **Stage:** 3-formalized
- **Type:** exact source coordinate law
- **Scientific status:** change-of-variables bridge; novelty not claimed
- **Lean source:** `formal/GaloisForLFunctions/RHTower/PrimeArchThetaSingleGibbsGammaCoordinate.lean`
- **Statement:** Every moment in the single-Gibbs low-degree certificate is a moment of one fixed
  positive incomplete-Gamma density on `(1,infinity)`.

## Theorem

For

\[
L_m=\int_0^\infty x^m e^{5x/2}e^{-\pi e^{2x}}\,dx,
\]

the substitution `t=e^{2x}` gives, for every nonnegative integer `m`,

\[
L_m=\frac1{2^{m+1}}
\int_1^\infty (\log t)^m t^{1/4}e^{-\pi t}\,dt.       \tag{1}
\]

The transformed integrand is continuous and absolutely integrable.  It is nonnegative on the
entire domain and all moment orders share the same base density `t^(1/4) exp(-pi t)`.

## Positive route consequence

The exact single-Gibbs reduction expresses both remaining low-degree source certificates using
only `L_0,...,L_8` and `e^{-pi}`.  Equation `(1)` therefore converts the complete verification
problem to certified rational enclosure of nine logarithmic moments of one fixed positive
incomplete-Gamma density.  No separate Born, Witten, radial, Morse, or Fisher quadrature is
required.

## Formal theorem surface

- `continuousOn_thetaCuspFirstAtomSingleGibbsGammaIntegrand`
- `integrableOn_thetaCuspFirstAtomSingleGibbsGammaIntegrand`
- `thetaCuspLiouvilleGibbsMoment_eq_singleGammaIntegral`

The module contains no project axioms or placeholders.
