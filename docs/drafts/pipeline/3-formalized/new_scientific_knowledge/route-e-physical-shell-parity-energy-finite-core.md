# Route E physical-shell parity--energy finite core

- **ID:** `ROUTE-E-PHYSICAL-SHELL-PARITY-ENERGY-FINITE-CORE-001`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / EXACT COVARIANCE SURVIVOR / ODD-CUBE PRESERVATION / NO-GO
- **Scientific status:** `[LEAN-PROVED] [BRIDGE] [NO-GO] [NOVELTY UNVERIFIED] [NOT RH]`
- **Parent:** `../../1-in-progress/route-e-physical-shell-conditioned-parity-energy-regression-law.md`
- **Route:** E
- **RH used:** no
- **Computation used:** no
- **Literature used:** no; internal-corpus formalization under current directive

## Result

The dependency-closed finite content of physical Gaussian shell conditioning is fully formalized.

For a covariance block `(A,B,C)` and Gaussian energy width `Delta`, conditioning transforms

\[
 A'=A-\frac{B^2}{C+\Delta^2},\qquad
 B'=B-\frac{BC}{C+\Delta^2},\qquad
 C'=C-\frac{C^2}{C+\Delta^2}.
\]

Lean proves

\[
 \frac{B'}{C'}=\frac BC,
 \qquad
 A'-\frac{(B')^2}{C'}=A-\frac{B^2}{C}.
\]

Thus Gaussian energy conditioning preserves both regression frequency and parity--energy Schur
complement exactly.

The centered Gaussian log shell

\[
 G_{X,\Delta}(m)=
 \exp\!\left(-\frac{(\log m-\log X)^2}{2\Delta^2}\right)
\]

cannot be the Laplace transform of a positive measure on nonnegative scales: such transforms are
antitone, whereas this shell is strictly increasing between `X/2` and `X`.

For arbitrary finite complex shell fields, Lean proves exact polarization

\[
 |Z|^2-|M|^2
 =\sum_{i,j}\alpha_i\overline{\alpha_j}
   (Z_i\overline{Z_j}-M_i\overline{M_j}).
\]

Finally, for every finite palette and arbitrary complex recurrence factors `B_p` and selected
factors `U_p`,

\[
 \prod_p(B_p+U_p)-\prod_p(B_p-U_p)
 =2\sum_{\substack{R\subseteq P\\|R|\text{ odd}}}
   \prod_{p\in R}U_p\prod_{p\notin R}B_p.
\]

Every odd grade and every unselected recurrence factor is retained. Multiplication by a common
shell factor preserves the identity exactly.

## Lean certificate

Module:

```text
GaloisForLFunctions.RHTower.RouteEPhysicalShellParityEnergyRegression
```

Principal declarations:

```text
RouteEGaussianCovarianceBlock.conditioned_regressionRatio
RouteEGaussianCovarianceBlock.conditioned_schurComplement
RouteEPositiveGaussianShell.no_positiveLaplaceRepresentation
routeESignedShell_polarization
routeEWeightedProductDifference_eq_paritySum
routeEWeightedProductDifference_eq_two_oddSubsetSum
routeECommonShellMultiplier_preservesWeightedOddCube
```

Module is imported by `GaloisForLFunctions.RHTower`. No `sorry`, `admit`, new `axiom`, `opaque`,
`unsafe`, numerical computation, RH premise, or asymptotic determinant premise occurs.

## No-go closure

- **Exact killing theorem/mechanism:** a centered Gaussian log shell is not antitone, so no
  positive Laplace mixture can represent it globally.
- **Strongest positive survivor:** exact signed cross-shell polarization and exact weighted
  odd-cube preservation.
- **New insight:** source-faithful shell descent must control cross-shell covariance while keeping
  recurrence factors; diagonal shell estimates and positive averaging cannot suffice.
- **Status:** survivor is dependency-closed and formalized by the declarations above.

## Frontier consequence

Finite covariance algebra, positive-Laplace obstruction, polarization, and odd-cube preservation
are not open. The parent card's claimed prime-array Gaussian determinant asymptotic is not included:
its current saddle argument lacks typed uniform remainder and tail hypotheses and has been returned
to Stage 1. No such asymptotic is claimed by this Stage-3 card.

## Novelty status

No external priority claim is made. Internal synthesis is exact preservation of parity--energy
Schur complement together with recurrence-weighted odd-cube survival and the positive-Laplace wall.

## Log

- 2026-08-12 — Exact finite covariance, Laplace no-go, polarization, and weighted odd-cube
  survivor separated from unclosed Gaussian saddle asymptotic and recorded at Stage 3.
