# CCM completed prime--Gamma accretivity criterion

- **ID:** `ccm-completed-prime-gamma-accretivity-criterion`
- **Stage:** 3-formalized
- **Type:** THEOREM / FORMALIZATION / BRIDGE / NOT NEW SCIENTIFIC KNOWLEDGE
- **Lean module:**
  `formal/GaloisForLFunctions/RHTower/CCM/CCMCompletedPrimeGammaAccretivityCriterion.lean`
- **Scientific status:** `[PROVED IN LEAN] [BRIDGE] [NOT AN RH PROOF]`

## Statement

Define the completed prime--Gamma flux

\[
\mathcal F(s)=\operatorname{infinitePrimeFlux}(s)
  -(\log \operatorname{archFactor})'(s).
\]

Its left-half-strip accretivity condition is

\[
0<\Re s<\frac12,quad \zeta(s)\ne0
\quad\Longrightarrow\quad
\Re\mathcal F(s)\ge0.
\]

Lean proves the exact equivalences

\[
\begin{aligned}
\mathrm{RH}
&\Longleftrightarrow
\texttt{CompletedPrimeGammaLeftHalfAccretive}\\
&\Longleftrightarrow
\texttt{ContinuedPrimeArchUpperAntiHerglotz}\\
&\Longleftrightarrow
\texttt{ContinuedPrimeArchUpperCauchyDiagonalNonnegative}\\
&\Longleftrightarrow
\texttt{XiWeilUpperOneCauchyNonnegative}.
\end{aligned}
\]

The completed flux condition is also equivalent to its restriction to the countable dense family
of Gaussian-rational points in the left half-strip:

\[
\mathrm{RH}
\Longleftrightarrow
\texttt{CompletedPrimeGammaGaussianRatLeftHalfAccretive}.
\]

## Positive carrier law

A successful CCM construction must carry a rank-one accretive source: at every pole-free point in
the left half of the critical strip, the completed arithmetic flux has nonnegative real part. It is
enough to carry this sign on one fixed countable dense source family because the completed flux is
continuous away from its poles.

The centered coordinate `s=1/2+zI` turns this real accretivity into the anti-Herglotz sign

\[
\Im T(z)\le0,
\]

and the diagonal Cauchy divided difference is exactly

\[
\frac{T(\overline z)-T(z)}{z-\overline z}
=-\frac{\Im T(z)}{\Im z}.
\]

Thus the two-pole carrier remains a valid Hermitian formulation, but the RH-bearing sign is already
visible on single Cauchy diagonals.

## Relation to the remaining source theorem

Accretivity is the sharp sign formulation:

```text
CompletedPrimeGammaGaussianRatLeftHalfAccretive
```

The broader formal corpus proves that a sign is stronger than necessary. It is enough to establish
a single finite lower floor on the same countable family:

```text
CompletedPrimeGammaGaussianRatLeftHalfBoundedBelow
```

This weaker predicate is also Lean-equivalent to RH. For the distinguished
Connes--Consani--Moscovici construction, either the sharp sign or merely this uniform floor must be
produced from the semilocal Sonin principal/residual graph together with the already isolated local
flux normalization.

No density of arbitrary Weil tests, determinant limit, zero transfer, or two-pole collision argument
remains in this final source statement.

## Formal declarations

```text
RHTower.completedPrimeGammaLeftHalfAccretive_of_continuedPrimeArchUpperAntiHerglotz
RHTower.completedPrimeGammaLeftHalfAccretive_iff_antiHerglotz
RHTower.continuedPrimeArchUpperAntiHerglotz_iff_riemannHypothesis
RHTower.completedPrimeGammaLeftHalfAccretive_iff_riemannHypothesis
RHTower.completedPrimeGammaGaussianRatLeftHalfAccretive_of_full
RHTower.completedPrimeGammaGaussianRatLeftHalfAccretive_iff_riemannHypothesis
```

## Verification

- [x] non-q62 anti-Herglotz and one-Cauchy source gates reused
- [x] reverse centered-coordinate implication compiled
- [x] full left-half accretivity equivalence compiled
- [x] countable Gaussian-rational equivalence compiled
- [x] narrow module build
- [ ] completed prime--Gamma accretivity proved for zeta
- [ ] RH
