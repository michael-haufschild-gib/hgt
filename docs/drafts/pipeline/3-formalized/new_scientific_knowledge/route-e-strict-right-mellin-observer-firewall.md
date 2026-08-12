# Route E strict-right Mellin observer firewall

- **ID:** `ROUTE-E-STRICT-RIGHT-MELLIN-OBSERVER-FIREWALL-001`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / EXACT NO-GO / PHASE-INVARIANT POSITIVE SURVIVOR
- **Scientific status:** `[LEAN-PROVED] [BRIDGE] [NO-GO] [NOVELTY UNVERIFIED] [NOT RH]`
- **Parent:** `../../2-fully-proven/new_scientific_knowledge/route-e-critical-antiscale-diffuse-codiagonal-transfer-law.md`
- **Route:** E
- **RH used:** no
- **Computation used:** no
- **Literature used:** no; internal-corpus proof under current directive

## Result

This card closes Theorem G's two missing formal statements.

For `1<sigma`, the graph-normal Gamma--Xi coordinate uses

\[
 s=\sigma+u(\sigma-1).
\]

Lean proves the exact half-line equation

\[
 \Re s=\frac12
 \quad\Longleftrightarrow\quad
 \Re u=\frac{1/2-\sigma}{\sigma-1}<0.
\]

Hence no inward node `0<=re u` reaches the Mellin half-line.

For a scalar observer at spectral parameter `s`, define its forced squared-magnitude profile

\[
 a_{\sigma,s}(n)=
 \begin{cases}
 \mathcal Z_\sigma n^{\sigma-2\Re s},&n\text{ squarefree},\\
 0,&\text{otherwise}.
 \end{cases}
\]

Lean proves the stronger phase-blind divergence range

\[
 \Re s\le\frac\sigma2
 \quad\Longrightarrow\quad
 \sum_n a_{\sigma,s}(n)=\infty.
\]

At `Re s=1/2`, this is exactly Equation (46):

\[
 a_{\sigma,s}(n)=\mathcal Z_\sigma n^{\sigma-1}
 \qquad(n\text{ squarefree}).
\]

More strongly, for every complex sequence `v`,

\[
 \bigl(\forall n,\ |v_n|^2=a_{\sigma,s}(n)\bigr)
 \quad\Longrightarrow\quad
 v\notin\ell^2.
\]

Thus no oscillatory phase choice can repair the scalar observer, and no vector in the countable
Hilbert carrier realizes the half-line norm profile.

## Proof

The affine real-part identity is elementary because `sigma-1` is positive and real. Solving
`sigma+(sigma-1) re u=1/2` gives the displayed quotient, whose numerator is negative.

For divergence, suppose the nonnegative norm-square profile were summable. Its terms would tend
to zero. Let `Z=squarefreeMobiusTotal sigma>0`. Eventual convergence gives an index `N` after
which every term is strictly below `Z`. Choose a prime `p>=N`. It is squarefree. If
`Re s<=sigma/2`, then `sigma-2 Re s>=0`, and

\[
 p^{\sigma-2\Re s}\ge1,
 \qquad a_{\sigma,s}(p)\ge Z,
\]

contradicting the eventual strict upper bound. The standard `Memℓp` square-summability
equivalence makes this contradiction independent of coefficient phases.

## No-go closure

- **Exact killing theorem/mechanism:** the safe graph-normal map is defined on inward nodes, but
  the half-line forces an outward node; independently, its scalar observer has a cofinal prime
  subsequence with squared magnitude bounded below by positive `Z_sigma`.
- **Strongest positive survivor:** complete boundary classification of the node real part and
  phase-invariant non-`ℓ²` theorem throughout `Re s<=sigma/2`.
- **New insight:** divergence is not caused by a poor branch or phase convention. It is forced by
  the magnitude profile on cofinally many squarefree prime coordinates. Any repair must change
  carrier or use a finite physical codiagonal; analytic phase retuning cannot help.
- **Status:** paper proof dependency-closed; exact theorem formalized in the module below.

## Lean certificate

Module:

```text
GaloisForLFunctions.RHTower.RouteEStrictRightMellinObserverFirewall
```

Principal declarations:

```text
routeEMellinObserverNormSqProfile
routeEMellinObserverNormSqProfile_halfLine
routeEMellinAffineRealPart_eq_half_iff
routeEMellinHalfLine_forces_outward_node
routeEMellinHalfLine_ne_of_inward_node
routeEMellinObserverNormSqProfile_nonneg
not_summable_routeEMellinObserverNormSqProfile
not_summable_routeEMellinHalfLineObserverNormSqProfile
routeEMellinHalfLineObserver_not_memℓp
no_routeEMellinHalfLineObserver_in_l2
routeEStrictRightMellinObserverFirewall
```

Module is imported by `GaloisForLFunctions.RHTower`. No `sorry`, `admit`, new `axiom`, `opaque`,
`unsafe`, numerical computation, RH premise, or Route E endpoint premise occurs.

## Frontier consequence

Theorem G is no longer a paper-only firewall. Strict-right graph normalization and the half-line
scalar observer are closed formal no-gos. They do not prove the finite physical column-ANOVA
estimate or signed recurrence seam. Those remain Route E's exact arithmetic core.

## Novelty status

No external priority claim is made. Internal formal strengthening is phase invariance and the
full elementary divergence range `Re s<=sigma/2`, rather than the single half-line instance.

## Log

- 2026-08-12 — Exact node boundary, squarefree norm-profile divergence, phase-independent
  non-`ℓ²`, and no-Hilbert-observer capstone formalized; umbrella import added.
