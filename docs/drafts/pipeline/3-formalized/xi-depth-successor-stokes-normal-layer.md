# Xi depth-successor Stokes normal layer

- **ID:** `xi-depth-successor-stokes-normal-layer`
- **Stage:** 3-formalized
- **Paper proof:**
  `../2-fully-proven/new_scientific_knowledge/xi-depth-successor-stokes-normal-layer.md`
- **Lean module:**
  `formal/GaloisForLFunctions/RHTower/XiDepthSuccessorStokesNormalLayer.lean`
- **Status:** `[LEAN-FORMALIZED] [UNCONDITIONAL] [NOT RH]`

## Formalized result

For every analytic carrier with local factorization
\[
 f(u)=(u-\rho)^m g(u),\qquad g(\rho)\ne0,
\]
Lean proves
\[
 \frac{f(\rho+\varepsilon z)}
 {f((1+\varepsilon)(\rho+\varepsilon z))}
 \longrightarrow
 \left(\frac{z}{z+\rho}\right)^m
\]
through the punctured complex neighborhood of \(\varepsilon=0\). The centered version replaces
\(\rho\) by \(\rho-c\).

Lean also constructs literal lower- and upper-endpoint depth steps and proves their half-aperture
composition
\[
 u\longmapsto
 1-(1+\varepsilon/2)\bigl(1-(1+\varepsilon/2)u\bigr)
\]
has same centered moving-zero layer. Specializing to Xi gives exact balanced normal layer
\[
 \left(
 \frac{z}{z+\rho-\tfrac12}
 \right)^{m_\rho},
\qquad
 m_\rho=(\operatorname{ord}_\rho\Xi)>0.
\]
The module also proves denominator identity retaining multiplicity, outer matching law
\[
 w^{-1}\bigl(P_{\rho-\frac12,m_\rho}(w^{-1})-1\bigr)
 \longrightarrow -m_\rho(\rho-\tfrac12),
\]
and conditional nearby-pole consumer: equality of source-inverse and analytic-adjoint pole
coordinates forces \(\Re\rho=\tfrac12\).

## Boundary

This does not construct the source-derived same-fibre dagger equality. Remaining theorem is the
strict nonzero landing of this balanced profile in the literal Gamma/co-Poisson/Sonin Bockstein.

## Verification

- [x] direct `lake env lean` check
- [x] targeted module build
- [x] axiom audit
- [ ] source-normal Burnol landing
- [ ] RH
