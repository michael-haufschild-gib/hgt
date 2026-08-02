# Xi depth / Möbius--Gamma outer-inner weld

- **ID:** `xi-depth-mobius-gamma-outer-inner-weld`
- **Stage:** 3-formalized
- **Type:** EXACT SOURCE-GRAPH / DIVISOR-NORMAL MATCHING LAW
- **Scientific status:** `[LEAN-FORMALIZED] [CORPUS-NEW SYNTHESIS]`
  `[NO EXTERNAL NOVELTY CLAIM] [NOT RH]`
- **Formal module:**
  `formal/GaloisForLFunctions/RHTower/XiDepthMobiusGammaOuterInnerWeld.lean`
- **Parents:**
  - `new_scientific_knowledge/other/xi-depth-successor-stokes-normal-layer.md`;
  - `mobius-gamma-xi-ward-julia-transport.md`;
  - `xi-source-normal-cone-divisor-conservation.md`.

## Theorem

Let
\[
 s=\sigma+u\varepsilon,\qquad \Re\sigma>1,\qquad \Re s>1,
\]
and let \(\mathfrak G_{\sigma,\varepsilon}\) be the singular Möbius--Gamma graph applied to its
actual squarefree Fisher score. After its strict-right correction, the coefficient-two output is
\[
 \mathcal G_\Xi(s)=-2\,\frac{\Xi'(s)}{\Xi(s)}.
\]
The balanced Euler vector field gives
\[
 \boxed{\quad
 -\left(s-\frac12\right)\frac{\Xi'(s)}{\Xi(s)}
 =
 \frac{s-\frac12}{2}
 \left(
 \mathfrak G_{\sigma,\varepsilon}(u)
 +4A(2s)
 \right).
 \quad}
\tag{1}
\]
Thus actual squarefree source graph reconstructs outer connection of two-endpoint balanced depth
transport, including exact normalization.

At any \(\rho\), set
\[
 m_\rho=(\operatorname{analyticOrderAt}\Xi,\rho)_{\mathbb N},
 \qquad a_\rho=\rho-\frac12.
\]
Then inner rational nearby chart and outer continued affine current carry same charge:
\[
 \lim_{w\to0,\ w\ne0}
 w^{-1}\left[
 \left(\frac{w^{-1}}{w^{-1}+a_\rho}\right)^{m_\rho}-1
 \right]
 =-m_\rho a_\rho,
\tag{2}
\]
\[
 \lim_{s\to\rho,\ s\ne\rho}
 (s-\rho)\left[
 -\left(s-\frac12\right)\frac{\Xi'(s)}{\Xi(s)}
 \right]
 =-m_\rho a_\rho.
\tag{3}
\]

Equations `(1)`--`(3)` prove paper’s singular source graph and new two-endpoint nearby profile are
outer and inner charts of one multiplicity-preserving divisor singularity.

## What this changes

Previously open-source graph and nearby profile could have been parallel detectors with coincident
residues. They are now joined by exact source normalization:

```text
actual squarefree Fisher score
  -> singular Möbius--Gamma division
  -> strict-right Xi correction
  -> balanced Euler-vector outer current
  -> same charge as two-endpoint rational nearby layer.
```

Missing RH theorem is no longer source-to-divisor normalization. It is strict same-fibre dagger
landing: prove ordinary-prime Gamma/co-Poisson/Sonin reflection identifies inverse nearby divisor
with analytic adjoint nearby divisor on same nonzero top class.

## Hostile audit

1. `(1)` is proved on safe Euler domain, then outer current has established meromorphic
   continuation. It does not prove source graph remains strict or conormal-faithful across
   continuation.
2. `(2)`--`(3)` hold at off-line zeros too. Charge matching alone is not a selector.
3. Generalized-prime systems can reproduce local nearby profile. Ordinary-prime source specificity
   enters through graph landing, and decisive dagger naturality remains open.
4. Four-unit Ward estimate is not derived. No positivity, contractivity, or orientation slogan is
   being substituted for missing dagger theorem.

## Verification

- [x] direct `lake env lean GaloisForLFunctions/RHTower/XiDepthMobiusGammaOuterInnerWeld.lean`
- [x] targeted `lake build GaloisForLFunctions.RHTower.XiDepthMobiusGammaOuterInnerWeld`
- [x] axiom audit: only `propext`, `Classical.choice`, `Quot.sound`
- [ ] same-fibre dagger landing
- [ ] RH
