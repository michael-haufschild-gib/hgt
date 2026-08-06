# Route E Gibbs antiscale Mellin resonance law

- **ID:** `ROUTE-E-GIBBS-ANTISCALE-MELLIN-RESONANCE-001`
- **Stage:** 3-formalized
- **Type:** `[THEOREM]` / `[NO-GO INFRASTRUCTURE]` / `[POSITIVE SURVIVOR]`
- **RH used:** no
- **Computation used:** no
- **External audit:** intentionally omitted under current instruction; no priority claim permitted
- **Lean:** `formal/GaloisForLFunctions/RHTower/GibbsCriticalDissipationAntiscaleResonance.lean`

## Formalized theorem package

For every finite positive dilation alphabet `S`, real activity `z`, and `Re(s)>0`, actual finite
Gibbs source has exact Mellin factorization

\[
 \int_0^\infty x^{s-1}P_S(z,x)\,dx
 =\Gamma(s)\prod_{p\in S}(1+zp^{-s}).
\]

At parity `z=-1` and `s=r+it`, its Euler factors are exactly

\[
 1-p^{-r}e^{-it\log p}.
\]

Their Euler-baseline-normalized squared modulus is

\[
 R_{r,t}(p)=\frac{1+p^{-2r}-2p^{-r}\cos(t\log p)}{1+p^{-r}}.
\]

If `cos(t log p)\le-2/3`, then

\[
 R_{r,t}(p)\ge1+p^{-r}/6.
\]

For `y\ge81`, every prime in `(y/3,y]` satisfies that chamber at `t=pi/log y`, giving exact finite
block bound

\[
 \prod_{y/3<p\le y}R_{r,\pi/\log y}(p)
 \ge (1+y^{-r}/6)^{\#\{p:y/3<p\le y\}}.
\]

Pointwise same-sign dissipation also has exact null-space classification

\[
 \mathcal D_{S,p}(x)=0\iff\psi_S(px)=-\psi_S(x).
\]

These results prove terminal antiscale coherence is realized by actual Gibbs Mellin source, not
only an abstract dilation model. Combined with paper-level Cauchy reporter inequality and
earlier-prime budget, they drive
`route-e-critical-dissipation-saturation-antiscale-resonance-no-go.md`.

## Lean declarations

- `gibbsSameSignDissipation_eq_zero_iff_antiscale`
- `gibbsMellinTransform`
- `mellinConvergent_gibbsDiag`
- `gibbsMellinTransform_eq_gamma_eulerProduct`
- `gibbsCriticalAntiscaleFactor_eq_cpow`
- `gibbsParityMellinTransform_eq_gamma_antiscaleProduct`
- `normSq_gibbsParityMellinTransform_eq_gamma_mul_antiscaleProduct`
- `normSq_gibbsCriticalAntiscaleFactor`
- `gibbsCriticalNormalizedReporterFactor_universal_lower`
- `gibbsCriticalPrimeWindow_cos_le_neg_two_thirds`
- `gibbsCriticalPrimeWindow_normalizedReporterProduct_lower`

## Verification

- Direct `lake env lean` passes without warnings.
- Targeted `lake build GaloisForLFunctions.RHTower.GibbsCriticalDissipationAntiscaleResonance`
  passes `8859/8859`; no full or umbrella build run.
- Capstone axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`.
- Umbrella import wired in `GaloisForLFunctions/RHTower.lean`.
- No `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration in module.

## Exact boundary

Lean module certifies finite source identities and terminal normalized gain. Cofinal divergence of
full natural-aperture residual energy is paper-proved on failed-route card; its Cauchy integral and
asymptotic earlier-prime comparison are not yet encoded in Lean. No RH conclusion is claimed.
