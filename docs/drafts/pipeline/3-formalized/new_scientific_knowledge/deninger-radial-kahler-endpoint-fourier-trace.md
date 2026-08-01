# Meyer endpoint conditions are Kähler apex restriction and leaf trace

- **ID:** `deninger-radial-kahler-endpoint-fourier-trace`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Labels:** `DAC_RADIAL_KAHLER_ENDPOINT_FOURIER_TRACE`,
  `DAC_Meyer_HCAP_GEOMETRIC_ENDPOINT_IDENTIFICATION`
- **Parent:** `deninger-hilbert-kummer-kahler-orbit-trivialization`
- **Statement:** on the canonical complex leaf, Meyer's two
  codimension-one endpoint functionals are exactly restriction to the
  cone apex and the leafwise Kähler trace.

## Setup

Use Meyer's Fourier convention
\[
 \mathcal Ff(y)=\int_{\mathbb R}f(x)e^{2\pi ixy}\,dx.           \tag{1}
\]
For an even Schwartz function \(f\in\mathcal S(\mathbb R)\), define
its radial Kähler lift
\[
 Rf(z)=f(|z|^2),\qquad z\in\mathbb C.                          \tag{2}
\]
Write \(\omega=du\wedge dv\) for standard Kähler area.

## Theorem

`[PROVED HERE] [DAC_RADIAL_KAHLER_ENDPOINT_FOURIER_TRACE]`

For every even \(f\in\mathcal S(\mathbb R)\),
\[
\begin{aligned}
 Rf(0)&=f(0),                                                   \tag{3}\\
 \int_{\mathbb C}Rf\,\omega
   &=\pi\int_0^\infty f(x)\,dx
    =\frac{\pi}{2}\mathcal Ff(0).                              \tag{4}
\end{aligned}
\]
Consequently Meyer's domain
\[
 H_\cap
 =
 \{f\in\mathcal S(\mathbb R):
       f\ {\rm even},\ f(0)=\mathcal Ff(0)=0\}                 \tag{5}
\]
is identified by `(2)` with radial Schwartz data satisfying
\[
  Rf|_{z=0}=0,\qquad
  \operatorname{Tr}_{\rm leaf}(Rf)
    :=\int_{\mathbb C}Rf\,\omega=0.                            \tag{6}
\]

### Proof

Equation `(3)` is immediate.  In polar coordinates
\(z=\rho e^{i\theta}\),
\[
 \omega=\rho\,d\rho\,d\theta.
\]
With \(x=\rho^2\), so \(\rho\,d\rho=\tfrac12dx\),
\[
\begin{aligned}
 \int_{\mathbb C} f(|z|^2)\,\omega
 &=\int_0^{2\pi}\int_0^\infty
      f(\rho^2)\rho\,d\rho\,d\theta\\
 &=\pi\int_0^\infty f(x)\,dx.
\end{aligned}
\]
Equation `(1)` at \(y=0\), followed by evenness, gives
\[
 \mathcal Ff(0)
 =\int_{\mathbb R}f(x)\,dx
 =2\int_0^\infty f(x)\,dx.
\]
This proves `(4)`, and `(5)` is therefore equivalent to `(6)`.

## Arithmetic interpretation

The two endpoint maps now have source-geometric meanings before zeta
or Mellin transformation:

1. \(f(0)\) is restriction of the radial \(0\)-cochain to the collapsed
   half-density circle at the cone apex.
2. \(\mathcal Ff(0)\) is, up to the fixed nonzero normalization
   \(2/\pi\), integration against the leafwise Kähler fundamental
   class.

Thus no second ad hoc “Fourier boundary point” is required.  The
second condition is the top-degree arithmetic trace.  This matches the
three-term cohomological amplitude:
\[
 H^0=\mathbb C,\qquad H^1=M_\zeta,\qquad H^2=\mathbb C(-1).
\]
The two endpoint lines are restriction in degree zero and trace in
degree two; their common kernel is the relative middle domain.

On the global positive-radius refinement
\(\Sigma_{\rm HK}\times\mathbb C^\times\), adjoining
\(\Sigma_{\rm HK}\times\{0\}\) gives the source cone apex.  After the
already-proved angular/invariant reduction, the degree-zero restriction
and degree-two trace are independent of the transverse representative.
What remains is to prove this attachment and trace are strict in the
mixed \(L^1/L^2\), residue, and nuclear sheaf topologies.

## Consequence for the Poisson comparison

The geometric comparison no longer needs to conjecture the shape of
the Poisson domain.  Its radial degree-zero source is forced to be the
closed relative subspace `(6)`, which is exactly \(H_\cap\).
Together with
`DAC_DENINGER_FLOW_POISSON_DILATION`, the interior differential is
\[
 f\longmapsto\sum_{n\ge1}f(n\,\cdot)=Zf.
\]
Remaining comparison work is strict sheafification, closed-range
identification with Meyer's \(H_-\), cup/trace compatibility on the
quotient, and harmonic faithfulness.

## Hostile audit

- Equation `(4)` uses additive Kähler area \(dx\), not multiplicative
  Haar measure \(dx/x\).  This is precisely Meyer's critical
  \(L^2_{1/2}\) measure.
- Vanishing of the Kähler trace is equivalent to
  \(\mathcal Ff(0)=0\) only because the source functions are even.
- The apex attachment does not identify Deninger's uncompactified
  unitary locus \(r(P)=0\) with \(u\to0\).
- Endpoint identification does not prove the strict Poisson
  quasi-isomorphism or Hodge positivity on \(M_\zeta\).

## References

- Ralf Meyer, *A spectral interpretation for the zeros of the Riemann
  zeta function*, arXiv:math/0412277, equations defining the Fourier
  transform, Poisson summation, and \(H_\cap\).
- Christopher Deninger and Wilhelm Singhof,
  *Real polarizable Hodge structures arising from foliations*,
  arXiv:math/0204111.

## Log

- 2026-07-27 — Identified both Meyer endpoint functionals directly on
  the canonical radial Kähler leaf.

## Lean status

### The whole theorem landed

`formal/GaloisForLFunctions/RHTower/DeningerRadialKahlerTrace.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

- `deningerRadialLift f z = f (‖z‖²)` — the radial Kähler lift `(2)`.
- `deningerRadialLift_zero` — **`(3)`**: the lift at the cone apex is `f(0)`.
- `deningerAngularIntegral_complex`, `deningerRadialSquareSubstitution_complex`,
  `deningerPolarTrace` — **the polar reduction**: `∫_ℂ F(‖z‖²) ω = π ∫_0^∞ F(x) dx`, from the
  polar change of variables (`ω = ρ dρ dθ`), the angular measure `2π`, and the substitution
  `x = ρ²` with `ρ dρ = dx/2`.  This is the additive Kähler area `dx`, not multiplicative Haar.
- `deningerRadialKahler_trace` — **the first half of `(4)`**: `∫_ℂ Rf ω = π ∫_0^∞ f`.
- `deningerMeyerFourier` with `deningerMeyerFourier_zero` — Meyer's convention `(1)` and its value
  at the origin, the total integral.
- `deningerEven_integral` — for an even integrable function the total integral is twice the ray
  integral, by reflecting the left half line.
- `deningerRadialKahler_trace_fourier` — **`(4)`**: `∫_ℂ Rf ω = (π/2) ℱf(0)`.
- `deningerMeyerEndpoint_iff`, `deningerMeyerEndpoint_schwartz` — **`(5)` ↔ `(6)`**: for an even
  integrable (in particular even Schwartz) function, `f(0) = ℱf(0) = 0` holds exactly when the
  lift vanishes at the apex and has vanishing leafwise Kähler trace.  Evenness is used exactly
  once, in the reflection, matching the card's hostile-audit note.

The polar reduction is the general form of the squared-modulus identity of
`DAC_DENINGER_HERMITIAN_RADIAL_LINE_POISSON_HODGE`; that card's `deningerCriticalMeasure` is now
derived from `deningerPolarTrace` rather than proved separately.

### Remaining

Nothing.  Every displayed equation of the theorem — `(1)`–`(6)` — is formalized unconditionally.
The card's own open items (strictness in the mixed `L¹/L²`, residue and nuclear topologies, the
apex attachment, the Poisson quasi-isomorphism) are explicitly outside the theorem.
