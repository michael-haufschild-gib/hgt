# Real orientation-twisted Hodge apex

- **ID:** `deninger-real-orientation-twisted-hodge-apex`
- **Stage:** 3-formalized
- **Type:** SOURCE REAL-BOUNDARY HODGE THEOREM
- **Labels:** `DAC_REAL_ORIENTATION_TWISTED_HODGE_APEX`,
  `DAC_REAL_APEX_RELATIVE_ENDPOINT`
- **Parent:** `deninger-poisson-hodge-polarization`
- **Statement:** the real-place quotient of the Hermitian radial leaf
  carries the required odd positive Hodge operator only after the
  canonical orientation-sign twist; its fixed apex realizes the
  degree-zero restriction and its relative Kähler trace realizes the
  degree-two endpoint.

## 1. Oriented double cover

Let
\[
 \widetilde L=\mathbb C,\qquad z=X+iY,\qquad
 \omega=dX\wedge dY,
\]
with involution
\[
 c_{\mathbb R}(z)=\overline z                                  \tag{1}
\]
and half-density flow
\[
 s_t(z)=e^{t/2}z.                                               \tag{2}
\]
The quotient \(L_{\mathbb R}=\widetilde L/\langle
c_{\mathbb R}\rangle\) is the real-place leaf germ.  Its apex is the
fixed point \(z=0\).

Complex conjugation reverses the leaf orientation:
\[
 c_{\mathbb R}^*\omega=-\omega.                                \tag{3}
\]
Let \(\mathfrak o_{\mathbb R}\) be the sign local system on the
quotient.  Smooth forms downstairs with values in
\(\mathfrak o_{\mathbb R}\) are the anti-invariant forms upstairs.

## 2. Twisted Hodge descent

On the oriented cover put
\[
 *dX=dY,\qquad *dY=-dX.                                        \tag{4}
\]
Then
\[
 c_{\mathbb R}^**=-*c_{\mathbb R}^*.                           \tag{5}
\]
Consequently \(*\) exchanges invariant and anti-invariant
one-forms:
\[
 *:
 \Omega^1(L_{\mathbb R})
 \rightleftarrows
 \Omega^1(L_{\mathbb R};\mathfrak o_{\mathbb R}).              \tag{6}
\]

`[PROVED HERE] [DAC_REAL_ORIENTATION_TWISTED_HODGE_APEX]`

On the complexified direct sum
\[
 E_{\mathbb R}^1
 =
 \Omega^1(L_{\mathbb R};\mathbb C)
 \oplus
 \Omega^1(L_{\mathbb R};
          \mathfrak o_{\mathbb R}\otimes\mathbb C),             \tag{7}
\]
coefficient conjugation followed by `(6)` defines a parallel
anti-linear operator
\[
 J=*c,\qquad J^2=-1.                                           \tag{8}
\]
The wedge pairing between the two summands is alternating and
\[
 \alpha\wedge J\alpha
 =
 \alpha\wedge *\overline\alpha                                \tag{9}
\]
is a strictly positive orientation density for every nonzero
one-form \(\alpha\).  The flow commutes with \(J\) and satisfies
\[
 s_t^*\omega=e^t\omega.                                       \tag{10}
\]

### Proof

Equation `(5)` is checked on the coframe:
\[
\begin{aligned}
 c_{\mathbb R}^**dX
   &=c_{\mathbb R}^*dY=-dY
    =-*c_{\mathbb R}^*dX,\\
 c_{\mathbb R}^**dY
   &=c_{\mathbb R}^*(-dX)=-dX
    =-*c_{\mathbb R}^*dY.
\end{aligned}
\]
This proves `(6)`.  The real star commutes with coefficient
conjugation and has square \(-1\), proving `(8)`.  Formula `(9)` is
the ordinary positive Hermitian energy on the oriented double cover;
the sign in `(3)` is canceled by the orientation local system, so it
descends as a positive density.  Finally `(2)` multiplies both
\(dX\) and \(dY\) by \(e^{t/2}\), proving `(10)` and flow
naturality.

The twist is forced.  Without
\(\mathfrak o_{\mathbb R}\), `(5)` prevents the Hodge star from
descending as an endomorphism on the quotient.

## 3. Relative endpoint

For an even Schwartz function \(f\), set
\[
 Rf(z)=f(|z|^2).
\]
It is \(c_{\mathbb R}\)-invariant and
\[
 Rf(0)=f(0).                                                    \tag{11}
\]
Integration over the real quotient is half the integral over the
oriented double cover:
\[
 \int_{L_{\mathbb R}}Rf\,|\omega|
 =
 \frac{\pi}{2}\int_0^\infty f(x)\,dx
 =
 \frac{\pi}{4}\mathcal Ff(0).                                  \tag{12}
\]

`[PROVED HERE] [DAC_REAL_APEX_RELATIVE_ENDPOINT]`

Thus the two Meyer relative conditions are exactly:

1. vanishing at the real fixed apex;
2. vanishing of the orientation-twisted leaf trace.

The nonzero scalar in `(12)` depends only on whether one integrates
on the double cover or quotient and has no effect on the kernel.

## 4. Arithmetic gluing

The real Kummer boundary
`DAC_REAL_KUMMER_ARAKELOV_BOUNDARY` supplies the real
orientation/Tate line at the source endpoint.  Equations
`(3)`--`(9)` identify its geometric origin: it is the orientation
sign needed for Hodge descent through the real involution, not an
extra untwisted real coefficient.

The Kähler apex restriction and trace agree with
`DAC_RADIAL_KAHLER_ENDPOINT_FOURIER_TRACE` on the oriented double
cover.  Their common kernel is \(H_\cap\).  Hence the real chart
extends the local source Hodge complex and preserves the already
constructed Poisson domain.

## Boundary of the theorem

This theorem closes local real-place Hodge descent, apex restriction,
and trace.  It does not by itself derive the full
\(\Gamma_{\mathbb R}\) fixed-point distribution, construct a global
harmonic projection, or prove faithfulness on \(M_\zeta\).  Those are
separate trace and comparison theorems.

The coordinate \(z\) here is leaf-tangent. It is not Deninger's
transverse real Rees coordinate. In
`DAC_REAL_STATIONARY_KAHLER_CONORMAL_PRODUCT_GERM`, the present flow
\(z\mapsto e^{t/2}z\) is paired with an independent square-root normal
\(r\mapsto e^{-t}r\), so the orbifold normal \(x=r^2\) has the required
archimedean law \(x\mapsto e^{-2t}x\).

## Hostile audit

- Orientation reversal is retained rather than silently discarded.
- Hodge star does not descend untwisted; sign local system is
  load-bearing.
- Positivity is proved on source differential forms before spectral
  decomposition.
- Endpoint scalar normalization is explicit and nonzero.
- No zeta zero, RH premise, CCM object, or numerical computation is
  used.

## References

- Christopher Deninger, *Dynamical systems for arithmetic schemes*,
  archimedean compactification in §8 and suspension in §12:
  https://arxiv.org/abs/1807.06400.
- `DAC_DENINGER_HERMITIAN_RADIAL_LINE_POISSON_HODGE`.
- `DAC_REAL_KUMMER_ARAKELOV_BOUNDARY`.
- `DAC_RADIAL_KAHLER_ENDPOINT_FOURIER_TRACE`.

## Log

- 2026-07-27 — Proved orientation-sign Hodge descent at the real
  quotient, positive odd parity, fixed-apex restriction, and relative
  Kähler trace.

- 2026-08-01 — Formalized the orientation-sign descent, the odd positive Hodge
  operator, the forced twist, and the relative apex/trace endpoint in Lean,
  including the quotient-versus-cover halving and Schwartz integrability.

## Lean status

### Both labelled theorems landed

`formal/GaloisForLFunctions/RHTower/Deninger/DeningerRealApexEndpoint.lean` (new), on top of
`DeningerLeafwiseKahler.lean`, `DeningerStationaryKahlerGerm.lean` and
`DeningerRadialKahlerTrace.lean`.  Axiom audit for all 19 new declarations:
`propext, Classical.choice, Quot.sound`.

`DAC_REAL_ORIENTATION_TWISTED_HODGE_APEX`:

- `(1)`, `(2)` — the involution `deningerGermSigma` (restricted to the leaf,
  `deningerGermSigma_leaf`, it is `z ↦ conj z`) and the half-density flow, whose leaf action is
  `deningerGermFlow_leafBlock` : multiplication by `e^{t/2}`.  The apex is the fixed point,
  `deningerGermSigma_fixed_iff` and `deningerGermFlow_apex`.
- `(3)` — `deningerGermSigmaOne_wedge` : `c_ℝ^*ω = -ω`, where `deningerGermSigmaOne` is the
  induced action on one-forms.
- `(4)` — `deningerLeafStar`, with `deningerLeafStar_du`, `deningerLeafStar_dv`.
- `(5)` — `deningerGermSigmaOne_star` : `c_ℝ^* ⋆ = -⋆ c_ℝ^*`.
- `(6)` — `deningerGermStar_of_invariant` and `deningerGermStar_of_antiInvariant` : the star
  carries invariant one-forms to anti-invariant ones and back, i.e. it exchanges
  `Ω¹(L_ℝ)` with `Ω¹(L_ℝ; o_ℝ)`.
- **The twist is forced** — `deningerRealTwist_forced` : an invariant one-form whose star is again
  invariant is zero, so the star admits no untwisted descent as an endomorphism.  This is the
  contentful form of the card's closing paragraph of §2.
- `(7)`, `(8)` — `deningerGermJ` on the complexified direct sum, with `deningerGermJ_sq` :
  `J² = -1`.
- `(9)` — `deningerGermJ_pos` : the cup trace of `α` against `Jα` is
  `‖Re α‖² + ‖Im α‖²`, and `deningerGermJ_pos_of_ne` : it is strictly positive for `α ≠ 0`.
  The one-form version on the cover is `deningerLeafWedge_star_pos`.
- `(10)` — `deningerGermKahler_weight` (equivalently `deningerLeafFlow_wedge`) : `s_t^*ω = e^{t}ω`;
  flow naturality is `deningerGermJ_flow_comm`, the flow acting on one-forms by the real scalar
  `e^{t/2}`, which commutes with `J` by `deningerGermJ_smul`.

`DAC_REAL_APEX_RELATIVE_ENDPOINT`:

- `(11)` — `deningerRealApex_restriction` : the radial lift restricted to the apex is `f(0)`.
- `(12)` — the quotient statement, which is what this card adds over the double cover:
  `deningerRealChart` is the closed upper half plane, a fundamental domain of the involution;
  `deningerConj_measurePreserving` (conjugation is a linear isometry, hence volume preserving),
  `deningerRealAxis_volume_zero` (its fixed axis is a proper real subspace, hence null),
  `deningerConj_setIntegral` (the two open half planes carry the same integral of a
  conjugation-invariant integrand) and `deningerRealChart_half` : **integration over the real
  quotient is exactly half the integral over the oriented double cover**.  Applied to the radial
  lift, `deningerRealApex_trace` gives `∫_{L_ℝ} Rf = (π/2)∫_0^∞ f` and
  `deningerRealApex_trace_fourier` gives `= (π/4) 𝓕f(0)`.
- **The two Meyer relative conditions** — `deningerRealApexEndpoint_iff` : vanishing at the real
  fixed apex together with vanishing of the orientation-twisted leaf trace is equivalent to
  `f(0) = 0` and `𝓕f(0) = 0`.  The proof isolates the nonzero scalar `π/4`, which is the card's
  claim that the normalization has no effect on the kernel.
- **Even Schwartz functions** — `deningerRadialLift_integrable` : the radial lift of a Schwartz
  function is integrable on the leaf.  This is new infrastructure (mathlib has no integrability
  transfer for polar coordinates): the zeroth and second decay estimates give the bound
  `‖Rf(z)‖ ≤ 8(C₀+C₂)(1+‖z‖)^{-3}`, integrable on a real plane by the Japanese-bracket estimate
  since `3 > 2 = dim_ℝ ℂ`.  `deningerRealApexEndpoint_schwartz` is the resulting hypothesis-free
  statement for even Schwartz functions.

### Remaining

Nothing for this theorem.  The three items named in the card's boundary section — the full
`Γ_ℝ` fixed-point distribution, a global harmonic projection, and faithfulness on `M_ζ` — are
separate trace and comparison theorems and stay open.
