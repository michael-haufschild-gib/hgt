# CLG/TTF: direct all-polynomial source-sign attempt

**Status:** sign open. The identities below are paper derivations from the existing source
calculus, not new Lean theorems or a proof of RH. No numerical experiment is required for them.

**Full chain:** literal theta source → every signed center-mixed Hankel form nonnegative →
Fourier-current sign → Xi Bezoutian orientation → RH.

The target is every polynomial at every critical aperture, not another fixed-rank determinant.
The finite coefficient queue and single-flux numerical probe do not discharge this target.

## Exact normalization and cancellation

Write `Φ = thetaCuspFullSource`, `ψ_a(x) = exp(ax) Φ(x)`, `M = -i d/dx`, and
`p(z) = Σ_i v_i z^i` with real coefficients. Put `r(z)=p(2z)` and
`f_a=r(M)ψ_a`. Throughout, `0<a<1/2` and inner products mean
`⟨f,g⟩=∫ conjugate(f) g` on the full real line.

The existing `ThetaCuspTiltedSchwartz` supplies these finite differential filters in Schwartz
space. `HedenmalmAutocorrelationPath` identifies the actual mixed density with the aperture
derivative of the tilted autocorrelation. With the plus-tilt convention used here, evenness gives

```
C_a(t) = ∫ exp(2ax) Φ(x+t) Φ(x-t) dx,
∂_a C_a(t) = ∫_(r>0) r sinh(ar) Φ(r/2+t) Φ(r/2-t) dr.
```

The factor two in `r(z)=p(2z)` retains the exact scale in
`ThetaCuspCenterMixedSignedJetCompleteness`: `m_n=2π·2^(-n)·s_n`.
Consequently, for the actual signed Hankel quadratic form `Q_a(v)`, Plancherel gives

```
Q_a(v) = d/da ||f_a||² = 2 ∫ x |f_a(x)|² dx.                 (1)
```

The second equality needs a cancellation, not a discarded term:
`∂_a f_a = x f_a - i r'(M)ψ_a`, and
`⟨r(M)ψ_a,r'(M)ψ_a⟩` is real because both Fourier multipliers are real.
Its contribution to the real energy derivative is therefore zero. This argument uses real
polynomial coefficients; it must not be asserted for arbitrary complex filters without adjustment.

Differentiation under the integral uses a compact aperture neighborhood inside `|a|<1` and the
finite derivative bounds in `ThetaCuspTiltedSchwartz`; no all-degree uniform domination is claimed.

## Attempt to produce the sign from the full source

Choose any fixed `c>0` and retain the exact Gaussian residual

```
h_c = -Φ' - c x Φ,
g_a = r(M)(exp(ax) h_c).
```

All terms are Schwartz: `exp(ax)h_c=(a-cx)ψ_a-ψ_a'`. Applying the filter to this identity yields

```
∂_x f_a = (a-cx)f_a + i c r'(M)ψ_a - g_a.
```

Integration by parts gives `Re⟨f_a,∂_x f_a⟩=0`; the same real-multiplier cancellation removes the
`i c` term. Thus the exact all-degree identity is

```
(c/2) Q_a(v) = a ||f_a||² - Re⟨f_a,g_a⟩.                    (2)
```

For a Gaussian source the residual vanishes and this supplies the sign at every degree.
For the literal theta source the remaining obligation is precisely

```
Re⟨r(M)ψ_a, r(M)(exp(ax)(-Φ'-cxΦ))⟩ ≤ a ||r(M)ψ_a||²       (3)
```

for every real polynomial and every critical aperture. Equation (3) is an unresolved
source-specific comparison, not an extra premise that may be inserted into a final RH theorem.
Changing `c` only rearranges the exact identity; it does not prove the comparison.

## Where the attempted estimate fails

The ordinary Cauchy–Schwarz bound loses the required cancellation already at zero aperture.
Here `Φ` is even, `h_c` is odd, and `Re⟨r(M)Φ,r(M)h_c⟩=0`. For the constant filter,
however, `||Φ|| ||h_c||` is strictly positive: `h_c=0` would make Φ Gaussian, inconsistent
with its positive value and proved `C exp(9x/2-π exp(2x))` upper tail envelope. By continuity this
absolute-norm estimate cannot be bounded by `a||ψ_a||²` for all sufficiently small positive `a`.
This rejects that estimate, not the exact signed comparison (3).

The modular drift and energy bounds in `ThetaCuspModularEnergyBounds` control the source orbit.
They do not currently bound (3). In a logarithmic-derivative approach, putting
`W=-Φ'/Φ-cx` introduces `[r(M),[r(M),W]]`; its differential expansion contains derivatives
of W through order `2 deg(r)`. Bounds at a fixed derivative order cannot silently discharge
the universal polynomial quantifier. No sign-preserving all-order estimate for this term has
been derived from the modular system.

The unresolved work is a phase-sensitive estimate for (3), retaining its cancellation at `a=0`
and controlling every polynomial degree. Ordinary source norm positivity, a finite collection
of coefficient identities, and fixed-order tail asymptotics do not supply that estimate.

**Progress assessment:** this attempt identifies the exact term left by a direct all-order
sign argument and rejects an inadequate bound. It does not reduce the proved RH sign gap.
No new Lean module, axiom audit, build, or computation is justified by these identities alone.
