# Fixed Xi-shift transport cannot carry the RH Hilbert implication

- **ID:** `xi-shift-ratio-fixed-aperture-rh-no-go`
- **Stage:** 5-failed
- **Type:** TERMINAL RH ROUTE NO-GO / POSITIVE SURVIVOR
- **Scientific status:** `[PAPER-PROVED] [KNOWN SUZUKI PARENT IDENTIFIED] [NOT AN RH PROOF]`
- **Lean sources:** `HTGeometry/SourceLogarithmicBoundary.lean`;
  `RHTower/XiShiftPrimeHypertranscendence.lean`;
  `RHTower/XiUpperEndHypertranscendence.lean`
- **Statement:** The fixed quotient `B_2(s)=xi(s)/xi(s+2)` is an all-valuation-impermeable,
  zero-carrying multiplicative primitive, but its Hardy leakage is already zero unconditionally.
  Consequently no positivity, innerness, or zero-leakage theorem at this one aperture can imply
  RH. The positive survivor is the full transverse shifted-Xi flow, not `B_2`.

## Exact carrier theorem retained

Put

```text
K_layer = C(s)<P(s),P(2s),P(3s),...>_d,
H_2(s) = logDeriv(xi)(s+2)-logDeriv(xi)(s),
B_2(s) = xi(s)/xi(s+2).
```

The paper-closed all-valuation source theorem and the coordinate-field bridge give

```text
H_2 is hypertranscendental over K_layer,
B_2'/B_2 = -H_2,
B_2 is hypertranscendental over K_layer.                    (N1)
```

On `0 < Re(s) < 1`, `xi(s+2)` is nonzero, so `B_2` is analytic and

```text
ord_rho(B_2)=ord_rho(xi).                                  (N2)
```

The exact Euler-side normalization, using the live project convention for `xi`, is

```text
B_2(s)
 = 2*pi*(s-1)/((s+1)*(s+2)) * zeta(s)/zeta(s+2)            (N3)
```

on the Euler half-plane. Its Dirichlet coefficient is

```text
a_2(n)=product_(p|n)(1-p^(-2))
      =sum_(d|n) mu(d)/d^2.                                (N4)
```

Thus `B_2` is the `omega=1` Suzuki shifted-Euler quotient, after the affine recentering of the
spectral variable, with an explicit rational archimedean calibration. Equivalently, `(N4)` is the
`omega=1` shifted Jordan--Euler coefficient divided by `n`.

## Why the proposed RH arrow fails

Suzuki's shifted quotient is

```text
Theta_omega(z)
 = xi(1/2-omega-i*z)/xi(1/2+omega-i*z).
```

With `s=-1/2-i*z`, one has

```text
Theta_1(z)=B_2(s).
```

The poles of `Theta_omega` in the upper half-plane correspond exactly to Xi zeros with

```text
Re(rho)>1/2+omega.
```

At `omega=1` this region is `Re(rho)>3/2`, which is zero-free unconditionally. Hence
`Theta_1` is already inner and its anti-causal Hardy leakage vanishes without RH. Off-critical
Xi zeros remain numerator zeros of this inner function; they do not create leakage at this safe
aperture.

Therefore the formerly proposed implication

```text
B_2(rho)=0 -> reflected aperture saturation -> Re(rho)=1/2
```

cannot follow from fixed-aperture innerness, positivity, or leakage cancellation. Those
properties hold before the horizontal position of `rho` is known.

## Direct-logarithmic Hilbert no-go retained

If `rho` is an Xi zero of multiplicity `m`, then `xi(s+2)` is nonzero near `rho` and

```text
Res_rho H_2=-m.
```

Thus `|H_2|^2` is not locally integrable on a curve through `rho`. Multiplicative integration to
`B_2` correctly replaces poles by zeros, but the fixed quotient then loses the transverse
horizontal detector. This is the exact obstruction: the additive source is too singular to norm
at a zero, while one safe multiplicative aperture is too coarse to locate that zero.

## Strongest positive survivor

The horizontal coordinate is carried by the *entry aperture* of the full family

```text
Theta_omega,   omega>0.
```

For `rho=1/2+a+i*gamma`, the associated Hardy leakage switches on precisely for `0<omega<a` and
switches off for `omega>a`; the crossing channel has asymptotically unit strength. Consequently

```text
RH <-> L_omega=0 for every omega>0,                         (S1)
```

where `L_omega=P_- M_(Theta_omega)|H^2_+`. A single fixed `omega`, including `omega=1`, cannot
replace `(S1)`.

The new source-side question exposed by HTGeometry is whether distinct corrected shift defects
form a differentially independent transverse family even over the completed valuation-layer
field. A positive answer would prove that the safe-shift flow cannot be compressed into finitely
many differential reporters. That theorem is pursued on
`xi-transverse-shift-defect-differential-rank.md`.

## Route closure

- [x] The logarithmic primitive and strip-divisor theorem are retained as correct mathematics.
- [x] The exact Suzuki identification and unconditional `omega=1` innerness close the fixed-ratio
      RH route.
- [x] Direct `|H_2|^2` norming is excluded by the zero poles.
- [x] Positive survivor isolated: the complete transverse leakage filtration and its differential
      rank, not one fixed quotient.
- [ ] Formalize `(N1)` only as a source theorem; do not present it as an RH bridge.
- [ ] Formalize finite transverse shift-defect differential rank.
- [ ] Attack the all-`omega` source-to-Hardy realization, which remains RH-strength.

## Log

- 2026-07-18 -- Initial multiplicative survivor `B_2` isolated from the direct-logarithmic norm
  obstruction.
- 2026-07-18 -- Whole RHTower audit identified `B_2` with Suzuki's `omega=1` quotient. Since its
  leakage is unconditionally zero, the fixed-aperture RH implication was retired and replaced by
  the transverse-family rank programme.
