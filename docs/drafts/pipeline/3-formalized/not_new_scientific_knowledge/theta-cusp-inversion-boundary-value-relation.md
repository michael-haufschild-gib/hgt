# Theta-cusp inversion boundary value relation

- **ID:** `theta-cusp-inversion-boundary-value-relation`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / SOURCE VALUE-REFLECTION BRIDGE
- **Scientific status:** `[PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean file:** `formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspInversionBoundaryValue.lean`
- **Statement:** The completed Xi value is the exact anti-invariance defect of the one-sided
  theta boundary primitive under simultaneous spectral and logarithmic inversion.

## Theorem

Let

```text
k(x) = thetaCuspFullSource(x),
F_w(x) = exp(-i w x) k(x),
U_w(a) = exp(i w a) integral_{x <= a} F_w(x) dx.
```

For every `w` in the Fourier--Laplace strip `|Im w|<1` and every real `a`,

```text
U_w(a) + U_{-w}(-a) = exp(i w a) XiC(w).                 (1)
```

In particular, at the inversion-fixed boundary,

```text
U_w(0) + U_{-w}(0) = XiC(w).                              (2)
```

Since the exponential factor never vanishes, `(1)` gives the pointwise and global constraint

```text
U_w(a) + U_{-w}(-a) = 0  iff  XiC(w)=0,                  (3)

(forall a, U_w(a)+U_{-w}(-a)=0)  iff  XiC(w)=0.          (4)
```

## Proof

The completed theta source is even:

```text
k(-x)=k(x).
```

Changing variables `x=-y` gives

```text
integral_{x <= -a} F_{-w}(x) dx
  = integral_{y > a} F_w(y) dy.                           (5)
```

Both prefactors in the left side of `(1)` equal `exp(i w a)`.  Adding the two half-line
integrals in `(5)` therefore yields the full Fourier--Laplace transform:

```text
U_w(a)+U_{-w}(-a)
  = exp(i w a) integral_R exp(-i w x) k(x) dx.
```

The formalized Fourier--Laplace identity identifies the last integral with `XiC(w)` throughout
`|Im w|<1`, proving `(1)`.  Equations `(2)`--`(4)` follow immediately.

## What this discharges

The Hedenmalm boundary eigenvalue condition can be presented without a second endpoint limit or an
operator-domain hypothesis.  On the natural strip, its exact static content is the source-only
anti-reflection proposition `ThetaCuspBoundaryAntiReflection w`; Lean proves that proposition
equivalent to `XiC w=0`.

This supplies a reusable relation for any route that needs to replace a two-ended theta boundary
condition by a fixed involutive constraint.  It also separates two questions cleanly:

1. source construction and reflection are unconditional;
2. forcing the anti-reflection parameters to be real remains the RH-bearing problem.

## Attack and boundary

1. **No zero localization is gained.**  The right side of `(1)` is exactly `XiC(w)`.  The relation
   detects zeros but gives no independent sign or reality mechanism.
2. **The exact multiplicity reader is now formalized, but it does not force simplicity.**
   Differentiating `(1)` in `w` gives a triangular Leibniz transform of the Xi jet by the
   nonvanishing cut-dependent exponential.  At a divisor of multiplicity `m`, every defect jet
   below `m` vanishes and the `m`th defect jet is that exponential times the explicit order-`m`
   theta Fourier--Laplace moment.  Thus every cut reads the same multiplicity; none proves that
   the multiplicity is one.
3. **The fixed-point relation alone is complete.**  Equation `(2)` already detects the same zero
   condition as the all-boundary equation `(4)`; quantifying over `a` adds covariance, not strength.
4. **No flow is required.**  The parameter `a` chooses a cut in one fixed completed source.  The
   proof uses only source evenness, a change of variables, and the completed Fourier--Laplace value.

## Literature boundary

Hedenmalm's 2026 preprint gives the inversion-symmetric theta source, its Mellin representation of
`Xi`, and the one-sided eigenfunction primitive.  The identity here is the direct boundary-splitting
consequence of those formulas.  It is therefore bridge infrastructure, not new scientific
knowledge.

Primary source:

- H. Hedenmalm, *Spectral interpretation of Riemann zeta zeros*, arXiv:2606.17494 (2026),
  <https://arxiv.org/abs/2606.17494>.

## Lean declarations

- `thetaCuspBoundaryPrimitive`;
- `thetaCuspBoundaryReflectionDefect`;
- `integral_thetaCuspFourierLaplaceIntegrand_reflection`;
- `thetaCuspBoundaryPrimitive_reflection_defect`;
- `thetaCuspBoundaryReflectionDefect_eq`;
- `iteratedDeriv_thetaCuspBoundaryReflectionDefect`;
- `thetaCuspBoundaryPrimitive_midpoint_value_relation`;
- `thetaCuspBoundaryPrimitive_anti_reflection_iff_XiC_eq_zero`;
- `ThetaCuspBoundaryAntiReflection`;
- `thetaCuspBoundaryAntiReflection_iff_XiC_eq_zero`;
- `iteratedDeriv_thetaCuspBoundaryReflectionDefect_eq_zero_before_supportMultiplicity`;
- `iteratedDeriv_thetaCuspBoundaryReflectionDefect_at_supportMultiplicity`;
- `iteratedDeriv_thetaCuspBoundaryReflectionDefect_ne_zero_at_supportMultiplicity`;
- `xiSupportMultiplicity_eq_iff_thetaCuspBoundaryReflectionDefectJet`.

## Gates

- [x] 0 → 1  source-pure statement and exact attack identified
- [x] 1 → 2  complete proof from theta evenness and the Fourier--Laplace identity
- [x] 2 → 3  Lean theorem in the RHTower umbrella; targeted module passes
- [ ] 3 → 4  no standalone preprint planned for a bridge-grade consequence
