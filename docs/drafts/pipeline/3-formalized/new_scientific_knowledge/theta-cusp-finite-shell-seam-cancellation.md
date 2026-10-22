# Theta-cusp finite-shell seam cancellation law

- **Stage:** 3-formalized
- **Type:** theorem / source obstruction with positive survivor
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspFiniteShellSeamCancellation.lean`

## Statement

Write the positive theta shells as

```text
phi_n(x) = thetaCuspSourceTerm x n,       n >= 1,
Phi(x)   = sum_(n>=1) phi_n(x).
```

The exact logarithmic seam slope of shell `n` is

```text
lambda_n
 = 9/2 - 2*pi*n^2 + 6/(2*pi*n^2-3),

phi_n'(0) = lambda_n phi_n(0).                         (1)
```

Then

```text
lambda_1 > 0,
lambda_n < 0                         for every n >= 2,
sum_(n>=1) phi_n'(0) = Phi'(0) = 0.                   (2)
```

For every finite nonempty canonical prefix

```text
Phi_N(x)=sum_(1<=n<=N) phi_n(x),
```

one has the strict identity and sign

```text
Phi_N'(0)
 = -sum_(n>N) phi_n'(0)
 > 0.                                                   (3)
```

Consequently no finite canonical shell prefix is even. Evenness of the completed theta source is
not present at any finite shell depth; it is created only by exact cancellation against the
infinite negative-slope tail.

## Proof

Direct logarithmic differentiation of

```text
phi_n(x)
 = 2*pi*exp(x/2)
   *(2*pi*n^4*exp(4x)-3*n^2*exp(2x))
   *exp(-pi*n^2*exp(2x))
```

at `x=0` gives `(1)`. Positivity of `phi_n(0)` follows from
`2*pi*n^2-3>0`.

The first-shell sign is the existing sharp endpoint theorem. For `n>=2`,

```text
2*pi*n^2-3 > 21,
6/(2*pi*n^2-3) < 2/7,
2*pi*n^2 > 24,
```

and therefore

```text
lambda_n < 9/2 - 24 + 2/7 < 0.
```

Termwise differentiation is justified by the existing compact-local derivative majorant. The
completed source is even, so its first seam derivative vanishes. This proves the third equality in
`(2)`.

For `N>=1`, every term of the tail in `(3)` is strictly negative. Its sum is strictly negative by
absolute summability, hence the prefix derivative is strictly positive. If `Phi_N` were even,
differentiating `Phi_N(-x)=Phi_N(x)` at zero would give
`-Phi_N'(0)=Phi_N'(0)`, contradicting `(3)`.

## Hedenmalm consequence

Let `Phi_N^ev(x)=Phi_N(|x|)` and let `X_N` be its bilateral Fourier--Laplace transform. Standard
endpoint integration by parts gives, for fixed `a>0` and `w=a+ib`,

```text
X_N(w)=2*Phi_N'(0)/w^2+O(|w|^-4),
X_N'(w)=-4*Phi_N'(0)/w^3+O(|w|^-5),
```

so its horizontal current satisfies

```text
lim_(|b|->infinity)
  ((a^2+b^2)^3/a) * partial_a |X_N(a+ib)|^2
 = -16*Phi_N'(0)^2 < 0.                                (4)
```

Equation `(4)` is paper-proved but not part of the current Lean module. The Lean theorem proves
its exact nonzero endpoint coefficient.

This rules out diagonal-shell positivity and every fixed finite-shell truncation as a producer for
the high-frequency Hedenmalm sign. A successful proof must control the complete cofinal
off-diagonal cancellation after all endpoint orders have disappeared. This is stronger than the
previous first-atom obstruction: failure persists at every finite canonical shell depth.

## Lean surface

```text
thetaCuspAtomBoundaryLogSlope
thetaCuspSourceTerm_zero_pos
thetaCuspAtomBoundaryLogSlope_neg
iteratedDeriv_one_thetaCuspSourceTerm_zero_eq_slope
iteratedDeriv_one_thetaCuspSourceTerm_zero_neg
thetaCuspFiniteShellPrefix
tsum_iteratedDeriv_one_thetaCuspSourceTerm_zero_eq_zero
thetaCuspFiniteShellPrefix_boundary_derivative_pos
deriv_thetaCuspFiniteShellPrefix_zero_pos
thetaCuspFiniteShellPrefix_not_even
```

## Open successor

Construct a cofinal shell regrouping whose reflected transform retains the complete modular seam
cancellation before taking the Hermitian current. The first live object is an absolutely convergent
double-shell current grouped by complete product or primitive-direction fibres; termwise diagonal
positivity is impossible by `(4)`.
