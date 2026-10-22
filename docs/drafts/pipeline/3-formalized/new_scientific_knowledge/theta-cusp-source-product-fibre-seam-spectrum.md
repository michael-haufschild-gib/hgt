# Theta-cusp completed-source product-fibre seam spectrum

- **Stage:** 3-formalized
- **Type:** theorem / exact RH-target decomposition
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspShellHedenmalmCurrent.lean`

## Statement

Let

```text
V_n(z) = integral_(0,infinity) phi_n(x)
           * (exp(ixz) + exp(-ixz)) dx,
D_n(z) = partial_z V_n(z),
phi_n(x) = thetaCuspSourceTerm x n.
```

For `|Im z| < 1`, both shell families are absolutely summable and Lean proves

```text
XiC(z)        = sum_n V_n(z),
XiC'(z)       = sum_n D_n(z),
J_Xi(z)       = sum_(m,n) 2 Im(D_m(z) conjugate(V_n(z))).
```

After deleting the identically zero shell and grouping positive pairs by `mn=k`, this becomes

```text
thetaCuspCenterMixedFourierCurrent(a,b)
  = sum_k thetaCuspSourceProductFiberHedenmalmCurrent
      k (b - i a).                                      (1)
```

This is the actual completed source `T''-T/4`, not the auxiliary positive `4T''` density.

Write the odd endpoint jets

```text
d_r(n) = phi_n^(2r+1)(0).
```

Modular reflection gives absolute convergence and

```text
sum_n d_r(n) = 0                                        (2)
```

for every `r`. If

```text
C_(r,s)(k) = sum_(mn=k) d_r(m)d_s(n),
```

then Lean proves the all-order arithmetic cancellation

```text
sum_k C_(r,s)(k) = 0                                    (3)
```

for every pair `(r,s)`.

For first slopes, the ground and prime fibres have opposite signs:

```text
C_(0,0)(1) > 0,
C_(0,0)(p) < 0                  for every prime p,
sum_k C_(0,0)(k) = 0.                                   (4)
```

## Proof

Positivity of every source shell on the positive half-line turns the shell expansion into an
absolute dominated-convergence argument. The two absolutely summable shell series may therefore
be multiplied, giving the ordered double Hedenmalm current. The axes vanish because shell zero is
identically zero. Absolute summability permits exact regrouping by the finite factor-pair fibres.

For `(2)`, termwise differentiation is already justified by the compact-local derivative
majorant. The completed source is even, so every odd derivative at zero vanishes. Equation `(3)`
is then the absolutely convergent Cauchy product

```text
(sum_m d_r(m)) (sum_n d_s(n)) = 0.
```

The ground coefficient is the square of the positive first-shell slope. A prime fibre has exactly
the two ordered pairs `(1,p)` and `(p,1)`; the first slope is positive and every shell slope from
index two onward is negative. This proves `(4)`.

## High-frequency consequence

For fixed shell indices and `w=a+ib`, endpoint integration by parts gives

```text
V_n =  2 d_0(n) / w^2 + O(|w|^-4),
D_n = -4 i d_0(n) / w^3 + O(|w|^-5).
```

Hence the fixed `k`-fibre current has paper-level leading law

```text
lim_(|b|->infinity)
  ((a^2+b^2)^3/a) J_k(a,b) = -16 C_(0,0)(k).             (5)
```

Thus the ground fibre is eventually negative and every prime fibre eventually positive. More
importantly, `(3)` says that the same cofinal cancellation occurs at every algebraic endpoint
order, not only the first. The complete current is therefore not determined by any finite
endpoint expansion. Its sign lives in a beyond-all-orders cofinal remainder.

Equation `(5)` is a paper derivation; the exact coefficients, their signs, absolute regrouping,
and all-order cancellation are Lean theorems.

## Lean surface

```text
hasSum_thetaCuspShellHalfLineTransform
XiC_eq_tsum_thetaCuspShellEvenPhaseValue
deriv_XiC_eq_tsum_thetaCuspShellEvenPhaseSpectralDerivativeValue
xiCHorizontalCurrent_eq_tsum_thetaCuspShellPairHedenmalmCurrent
thetaCuspCenterMixedFourierCurrent_eq_tsum_sourceProductFiber
tsum_thetaCuspShellOddSeamJet_eq_zero
tsum_thetaCuspSourceProductFiberOddJetCoefficient_eq_zero
thetaCuspSourceProductFiberSeamCoefficient_one_pos
thetaCuspSourceProductFiberSeamCoefficient_prime_neg
tsum_thetaCuspSourceProductFiberSeamCoefficient_eq_zero
```

## Open successor

Control the beyond-all-orders remainder uniformly in the cofinal shell scale. Fixed-shell
asymptotics cannot do this. The exact successor coordinate is the shellwise incomplete-Gamma
tail with moving lower cut `n^2`.
