# Exact theta factorization of the finite-energy Mayer core

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Parent:** [PM tasks](route-pm-mayer-scattering-and-escape.md), Mayer 3.

## Target

For `t>0`, put `R(t)=(θ(t)−1−t^(−1/2))/2`, with the actual Jacobi
Gaussian count. Prove

```text
M R(u) = Γ_R(2u) ζ(2u),                 0<Re u<1/2,
F_w(a) = [2/Γ_R(w)] ∫₀∞ t^(w/2−1) R(t)R(a²t) dt,
M F_w(u) = Γ(u/2)Γ((w−u)/2)ζ(u)ζ(w−u)/Γ(w/2).
```

The core identity uses `a>0`, `0<Re w<2`, `Im w>0`. The last Mellin
integral must converge absolutely for
`max(0,Re w−1)<Re u<min(Re w,1)`.

## Proof mechanism

The modified even theta kernel already has an entire Mellin transform.
Almost everywhere on positive heights,
`2R = modifiedEvenKernel − 1_(0,1) − t^(−1/2)1_(1,∞)`.
The two explicit power integrals recover the completed zeta function.

For `P_a(t)=R(t)R(a²t)`, `θ_a(t)=θ(t)θ(a²t)`, and `c=1/(4a)`, use

```text
J(w,a) = ∫₀¹ t^(w/2−1) P_a(t) dt
       + ∫₁∞ t^(w/2−1)(P_a(t)−c/t) dt − 1/[2a(w−2)].
```

Theta inversion gives `P_a(1/t)=(t/a)P_(1/a)(t)`. Hence
`f_a(t)=P_a(t)−1/4−1/(4at)` forms a weight-one functional-equation
pair with root number `1/a` and both constant terms `−1/4`.
Its continued Mellin transform is precisely `J(w,a)`. This reduces
holomorphy to the existing functional-equation-pair theorem. The exact expansion

```text
4(P_a−c/t) = (θ_a−1) − (θ−1) − (θ(a²·)−1)
            − a⁻¹t⁻¹/²(θ−1) − t⁻¹/²(θ(a²·)−1)
```

gives rapid decay of `f_a+1/4` at infinity. For `Re w>2`, each of the
five source Mellins converges absolutely and gives `J=Γ_R(w)F_w/2`.
Continue that identity; for `0<Re w<2`, restoring the explicit power
tail turns `J` into the convergent integral of `P_a`.

Finally multiplicative convolution and the first Mellin identity give
the two-zeta product. This would identify the actual core's arithmetic
spectrum rather than merely bound its averaging operator.

## Boundary

The theta/core identity and its convergence estimates remain to be
formalized. No all-eigenfunction correspondence or resonance exclusion
is asserted.
