# Totient grids obstruct seventy percent at every bandwidth

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [Positivity ceiling](fable-route-closures.md).
- **Lean theorem:** `positivity_does_not_reach_seventy_percent_at_any_bandwidth`.
- **Lean status:** All six modules pass `lake --old env lean`; umbrella imports added.

## Exact statement

For every `λ>0`, there is a continuous even form factor `F` with `F≥0`,
`F(α)=|α|` on `[-1,1]`, `F−1∈L¹`, and real nonnegative pair density
`p=1+𝓕(F−1)`, such that

```
frobenius(F,λ) = 1/λ + (2/λ²) ∫₀^λ (λ−α)F(α) dα > 13/10.
```

Thus raw spectral and pair-density positivity cannot certify seventy percent
at any bandwidth. The witness depends on `λ`. The stronger constraint
`F≥1` outside `[-1,1]` is not part of this theorem.

## Totient grid law

Let `U_m` be uniform probability on the `m` equally spaced points of the
circle of circumference `L`. Set

```
w_m=φ(m)/L² (1≤m≤L),  w_*=1−Σw_m,
μ_L=L(Σw_m U_m+w_* U_(L+1)).
```

The weights are nonnegative since `Σφ(m)≤L(L+1)/2≤L²`. Its Fourier
coefficients are

```
c_k=Σ_(m≤L,m|k)φ(m)/L²+w_*1_(L+1|k).
```

Hence `c₀=1`, all `c_k≥0`, and `c_k=|k|/L²` for `1≤|k|≤L`, by
`Σ_(m|k)φ(m)=|k|`. Its origin mass is

```
A_L=(1/L)Σ_(m≤L)φ(m)/m + L/(L+1)(1−Σ_(m≤L)φ(m)/L²)
   → 1+3/π² > 13/10.
```

Möbius inversion gives the mean `6/π²` of `φ(m)/m`; weighted Cesàro
averaging gives the mean `3/π²` of `Σφ(m)/L²`.
These statements are formalized in `TotientGridPairLaw.lean`.

## Interpolation and the bandwidth bound

Write `Λ_a(t)=max(1−|t|/a,0)` and

```
P_m(α)=L Σ_(j∈ℤ) Λ_1(Lα+mj),
F_L=Σw_m P_m+w_*P_(L+1)−LΛ_1(Lα).
```

Equivalently, `F_L=LΣ_(k≠0)c_kΛ_1(Lα−k)`. At most two triangles overlap.
Thus `F_L` is continuous, even, lies in `[0,L]`, and equals `|α|` on the
unit band. Each grid has the absolutely convergent Fourier expansion

```
P_m(α)=Σ_(r∈ℤ) (L/m)sinc²(πr/m) exp(2πi(rL/m)α).
```

All coefficients are nonnegative. Since `𝓕Λ_λ=λ sinc²(πλ·)≥0`, retaining
the constant term gives `∫Λ_λ P_m≥λL/m`. The removed central triangle
has integral one, and `Λ_λ≤1`. Therefore

```
∫Λ_λ F_L ≥ λA_L−1,     frobenius(F_L,λ)≥A_L.
```

`IntegerTriangleInterpolation.lean`, `TotientGridFormFactor.lean`, and
`GridFourierMultiplier.lean` formalize these identities and inequalities.

## Exact Gaussian regularization

Choose `L` with `A_L>13/10`. Set

```
χ_R(α)=exp(−π(α/R)²),   η_R(x)=R exp(−π(Rx)²),
e_R=Λ_1(1−χ_R),
F̃_R=χ_RF_L+(1−χ_R)min(|α|,1).
```

The blend preserves spectral positivity and the exact unit band, and
`F̃_R−1=χ_R(F_L−1)−e_R` is integrable. Also
`|𝓕e_R|≤∫e_R≤π/R²`, using `1−exp(−u)≤u` and `∫Λ_1=1`.

The positive grid expansions and Gaussian Fourier transform give

```
1+𝓕[χ_R(F_L−1)](x) ≥ D_R(x)+(A_L−1)η_R(x),
D_R(x)=∫η_R(y)[1−sinc²(π(x+y)/L)]dy.
```

The inequality `1−sinc²(t)≥min(t²,1)/12`, followed by integration over
the half-line directed away from `x`, gives

```
D_R(x)≥c min(x²,1),    c=min((π/L)²,1)/24>0.
```

Choose `D≥1` with `cD²≥π`. For `|Rx|≥D` and `R≥D`, this background
absorbs `π/R²`. For `|Rx|≤D`, the origin surplus is at least
`(A_L−1)R exp(−πD²)`, which also absorbs `π/R²` for large `R`.
Consequently `1+𝓕(F̃_R−1)≥0` everywhere. Evenness makes the transform real.

For fixed `λ`, dominated convergence gives
`frobenius(F̃_R,λ)→frobenius(F_L,λ)≥A_L>13/10`; the strict margin survives.
`SincGapAndGaussianMargin.lean` and `TotientGridGaussianRegularization.lean`
contain the estimates and the resulting existence theorem.
