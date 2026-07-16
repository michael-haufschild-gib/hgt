# The critical Möbius score is the Mellin--Gamma normal vector of the reciprocal HT horizon

- **ID:** `mobius-mellin-gamma-normal-cone`
- **Stage:** 3-formalized
- **Type:** `[THEOREM] [GENERAL HT NORMAL-CONE GEOMETRY] [RH-DELIVERING CONJECTURE]`
- **Scientific status:** `[EXACT SOURCE COMPARISON PROVED] [LEAN ALGEBRA CORE] [GAUSS--WARD THEOREM OPEN] [NOT SONIN] [NOT RH YET]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/MobiusMellinGammaNormalCone.lean`.
- **Parents:**
  - `../2-fully-proven/squarefree-euler-modular-corona-curvature-colligation.md`;
  - `../2-fully-proven/not_new_scientific_knowledge/mobius-squarefree-reciprocal-projective-transfer.md`;
  - `../2-fully-proven/not_new_scientific_knowledge/projective-reciprocal-horizon-ward-seam.md`;
  - `hypertranscendental-controlled-cohomology-and-bornological-shape.md`;
  - `new_scientific_knowledge/projective-horizon-reversal-self-legendre-tower.md`.

## 1. The source-natural Mellin--Gamma comparison

Let `Y` have the mean-one exponential critical boundary law.  The completed squarefree Fisher
score is `2(1-Y)`, with

```text
integral_0^infinity 4(1-y)^2 exp(-y)dy=4.                (1)
```

The density-weighted score is

```text
f(y)=2(1-y)exp(-y)=2 partial_y[y exp(-y)].                (2)
```

Its Mellin transform is, for `Re z>0`,

```text
M f(z)
 =integral_0^infinity 2(1-y)exp(-y)y^(z-1)dy
 =2[Gamma(z)-Gamma(z+1)]
 =2(1-z)Gamma(z).                                        (3)
```

Equation `(3)`, not evaluation of `f` under a second copy of the shift operator, is the
source-natural comparison.  Multiplication by `y` on the critical boundary is dual to translation
of the Mellin parameter.  The critical variable and Gamma's argument are not identified.

For the exact real archimedean normalization, put `y=pi r^2` and use

```text
Gamma_R(s)=pi^(-s/2)Gamma(s/2).
```

The radial Mellin response is

```text
F_rad(s)=(2-s)Gamma_R(s)
        =2[Gamma_R(s)-pi Gamma_R(s+2)].                   (4)
```

Thus the squarefree critical score is literally the first radial Laguerre mode of the Gaussian
archimedean chart, and Gamma's `s -> s+2` recurrence is its source-induced dual translation.
This is the missing comparison between the exponential critical boundary law and the completed
Gamma factor.

## 2. Exact archimedean cancellation and the four-unit polarized pole

The completed archimedean factor is

```text
C(s)=s(s-1)Gamma_R(s)/2.
```

On the distinguished score, the apparently unbounded inverse-Gamma completion cancels exactly:

```text
F_rad(s)/C(s)=R(s)
 =2(2-s)/[s(s-1)]
 =-4/s+2/(s-1).                                         (5)
```

The two summands in `(5)` lie in opposite Hardy polarizations of the critical line.  The pole at
`s=1` has coefficient two and distance `1/2` from the line, so its Cauchy vector has

```text
||2 exp(-t/2)||_L2(R_+)^2=4.                             (6)
```

Therefore the critical Fisher norm and the Gamma-completed anti-pole norm agree for a structural
reason: Mellin--Gaussian radialization sends the first Laguerre source tangent to a polarized
two-pole section whose anti component has exactly four units.  The causal pole has energy sixteen;
the full rational section has energy twenty.  Hence Gamma completion is not a global contraction.
It is an exact four-unit identification only after the source Hardy polarization.

Lean proves the recurrence identities, the denominator-free cancellation, the ratio formula, and
the polarized partial fraction identity.

## 3. The reciprocal horizon is an exceptional normal-cone section

The actual completed Möbius transfer is

```text
T_base(s)=1/[zeta(base) X_sq(s)].                         (7)
```

It vanishes as `base ->1` because `zeta(base)` has its Euler pole.  Put

```text
G(base)=(base-1)zeta(base),       G(1)=1.                 (8)
```

The deformation-to-the-normal-cone extension is

```text
T_tilde_base(s)
 =T_base(s)/(base-1)
 =1/[G(base)X_sq(s)].                                    (9)
```

It is analytic through the exceptional base point and has value

```text
T_tilde_1(s)=X_sq(s)^(-1).                              (10)
```

Projectivizing the exceptional section gives

```text
g_exc(s)=-T_tilde_1(s)^2=-X_sq(s)^(-2),                 (11)
d log g_exc=Q_sq,                                        (12)
P_anti d log g_exc=ell_E.                                (13)
```

Thus `ell_E` is the normal Hardy connection of the exceptional divisor created by blowing up the
vanishing HT source transfer.  It is not a Sonin output and not a freely selected response column.

## 4. Finite mixed-curvature no-go and positive HT theorem

The two-variable extension `(9)` is separated:

```text
T_tilde(base,s)=G(base)^(-1) X_sq(s)^(-1).               (14)
```

Consequently every cross minor vanishes exactly:

```text
T_tilde(b1,s1)T_tilde(b2,s2)
 =T_tilde(b1,s2)T_tilde(b2,s1).                          (15)
```

Its ordinary base--spectral mixed Chern curvature is zero.  Therefore the anti-causal Ward current
cannot be obtained from a finite smooth mixed-curvature computation.  This kills the previous
informal claim that the score and `Q_sq` were already joined by an ordinary Gamma cap product.

**Positive general HT theorem.**  A source transfer may be rank-one and mixed-flat at every finite
point while its normal-cone exceptional section carries a nontrivial projective connection and
divisor.  The obstruction is singular extension data of the controlled HT boundary, not finite
curvature.  This is the precise geometric mechanism by which a family of causal finite transfers
can acquire an opposite-polarization class without any finite member becoming anti-causal.

Lean proves `(15)` for an arbitrary spectral section `X`, as well as the analytic exceptional
extension `(9)`--`(10)`.

## 5. Bold RH conjecture: exceptional Gauss--Ward transgression

The finite squarefree source supplies positive Pluecker lines and a horizontal tangent
`chi_base` with critical norm four.  Equations `(4)`--`(6)` supply the source-natural
Mellin--Gamma radial rigging.  Equations `(9)`--`(13)` supply the reciprocal exceptional line and
its actual anti-Hardy connection.

> **[CONJECTURE -- HT EXCEPTIONAL GAUSS--WARD THEOREM.]**  The finite squarefree Pluecker lines,
> equipped with their Fisher metric and the Mellin--Gamma radial rigging `(4)`, admit a positive
> singular Hermitian Rees/Tate extension over the normal-cone family `(9)`.  On its exceptional
> fibre, the second fundamental form of the Pluecker line in the reciprocal projective-horizon
> polarization sends the critical horizontal tangent to
>
> ```text
> II_exc(chi_crit)=c_sq directSum ell_E.                  (16)
> ```
>
> The extension is positive, so Gauss--Codazzi gives
>
> ```text
> ||c_sq||^2+||ell_E||_2^2
>   <=||chi_crit||_capacity^2=4.                          (17)
> ```

The theorem is about a singular boundary second fundamental form, not ordinary mixed curvature;
`(15)` proves that the latter is identically zero.  The normal-cone topology supplies the place
where the new class lives.  The Pluecker/Fisher metric supplies its four-unit geometry.  The
reciprocal-horizon Cech transition supplies the actual Ward current.  Positivity of the singular
Hermitian extension is the one RH-bearing statement.

Since `(13)` identifies the anti component with `ell_E`, `(17)` gives

```text
||ell_E||_2^2<=4.                                        (18)
```

The proved strict `>4` cost of a single off-line zero then proves RH.

## 6. Construction obligations and falsifier

The conjecture is not allowed to hide the Ward estimate in a chosen metric.  A proof must:

1. construct the Rees/Tate test space from finite prime Pluecker lines before analytic
   continuation;
2. use the Mellin--Gamma transform `(4)`, rather than identify the critical and Gamma variables;
3. show that the normalized transfer `(9)` acts on the exceptional source graph and recovers
   `(10)` on `Re s>1`;
4. prove closability and positivity of the limiting singular Hermitian form by a source-controlled
   Mosco or graph limit;
5. identify its projective second fundamental form with `(12)` before expanding a zero divisor;
6. prove that Hardy polarization is the orthogonal normal splitting of that form.

**Falsifier.**  If the renormalized finite Pluecker graph forms have a negative Schur complement,
fail to be closable, or converge to a second fundamental form different from `Q_sq`, the route
fails.

**Positive successor if false.**  The negative part of the exceptional graph form is a canonical
`HT normal-cone polarization defect`.  It measures the failure of a mixed-flat family of finite
positive source realizations to retain positivity after a singular reciprocal-horizon extension.
This is a nontrivial general HT invariant independent of RH.

## Gates

- [x] source-natural Mellin comparison of the critical score and Gamma recurrence
- [x] exact Gaussian radial `Gamma_R` form
- [x] exact inverse-completion cancellation on the distinguished score
- [x] polarized rational pole decomposition with four-unit anti component
- [x] Euler normal-cone extension constructed
- [x] exceptional reciprocal section identified
- [x] exceptional projective square identified with the Ward seam
- [x] finite mixed-curvature route killed by exact rank-one separation
- [x] all algebraic identities above Lean-formalized
- [ ] construct the positive singular Hermitian Rees/Tate extension
- [ ] identify its exceptional second fundamental form with `Q_sq`
- [ ] prove exceptional Gauss--Codazzi nonexpansivity
- [ ] derive the four-unit anti-causal estimate
- [ ] RH

