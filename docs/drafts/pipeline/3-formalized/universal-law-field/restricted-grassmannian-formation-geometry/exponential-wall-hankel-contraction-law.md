# Exponential-wall Hankel contraction law

- **ID:** ULF-EWHC-001
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** `ULF-SCIN-001`
- **Statement:** literal prime-mixed Stokes formation lands at a positive trace-one strict
  contraction whose Burnol supersymmetric partner has kernel `24rs/(1+r+s)^4`.

## 1. Why this theorem matters

The wall landing in `ULF-SCIN-001` was known to be nuclear with integral trace, but nuclearity
alone gives no sub-unit control. The corpus's exact two-copy coherence value supplies a stronger
law: the whole infinite-rank formation operator has operator norm strictly below one before any
zero or divisor is supplied.

This is a direct sub-unit source anchor, not amplification and not an assumed positivity. It does
**not** identify the wall determinant with Xi; that identification is already false.

## 2. Source operator

Let

```text
mu(dx)=exp(-x) dx on (0,infinity),
kappa(x,y)=8(xy)^(3/2)/(x+y)^3,
(A f)(x)=integral kappa(x,y) f(y) mu(dy).              (EWHC.1)
```

Under exponential quantile transport, `A` is exactly the positive wall operator `A_0` of
`ULF-SCIN-001`. Hence

```text
A=A*,   A>=0,   A is Schatten-one,   Tr A=1.           (EWHC.2)
```

No spectral parameter occurs in `(EWHC.1)`.

## 3. Theorem A: exact Burnol partner

Define the feature and synthesis maps

```text
v_x(r)=2 x^(3/2) r exp(-xr),
(Vf)(r)=integral v_x(r)f(x)mu(dx).                     (EWHC.3)
```

Then `V` is Hilbert--Schmidt, `||V||_2^2=1`, and

```text
A=V*V.                                                 (EWHC.4)
```

Its opposite-order partner `B=VV*` acts on `L2((0,infinity),dr)` by the explicit weighted
Hankel kernel

```text
b(r,s)=24rs/(1+r+s)^4.                                 (EWHC.5)
```

Consequently `B` is positive Schatten-one, `Tr B=1`, and `A,B` have the same nonzero
eigenvalues with multiplicity. In particular their ordinary Fredholm determinants agree.

**Proof.** Direct Gamma integration gives

```text
integral_0^infinity |v_x(r)|^2 dr
 =4x^3 integral_0^infinity r^2 exp(-2xr)dr=1,
<v_x,v_y>=8(xy)^(3/2)/(x+y)^3=kappa(x,y).
```

Since `mu` is a probability measure, `V` is Hilbert--Schmidt with squared norm one, and the
Gram identity gives `(EWHC.4)`. Reversing the order gives

```text
b(r,s)
 =4rs integral_0^infinity x^3 exp(-(1+r+s)x)dx
 =4rs * 3!/(1+r+s)^4,
```

which is `(EWHC.5)`. Standard Hilbert--Schmidt product and cyclic spectral laws give the
remaining statements. QED.

## 4. Theorem B: exact strict contraction

The corpus proves the squared-coherence identity

```text
Tr(A^2)=||A||_2^2
 =integral integral kappa(x,y)^2 mu(dx)mu(dy)
 =16/35.                                               (EWHC.6)
```

Therefore

```text
||A||=||B|| <= 4/sqrt(35) < 1.                        (EWHC.7)
```

Thus `I-A` and `I-B` are boundedly invertible, with norm-convergent Neumann series. Moreover

```text
det(I-zA)=det(I-zB) != 0  whenever |z|<sqrt(35)/4,      (EWHC.8)
e_2(A)=(Tr(A)^2-Tr(A^2))/2=19/70.                      (EWHC.9)
```

**Proof.** Positivity and Schatten-one membership make `(EWHC.6)` the Hilbert--Schmidt norm
identity. Operator norm is bounded by Hilbert--Schmidt norm, and `16/35<1`. Neumann
invertibility and the zero-free Fredholm disc follow from `(EWHC.7)`. The second elementary
symmetric trace identity gives `(EWHC.9)`. QED.

## 5. Checked corpus locks

- `routePPrimitiveGammaJuliaStokesCofinalChildTraceClass` supplies positive nuclearity and trace.
- `integral_routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence_exp_prod_eq` supplies
  exact value `16/35`.
- `routePPrimitiveGammaJuliaStokesWallFredholmCoefficient_exp_two` independently gives `19/70`.
- `routePPrimitive_GammaJulia_Stokes_expWallXiTau_projectiveJetNoGo` rules out every scalar
  rescaling of wall tau germ to Xi tau germ.
- `routePPrimitiveGammaJuliaStokesWallSignedSquareQuadraticJet_ne_thetaCanonical` rules out fixed
  canonical theta/Xi jet identification.
- `RoutePPrimitiveGammaJuliaStokesApertureWallXiDivisorNoGo` proves exact wall/Xi divisor
  identification false.

## 6. Exact significance and limit

This theorem upgrades source object from “trace-one nuclear” to “trace-one strict contraction”
and places it on the same Burnol continuum used by prime collision budget. It therefore supplies
a canonical source resolvent `(I-A)^-1` and a zero-free determinant neighborhood larger than unit
disc.

It cannot by itself select RH. Direct conjugacy, scalar rescaling, and equality of its divisor
with Xi are closed by locks above. Any valid completion law must add a source-derived
theta/Poisson relative boundary operation which changes divisor-bearing operator while preserving
unsquared prime formation data and strict bound `(EWHC.7)`.

## 7. Lean status

Paper theorem only. Its analytic inputs are already Lean-proved; operator synthesis,
opposite-order kernel, and strict operator-norm corollaries are not yet packaged as one Lean
module.

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.SquareIntegrableKernelOperator`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Modules `GaloisForLFunctions.HTGeometry.SquareIntegrableKernelOperator` (67 constants: two-space L²-kernel operators, adjoint kernel, composed kernel, Hilbert–Schmidt with `‖K‖²_HS = ∬|k|²`), `GaloisForLFunctions.HTGeometry.SquareIntegrableKernelTransport` (10: transport along measure-preserving maps), `GaloisForLFunctions.HTGeometry.FredholmDeterminantTracePowers` (24: `det(1 - zT)` via `RHTower.fredholmDetOp`, trace-power comparison, `det(1 - zV*V) = det(1 - zVV*)`, eigenspace isomorphism, second coefficient, zero-free disc), `GaloisForLFunctions.HTGeometry.ExponentialWallBurnolPartner` (40), `GaloisForLFunctions.HTGeometry.ExponentialWallStrictContraction` (30), `GaloisForLFunctions.HTGeometry.ExponentialWallQuantileTransport` (13). All are axiom-audit clean. They reuse the corpus Hilbert–Schmidt / trace / regularized-determinant stack (`opTrace_comp_comm`, `entireDet2`, `detCoeff_two_eq_neg_half_traceSquare`, `fredholmDetOp_eq_zero_iff`, `memSchattenClass_one_comp`, `opTrace_sq_eq_ofReal_hsNormSq`), the corpus wall kernel `routePPrimitiveGammaJuliaStokesWallCubicKernel`, and the corpus value `∬ 64a³b³/(a+b)⁶ = 16/35`. `μ = expMeasure 1`; `dr` is the corpus `halfLineMeasure = volume.restrict (Ici 0)`.

| Claim | Lean declaration |
|-|-|
| (EWHC.1) `μ`, `κ`, `A` | `wallCubicKernel`, `wallKernel`, `wallOperator` |
| (EWHC.2) `A = A*`, `A ≥ 0`, Schatten-one, `Tr A = 1` | `isSelfAdjoint_wallOperator`, `isPositive_wallOperator`, `memSchattenClass_one_wallOperator`, `opTrace_wallOperator` |
| (EWHC.3) features `v_x(r)`, synthesis `V` | `burnolFeature`, `HTGeometry.burnolKernel`, `burnolSynthesis` |
| Thm A: `V` Hilbert–Schmidt, `‖V‖₂² = 1` (Gamma integration) | `isHilbertSchmidt_burnolSynthesis`, `hsNormSq_burnolSynthesis`, `burnolKernel_energy`, `integral_burnolFeature_sq`, `HTGeometry.integral_pow_mul_exp_neg_mul_Ioi` |
| (EWHC.4) `⟨v_x, v_y⟩ = κ(x,y)`, `A = V*V` | `integral_burnolFeature_mul`, `wallOperator_eq_adjoint_comp` |
| (EWHC.5) `B = VV*` with kernel `24rs/(1+r+s)⁴` | `partnerOperator`, `partnerKernel_toFun`, `partnerOperator_apply`, `partnerOperator_eq`, `integral_burnolFeature_mul_expMeasure` |
| Thm A: `B` positive, Schatten-one, `Tr B = 1` | `isPositive_partnerOperator`, `memSchattenClass_one_partnerOperator`, `opTrace_partnerOperator` |
| Thm A: same nonzero eigenvalues with multiplicity | `finrank_eigenspace_wallOperator_eq`, `eigenspaceEquiv`, `finrank_eigenspace_adjoint_comp_self_eq` |
| Thm A: Fredholm determinants agree | `detOneSub_wallOperator_eq`, `detOneSub_adjoint_comp_self_eq`, `detOneSub_eq_of_opTrace_pow_eq`, `opTrace_adjoint_comp_self_pow` |
| (EWHC.6) `Tr(A²) = ‖A‖₂² = ∬κ² = 16/35` | `opTrace_wallOperator_sq`, `hsNormSq_wallOperator`, `wallKernel_energy`, `SqIntKernel.hsNormSq_op` |
| (EWHC.7) `‖A‖ = ‖B‖ ≤ 4/√35 < 1` | `norm_wallOperator_le`, `norm_partnerOperator`, `norm_wallOperator_lt_one`, `norm_partnerOperator_lt_one` |
| Thm B: `I - A`, `I - B` invertible, Neumann series | `wallOperator_neumann`, `partnerOperator_neumann` |
| (EWHC.8) `det(I - zA) = det(I - zB) ≠ 0` for `∣z∣ < √35/4` | `detOneSub_wallOperator_ne_zero`, `detOneSub_ne_zero` |
| (EWHC.9) `e₂(A) = (Tr(A)² - Tr(A²))/2 = 19/70` (second Taylor coefficient of `det(1 - zA)`) | `taylorCoeff_detOneSub_wallOperator_two`, `taylorCoeff_detOneSub_two` |
| §2 exponential quantile transport identifies `A` with the comoving landing `A₀` | `quantileWallKernel`, `quantileWallKernel_toFun_eq` (kernel = corpus `routePPrimitiveGammaJuliaStokesWallQuantileKernel`), `compL2_quantile_cdf_inverse` (unitarity), `quantileWallOperator_eq` (`A₀ = U A U⁻¹`) |

§5 lists existing corpus Lean locks, already formal. §6 is interpretation.

## Log

- 2026-09-28 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
