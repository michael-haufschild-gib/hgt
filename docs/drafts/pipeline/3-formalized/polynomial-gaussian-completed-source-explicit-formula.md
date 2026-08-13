# Polynomial-square Gaussian completed-source explicit formula

- **ID:** `polynomial-gaussian-completed-source-explicit-formula`
- **Stage:** 3-formalized
- **Type:** BRIDGE / ROUTE-U POSITIVE SURVIVOR
- **Scientific status:** `[LEAN-PROVED] [BRIDGE] [NOVELTY UNVERIFIED]`
- **Parent:** `../1-in-progress/squared-xi-polynomial-gaussian-weil-disproof.md`
- **Lean artifact:** `formal/GaloisForLFunctions/RHTower/XiPolynomialGaussianExplicitFormula.lean`
- **Axiom audit:** only `propext`, `Classical.choice`, `Quot.sound`

## Exact claim

For every real polynomial `Q` and positive heat time `t`, let

```text
T(Q,t) = sum_rho Q(z_rho^2)^2 exp(-t z_rho^2)
F(Q,t;xi) = integral_R exp(-i xi x) Q(x^2)^2 exp(-t x^2) dx.
```

Zeros are counted with exact multiplicity. Then

```text
pi T(Q,t)
  = integral_R Q(x^2)^2 exp(-t x^2) gammaHardyPhaseRate(x) dx
      + 2 pi Q(-1/4)^2 exp(t/4)
      - Re sum_n Lambda(n)/sqrt(n) F(Q,t;log n).
```

The trace is real unconditionally. On `routeUCompletedPrimeGammaWedge Q`, every nonzero `Q`
satisfies `T(Q,t)>0`.

## Dependency-closed proof

Put `N=natDegree(Q)+1` and `a_j=coeff(Q,j)`. Polynomial expansion gives

```text
Q(U)=sum_(j<N) a_j U^j,
Q(U)^2=sum_(j,k<N) a_j a_k U^(j+k).
```

The formal Hankel identity therefore writes `T(Q,t)` as the finite double sum of the monomial
Gaussian moments `M_(j+k)(t)`. The monomial completed-source theorem gives

```text
pi Re M_m(t)
  = integral_R x^(2m) exp(-t x^2) gammaHardyPhaseRate(x) dx
      + 2 pi (-1/4)^m exp(t/4)
      - Re sum_n A_(m,n)(t).
```

All coefficient sums are finite. Distributivity and `x^(2(j+k))=x^(2j)x^(2k)` identify their
archimedean sum with the displayed `Q(x^2)^2` integral. The polar double sum is

```text
(sum_(j<N) a_j (-1/4)^j)^2 exp(t/4)=Q(-1/4)^2 exp(t/4).
```

Fourier linearity identifies the prime double sum with `F(Q,t;log n)`. Interchanging this finite
sum with the prime series is valid because every Gaussian--Hermite centered prime atom is
absolutely summable; this follows from the already proved bottom-edge `L1` atom majorant and the
norm-of-integral inequality. This proves the formula.

For the wedge theorem, each prime term has real part at most its norm, and the critical
half-density Dirichlet coefficient has norm `Lambda(n)/sqrt(n)`. Hence the real prime source is at
most `routeUPolynomialGaussianPrimeAbsoluteTail`. The existing completed prime--Gamma gap is
strictly positive for nonzero `Q`, while the polar term is nonnegative. Thus `pi*T(Q,t)>0`, and
`pi>0` gives `T(Q,t)>0`.

## Hostile audit

- The explicit formula is a finite-linearity lift of the monomial Guinand--Weil formula and is a
  `[BRIDGE]`, not a novelty claim.
- It does not prove RH. It covers only `t*(natDegree(Q)+1)` below the fixed completed aperture.
- Strongest positive survivor: every negative polynomial-square RH witness lies strictly outside
  that aperture. The remaining route is therefore a sharp aperture-transfer or a different
  representation; fixed-polynomial heat transfer does not supply it.

## Formal theorem surface

- `RHTower.pi_mul_xiPolynomialGaussianHeatTraceReal_eq_primeGamma`
- `RHTower.xiPolynomialGaussianHeatTraceReal_pos_of_completedWedge`
- `RHTower.not_riemannHypothesis_forces_negative_trace_beyond_completedAperture`

Audited with named module build and full `GaloisForLFunctions.RHTower` umbrella build.
