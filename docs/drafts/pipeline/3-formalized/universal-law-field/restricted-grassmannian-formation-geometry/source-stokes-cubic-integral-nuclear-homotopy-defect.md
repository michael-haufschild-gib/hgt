# Source Stokes cubic integral--nuclear homotopy defect

- **ID:** ULF-SCIN-001
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parents:** `ULF-SSIN-001`, `ULF-CAGC-001`
- **Purpose:** replace the rank-one all-ones prime lift by one nuclear operator carrying the
  literal complete cross-prime formation kernel.

## 1. Big-picture interpretation

The critical wall does not destroy the Euler state.  It destroys the fixed-prime chart in which
that state is being observed.  In the fixed chart, every prime coordinate and the whole operator
vanish strongly.  In the source's own quantile chart, the same operator has a nonzero trace-norm
limit.  Its integer trace is conserved, while its support moves to infinity.

Thus the relevant object is not a static operator but a nuclear section together with its
singular change of frame.  This is the minimal mechanism able to make all three statements true:

```text
every fixed observer sees zero;
the complete cross-prime formation law survives;
one integral oriented unit crosses the wall.
```

## 2. Checked corpus input

For `d>0`, put

```text
J(d)    = gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d,
pi_d(p) = routePPrimitiveGammaJuliaStokesWallNormalizedWeight d p.
```

The corpus proves `pi_d(p)>0`, `sum_p pi_d(p)=1`, and `J(d)>0`.  It also constructs the literal
cofinal child operator `K_d` with kernel

```text
K_d(p,q)=sqrt(J(d)pi_d(p)) sqrt(J(d)pi_d(q)) kappa(log p,log q),       (SCIN.1)
kappa(a,b)=8(a b)^(3/2)/(a+b)^3.                                     (SCIN.2)
```

The exact identity `(SCIN.1)` is
`routePPrimitiveGammaJuliaStokesCofinalChildKernel_eq_wallCubicKernel`; positivity,
Schatten-one membership, and `Tr K_d=J(d)` are
`routePPrimitiveGammaJuliaStokesCofinalChildTraceClass`.  The wall probability law under
`x_d(p)=2d log p` converges to the unit exponential law, and the quantile-pulled kernels converge
in `L2((0,1)^2)` by
`tendsto_integral_routePPrimitiveGammaJuliaStokesWallQuantileKernel_sub_sq_nhdsGT_zero`.

No zero, divisor, Xi eigenvector, or fitted spectral parameter occurs in these inputs.

## 3. Definition of the object nobody asked for

On `H_P=ell2(Nat.Primes)`, define, for `t!=0`,

```text
mathsf T(t) = sign(t) K_|t| / J(|t|).                                 (SCIN.3)
```

Equivalently its complete prime matrix is

```text
mathsf T(t)_(p,q)
  = sign(t) sqrt(pi_|t|(p) pi_|t|(q)) kappa(log p,log q).             (SCIN.4)
```

This is not the rank-one matrix `sqrt(pi_p pi_q)`: `kappa(log p,log q)` is the actual normalized
Burnol cubic Gram coherence.  Every off-diagonal entry is retained and is strictly nonzero.

Set `mathsf T(0)=0` only in the fixed-chart strong completion.

## 4. Theorem SCIN-A: prime-mixed integral nuclearity

For every `t!=0`:

```text
mathsf T(t)*=mathsf T(t),
sign(t) mathsf T(t) >= 0,
mathsf T(t) is Schatten-one,
Tr mathsf T(t)=sign(t) in Z,
||mathsf T(t)||_1=1,
mathsf T(-t)=-mathsf T(t).                                           (SCIN.5)
```

Its diagonal is the unsquared normalized literal Stokes current:

```text
mathsf T(t)_(p,p)=sign(t) pi_|t|(p)=j_p(t)/abs(J(t)).                 (SCIN.6)
```

**Proof.**  `K_d` is positive Schatten-one and has trace `J(d)>0`.  Division by `J(d)` gives a
positive trace-one operator, hence trace norm one.  Multiplication by `sign(t)` gives `(SCIN.5)`.
Since `kappa(a,a)=1`, `(SCIN.6)` follows.  Strict positivity of every weight and of the cubic
Cauchy Gram gives nonzero `p,q` entries.  QED.

## 5. Theorem SCIN-B: genuine nuclear homotopy on each chamber

The maps `t |-> mathsf T(t)` on `t>0` and `t<0` are trace-norm continuous.

**Proof.**  Let

```text
v_p(r)=2 (log p)^(3/2) r exp(-(log p)r),
V_d e_p=sqrt(pi_d(p)) v_p.
```

The Burnol integral gives `||v_p||=1` and `<v_p,v_q>=kappa(log p,log q)`, hence

```text
K_d/J(d)=V_d* V_d,             ||V_d||_2=1.                           (SCIN.7)
```

On every compact positive `d`-interval, dominated convergence gives `pi_d -> pi_e` in `ell1`.
The Hellinger inequality yields

```text
||V_d-V_e||_2^2
  =sum_p (sqrt(pi_d(p))-sqrt(pi_e(p)))^2
  <=sum_p |pi_d(p)-pi_e(p)| ->0.                                    (SCIN.8)
```

The ideal inequality

```text
||V_d*V_d-V_e*V_e||_1
  <= (||V_d||_2+||V_e||_2)||V_d-V_e||_2                              (SCIN.9)
```

proves trace-norm continuity.  QED.

## 6. Theorem SCIN-C: fixed-chart disappearance

As `t->0` from either side,

```text
mathsf T(t) -> 0 strongly,                                           (SCIN.10)
```

while `||mathsf T(t)||_1=1` and its one-sided traces are `+1` and `-1`.

**Proof.**  For each fixed prime, `pi_d(p)->0`.  If `x` has finite support, `(SCIN.7)` gives
`V_d x->0`, so `<x,(K_d/J(d))x>->0`.  Since every positive trace-one operator is a contraction,

```text
||(K_d/J(d))x||^2 <= <x,(K_d/J(d))x> ->0.
```

Density and the uniform operator bound extend this to every `x in H_P`.  The trace statements
are `(SCIN.5)`.  Consequently every compact fixed-chart observer `C` satisfies

```text
Tr(mathsf T(t) C)->0.                                                (SCIN.11)
```

QED.

## 7. Theorem SCIN-D: comoving integral landing

Let `mu_d` be the pushforward of `pi_d` by `x_d(p)=2d log p`, and let `Q_d` be its quantile.
There is a canonical isometric embedding

```text
U_d : ell2(Primes) -> L2(0,1)                                       (SCIN.12)
```

obtained by three source-forced steps:

```text
a_p |-> a_p/sqrt(pi_d(p)) in L2(Primes,pi_d),
p   |-> x_d(p)              in L2(mu_d),
f   |-> f o Q_d             in L2(0,1).
```

It exactly conjugates the positive half of `mathsf T` to the integral operator `A_d` with kernel

```text
a_d(u,v)=kappa(Q_d(u),Q_d(v)).                                      (SCIN.13)
```

That is,

```text
U_d mathsf T(d) U_d* = A_d.                                         (SCIN.14)
```

If `Q_0(u)=-log(1-u)` and `A_0` has kernel
`a_0(u,v)=kappa(Q_0(u),Q_0(v))`, then

```text
||A_d-A_0||_1 ->0 as d->0+.                                         (SCIN.15)
```

The negative chamber lands at `-A_0`.

**Proof.**  The first map in `(SCIN.12)` is unitary because all `pi_d(p)` are positive.  The
second is unitary onto the atomic support because `p |-> 2d log p` is injective.  Quantile
pushforward makes the third map an isometry.  Direct substitution in `(SCIN.4)` gives
`(SCIN.14)`.

The corpus `L2` kernel limit is exactly `||A_d-A_0||_2->0`, hence operator-norm convergence.
All `A_d` are positive trace-class with trace one by `(SCIN.14)`.  The same Burnol synthesis over
the exponential quantile gives `A_0>=0`, Schatten-one, and `Tr A_0=1`.

Use the positive trace-tightness lemma: if positive trace-class operators converge in operator
norm and their traces converge to the trace of the limit, then they converge in trace norm.
For completeness, choose a finite-rank spectral projection `P` of the limit with arbitrarily
small complementary trace.  Operator convergence controls the finite `P` block; trace
convergence controls the positive complementary block; positivity bounds the two cross blocks by
the geometric mean of their diagonal traces.  All four blocks therefore converge in trace norm.
This proves `(SCIN.15)`.  QED.

## 8. Corollary: all compound orders land together

Trace-norm continuity of the ordinary Fredholm determinant gives, locally uniformly in `z`,

```text
det(1+z U_d mathsf T(d) U_d*) -> det(1+z A_0),
det(1+z U_d mathsf T(-d) U_d*) -> det(1-z A_0).                       (SCIN.16)
```

The coefficients on the left are exactly the complete ordered prime-tuple determinant
coefficients in `RoutePPrimitiveGammaJuliaStokesWallAtomicFredholmLimit`; repeated tuples vanish
inside the determinant rather than being deleted.  Thus one moving frame transports the linear
Stokes charge, every cross-prime matrix entry, and every Fredholm compound order.  This closes the
ordinary normalized-child determinant identification; it does not identify that determinant
with Xi or with the physical squared-child determinant.

## 8A. Strict contractive wall law

The exact corpus identity for two independent exponential wall clocks gives

```text
Tr(A_0^2)=||A_0||_2^2=16/35.
```

Hence `||A_0||<=4/sqrt(35)<1`: the comoving limit is not merely nuclear but a strict
contraction. Its opposite-order Burnol partner has explicit kernel `24rs/(1+r+s)^4`. Complete
proof and resulting determinant zero-free disc are in `ULF-EWHC-001`.

## 9. Exact conservation law and meaning

In the fixed chart the wall value is zero; in the comoving chart the right and left limits are
`+A_0` and `-A_0`.  Therefore

```text
(1/2)(Tr A_0-Tr(-A_0))=1,                                           (SCIN.17)
```

the normalized prime Stokes charge.  The existing pole--Gamma countercharge is `-1`, so the
completed scalar charge remains zero.

The new law is:

> **Nuclear formation is conserved only in source-comoving frames.  Strong closure in a fixed
> frame forgets an integral trace unit; quantile transport recovers the full prime-mixed unit and
> all its compound orders.**

This recasts source noncompactness as failure of global trivialization, not divergence of the
formation operator.

## 10. Exact surviving RH edge

This theorem constructs the source object and its canonical wall landing.  RH would follow from a
different, still missing comparison:

```text
(A_0 together with the pole--Gamma countercurrent)
  --theta/Poisson relative boundary functor-->
completed cubic formation defect mathsf T_D,                         (SCIN.18)
```

with the target positive energy dominated by the already proved primitive Euler budget `<1`.
The completed defect has integral multiplicity and costs at least one unit when nonzero; the
budget would force it to vanish.  `(SCIN.18)` must compare marked relative currents.  It cannot
be covariance-only, compact-observer continuous, or direct aperture-wall Xi identification;
those classes are already disproved in the corpus.

## 11. Hostile audit

1. `K_d` and the `L2` quantile-kernel limit already existed.  New content is the signed trace-one
   normalization as one homotopy defect, its fixed/comoving two-chart theorem, the trace-norm
   upgrade, and ordinary determinant landing.
2. The construction is pre-divisor but not an RH selector.  It narrows the missing map to the
   relative boundary functor `(SCIN.18)`.
3. Quantile transport is standard measure theory.  Significance comes from the simultaneous exact
   transport of corpus Stokes orientation, literal cofinal child, and all determinant orders.
4. The comoving isometries have no fixed-chart limit.  Treating them as a regular global unitary
   would erase the proved anomaly.
5. No novelty claim is made.  Adjacent varying-Hilbert-space/Mosco and spectral-flow theories do
   not supply the arithmetic theta/Poisson functor `(SCIN.18)`.

## Status

Paper proof dependency-closed.  Lean formalization deferred by current read-only research phase.

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.CompactObserverTraceBlindness`, `GaloisForLFunctions.HTGeometry.SourceStokesNormalizedChildUnit`, `GaloisForLFunctions.HTGeometry.QuantileBurnolLanding`, `GaloisForLFunctions.HTGeometry.SourceStokesComovingLanding`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Modules `GaloisForLFunctions.HTGeometry.CompactObserverTraceBlindness` (13 constants), `GaloisForLFunctions.HTGeometry.SourceStokesNormalizedChildUnit` (44), `GaloisForLFunctions.HTGeometry.QuantileBurnolLanding` (75) and `GaloisForLFunctions.HTGeometry.SourceStokesComovingLanding` (56), all axiom-audit clean. They reuse the corpus normalized child `normalizedStokesPrimeOperator` (= `K_d/J(d)`, positive, Schatten-one, trace one), the common radial synthesis `commonRadialPrimeSynthesis` (`V_d`, `‖V_d‖_HS = 1`), the wall law `routePPrimitiveGammaJuliaStokesWallHalfLineLaw`, its quantile convergence `tendsto_wallHalfLineQuantile_nhdsGT_zero`, the corpus quantile kernel `routePPrimitiveGammaJuliaStokesWallQuantileKernel`, the finite-block prime-tuple Fredholm expansion `tendsto_routePPrimitiveGammaJuliaStokesNormalizedChildFiniteDet`, its wall limit `tendstoUniformlyOn_routePPrimitiveGammaJuliaStokesWallFredholmEntireDet_nhdsGT_zero`, the EWHC wall operator (`wallKernel`, `burnolSynthesis`, `partnerOperator`, `quantileWallOperator`), `SqIntKernel`, and the corpus trace-norm / Fredholm-determinant API (`traceNorm_add_le`, `tsum_approxNumber_comp_le`, `fredholmDetOp`, `detOneSub_eq_of_opTrace_pow_eq`, `tendsto_entireDet2_of_hsNorm_sub_tendsto_zero`). `H_P = ℓ²(Nat.Primes)` is `PrimeHilbert`; `T(t)` is `stokesCubicUnit t`; `A_d` is `wallLandingOp d`; `A_0` is `quantileWallOperator`.

| Claim | Lean declaration |
|-|-|
| (SCIN.1)–(SCIN.2) literal cofinal child kernel `√(π_p π_q) κ(log p, log q)` | `normalizedStokesPrimeKernel_eq`, `normalizedStokesUnit_basis_coord` |
| (SCIN.3)–(SCIN.4) `T(t) = sign(t) K_{|t|}/J(|t|)` and its prime matrix | `normalizedStokesUnit`, `stokesCubicUnit`, `stokesCubicUnit_basis_coord` |
| Thm SCIN-A (SCIN.5): self-adjoint, `sign(t) T(t) ≥ 0`, Schatten-one, `Tr = sign t`, `‖T(t)‖₁ = 1`, `T(-t) = -T(t)` | `isSelfAdjoint_stokesCubicUnit`, `sign_smul_stokesCubicUnit`, `memSchattenClass_one_stokesCubicUnit`, `opTrace_stokesCubicUnit`, `traceNorm_stokesCubicUnit`, `stokesCubicUnit_neg` |
| (SCIN.6) diagonal `sign(t) π_{|t|}(p)`; every entry nonzero | `stokesCubicUnit_diag`, `stokesCubicUnit_basis_coord_ne_zero`, `wallCubicKernel_log_pos` |
| (SCIN.7) `K_d/J(d) = V_d* V_d`, `‖V_d‖_HS = 1` | `normalizedStokesUnit_eq_adjoint_comp`, `hsNorm_burnolPrimeSynthesis` |
| (SCIN.8) `‖V_d - V_e‖²_HS = ∑(√π_d - √π_e)² ≤ ∑|π_d - π_e|` | `hsNormSq_burnolPrimeSynthesis_sub`, `norm_stokesRay_sub_sq`, `hsNormSq_burnolPrimeSynthesis_sub_le` |
| (SCIN.9) `‖V_d*V_d - V_e*V_e‖₁ ≤ (‖V_d‖₂ + ‖V_e‖₂)‖V_d - V_e‖₂` | `traceNorm_adjoint_comp_self_sub_le`, `traceNorm_normalizedStokesUnit_sub_le` |
| Thm SCIN-B: trace-norm continuity on each chamber | `tendsto_traceNorm_stokesCubicUnit_sub` |
| Thm SCIN-C (SCIN.10): `T(t) → 0` strongly as `t → 0` | `tendsto_stokesCubicUnit_apply`, `norm_normalizedStokesUnit_basis_le`, `norm_normalizedStokesUnit_le_one` |
| Thm SCIN-C: `‖T(t)‖₁ = 1`, one-sided traces `±1` | `stokesCubicUnit_wall` |
| (SCIN.11) `Tr(T(t) C) → 0` for every compact `C` | `tendsto_opTrace_stokesCubicUnit_comp`, `tendsto_opTrace_comp_of_isCompactOperator`, `exists_norm_sub_coordTruncation_comp_le` |
| (SCIN.12) `U_d = (f ↦ f∘Q_d) J_d`, `J_d e_p = π_d(p)^{-1/2} 1_{x_d(p)}` unitary onto `L²(μ_d)`, `U_d` isometric | `wallAtomBasis`, `primeAtomChart`, `primeAtomChart_basis`, `primeAtomChart_comp_adjoint`, `adjoint_primeAtomChart_comp`, `comovingChart`, `comovingChart_basis`, `adjoint_comovingChart_comp`, `norm_comovingChart_apply`, `wallLogCoordinate_injective`, `wallHalfLineLaw_atom`, `measurePreserving_quantile` |
| (SCIN.13) `a_d(u,v) = κ(Q_d u, Q_d v)` (the corpus quantile kernel) | `quantileLandingKernel`, `quantileLandingKernel_toFun` |
| (SCIN.14) `U_d T(d) U_d* = A_d`; negative chamber `-A_d` | `comovingChart_conj_stokesCubicUnit`, `comovingChart_conj_stokesCubicUnit_neg`, `normalizedStokesUnit_eq_primeAtomChart`, `quantileLandingOp_eq_conj`, `SqIntKernel.op_pullback` |
| `A_d`, `A_0` positive, Schatten-one, trace one | `isPositive_quantileLandingOp`, `memSchattenClass_one_quantileLandingOp`, `opTrace_wallLandingOp`, `isPositive_quantileWallOperator`, `memSchattenClass_one_quantileWallOperator`, `opTrace_quantileWallOperator` |
| `‖A_d - A_0‖₂ → 0`, hence operator-norm convergence | `tendsto_hsNorm_wallLandingOp_sub`, `hsNorm_wallLandingOp_sub_le`, `tendsto_hsNorm_wallSynthesis_sub` |
| (SCIN.15) `‖A_d - A_0‖₁ → 0`; negative chamber lands at `-A_0` | `tendsto_traceNorm_wallLandingOp_sub`, `tendsto_traceNorm_comovingChart_conj` |
| (SCIN.16) `det(1 + z U_d T(±d) U_d*) → det(1 ± z A_0)` locally uniformly in `z` | `tendstoLocallyUniformly_fredholmDetOp_wallLandingOp`, `tendstoLocallyUniformly_fredholmDetOp_wallLandingOp_neg`, `tendsto_fredholmDetOp_wallLandingOp` |
| §8: left coefficients are the complete ordered prime-tuple Fredholm coefficients | `fredholmDetOp_comovingChart_conj`, `fredholmDetOp_normalizedStokesUnit`, `opTrace_conj_pow_succ`, `fredholmDetOp_wallLandingOp`, `fredholmDetOp_quantileWallOperator` |
| §8A `Tr A_0² = ‖A_0‖²₂ = 16/35`, `‖A_0‖ ≤ 4/√35 < 1`, partner `24rs/(1+r+s)⁴` | `opTrace_quantileWallOperator_sq`, `hsNormSq_quantileWallOperator`, `norm_quantileWallOperator_le`, `quantileBurnolSynthesis_comp_adjoint_expMeasure_one`, `partnerOperator_eq` |
| (SCIN.17) `½(Tr A_0 - Tr(-A_0)) = 1`; the pole–Gamma countercharge `-1` cancels it | `half_opTrace_quantileWallOperator_sub_neg`, `comoving_charge_conservation` |
| Summary | `sourceStokes_comoving_landing` |

§1, §9 (the law in words), §10 and §11 are interpretation. The card states that the comparison (SCIN.18) is missing and does not claim it.

## Log

- 2026-09-29 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
