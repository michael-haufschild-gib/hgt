# Euler--Hellinger/Gamma relative Mellin anomaly law

- **ID:** ULF-EHGM-001
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parents:** ULF-ESAC-001; `cubic-ward-hellinger-completed-source-trace-incidence`
- **Status:** `[PAPER-PROVED] [BRIDGE] [LEAN-PROVED]`
- **Surviving RH edge:** identify the actual anomaly-subtracted Euler--theta completion with the
  source-side Mellin transport below and prove its residual Xi boundary is a positive contraction
  of the order-six aperture carrier.

## 1. Higher-law interpretation

Two source gauges can agree on every individual cell and still disagree on every mixed packet.
The missing datum is neither another producer nor a scalar correction.  It is the unique
equivariant operator changing one coherent orbit into the other.  Its metric defect is invisible
on each orbit vector, lives only in cross-label incidence, has zero trace, and is necessarily
indefinite.

This is the first literal realization in the corpus of the proposed relative-completion law:

```text
same Euler weights + same dilation orbit
  local gauge 1: order-six aperture/Gamma feature
  local gauge 2: cubic Hellinger/collision feature
  unique Mellin transport M between gauges
  metric anomaly Q=M* M-I
  relative completion: collision Gram = aperture Gram + compressed anomaly.
```

The polar phase of `M` disappears from positive Grams; only its positive modulus survives.  Its
modulus tends to zero at high Mellin frequency, so `M` is injective with dense nonclosed range and
unbounded inverse.  Thus phase quotient, open lifted history, noncompact completion, and an exact
zero-trace anomaly arise from one mechanism rather than four analogies.

## 2. Corpus audit and correction

The in-progress card `cubic-ward-hellinger-completed-source-trace-incidence` already proves more
than a diagonal budget.  Its P-G177-A constructs the full Euler/Hellinger synthesis and proves

```text
Tr K=(115/1728) integral_0^infinity t^2[-zeta'/zeta](1+t)dt
    =routePPrimitiveCollisionCubicTraceBudget.        (EHGM.1)
```

Therefore the scalar aperture identity in ULF-ESAC-001 is a new Stokes interpretation of an
existing equality, not a new scalar theorem.  What ULF-ESAC-001 adds is a different canonical
off-diagonal operator `C`, its order-six Gamma Gram, and its singular sixth boundary.

Required corpus searches for `Mellin multiplier Gamma ratio dilation`, `Hellinger Gamma coherent
vector`, `same diagonal Gram anomaly`, and the exact constant `18/sqrt(23)` found no theorem or
paper card relating those two source syntheses.  General Mellin-multiplier, Gamma-six, Hellinger,
and Gram-anomaly machinery exists, but not the transport or conservation law below.

## 3. The two forced dilation gauges

Let `H=L2((0,infinity),dt)` and use the unitary dilation

```text
(D_lambda u)(t)=sqrt(lambda)u(lambda t), lambda>0.    (EHGM.2)
```

Define two unit vectors

```text
h_lambda(t)=sqrt(8/15) lambda^3 t^(5/2)exp(-lambda t),
f_lambda(t)=sqrt(864/115) lambda^(3/2)t
              [exp(-lambda t)-exp(-2lambda t)].      (EHGM.3)
```

Both are dilation orbits: `h_lambda=D_lambda h_1` and
`f_lambda=D_lambda f_1`.  Elementary Gamma integrals give

```text
||h_lambda||=||f_lambda||=1,                         (EHGM.4)
<h_mu,h_lambda>=[2sqrt(lambda mu)/(lambda+mu)]^6.    (EHGM.5)
```

Let `I=Primes x Nat`, `lambda_i=log(p^(e+1))`, and

```text
s_i=115/[864 p^(e+1)(e+1)^3 log(p)^2].               (EHGM.6)
```

Define Hilbert--Schmidt syntheses

```text
W_6 e_i=sqrt(s_i)h_(lambda_i),
W_H e_i=sqrt(s_i)f_(lambda_i).                       (EHGM.7)
```

Then

```text
C=W_6*W_6                                             (EHGM.8)
```

is exactly ULF-ESAC-001's aperture capacity.  Moreover

```text
sqrt(s_i)f_(lambda_i)
 =sqrt(Lambda(p^(e+1))/p^(e+1)) t
    [exp(-lambda_i t)-exp(-2lambda_i t)],             (EHGM.9)
```

so

```text
K=W_H*W_H                                             (EHGM.10)
```

is exactly P-G177-A's full primitive Euler/Hellinger collision Gram at `R=1`, `kappa=0`.

## 4. Unique equivariant Mellin transport

Use the unitary Mellin transform, up to the harmless common `1/sqrt(2pi)` normalization,

```text
(Mellin u)(xi)=integral_0^infinity u(t)t^(-1/2-i xi)dt. (EHGM.11)
```

The base vectors have transforms

```text
Mellin(h_1)(xi)=sqrt(8/15) Gamma(3-i xi),
Mellin(f_1)(xi)=sqrt(864/115) Gamma(3/2-i xi)
                  [1-2^(-3/2+i xi)].                 (EHGM.12)
```

Hence define

```text
m(xi)=(18/sqrt(23))
       Gamma(3/2-i xi)/Gamma(3-i xi)
       [1-2^(-3/2+i xi)].                            (EHGM.13)
```

The Gamma function has no zeros, its denominator has no real-line poles, and
`|1-2^(-3/2+i xi)|>=1-2^(-3/2)>0`.  Stirling's formula gives

```text
m is bounded and continuous,
m(xi)!=0 for every real xi,
|m(xi)|=O(|xi|^(-3/2)).                              (EHGM.14)
```

Let `M` be multiplication by `m` in Mellin coordinates.  Equations
`(EHGM.12)--(EHGM.13)` and dilation covariance give

```text
boxed: M h_lambda=f_lambda for every lambda>0.        (EHGM.15)
```

This transport is canonical.  After the logarithmic unitary
`u(t)->exp(x/2)u(exp x)`, dilations become translations and Mellin transform becomes Fourier
transform.  Every bounded operator commuting with all translations is a Fourier multiplier.  A
dilation-equivariant operator sending `h_1` to `f_1` must therefore have symbol `(EHGM.13)`, since
`Mellin(h_1)` never vanishes.  Thus `M` is the unique bounded dilation-equivariant gauge change.

Since `m` is nowhere zero, `M` is injective and has dense range.  Since `|m(xi)|->0`, its range is
not closed and `M^(-1)` is unbounded.  This properness is not imposed after construction; it is
forced by the relative Gamma orders in the two source features.

## 5. Phase quotient and local information neutrality

Write the polar decomposition pointwise:

```text
m=(m/|m|)|m|,  M=U|M|.                               (EHGM.16)
```

Because `m` never vanishes, `U` is a unitary Mellin multiplier.  Positive Gram formation quotients
out this entire phase:

```text
<M h_mu,M h_lambda>=<|M|h_mu,|M|h_lambda>.           (EHGM.17)
```

Put

```text
Q=M* M-I.                                            (EHGM.18)
```

Although `Q` is nonzero, `(EHGM.4)` and `(EHGM.15)` prove exact cellwise neutrality:

```text
boxed: <h_lambda,Q h_lambda>=0 for every lambda>0.    (EHGM.19)
```

The operator is not globally neutral.  Its multiplier `|m|^2-1` is negative at high frequency.
At zero,

```text
|m(0)|^2=(81 pi/92)(9/8-1/sqrt(2))>1.                (EHGM.20)
```

For an entirely symbolic lower bound, use `pi>3` and `1/sqrt(2)<29/40`; the right side is then
strictly larger than `243/230`.  Thus `Q` has both positive and negative spectral regions.  Local
norm equality has hidden a genuinely indefinite global mixing defect.

## 6. Exact relative-completion conservation law

From `(EHGM.15)` and `(EHGM.7)`,

```text
W_H=M W_6.
```

Therefore

```text
boxed: K=C+D,
D=W_6*QW_6.                                          (EHGM.21)
```

Here `D` is self-adjoint trace class.  Equations `(EHGM.19)` and `(EHGM.7)` give

```text
D(i,i)=0 for every Euler label i,
Tr D=0.                                              (EHGM.22)
```

The anomaly is not zero.  For the two labels `(p,0)` and `(p,1)`, whose clocks are `lambda` and
`2lambda`, the normalized correlations are

```text
<h_(2lambda),h_lambda>=512/729,
<f_(2lambda),f_lambda>=7794 sqrt(2)/14375.            (EHGM.23)
```

They are unequal because `sqrt(2)` is irrational.  Hence `D!=0`.  A nonzero self-adjoint
trace-class operator of trace zero cannot be positive or negative semidefinite, so `D` is
indefinite.

This is an exact conservation identity, not a bound:

```text
same diagonal capacity + same total capacity
  = order-six aperture Gram
  + zero-diagonal, zero-trace, sign-indefinite mixing anomaly
  = cubic Hellinger collision Gram.                  (EHGM.24)
```

No prime-independent scalar can express `D`; its entire content is off-diagonal incidence.  Yet
the generating multiplier `M` is universal and prime-independent.  This escapes the corpus no-go
against one shared scalar ghost without introducing label-fitted data.

## 7. Theta history lift

Let `Phi` be the theta Mellin-six history flux, `Tr Phi=1`.  Define

```text
T_6=Phi tensor C,
T_H=Phi tensor K,
Delta_rel=Phi tensor D.                              (EHGM.25)
```

Then

```text
boxed: T_H=T_6+Delta_rel,
Tr(T_H)=Tr(T_6)=routePPrimitiveCollisionCubicTraceBudget,
Tr(Delta_rel)=0.                                     (EHGM.26)
```

The two positive endpoints are integral--nuclear and retain every unsquared Euler coefficient.
Their relative anomaly is nuclear, purely mixed, and indefinite.  The order-six endpoint also
retains ULF-ESAC-001's singular sixth source boundary.  Thus theta history, Stokes aperture,
Euler prime powers, Gamma coherence, and collision formation are now connected by one exact
transport and one exact conservation identity.

## 8. RH-facing consequence and exact remaining theorem

This theorem supplies the previously missing source-side anomaly subtraction:

```text
boxed: T_6=T_H-Delta_rel.                             (EHGM.27)
```

It is derived from literal source features, preserves unsquared Euler coefficients, and requires
no divisor.  It also explains why scalar and positive-compression attempts failed: the correction
has zero diagonal and zero trace but is irreducibly indefinite.

What remains is not to invent that subtraction.  It is to prove that actual Euler--theta
completion uses this unique dilation-equivariant gauge change and that, after `(EHGM.27)`, the
completed Xi cubic Loewner synthesis factors contractively through `W_6` with no residual boundary.
If so, its total strict-right energy is at most
`Tr C<115/108`, while one strict-right copy costs at least `115/108`; functional equation then
gives RH.

This is still open.  The theorem does, however, remove three degrees of freedom from that edge:

1. source operator is fixed (`C`);
2. metric subtraction is fixed (`D`);
3. completion gauge change is fixed uniquely (`M`).

Only the Xi landing/residual-boundary theorem remains.  Supplying a zero before constructing that
landing would still be circular.

### Exact limitation: `M` is not the Xi landing

The corpus's primitive spectral-floor theorem must be applied here.  Every Euler source clock has
`lambda_i>=log 2`, whereas every strict-right Xi conormal has real rate `0<a<1/2`.  The multiplier
`M` sends `h_lambda` to `f_lambda`, whose slowest exponential is still `exp(-lambda t)`.  It changes
coherent gauge and regularity, not spectral rate.  Therefore `M` cannot map a primitive source
column to a strict-right Xi column and does not discharge W-H184.

The surviving architecture is a forced factorization, not a completed proof:

```text
order-six Euler aperture gauge
  -- unique equivariant M --> cubic Euler/Hellinger gauge
  -- missing noncommuting polar--Gamma rate changer R --> completed Xi conormal gauge. (EHGM.28)
```

Attack 38 in the audited frontier proves that `R` cannot intertwine the aperture semigroup: its
commutator must carry the source/target rate gap.  ULF-EHGM-001 fixes the first arrow and its metric
anomaly.  The only unsolved mechanism is now the second arrow together with its augmented
conservation law.

## 9. Hostile novelty and failure audit

1. Mellin diagonalization of dilation-equivariant operators and scale filtering are classical;
   see Gerald Kaiser, [*Wavelet Filtering with the Mellin Transform*](https://arxiv.org/abs/math-ph/0108013).
2. Gamma-integral coherent vectors and Gram factorizations are classical.  No novelty is claimed
   for `(EHGM.12)` in isolation.
3. Scalar equality `(EHGM.1)` is explicitly pre-existing corpus work.  ULF-ESAC-001's scalar
   novelty claim is corrected accordingly.
4. The surviving corpus-specific theorem is the unique explicit multiplier `(EHGM.13)` between
   the two already-forced Euler gauges and the compressed anomaly law
   `(EHGM.21)--(EHGM.27)`.
5. Failure condition: if the actual completed Xi synthesis does not factor through the
   anomaly-subtracted `W_6`, this is a source-geometry theorem but not an RH selector.
6. Stronger failure already proved: `M` alone preserves the Euler spectral floor and cannot be the
   Xi landing.  It is the source-gauge component of completion, not the rate-changing component.

## 10. Lean status

Every numbered claim (EHGM.1)–(EHGM.28) is proved unconditionally in Lean. This covers the Mellin
multiplier and its uniqueness, the dense nonclosed range, the polar quotient, cellwise neutrality, the
conservation law `K = C + D` with zero diagonal, zero trace, a nonzero mixed entry and indefiniteness,
the theta lift, the identification with the primitive collision kernel, the `-ζ'/ζ` moment identity,
and the spectral-floor limitation. See the Lean certificate below. §8's Xi landing theorem is open
and is not claimed.

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.HalfLineMellinMultiplier`, `GaloisForLFunctions.HTGeometry.EulerHellingerGammaTransport`, `GaloisForLFunctions.HTGeometry.EulerHellingerAnomalyConservation`, `GaloisForLFunctions.HTGeometry.EulerHellingerThetaLift`, `GaloisForLFunctions.HTGeometry.EulerHellingerCollisionKernel`, `GaloisForLFunctions.HTGeometry.HalfLineMellinUnitary`, `GaloisForLFunctions.HTGeometry.FourierTranslationModulation`, `GaloisForLFunctions.HTGeometry.LpBoundedMultiplier`, `GaloisForLFunctions.HTGeometry.PoissonGammaCoherentLadder`, `GaloisForLFunctions.HTGeometry.PrimeGammaRelativeModularTransport`, `GaloisForLFunctions.HTGeometry.EulerStokesApertureCapacity`, `GaloisForLFunctions.HTGeometry.EulerStokesThetaCapacity`, `GaloisForLFunctions.RHTower.RoutePPrimitiveCollisionTraceBudget`, `GaloisForLFunctions.RHTower.EulerLogPrimePowerLaplace`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

New modules: `GaloisForLFunctions.HTGeometry.HalfLineMellinMultiplier` (general Mellin-multiplier calculus on `L²(0,∞)`), `GaloisForLFunctions.HTGeometry.EulerHellingerGammaTransport`,
`GaloisForLFunctions.HTGeometry.EulerHellingerAnomalyConservation`, `GaloisForLFunctions.HTGeometry.EulerHellingerThetaLift` and
`GaloisForLFunctions.HTGeometry.EulerHellingerCollisionKernel`. They build on the corpus modules
`GaloisForLFunctions.HTGeometry.HalfLineMellinUnitary` (unitary Mellin transform `𝓜 = 𝓕 ∘ (log-chart unitary)`),
`GaloisForLFunctions.HTGeometry.FourierTranslationModulation`, `GaloisForLFunctions.HTGeometry.LpBoundedMultiplier`,
`GaloisForLFunctions.HTGeometry.PoissonGammaCoherentLadder` (coherent vectors `ψ_t^{(k)}`, Gram `k_m`, Mellin transforms),
`GaloisForLFunctions.HTGeometry.PrimeGammaRelativeModularTransport`, `GaloisForLFunctions.HTGeometry.EulerStokesApertureCapacity`
and `GaloisForLFunctions.HTGeometry.EulerStokesThetaCapacity` (the aperture synthesis `W_6`, `C`, `T_6`),
`GaloisForLFunctions.RHTower.RoutePPrimitiveCollisionTraceBudget` (collision kernel matrix, budget), and
`GaloisForLFunctions.RHTower.EulerLogPrimePowerLaplace` (`-ζ'/ζ(1+t)` as a prime-power Laplace sum). Every module is clean under
`lake env lean`, builds as a module, and its axiom audit shows only `[propext, Classical.choice, Quot.sound]`.
Notation: `h_λ = gammaCoherentVector 6`, `f_λ = hellingerVector`, `M = ehgmTransport`, `Q = ehgmAnomaly`,
`λ_i = xiGammaEulerPrimitiveLogFrequency i`, `s_i = xiGammaEulerPrimitiveCubicLogMomentWeight i`. The Mellin variable
is `2πξ` (Fourier normalisation of `𝓜`).

| Claim | Lean declaration |
|-|-|
| (EHGM.1) `Tr K = (115/1728)∫_0^∞ t²(-ζ'/ζ)(1+t)dt = ` budget (Tonelli over the prime-power Laplace sum, `∫t²e^{-λt} = 2/λ³`) | `eulerZetaMomentIntegrand`, `eulerZetaMomentIntegrand_nonneg`, `integral_eulerZetaMomentIntegrand`, `integrable_eulerZetaMomentIntegrand`, `integral_sq_mul_zetaLogDeriv`, `hellingerGram_opTrace_eq_zeta_moment` |
| (EHGM.2) unitary dilation `D_κ u(t) = √κ u(κt)`; `𝓜 D_κ = ` modulation `∘ 𝓜` | `halfLineDilation`, `halfLineExpUnitary_halfLineDilation`, `halfLineMellinUnitary_halfLineDilation`, `halfLineExpUnitary_ae_halfDensityPullback`, `halfLineDilation_eq_of_ae` |
| (EHGM.3) profiles of `h_λ` and `f_λ = √(864/115)λ^{3/2}t(e^{-λt}-e^{-2λt})`; dilation covariance | `gammaCoherentProfile_dilation`, `halfLineDilation_gammaCoherentVector`, `halfLineDilation_sixth`, `halfLineDilation_hellingerVector`, `hellingerVector`, `hellingerProfile`, `hellingerVector_ae` |
| (EHGM.4) `‖h_λ‖ = ‖f_λ‖ = 1` | `norm_gammaCoherentVector`, `norm_hellingerVector`, `cubicGram_double`, `two_rpow_neg_three_halves_sq`, `two_rpow_neg_three_halves_mul_sqrt_two` |
| (EHGM.5) `⟨h_μ,h_λ⟩ = [2√(λμ)/(λ+μ)]⁶` | `inner_gammaCoherentVector` |
| (EHGM.6)–(EHGM.8) `W_6 e_i = √s_i h_{λ_i}`, `C = W_6^*W_6` | `capacityFrame`, `capacitySynthesis`, `capacityGram`, `sqrt_xiGammaEulerPrimitiveCubicLogMomentWeight` |
| (EHGM.7) `W_H e_i = √s_i f_{λ_i}` | `hellingerFrame`, `norm_sq_hellingerFrame`, `summable_norm_sq_hellingerFrame`, `hellingerSynthesis` |
| (EHGM.9) `√s_i f_{λ_i} = √(Λ(n_i)/n_i) t(e^{-λ_i t}-e^{-2λ_i t})` | `vonMangoldt_eulerValuation`, `sqrt_weight_mul_hellinger_amplitude` |
| (EHGM.10) `K = W_H^*W_H ≥ 0`, `𝒮₁`, `Tr K = ‖K‖₁ = ` budget; `⟨f_λ,f_μ⟩ = (864/115)(λμ)^{3/2}[2/(λ+μ)³-2/(λ+2μ)³-2/(2λ+μ)³+2/(2λ+2μ)³]`; every finite compression of `K` is `routePPrimitiveCollisionCubicKernelMatrix 1 pe 0` | `hellingerGram`, `hellingerGram_traceClass`, `inner_single_hellingerGram`, `integral_sq_mul_exp_neg`, `integrableOn_sq_mul_exp_neg`, `collisionKernelReal`, `integral_hellingerProfile_mul`, `inner_hellingerVector`, `inner_single_hellingerGram_eq_collision`, `routePCollisionCubicKernel_one_zero`, `hellingerGram_compression_eq_collisionKernelMatrix` |
| (EHGM.11) unitary Mellin transform | `halfLineMellinUnitary_ae_eq_mellin`, `halfLineMellinUnitary_gammaCoherentVector_eq` |
| (EHGM.12) `𝓜h_1 = √(8/15)Γ(3-2πiξ)`, `𝓜f_1 = √(864/115)Γ(3/2-2πiξ)(1-2^{-3/2}2^{2πiξ})` | `halfLineMellinUnitary_sixth_one`, `halfLineMellinUnitary_hellingerVector_one` |
| (EHGM.13) the symbol `m(ξ) = (18/√23)Γ(3/2-2πiξ)/Γ(3-2πiξ)·(1-2^{-3/2}2^{2πiξ})` and the multiplier operator | `ehgmSymbol`, `mellinMultiplier`, `halfLineMellinUnitary_mellinMultiplier`, `coeFn_halfLineMellinUnitary_mellinMultiplier`, `ehgmTransport`, `ehgm_constant` |
| (EHGM.14) `m` continuous, nowhere zero, bounded; `‖m(ξ)‖² ≤ 324/|2πξ|³` for `|2πξ| ≥ 1` | `Gamma_ne_zero_of_re_pos`, `Gamma_three_halves_sub_ne_zero`, `Gamma_three_sub_ne_zero`, `norm_two_cpow_mul_I`, `one_sub_two_factor_ne_zero`, `ehgmSymbol_ne_zero`, `continuous_ehgmSymbol`, `norm_sq_Gamma_three_halves`, `norm_sq_Gamma_three`, `gammaRatio_bound`, `norm_sq_ehgmSymbol_le`, `norm_ehgmSymbol_le_of_large`, `exists_bound_ehgmSymbol`, `norm_ehgmSymbol_le_bound`, `ehgmSymbol_small` |
| (EHGM.15) `M h_λ = f_λ` for every `λ > 0`; `M` commutes with dilations; uniqueness: a bounded dilation-equivariant `A` with `A h_1 = f_1` equals `M`; `M` injective, dense range, range not closed, not bounded below | `ehgmTransport_sixth`, `mellinMultiplier_halfLineDilation`, `ehgmTransport_halfLineDilation`, `eq_ehgmTransport_of_equivariant`, `mellinMultiplier_injective`, `denseRange_mellinMultiplier`, `not_boundedBelow_mellinMultiplier`, `not_isClosed_range_mellinMultiplier`, `ehgmTransport_properties` |
| (EHGM.16)–(EHGM.17) `M = U|M|`, `⟨Mu,Mv⟩ = ⟨|M|u,|M|v⟩` | `measurable_norm_symbol`, `measurable_phase_symbol`, `norm_phase_symbol`, `mellinMultiplier_eq_phase_comp_modulus`, `inner_phase_mellinMultiplier`, `inner_mellinMultiplier_eq_modulus`, `ehgmTransport_eq_phase_comp_modulus`, `inner_ehgmTransport_eq_modulus` |
| (EHGM.18)–(EHGM.19) `Q = M^*M - I`, `⟨h_λ,Qh_λ⟩ = 0` | `ehgmAnomaly`, `re_inner_ehgmAnomaly`, `inner_ehgmAnomaly_sixth` |
| (EHGM.20) `|m(0)|² = (81π/92)(9/8-1/√2) > 243/230 > 1`; `Q` indefinite | `norm_sq_ehgmSymbol_zero`, `one_lt_norm_sq_ehgmSymbol_zero`, `ehgmAnomaly_indefinite` |
| (EHGM.21) `W_H = M W_6`, `K = C + D`, `D = W_6^*QW_6` | `hellingerSynthesis_eq`, `relativeAnomaly`, `hellingerGram_eq_add` |
| (EHGM.22) `D` self-adjoint, `𝒮₁`, `D(i,i) = 0`, `Tr D = 0` | `isHilbertSchmidt_capacitySynthesis`, `relativeAnomaly_memSchattenClass`, `adjoint_ehgmAnomaly`, `adjoint_relativeAnomaly`, `inner_single_relativeAnomaly`, `relativeAnomaly_diagonal`, `opTrace_relativeAnomaly` |
| (EHGM.23) `⟨h_λ,h_{2λ}⟩ = 512/729`, `⟨f_λ,f_{2λ}⟩ = 7794√2/14375`; `D ≠ 0`; `D` indefinite | `two_rpow_neg_three_halves_eq`, `inner_sixth_double`, `inner_hellinger_double`, `relativeAnomaly_ne_zero`, `relativeAnomaly_indefinite` |
| (EHGM.24) conservation identity | `hellingerGram_eq_add` together with `apertureCapacity_traceClass`, `hellingerGram_traceClass`, `relativeAnomaly_diagonal`, `opTrace_relativeAnomaly`, `relativeAnomaly_indefinite` |
| (EHGM.25) `T_H = Φ⊗K`, `Δ_rel = T_H - T_6 = Φ⊗D` entrywise | `thetaHellingerFrame`, `norm_sq_thetaHellingerFrame`, `summable_norm_sq_thetaHellingerFrame`, `thetaHellinger`, `inner_single_thetaHellinger`, `relativeThetaAnomaly`, `inner_single_relativeThetaAnomaly` |
| (EHGM.26) `Tr T_H = Tr T_6 = ` budget, `Δ_rel ∈ 𝒮₁`, `Tr Δ_rel = 0` | `thetaHellinger_traceClass`, `thetaCapacity_traceClass`, `relativeThetaAnomaly_traceClass` |
| (EHGM.27) `T_6 = T_H - Δ_rel` | `thetaCapacity_eq_sub` |
| (EHGM.28) spectral floor: `λ_i ≥ log 2 > 1/2`; `e^{μt}f_λ(t) → 0` for `μ < λ` and `→ ∞` for `μ > λ`; `M(W_6e_i) = W_He_i` decays faster than `e^{-at}` for every `a < log 2`; no profile of rate below `log 2` is eventually a multiple of `f_{λ_i}` | `half_lt_log_two_le_eulerClock`, `tendsto_exp_mul_hellingerProfile_of_lt`, `tendsto_exp_mul_hellingerProfile_of_gt`, `ehgmTransport_preserves_spectral_floor`, `not_eventuallyEq_hellingerProfile_of_slow_rate` |

Not claimed: §8's Xi landing and residual-boundary theorem, and the rate-changing arrow `R` in (EHGM.28). The card itself states these as open.

## Log

- 2026-10-03 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
