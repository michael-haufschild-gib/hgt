# Double-Hellinger nuclear homotopy-jet law

- **ID:** ULF-DHNJ-001
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parents:** `ULF-SCIN-001`, `ULF-SKPM-001`
- **Statement:** every normalized even phase jet of the prime-mixed nuclear wall is exactly the
  product of two source-forced Euler Hodge--Beta responses separated by one half-density grade.

## 1. Big-picture law

The new object is not only a trace-one operator. It carries a canonical noncommutative phase
derivation, and the complete energy tower of that derivation is an archimedean Hodge response.
The match is forced at every order:

```text
prime Stokes/Burnol formation
  --Kummer commutator jets-->
compact Cayley-contrast moment law
  = two source-forced Euler odd-Hodge responses.
```

This is stronger than matching a scalar, sign, or low jet. One probability law and one
half-density coface determine the whole infinite tower. No zero, Xi divisor, fitted ordinate, or
RH premise occurs.

## 2. Nuclear homotopy jets

Let `A` be the exponential-wall operator of `ULF-SCIN-001` and let `X` be multiplication by the
wall coordinate on `L2((0,infinity),exp(-x)dx)`. Its Kummer orbit is

```text
A_tau=exp(i tau X) A exp(-i tau X).
```

Write `ad_X(B)=XB-BX` initially on bounded compactly supported vectors. Every iterated
commutator of `A` has a unique Hilbert--Schmidt extension, and

```text
||ad_X^n(A)||_2^2
 = 48 (2n)!/((2n+3)(2n+5)(2n+7)).                  (DHNJ.1)
```

Define the factorially normalized homotopy energy

```text
m_n=||ad_X^n(A)||_2^2/((2n)! ||A||_2^2).            (DHNJ.2)
```

Since `||A||_2^2=16/35`,

```text
m_n=105/((2n+3)(2n+5)(2n+7)),
m_0=1,
m_(n+1)/m_n=(n+3/2)/(n+9/2).                        (DHNJ.3)
```

**Proof.** On the compactly supported core, the kernel of `ad_X^n(A)` is
`(x-y)^n kappa(x,y)`. Its square is integrable because polynomial growth is absorbed by the
exponential carrier, so this kernel defines the asserted unique Hilbert--Schmidt extension. Its
squared norm is the `2n`-th frequency derivative of the phase overlap:

```text
||ad_X^n(A)||_2^2=(-1)^n C^(2n)(0).
```

Writing `C(tau)=F(tau^2)`, `ULF-SKPM-001` gives

```text
(-1)^n F^(n)(0)=48n!/((2n+3)(2n+5)(2n+7)).
```

The chain rule at zero gives
`C^(2n)(0)=(2n)!F^(n)(0)/n!`, proving `(DHNJ.1)--(DHNJ.3)`. QED.

## 3. Double-Hellinger factorization

Let

```text
h(s)=-B(s+1/2,3/2)
    =-Gamma(s+1/2)Gamma(3/2)/Gamma(s+2).             (DHNJ.4)
```

This is not an introduced special function: corpus theorem
`eulerPrimitiveBoundaryHodgeBetaColumn_eq_gammaRatio` proves that `h(s)` is exactly the common
Laplace test applied to the forced odd-Hodge conjugate of the elementary Euler head source.

For every `n>=0`,

```text
m_n = h(n+1)h(n+5/2)/(h(1)h(5/2)).                  (DHNJ.5)
```

Equivalently, if

```text
q(s)=(s+1/2)/(s+2),
```

the unique horizontal coefficient of the corpus Hellinger--Beta coface, then

```text
m_(n+1)/m_n=q(n+1)q(n+5/2).                          (DHNJ.6)
```

**Proof.** The beta multiplication identity

```text
B(a,b)B(a+b,c)=B(a,b+c)B(b,c)
```

with `a=n+3/2` and `b=c=3/2` gives

```text
B(n+3/2,3/2)B(n+3,3/2)
  =B(n+3/2,3)B(3/2,3/2).
```

Divide by the same identity at `n=0`. The result is
`B(n+3/2,3)/B(3/2,3)=m_n`, proving `(DHNJ.5)`. The source-forced recurrence
`h(s+1)=q(s)h(s)` gives `(DHNJ.6)`. QED.

The separation `3/2` between the two test grades is not tunable. It is exactly the second beta
parameter of the odd-Hodge half-density. Probabilistically, three independent
`Gamma(3/2)` chambers give a `Dirichlet(3/2,3/2,3/2)` simplex; one barycentric coordinate has
law `Beta(3/2,3)`. Thus the hidden contrast of the nuclear homotopy is the boundary coordinate
left after two successive half-density sewings.

## 4. Positive history flux and exact reconstruction

Define the adjacent homotopy flux

```text
w_n=m_n-m_(n+1)
   =630/((2n+3)(2n+5)(2n+7)(2n+9)).                 (DHNJ.7)
```

Then

```text
w_n>0,
sum_(n>=0) w_n=1,
m_n=sum_(k>=n) w_k.                                  (DHNJ.8)
```

**Proof.** Subtract the two rational formulas in `(DHNJ.3)`. Positivity is immediate. Every
finite sum telescopes to `m_0-m_(N+1)`; the explicit denominator gives `m_(N+1)->0`. The tail
identity follows by starting the same telescope at `n`. QED.

Equivalently, conditional on the Cayley contrast `Lambda`, the history lifetime is geometric:

```text
w_n=E[(1-Lambda)Lambda^n].                           (DHNJ.9)
```

Thus the integral unit is not a constant charge attached to every vanishing Hodge grade. It is
the total positive flux through the open history, and every phase jet is reconstructed from the
unspent tail. This is the exact mechanism missed by one-marginal coface closure.

## 5. What this proves about the object `T`

The integral--nuclear defect `mathsf T` now has four coordinate-free pieces of structure:

1. integral orientation: one-sided trace `+1/-1`;
2. prime mixing: every cross-prime Burnol entry survives;
3. nuclear wall transport: fixed-chart strong loss but comoving trace-norm landing;
4. Hodge-generated homotopy: every Kummer commutator energy is the double odd-Hodge response
   `(DHNJ.5)`.

The fourth property narrows the source model class. A generic trace-one positive contraction, a
rank-one lift, or an arbitrary compact homotopy does not satisfy `(DHNJ.5)`.

## 6. Exact completion consequence and remaining gate

Corpus theorem `tendsto_fourier_sum_range_hellingerBetaMobiusThetaCompletePhysicalCoface` already
transports one normalized Hellinger--Beta coface from literal Möbius--theta source to the Xi
`L2` profile. Equation `(DHNJ.5)` predicts the missing completion theorem precisely:

> theta/Poisson completion must transport the **correlated two-grade Hodge state** at grades
> `n+1` and `n+5/2`, preserving its positive flux `(DHNJ.7)` and tail reconstruction `(DHNJ.8)`.

If proved on a correlated two-grade carrier before marginal closure, it would transport the
entire marked phase profile, not merely its trace. The source profile is a strict completely
monotone decoherence law; an off-line recurrent completion class cannot preserve it indefinitely.
Combined with the existing integral escape multiplicity and sub-unit source budget, this is the
intended relative-index selection route.

This card does **not** assert that completed transport. Corpus hostile audit proves more than an
open gap: ordinary completed adjacent-coface closure saturates the entire two-channel space off
centre, zero recovery does not descend to the central quotient, and a nonzero charge conserved
along factorially vanishing grades forces a nonclosed graph. Therefore the required completion
cannot be quotient injectivity or a one-marginal closed boundary. It must retain the correlated
two-grade provenance before closure and transport the **decaying positive coboundary** `w_n`, not
a constant scalar charge. Equality `(DHNJ.5)` alone cannot do this.

## 7. Corpus audit

Checked before formulation:

- `hellingerHodgeBetaColumnComplex_add_one` proves the unique one-step coefficient `q(s)`;
- `eulerPrimitiveBoundaryHodgeBetaColumn_eq_gammaRatio` makes each factor a literal Euler-source
  odd-Hodge response;
- `hellingerBetaCovariantCoface_coefficient_unique` rules out changing its coefficient;
- `HellingerBetaMobiusThetaCofinalCoface` supplies physical theta-source/Fourier landing for one
  coface;
- `hellingerGammaCompletedAdjacentCofaceClosedSpan_eq_top` and
  `hellingerGammaCompletedCofaceRecovery_zero_not_quotient_descending` kill ordinary quotient
  descent;
- `hellingerGammaCompletedGradedCoface_not_isClosed_graph` kills any one-marginal closed graph
  carrying constant nonzero endpoint charge;
- corpus search found no declaration equating nuclear phase jets with the normalized product
  `(DHNJ.5)`.

## 8. Lean status

Paper theorem only. Constituent Hodge--Beta recurrence, source realization, zero-frequency cubic
energy, and phase-free wall law are Lean-proved. The all-order commutator formula and exact
double-column factorization have not yet been assembled in one Lean module.

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.CubicWallJetEnergies`, `GaloisForLFunctions.HTGeometry.CubicWallHodgeBetaFlux`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Modules `GaloisForLFunctions.HTGeometry.CubicWallJetEnergies` (31 constants) and `GaloisForLFunctions.HTGeometry.CubicWallHodgeBetaFlux` (32), both axiom-audit clean. They reuse the EWHC wall operator and Burnol ratio kernel, the SKPM profile layer (`phaseResponse`, `phaseResponse_jet_zero`, `phaseBetaLaw`, `integral_phaseBetaLaw`, `integral_Ioi_eq_cayley`), `SqIntKernel`, and the corpus Euler odd-Hodge column `eulerPrimitiveBoundaryHodgeBetaColumn` with its Gamma evaluation `eulerPrimitiveBoundaryHodgeBetaColumn_eq_gammaRatio`. `X` is multiplication by the wall coordinate on `Lp ℂ 2 (expMeasure 1)`; its core is the space of functions carried by a bounded window (`IsWindowCarried`).

| Claim | Lean declaration |
|-|-|
| §2 kernel of `adⁿ_X(A)` is `(x-y)ⁿκ(x,y)`; it is Hilbert–Schmidt | `jetKernel`, `jetKernel_zero_op`, `lintegral_lintegral_jet` |
| §2 commutator recursion on the core: `K_{n+1} f = X K_n f - K_n X f`, core stable under `X` | `jetKernel_succ_op_ae`, `coordMul`, `coordMul_ae`, `memLp_coordMul`, `isWindowCarried_coordMul` |
| §2 unique extension: a bounded operator agreeing with `K_n` on the core is `K_n` | `eq_jetKernel_op_of_eqOn_core`, `tendsto_windowTruncation`, `isWindowCarried_windowTruncation` |
| (DHNJ.1) `‖adⁿ_X(A)‖²₂ = 48(2n)!/((2n+3)(2n+5)(2n+7))` | `hsNormSq_jetKernel`, `integral_coherence_mul_sub_pow`, `integral_pow_mul_one_sub_sq_cube`, `integral_Ioo_neg_one_one_of_even` |
| §2 proof link: `‖K_n‖²₂ = (2n)!/n! · (-1)ⁿF⁽ⁿ⁾(0)` | `hsNormSq_jetKernel_eq_phaseJet` |
| (DHNJ.2)–(DHNJ.3) `m_n = 105/((2n+3)(2n+5)(2n+7))`, `m_0 = 1`, `m_{n+1}/m_n = (n+3/2)/(n+9/2)` | `homotopyEnergy`, `homotopyEnergy_eq`, `homotopyEnergy_zero`, `homotopyEnergy_succ_div` |
| (DHNJ.4) `h(s) = -B(s+1/2,3/2) = -Γ(s+1/2)Γ(3/2)/Γ(s+2)` (corpus source-forced column) | `hodgeBetaColumn_eq_neg_gammaBeta`, `gammaBeta` |
| (DHNJ.5) `m_n = h(n+1)h(n+5/2)/(h(1)h(5/2))`; `m_n = B(n+3/2,3)/B(3/2,3)` | `homotopyEnergy_eq_hodgeBeta`, `hodgeBetaColumn_product`, `homotopyEnergy_eq_gammaBeta` |
| Beta multiplication identity `B(a,b)B(a+b,c) = B(a,b+c)B(b,c)` | `gammaBeta_mul_gammaBeta` |
| (DHNJ.6) `m_{n+1}/m_n = q(n+1)q(n+5/2)`, `h(s+1) = q(s)h(s)` | `hodgeCoface`, `homotopyEnergy_succ_div_eq_coface`, `hodgeBetaColumn_succ` |
| (DHNJ.7) `w_n = 630/((2n+3)(2n+5)(2n+7)(2n+9))` | `homotopyFlux`, `homotopyFlux_eq` |
| (DHNJ.8) `w_n > 0`, `∑ w_n = 1`, `m_n = ∑_{k≥n} w_k` | `homotopyFlux_pos`, `hasSum_homotopyFlux`, `hasSum_homotopyFlux_tail`, `tendsto_homotopyEnergy` |
| (DHNJ.9) `w_n = E[(1-Λ)Λⁿ]`, and `m_n = E[Λⁿ]` for `Λ ~ Beta(3/2,3)` | `homotopyFlux_eq_beta`, `homotopyEnergy_eq_beta_moment`, `integral_sqrt_mul_eq` |
| Summary | `double_hellinger_homotopy_law` |

§1, the Dirichlet reading of `Beta(3/2,3)` in §3, §5 and §7 are interpretation. The card states that the completed two-grade transport of §6 is not asserted.

## Log

- 2026-09-29 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
