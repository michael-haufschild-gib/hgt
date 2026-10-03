# Euler--Stokes aperture capacity and singular sixth-boundary law

- **ID:** ULF-ESAC-001
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parents:** ULF-PCOB-001, ULF-TM6H-001, ULF-PHFI-001;
  `cubic-ward-hellinger-completed-source-trace-incidence`;
  `HedenmalmStokesOrientedFirstTraceQuantizedJump`,
  `XiWardCubicLogMomentEulerSource`, `RoutePPrimitiveCollisionSubquantum`
- **Status:** `[PAPER-PROVED] [BRIDGE] [SCALAR IDENTITY PRE-EXISTING] [LEAN-PROVED]`
- **Surviving RH edge:** construct the actual anomaly-subtracted Euler--theta completion as a
  positive, capacity-nonincreasing transport of the singular sixth boundary form; bounded
  multiplicative transport is already impossible.

## 1. Higher-law interpretation

Completion is not fundamentally a map from one bounded operator to another.  Literal Euler
formation creates an unbounded boundary charge.  Aperture evolution regularizes that charge into
a nuclear observer, and the amount of regularization is a conserved capacity.  A completion may
fracture multiplication, but it must preserve the singular boundary form from which the observer
is uniquely recovered.

The corpus forces one exact instance.  Lift the oriented Stokes current from primes to every
literal Euler prime power, retain the cubic Gamma coherence, multiply by the already forced
covariant aperture factor, and integrate the open aperture history.  The result is one positive,
prime-mixed, depth-mixed trace-class operator whose diagonal and trace are exactly the complete
primitive collision budget.  Its sixth Sylvester boundary is rank one on the algebraic core but
has a source vector outside `ell2`.  Thus finite observed capacity and noncompact source history
are two faces of one law.

```text
Euler prime powers + oriented Stokes current
  -- cubic Gamma coherence --> moving S1 Gram A_delta
  -- covariant aperture integral --> fixed S1 capacity C
  -- sixth Sylvester boundary --> non-ell2 rank-one source charge
  -- theta Mellin-six flux --> integral--nuclear object T_cap = Phi tensor C.
```

This narrows the completion model class.  A bounded source generator or bounded multiplicative
map cannot be the missing mechanism.  The admissible object is an inverse-boundary regularization:
bounded/nuclear after six inverse source derivatives, singular before them.

## 2. Corpus audit before formulation

Required Lean-corpus searches for `primitive collision cubic trace budget`, `Stokes current 8 d
log p`, `Cauchy coherence power six Gamma vector`, `Sylvester sixth power rank one`, and `prime
harmonic not summable` found:

- `gammaSewnMobiusApertureStokesOrientedFirstTracePrimeTerm d p`
  is `8 d log(p) p^(-(1+2d))` on the right aperture;
- `gammaSewnMobiusApertureStokesCovariantFirstTracePrimeMoment` is exactly `d` times that
  oriented term: the extra aperture factor below is forced, not selected;
- `xiGammaEulerPrimitiveCubicLogMomentWeight (p,e)` is
  `115/[864 p^(e+1)(e+1)^3 log(p)^2]`, is summable, and its total is
  `routePPrimitiveCollisionCubicTraceBudget`;
- `routePPrimitiveCollisionCubicTraceBudget_lt_quantum` proves that total is strictly below
  `115/108`, the least strict-right cubic charge;
- ULF-PCOB-001 constructs the cubic prime heat Gram and its cubic Sylvester birth at each positive
  aperture, but only on the valuation-one prime face and after normalization;
- ULF-TM6H-001 proves that the independent theta/Hodge history is a forced Mellin shift by six;
- ULF-PHFI-001 proves that no nonzero divisor horizon can be a bounded multiplicative image of the
  faithful compact formation operator.
- P-G177-A in `cubic-ward-hellinger-completed-source-trace-incidence` already proves the scalar
  identity `(115/1728) integral t^2[-zeta'/zeta](1+t)dt` and constructs a different full
  prime-power Hellinger Gram with the same diagonal and trace.

No checked declaration takes the **operator-valued** covariant aperture integral of the cubic
all-prime-power Stokes lift, proves that it changes Cauchy order three to order six, or proves its
singular sixth boundary.  The scalar trace identity below is therefore a new Stokes derivation and
interpretation of P-G177-A `(A8)`, not a new scalar equality.  The existing Stokes current is
valuation one; the Euler lift below remains part of the theorem.

## 3. Literal Euler-depth Stokes lift

Let

```text
I={(p,e): p prime, e>=0},
r_i=e+1,  n_i=p^r_i,  lambda_i=log(n_i)=r_i log(p).
```

For aperture `delta>0`, define the unsigned right current

```text
j_delta(i)=8 delta log(p) n_i^(-(1+2 delta)).          (ESAC.1)
```

At `e=0`, this is exactly the corpus's oriented Stokes prime term on the right ray.  The extension
is forced by literal Euler formation: the coefficient of every `p^r` in `-zeta'/zeta` is
`Lambda(p^r)=log p`, while the radial clock is `log(p^r)`.  In particular,

```text
sum_(e>=0) j_delta(p,e)
 =8 delta log(p)/(p^(1+2delta)-1),
sum_i j_delta(i)
 =8 delta sum_(n>=2) Lambda(n)n^(-(1+2delta)).         (ESAC.2)
```

Both sums are finite for every `delta>0`.  The covariant Stokes energy is
`delta j_delta(i)`: this is precisely the signed-current-to-positive-moment multiplication already
proved on the valuation-one face, now applied coefficientwise to the literal Euler lift.

## 4. Moving cubic formation

For positive `lambda,mu`, put

```text
k_3(lambda,mu)=[2 sqrt(lambda mu)/(lambda+mu)]^3.     (ESAC.3)
```

The functions

```text
g_lambda(t)=2 lambda^(3/2) t exp(-lambda t)
```

have unit norm in `L2(0,infinity)` and inner product `k_3(lambda,mu)`.  Therefore

```text
A_delta(i,j)=sqrt(j_delta(i)j_delta(j))
               k_3(lambda_i,lambda_j)                (ESAC.4)
```

is a positive Gram operator.  Its diagonal is `j_delta`, so `(ESAC.2)` gives

```text
A_delta is S1,
Tr(A_delta)=||A_delta||_1=sum_i j_delta(i).           (ESAC.5)
```

Every matrix entry is strictly positive.  Thus prime and valuation depths are mixed before any
zero, ordinate, or divisor is supplied.

## 5. Exact aperture-capacity identity

Define the aperture capacity in trace norm by

```text
C=(115/1728) integral_(0,infinity) delta A_delta ddelta. (ESAC.6)
```

For `lambda>0`,

```text
integral_0^infinity delta^2 exp(-2 lambda delta) ddelta
 =1/(4 lambda^3).                                    (ESAC.7)
```

Consequently, label by label,

```text
(115/1728) integral_0^infinity delta j_delta(p,e) ddelta
 =115/[864 p^(e+1)(e+1)^3 log(p)^2]
 =xiGammaEulerPrimitiveCubicLogMomentWeight(p,e).     (ESAC.8)
```

After the substitution `t=2delta` and summation over labels, this is exactly P-G177-A `(A8)`.
The new content begins with retaining the full moving cubic Gram before integration.

Tonelli and the corpus's summability theorem give

```text
(115/1728) integral delta ||A_delta||_1 ddelta
 =sum_i xiGammaEulerPrimitiveCubicLogMomentWeight(i)<infinity. (ESAC.9)
```

Hence `(ESAC.6)` exists as an `S1` Bochner integral.

For completeness, strong measurability is not being hidden here.  On every compact aperture
interval `[a,b]` with `a>0`, the synthesis maps with columns
`sqrt(j_delta(i))g_(lambda_i)` vary continuously in Hilbert--Schmidt norm by dominated
convergence, dominated by the summable `log(p)n_i^(-(1+2a))` tail.  The inequality
`||W*W-V*V||_1 <=(||W||_2+||V||_2)||W-V||_2` makes `delta -> A_delta` trace-norm continuous
there.  Equation `(ESAC.9)` supplies global trace-norm integrability.

Direct integration of `(ESAC.4)` gives

```text
C(i,j)=(230/27)
  sqrt(log(p)log(q)) (lambda_i lambda_j)^(3/2)
  /[sqrt(n_i n_j)(lambda_i+lambda_j)^6].             (ESAC.10)
```

Equivalently, with

```text
s_i=xiGammaEulerPrimitiveCubicLogMomentWeight(i),
k_6(lambda,mu)=[2 sqrt(lambda mu)/(lambda+mu)]^6,
```

one has

```text
C(i,j)=sqrt(s_i s_j) k_6(lambda_i,lambda_j).          (ESAC.11)
```

Indeed

```text
h_lambda(t)=sqrt(8/15) lambda^3 t^(5/2)exp(-lambda t)
```

has unit norm and Gram `k_6`.  This proves independently that `C` is positive and trace class.
Its diagonal is `s_i`, and therefore

```text
boxed: Tr C=||C||_1
 =routePPrimitiveCollisionCubicTraceBudget <115/108. (ESAC.12)
```

This does not identify `C` with the corpus's moving-ordinate collision kernel.  It does something
different and source-side: it lifts that kernel's exact diagonal capacity to a canonical,
pre-divisor, fully prime-power-mixed nuclear operator.

## 6. Singular sixth-boundary theorem

Let `L` be the diagonal source clock `L e_i=lambda_i e_i` and
`S_L(X)=LX+XL` on the finite-support core.  Put

```text
c_i=sqrt(log p) lambda_i^(3/2)/sqrt(n_i).             (ESAC.13)
```

Multiplying `(ESAC.10)` by `(lambda_i+lambda_j)^6` proves the exact form identity

```text
boxed: S_L^6(C)=(230/27)|c><c|                       (ESAC.14)
```

on finite-support vectors.  This source charge is not a bounded rank-one operator.  On the
valuation-one face,

```text
sum_p |c_(p,0)|^2=sum_p (log p)^4/p=infinity,         (ESAC.15)
```

by Euler's divergence of `sum_p 1/p`.  Thus `c` is not in `ell2`, and the quadratic form on the
right of `(ESAC.14)` is unbounded on the unit sphere of the algebraic core.

There is nevertheless a unique bounded matrix solution of `(ESAC.14)`: every entry is forced to
be `(ESAC.10)`, hence the solution is `C`.  It is not merely bounded but positive `S1`.  Six
inverse Sylvester derivatives therefore turn a non-Hilbert source charge into finite nuclear
capacity.

**Bounded-boundary no-go.** No bounded rank-one source vector can generate the complete Euler
aperture capacity through the sixth boundary law.  Replacing `c` by an `ell2` vector changes the
depth-zero prime density and loses literal Euler formation.  The noncompact boundary is forced,
not a removable defect of presentation.

## 7. Theta fusion: one bi-six integral--nuclear object

Let `Phi=diag(w_m)` be the theta Mellin-six history flux of ULF-TM6H-001.  It is positive `S1` and
`Tr Phi=1`.  Define

```text
T_cap=Phi tensor C.                                  (ESAC.16)
```

Then

```text
T_cap>=0,  T_cap is S1,
Tr(T_cap)=routePPrimitiveCollisionCubicTraceBudget<115/108,
S_(I tensor L)^6(T_cap)
  =(230/27) Phi tensor |c><c|                        (ESAC.17)
```

as a finite-core form.  Its history-tail trace is

```text
Tr((projection_[m,infinity) tensor I)T_cap)
 =m_m routePPrimitiveCollisionCubicTraceBudget.      (ESAC.18)
```

Thus two independently forced sixes meet in one object:

- archimedean theta completion supplies Mellin displacement six and integral history flux;
- covariant aperture integration turns cubic prime coherence into a sixth-order Cauchy kernel;
- literal Euler formation supplies the non-`ell2` sixth boundary charge;
- Route P reads the nuclear trace as its complete primitive collision capacity.

No equality of the two parent mechanisms is assumed.  Their tensor compatibility and common
order are consequences of the explicit formulas.

## 8. What this changes about the RH problem

Before this theorem, P-G177-A had already made the complete prime-power budget the trace of a
canonical Hellinger Gram.  The new result produces a second, aperture-generated gauge with the
same diagonal and trace but an order-six Gamma kernel, and identifies it as the unique nuclear
inverse of an explicit singular boundary charge.  ULF-EHGM-001 proves the exact relative Mellin
transport and zero-trace anomaly between the two gauges.

The exact remaining theorem is no longer an unspecified source-budget/resolvent comparison.  It
is the following form-transport statement:

> Literal Euler--theta completion, after subtraction of its universal metric anomaly, transports
> the finite-core boundary form `(230/27) Phi tensor |c><c|` to completed Xi cubic Loewner energy,
> is capacity-nonincreasing under sixth inverse regularization, and has zero residual completion
> boundary.

If proved before divisor specialization, `(ESAC.12)` would bound total completed strict-right
energy below `115/108`, whereas one strict-right copy costs at least `115/108`; hence none exists.
Functional equation then excludes strict-left copies and proves RH.

ULF-PHFI-001 already forbids interpreting this transport as a bounded multiplicative homomorphism.
The viable completion is form-valued and nonmultiplicative: it preserves the singular boundary
charge and computes its multiplicativity fracture.  This is a strict narrowing of the source
model class, not a renamed request for source faithfulness.

The form-transport theorem remains open.  Nothing here asserts RH.

## 9. Hostile literature and significance audit

1. **Time-weighted Gramians:** established control theory.  Monomial trajectory weighting and
   recursive Lyapunov relations occur in Schelfhout--De Moor (1995), Sreeram (2002), and the
   [current empirical-Gramian framework](https://gramian.de/himpe23-emgr599.pdf).  No novelty is
   claimed for integrating `delta A_delta`.
2. **Cauchy/Gamma Gram kernels and Schatten ideals:** established operator theory.  Generalized
   Hilbert matrices and their Schatten properties are
   [well studied](https://arxiv.org/abs/1309.6125); no novelty is claimed for positivity of `k_6`.
3. **Corpus collision check:** P-G177-A already contains the summed scalar form of `(ESAC.8)`.
   No existing declaration or paper card contains the operator integral `(ESAC.6)`, the
   cubic-to-sixth kernel law `(ESAC.11)`, or the non-`ell2` sixth boundary
   `(ESAC.14)--(ESAC.15)`.
4. **Exact surviving residue:** the corpus-specific equality between literal Euler-depth Stokes
   covariance, complete primitive collision capacity, theta history flux, and singular
   sixth-boundary regularization.  Classification: `[BRIDGE]`, not a claim that its ingredients
   define an externally unprecedented subject.
5. **Falsifier:** if the actual anomaly-subtracted completion does not preserve the form boundary,
   or preserves it only after a divisor is supplied, this object explains source capacity but
   gives no RH selection.

## 10. Lean status

Every numbered claim (ESAC.1)–(ESAC.18), including the Schatten-one Bochner integral (ESAC.6), the
singular sixth boundary and the bounded-boundary no-go, is formalized unconditionally; see the Lean
certificate below.

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.EulerStokesDepthLift`, `GaloisForLFunctions.HTGeometry.EulerStokesApertureCapacity`, `GaloisForLFunctions.HTGeometry.EulerStokesThetaCapacity`, `GaloisForLFunctions.RHTower.XiWardCubicLogMomentEulerSource`, `GaloisForLFunctions.RHTower.RoutePPrimitiveCollisionSubquantum`, `GaloisForLFunctions.HTGeometry.AbelianZetaGas.VonMangoldtEuler`, `GaloisForLFunctions.HTGeometry.PoissonGammaCoherentLadder`, `GaloisForLFunctions.HTGeometry.SquareSummableFrameSynthesis`, `GaloisForLFunctions.HTGeometry.SchattenOneBanach`, `GaloisForLFunctions.HTGeometry.SourceStokesNormalizedChildUnit`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Modules `GaloisForLFunctions.HTGeometry.EulerStokesDepthLift`, `GaloisForLFunctions.HTGeometry.EulerStokesApertureCapacity`
and `GaloisForLFunctions.HTGeometry.EulerStokesThetaCapacity` (new), on the corpus modules
`GaloisForLFunctions.RHTower.XiWardCubicLogMomentEulerSource` (weights `s_i`, summability),
`GaloisForLFunctions.RHTower.RoutePPrimitiveCollisionSubquantum` (budget `< 115/108`),
`GaloisForLFunctions.HTGeometry.AbelianZetaGas.VonMangoldtEuler` (Euler form of `Σ Λ(n) n^{-σ}`),
`GaloisForLFunctions.HTGeometry.PoissonGammaCoherentLadder` (coherent vectors, Gram `k_m`),
`GaloisForLFunctions.HTGeometry.SquareSummableFrameSynthesis`, `GaloisForLFunctions.HTGeometry.SchattenOneBanach`
(the Schatten-one Banach space), `GaloisForLFunctions.HTGeometry.SourceStokesNormalizedChildUnit`
(`‖V*V − W*W‖₁` bound) and the theta history flux `PrimeHodgeHistory.w`; all `lake env lean` clean, built,
axiom audit `[propext, Classical.choice, Quot.sound]` only.  Labels `I = Nat.Primes × ℕ`, `n_i = p^{e+1}`,
`λ_i = xiGammaEulerPrimitiveLogFrequency i`, `s_i = xiGammaEulerPrimitiveCubicLogMomentWeight i`.

| Claim | Lean declaration |
|-|-|
| (ESAC.1) `j_δ(i) = 8δ log p n_i^{-(1+2δ)}`; depth zero = oriented Stokes term; `δ j_δ` = covariant moment | `eulerStokesCurrent`, `eulerStokesCurrent_pos`, `eulerStokesCurrent_eq_exp`, `eulerStokesCurrent_depth_zero`, `mul_eulerStokesCurrent_depth_zero`, `xiGammaEulerPrimitiveLogFrequency_eq` |
| (ESAC.2) `Σ_e j_δ(p,e) = 8δ log p/(p^{1+2δ}−1)`, `Σ_i j_δ = 8δ Σ_n Λ(n) n^{-(1+2δ)}`, finite | `hasSum_eulerStokesCurrent_depth`, `rpow_eulerValuation`, `eulerStokesCurrent_le`, `summable_eulerStokesCurrent`, `tsum_eulerStokesCurrent` |
| (ESAC.3)–(ESAC.4) unit `g_λ` with Gram `k₃`; `A_δ(i,j) = √(j_δ(i)j_δ(j)) k₃(λ_i,λ_j)` | `eulerStokesFrame`, `norm_sq_eulerStokesFrame`, `eulerStokesSynthesis`, `eulerStokesGram`, `cubicCoherence`, `inner_single_eulerStokesGram` |
| (ESAC.5) `A_δ ≥ 0`, `𝒮₁`, `Tr A_δ = ‖A_δ‖₁ = Σ j_δ`, entries `> 0` | `eulerStokesGram_traceClass`, `inner_single_eulerStokesGram_pos` |
| (ESAC.6) `C = (115/1728)∫ δ A_δ dδ` exists as an `𝒮₁` Bochner integral: trace-norm continuity on `(0,∞)` via `‖W*W − V*V‖₁ ≤ (‖W‖₂+‖V‖₂)‖W−V‖₂` and dominated convergence of `‖W_δ − W_δ₀‖₂²` | `squareSummableSynthesis_sub`, `eulerStokesCurrent_le_four_mul`, `continuous_eulerStokesCurrent`, `hsNormSq_eulerStokesSynthesis_sub`, `tendsto_hsNorm_eulerStokesSynthesis_sub`, `eulerStokesGramS1`, `eulerStokesGramS1_of_pos`, `norm_eulerStokesGramS1`, `continuousOn_eulerStokesGramS1`, `eulerApertureIntegrand`, `integrableOn_eulerApertureIntegrand`, `apertureCapacity` |
| (ESAC.7)–(ESAC.9) `∫ δ² e^{-2λδ} = 1/(4λ³)`; `(115/1728)∫ δ j_δ(i) dδ = s_i`; total = budget; `∫ ‖(115/1728)δA_δ‖₁ = budget` | `integral_sq_mul_exp_neg_two_mul`, `integral_mul_eulerStokesCurrent`, `tsum_integral_mul_eulerStokesCurrent`, `integrableOn_mul_eulerStokesCurrent`, `lintegral_norm_eulerApertureIntegrand` |
| (ESAC.10) `C(i,j) = (230/27)√(log p log q)(λλ')^{3/2}/(√(nn')(λ+λ')⁶)` | `capacityEntry`, `schattenOneEntry`, `schattenOneEntry_apply`, `sqrt_eulerStokesCurrent_mul`, `schattenOneEntry_apertureCapacity` |
| (ESAC.11) `C(i,j) = √(s_i s_j) k₆(λ_i,λ_j)`; `C` = Gram of unit `h_λ` | `capacityFrame`, `norm_sq_capacityFrame`, `capacitySynthesis`, `capacityGram`, `sqrt_xiGammaEulerPrimitiveCubicLogMomentWeight`, `coherence_pow_eq`, `inner_single_capacityGram`, `apertureCapacity_eq_capacityGram` |
| (ESAC.12) `C ≥ 0`, `Tr C = ‖C‖₁ = ` budget `< 115/108` | `apertureCapacity_traceClass` |
| (ESAC.13)–(ESAC.14) `c_i = √(log p)λ_i^{3/2}/√n_i`; `S_L⁶(C) = (230/27)|c⟩⟨c|` on the basis; unique bounded solution | `sixthBoundaryVector`, `sixthBoundary_law`, `sixthBoundary_law_entry`, `eq_apertureCapacity_of_sixthBoundary_law` |
| (ESAC.15) `Σ_p c_{(p,0)}² = Σ (log p)⁴/p = ∞`; form unbounded on the unit sphere of the core | `sq_sqrt_mul_sqrt_pow_three_div`, `sixthBoundaryVector_sq_depth_zero`, `not_summable_sixthBoundaryVector_sq_depth_zero`, `not_summable_sixthBoundaryVector_sq`, `exists_unit_core_vector_boundaryForm_ge` |
| Bounded-boundary no-go: no `ℓ²` source `b`, scalar `κ` with `S_L⁶(C) = κ|b⟩⟨b|` | `not_exists_ell2_sixthBoundary_source` |
| (ESAC.16) `T_cap = Φ ⊗ C` | `thetaCapacityFrame`, `norm_sq_thetaCapacityFrame`, `summable_thetaCapacityWeight`, `tsum_thetaCapacityWeight`, `thetaCapacitySynthesis`, `thetaCapacity`, `inner_single_thetaCapacity` |
| (ESAC.17) `T_cap ≥ 0`, `𝒮₁`, `Tr = ‖·‖₁ = ` budget `< 115/108`; `S_{I⊗L}⁶(T_cap) = (230/27)Φ⊗|c⟩⟨c|` | `thetaCapacity_traceClass`, `thetaCapacity_sixthBoundary_law` |
| (ESAC.18) `Tr((P_{[m,∞)}⊗I)T_cap) = m_m · ` budget | `eulerHistoryTailProjection`, `adjoint_eulerHistoryTailProjection`, `historyTail_trace_thetaCapacity` |

§8's form-transport theorem is stated on the card as open and is not claimed.

## Log

- 2026-10-03 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
