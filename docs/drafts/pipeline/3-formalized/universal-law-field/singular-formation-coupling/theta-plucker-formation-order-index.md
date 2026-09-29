# Theta--Pluecker formation-order index

- **ID:** `ULF-TPFOI-001`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Status:** `[PAPER-PROVED] [BRIDGE] [NOVELTY UNVERIFIED] [NOT RH SELECTION]`
- **Lean status:** not formalized; no Lean was written or built in this research pass

## Big-picture interpretation

Literal multiplicative formation and theta completion do not disagree by a bounded error. They
assign different polynomial orders to the same open history. Their unique positive half-density
comparison is therefore an unbounded first-order operator. Completion is not extra mass; it is a
change of formation order.

This narrows the missing RH source model: a coefficient-faithful theta completion of the physical
Pluecker packet cannot be a bounded diagonal gauge. It must use the number-operator graph domain,
mix depths non-diagonally, or abandon coefficient faithfulness.

## Checked internal frontier

`scripts/formal_tools.py research` was run for the physical Pluecker covariance, theta Mellin-six
flux, graph domains, linear completion growth, and prime-depth inverse-Wold landing. Relevant exact
corpus facts are:

- `[CORPUS]` `twoBoundaryCauchyPairPlucker` gives
  `2*a*(lambda-mu)/((lambda^2-a^2)*(mu^2-a^2))` in
  `GammaSewnFourRateSchurFisherCurvature.lean`.
- `[CORPUS]` `gammaSewnOrderedPrimeDepthPlucker_cell` is the four-cell packet
  `(p,e),(p,e+1),(q,e),(q,e+1)`.
- `[CORPUS]` `gammaSewnCriticalPhysicalPlucker_boundaryAmplitude_eq` gives the unsquared boundary
  amplitude `B_r=log(r)/(r+1)`.
- `[CORPUS]` `gammaSewnCriticalPrimeDepthPacket_Partition_pos` and
  `gammaSewnCriticalPrimeDepthPacket_Total_pos` give positive packet mass and Fisher clock.
- `[CORPUS]` `gammaSewnCriticalAdjacentPrime_DenominatorTerm` is their product in the global
  adjacent-prime Pluecker operator; its normalized global block weights sum to one.
- `[CORPUS]` `thetaCuspMellinSixFlux_eq_primeHodgeHistory_w` identifies theta first-exit mass with
  `w_e=630/((2e+3)(2e+5)(2e+7)(2e+9))`.
- `[CORPUS]` `not_sublinear_of_forall_bddBelow` already says any completion restoring every Sonin
  floor cannot be sublinear. It does not identify a source coefficient or a canonical graph domain.
- `[CORPUS]` `primeDepthBVWoldXiSourceNormalDepthLoweringLanding_iff_riemannHypothesis` warns that
  divisor-specialized inverse-depth landing is exactly RH. No divisor is used below.

## External parent theories

- `[LITERATURE]` Franks, *Operator scaling with specified marginals*,
  <https://arxiv.org/abs/1801.01412>, treats finite-dimensional completely positive operator
  scaling with prescribed marginals.
- `[LITERATURE]` Matsuda--Soma, *Information geometry of operator scaling*,
  <https://arxiv.org/abs/2005.01453>, interprets operator Sinkhorn scaling by information-geometric
  projections.
- `[LITERATURE]` Cole--Eckstein--Friedland--Zyczkowski, *Quantum Optimal Transport*,
  <https://arxiv.org/abs/2105.06922>, studies positive bipartite couplings with fixed marginals.
- `[LITERATURE]` Bownik--Jasper, *Diagonals of self-adjoint operators I*,
  <https://arxiv.org/abs/2212.08182>, characterizes diagonals of compact self-adjoint operators.
- `[LITERATURE]` Gao--Ji--Yu, *No-Go Theorems for Quantum Transport Metrics from Fixed Cost
  Operators*, <https://arxiv.org/abs/2607.28358>, shows that fixed-cost coupling constructions do
  not produce metrics on the full quantum state space in dimensions at least three.

Radon--Nikodym half-densities and polynomial-tail comparison are standard. No novelty is claimed
for that abstraction. The unverified residue is the exact source-forced exponent pair `(6,4)` and
its identification of the minimal theta-completion order of the physical prime-depth packet.

## The exact theorem

Fix primes `p<q`. Put

```text
L=log p,  M=log q,  Bp=L/(p+1),  Bq=M/(q+1),
a=gammaSewnCriticalFinitePacket_aperture,
c_e=e+1/2,  d_e=e+3/2.
```

The four physical rates are

```text
lambda_0=c_e L,  lambda_1=d_e L,
lambda_2=c_e M,  lambda_3=d_e M.
```

For `0<=i<j<=3`, let

```text
R_ij(e)=
  [2a(lambda_i-lambda_j)/
    ((lambda_i^2-a^2)(lambda_j^2-a^2))]^2 (B_i B_j)^2,
```

where `B_0=B_1=Bp` and `B_2=B_3=Bq`. Define

```text
P_e=sum_(i<j) R_ij(e),
F_pq=(4/3)(L^2+M^2),
D_e=F_pq P_e,
Z_pq=sum_(e>=0) D_e,
pi_e=D_e/Z_pq.
```

Thus `pi` is the conditional valuation-depth law of the physical Pluecker block weight on the
fixed prime edge `(p,q)`. Let

```text
w_e=630/((2e+3)(2e+5)(2e+7)(2e+9))
```

be theta's Mellin-six first-exit law.

**Theorem TPFOI.** Set

```text
K_pq=16 a^2 (M-L)^2 Bp^2 Bq^2/(L^4 M^4),
C_pq=F_pq K_pq/Z_pq.
```

Then all constants are finite and strictly positive, and

```text
e^6 P_e -> K_pq,
e^6 D_e -> F_pq K_pq,
e^6 pi_e -> C_pq,
e^4 w_e -> 315/8.
```

The unique positive diagonal half-density taking `pi` to `w` is

```text
s_e=sqrt(w_e/pi_e).
```

It satisfies

```text
s_e/e -> sqrt((315/8)/C_pq) > 0.                       (TPFOI.1)
```

Consequently:

1. `diag(s_e)` is unbounded and has the same domain as the depth number operator `N+1`, with
   equivalent graph norms.
2. No bounded diagonal operator `G` can satisfy
   `G diag(pi_e) G*=diag(w_e)`.
3. More generally, every complex diagonal coefficient-faithful congruence has modulus `s_e` and
   is therefore first-order unbounded.

## Proof

For a same-prime pair, `lambda_i-lambda_j` is the constant `+-L` or `+-M`. Each of the two
quadratic denominators is asymptotic to `e^2 L^2` or `e^2 M^2`. Hence

```text
e^6 R_01(e) -> 0,  e^6 R_23(e) -> 0.                  (1)
```

For each of the four cross-prime pairs, with offsets `alpha,beta` in `{1/2,3/2}`,

```text
(c_e L-d_e M)/e -> L-M,
((e+alpha)^2 L^2-a^2)/e^2 -> L^2,
((e+beta )^2 M^2-a^2)/e^2 -> M^2.
```

Therefore every cross-prime raw weight has the same positive limit

```text
e^6 R_ij(e) ->
  4 a^2 (M-L)^2 Bp^2 Bq^2/(L^4 M^4).                 (2)
```

There are four cross-prime pairs. Summing `(1)` and `(2)` proves
`e^6 P_e -> K_pq>0`.

Each prime occurs twice in the four-cell packet and its boundary Fisher clock is
`(2/3)(log r)^2`; hence its total clock is exactly `F_pq`. Multiplication proves the limit for
`D_e`. The limit gives `D_e<=2 F_pq K_pq/e^6` eventually, so `sum D_e` converges. Every `D_e` is
positive, so `0<Z_pq<infinity`; division gives `e^6 pi_e -> C_pq>0`.

Directly from the four linear factors in `w_e`,

```text
e^4 w_e -> 630/2^4=315/8.                             (3)
```

Since `pi_e,w_e>0`, a positive diagonal congruence must obey `s_e^2 pi_e=w_e`, proving uniqueness.
Moreover

```text
s_e/e = sqrt((e^4 w_e)/(e^6 pi_e)).                   (4)
```

The limits above and continuity of the positive square root prove `(TPFOI.1)`. Thus positive
constants bound `s_e/(e+1)` above and below outside a finite set; enlarging the constants handles
the finite head. This proves equality of the multiplication domains of `diag(s_e)` and `N+1`, and
equivalence of their graph norms. Unboundedness follows from the positive linear limit. Finally,
if a complex diagonal `G=diag(g_e)` implements the same congruence, then
`|g_e|^2 pi_e=w_e`, so `|g_e|=s_e`; `G` cannot be bounded. QED.

## Hostile review

**Wrong first:** as a general theorem about two regularly varying probability laws, this is
routine Radon--Nikodym comparison. Calling it a new geometry would be theatre. Operator scaling,
quantum couplings, and unbounded diagonal operators are established subjects.

**Corpus collision:** `SoninCompletionMustGrowLinearly` already forces non-sublinear growth from a
different floor-restoration hypothesis. TPFOI does not supersede it. It supplies a literal
prime-depth coefficient, an exact order, and a canonical graph domain; Sonin supplies an
independent route shadow of the same order.

**Circularity attack:** no Xi zero, divisor copy, horizontal grade, or RH-equivalent landing enters
the theorem. It therefore survives the prime-depth inverse-Wold circularity lock.

**Significance verdict:** `BRIDGE`. It gives unconditional new leverage by eliminating every
bounded diagonal coefficient-faithful Pluecker-to-theta completion and by fixing the minimal
singular order to one. It neither constructs the completed Xi boundary nor proves residual
vanishing, so it is not RH selection.

## Exact RH-chain edge

The surviving completion problem is no longer

```text
find a bounded transport from physical Euler formation to theta history.
```

TPFOI proves that such transport does not exist in the diagonal coefficient-faithful class. The
next admissible edge is exactly:

```text
physical nonseparable Pluecker block
  -- first-order graph completion on Dom(N+1), preserving unsquared coefficients -->
theta first-exit marginal
  -- prove anomaly subtraction and zero residual boundary --> neutral grade.
```

The first arrow now has a forced domain and forced diagonal modulus. The second arrow remains open.

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.ThetaPluckerFormationOrderIndex`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Module `GaloisForLFunctions.HTGeometry.ThetaPluckerFormationOrderIndex` (57 constants) on top of the corpus cores `RHTower.GammaSewnMobiusApertureStokesCofinalPluckerSpectralOperator`, `RHTower.GammaSewnMobiusApertureStokesCriticalPhysicalPluckerChiralityGain`, `RHTower.ThetaMellinSixIntegralNuclearFormation`, `HTGeometry.DiagonalEllTwoIndexed`; all axiom-audit clean. `P_e = gammaSewnCriticalPrimeDepthPacket_Partition e p q`, `a = gammaSewnCriticalFinitePacket_aperture`, `B_r = gammaSewnMobiusApertureBoundaryAmplitude r`, `w_e = thetaCuspMellinSixFlux e`.

| Claim | Lean declaration |
|-|-|
| `P_e = ∑_{i<j} R_ij(e)` over the six minors of the rates `(e+1/2)L, (e+3/2)L, (e+1/2)M, (e+3/2)M` | `gammaSewnCriticalPrimeDepthPacket_Partition_eq` |
| `F_pq = (4/3)(L²+M²)` is the packet Fisher clock; `D_e = F_pq P_e`; adjacent-prime identification | `pluckerFisherClock`, `gammaSewnCriticalPrimeDepthPacket_Total_eq`, `pluckerDepthWeight`, `pluckerDepthWeight_eq`, `pluckerDepthWeight_adjacentPrime` |
| (1), (2): per-minor limit `e⁶R → 4a²(A−B)²/(A⁴B⁴)` (same-prime → 0, cross-prime common limit) | `pow_six_mul_twoBoundaryCauchyPairPluckerSq`, `tendsto_pow_six_mul_twoBoundaryCauchyPairPluckerSq` |
| `K_pq > 0` and `e⁶ P_e → K_pq` | `pluckerOrderConstant`, `pluckerOrderConstant_pos`, `tendsto_pow_six_mul_gammaSewnCriticalPrimeDepthPacket_Partition` |
| `e⁶ D_e → F_pq K_pq`; `∑ D_e` converges; `0 < Z_pq < ∞` | `tendsto_pow_six_mul_pluckerDepthWeight`, `summable_pluckerDepthWeight`, `pluckerDepthTotal`, `pluckerDepthTotal_pos` |
| `π_e = D_e/Z_pq` is a probability law, the conditional physical Plücker block weight on the edge; `C_pq > 0`; `e⁶ π_e → C_pq` | `pluckerDepthLaw`, `pluckerDepthLaw_pos`, `hasSum_pluckerDepthLaw`, `pluckerDepthLaw_adjacentPrime`, `pluckerDepthLawConstant_pos`, `tendsto_pow_six_mul_pluckerDepthLaw` |
| `w_e = 630/((2e+3)(2e+5)(2e+7)(2e+9))`; (3) `e⁴ w_e → 315/8` | `thetaCuspMellinSixFlux_eq`, `thetaCuspMellinSixFlux_pos`, `tendsto_pow_four_mul_thetaCuspMellinSixFlux` |
| Unique positive half-density `s_e = √(w_e/π_e)`: `s² π = w`, uniqueness among `x ≥ 0` | `formationHalfDensity`, `formationHalfDensity_pos`, `formationHalfDensity_sq_mul`, `sq_mul_pluckerDepthLaw_eq_iff` |
| (4), (TPFOI.1): `s_e/e → √((315/8)/C_pq) > 0` | `formationOrderSlope`, `formationOrderSlope_pos`, `tendsto_formationHalfDensity_div` |
| Two-sided bounds `c₁(e+1) ≤ s_e ≤ c₂(e+1)` including the finite head | `tendsto_formationHalfDensity_div_succ`, `exists_formationHalfDensity_bounds` |
| Consequence 1: `Dom diag(s) = Dom(N+1)` in `ℓ²`, equivalent graph norms, unbounded | `memℓp_formationHalfDensity_mul_iff`, `formationHalfDensity_graphNorm_equiv`, `norm_le_of_forall_norm_apply_le`, `not_bddAbove_formationHalfDensity` |
| Consequence 3: every complex diagonal congruence has `‖g_e‖ = s_e`, hence unbounded | `norm_eq_formationHalfDensity_of_congruence`, `not_bddAbove_norm_of_congruence` |
| Consequence 2: no bounded diagonal `G` with `G diag(π) G* = diag(w)` on `ℓ²(ℕ)` | `norm_pluckerDepthLaw_le`, `norm_thetaCuspMellinSixFlux_le`, `diagonal_congruence_ne` |
| Theorem TPFOI (summary) | `theta_plucker_formation_order_index` |

The hostile review, significance verdict and RH-chain edge are interpretation and audit.

## Log

- 2026-09-29 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
