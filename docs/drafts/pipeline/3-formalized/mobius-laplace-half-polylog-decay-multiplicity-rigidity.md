# Möbius--Laplace half-polylog decay and zeta-multiplicity rigidity

- **ID:** `mobius-laplace-half-polylog-decay-multiplicity-rigidity`
- **Stage:** 2-fully-proven
- **Type:** `[THEOREM] [MOBIUS--LAPLACE FRONTIER WEAKENING]`
- **Scientific status:** `[PAPER-PROVED] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
  `[GENERAL IRREGULARITY PARENT] [NOT AN UNCONDITIONAL RH PROOF]`
- **Lean parent:**
  `formal/GaloisForLFunctions/RHTower/MobiusLaplaceCriterionFrontier.lean`
- **Lean frontier module:**
  `formal/GaloisForLFunctions/RHTower/MobiusLaplaceHalfPolylogCriterion.lean`
- **Lean boundary module:**
  `formal/GaloisForLFunctions/RHTower/MobiusLaplaceBoundaryMultiplicity.lean`
- **Lean polylog-boundary module:**
  `formal/GaloisForLFunctions/RHTower/MobiusLaplacePolylogBoundaryMultiplicity.lean`
- **Lean sharp-coefficient module:**
  `formal/GaloisForLFunctions/RHTower/MobiusLaplacePolylogSharpCoefficientLaw.lean`
- **Analytic parent:** Sergey Liflandsky's half-power criterion and general Mellin/Landau
  irregularity theory.

## One active claim

Put

```text
Phi(x)=sum_(n>=1) mu(n) exp(-n x),   x>0.
```

For `q : Nat`, define the half-polylog source bound

```text
HP_q:
  exists C,delta>0, for all 0<x<delta,
  |Phi(x)| <= C x^(-1/2) (log(1/x))^q.                  (1)
```

After shrinking `delta`, `log(1/x)>0`.  The active theorem is:

> **Half-polylog Mellin wall and multiplicity law.**  If `HP_q` holds for one finite `q`, then
> the Möbius--Laplace Mellin transform continues analytically to `Re s>1/2`, RH follows, and every
> nontrivial zero of `zeta` has analytic order at most `q+1`.  If a zero `rho` has order exactly
> `q+1` and
>
> ```text
> zeta(s)=(s-rho)^(q+1) u_rho(s),  u_rho(rho)!=0,
> ```
>
> then every admissible constant `C` in `(1)` obeys
>
> ```text
> |Gamma(rho)/u_rho(rho)| <= C q!.                     (2)
> ```

For `q=0`, exact half-decay therefore implies not only RH but simplicity of every nontrivial
zeta zero and the residue cap

```text
|Gamma(rho)/zeta'(rho)| <= C.                           (3)
```

This is a strict weakening of the open source target as an RH criterion: any fixed logarithmic
loss is admissible.

## Dependency-closed paper proof

### 1. Every fixed logarithmic loss is smaller than every power margin

Shrink `delta` below `1`.  On this interval `log(1/x)=|log x|`.  For every `eta>0`,

```text
|log x|^q=o(x^(-eta)),  x->0+.
```

This is the standard logarithm-versus-power limit, including `q=0`.  Multiplying `(1)` by this
comparison gives

```text
Phi(x)=O(x^(-1/2-eta))                                  (4a)
```

for every `eta>0`.  Given `s` with `Re s>1/2`, choose

```text
eta=(Re s-1/2)/2,
b=1/2+eta<Re s.
```

The existing local integrability and exponential decay at infinity, together with `(4a)`, make
the Mellin integral differentiable at `s`.  Since `s` was arbitrary,

```text
G(s)=Mellin(Phi)(s)
```

is analytic throughout `Re s>1/2`.

### 2. Denominator-free continuation and RH

On `Re s>1`, the already proved Mellin--Dirichlet identity is

```text
G(s)=Gamma(s)/zeta(s).
```

Both sides of
```text
G(s) zetaResidueUnit(s)=Gamma(s)(s-1)                  (4)
```

are analytic on this connected half-plane.  The identity theorem propagates their equality from
`Re s>1`.  At a hypothetical strict-right nontrivial zeta zero, left side vanishes while right
side is nonzero: Gamma has no zero for positive real part and the zero is not the Euler pole.
Thus no strict-right zero exists.  Functional-equation reflection gives RH.  Equivalently, this
is exactly the existing `MobiusLaplaceMellinContinuationWall` consumer.

### 3. Radial Abel bound at a boundary zero

Let `rho=1/2+i gamma` be any nontrivial zeta zero.  RH from the previous step places every such
zero on this line.  Choose

```text
0<delta_0<min(delta,1)
```

and approach radially by `s=rho+r`, `r>0`.  Split the Mellin integral at `delta_0`.

The tail over `[delta_0,infinity)` is bounded uniformly for `0<r<=1/2`.  On
`[delta_0,1]`, continuity of `Phi` and `x^(-1/2+r)<=delta_0^(-1/2)` give a fixed integrable
majorant.  On `[1,infinity)`, the proved exponential estimate for `Phi` gives a fixed exponential
majorant, while `x^(-1/2+r)<=1`.

On `(0,delta_0)`, `(1)` and the norm formula for positive real complex powers give

```text
|Phi(x)x^(rho+r-1)|
  <=C x^(r-1) log(1/x)^q.
```

Substitution `x=exp(-u)` now yields

```text
integral_0^delta_0 x^(r-1) log(1/x)^q dx
  =integral_(log(1/delta_0))^infinity exp(-r u)u^q du
  <=integral_0^infinity exp(-r u)u^q du
  =q!/r^(q+1).                                          (5)
```

Multiplying the uniformly bounded tail by `r^(q+1)` sends it to zero.  Therefore

```text
limsup_(r->0+) r^(q+1)|G(rho+r)| <= C q!.              (6)
```

### 4. Multiplicity and maximal-order coefficient

Zeta is analytic at `rho`.  If its analytic order there is `m>=1`, local factorization gives

```text
zeta(s)=(s-rho)^m u_rho(s),  u_rho(rho)!=0.             (7a)
```

For small positive `r`, equation `(4)` and cancellation of the nonzero factor `rho+r-1` give

```text
G(rho+r)=Gamma(rho+r)/(r^m u_rho(rho+r)).               (7)
```

Continuity and nonvanishing of `Gamma(rho)` and `u_rho(rho)` make the right side of `(6)` diverge
when `m>q+1`; hence `m<=q+1`.  If `m=q+1`, then

```text
r^(q+1)G(rho+r) -> Gamma(rho)/u_rho(rho).
```

Taking norms in `(6)` proves `(2)`.  For `q=0`, `m=1` and
`u_rho(rho)=zeta'(rho)`, giving `(3)`.  `[PAPER-PROVED]`

## Hostile audit outcome

1. **Polylog-to-power uniformity.**  No uniform exponent is asserted on the entire half-plane.
   Margin is chosen after `s`; analyticity is pointwise local, which is sufficient.
2. **Boundary versus interior.**  RH follows from interior analyticity, but simplicity does not.
   Multiplicity cap uses separate radial estimate `(5)`.
3. **Multiple zero cancellation.**  Gamma has no zero and `rho!=1`; nothing cancels the order-`m`
   zeta zero in `(7)`.
4. **Tail leakage.**  Tail is uniformly `O(1)`, so it vanishes after multiplication by
   `r^(q+1)` and cannot alter maximal Laurent coefficient.
5. **Sharp constant.**  `q!` is exact full Laplace moment.  Truncating lower limit only decreases
   positive integral, so direction in `(5)` is correct.
6. **Not an unconditional RH proof.**  `HP_q` remains unproved for every `q`; theorem weakens and
   sharpens source target but does not supply source cancellation.

## Literature and corpus audit

- Liflandsky (2026) proves only stated exact half-power implication `O(x^(-1/2))->RH`; his
  explicit formula assumes simple zeros.  Paper does not state fixed-polylog losses, resulting
  multiplicity cap, or coefficient bound `(2)`.
- Lowry-Duda (2020) proves general nonreal-pole irregularity with logarithmic factors determined
  by pole order.  It subsumes qualitative obstruction behind `m<=q+1`, so no priority claim is
  made for general Mellin mechanism.
- Inoue (2017) records analogous implications from Mertens and Riesz-mean bounds to simplicity of
  zeta zeros.  Those are different source transforms and do not state `(1)`--`(3)`.
- Targeted searches found no discrete Möbius--Laplace theorem allowing arbitrary fixed polylog
  loss while simultaneously giving RH, zero-order cap, and sharp top-coefficient bound.

Scientific delta is therefore the explicit object-specific package `(1)`--`(3)` and, most
importantly for current frontier, replacement of exact half-decay by any finite polylog loss.
Classification remains `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE]` pending specialist priority review;
general irregularity parent is explicit.

## Gates

- [x] source object and exact weakened target fixed
- [x] dependency-closed proof skeleton
- [x] complete every analytic estimate on paper
- [x] hostile falsifier audit
- [x] corpus and literature novelty audit
- [x] move to 2-fully-proven
- [x] formalize the polylog-to-Mellin bridge
- [x] formalize `q=0` boundary Abel bound and zeta simplicity
- [x] formalize general `q` critical Abel bound and zeta-order cap
- [x] formalize maximal-order coefficient bound
- [x] connect to `MobiusLaplaceMellinContinuationWall`
- [ ] RH from an unconditional `HP_q` source proof

## Lean status

The frontier module now proves, for every `q : Nat`:

```text
MobiusDiscreteLaplaceHalfPolylogDecay q
  -> MobiusLaplaceMellinContinuationWall
  -> RiemannHypothesis.
```

Principal declarations:

```text
mobiusLaplaceHalfPolylogKernel
MobiusDiscreteLaplaceHalfPolylogDecay
MobiusDiscreteLaplaceHalfPolylogDecay.isBigO_kernel
mobiusLaplaceHalfPolylogKernel_isBigO_rpow
MobiusDiscreteLaplaceHalfPolylogDecay.isBigO_rpow
analyticOnNhd_mellin_mobiusDiscreteLaplaceTransform_of_halfPolylog
mobiusLaplaceMellinContinuationWall_of_halfPolylog
mobiusDiscreteLaplaceHalfPolylogDecay_implies_riemannHypothesis
```

The shared criterion module also exposes the source-independent connector
`mobiusLaplaceMellinContinuationWall_of_analyticOnNhd_mellin`, plus the canonical-witness identity
`mellin_mobiusDiscreteLaplaceTransform_mul_zetaResidueUnit_eq_of_analyticOnNhd`.

The boundary module now machine-checks the full `q=0` strengthening:

```text
MobiusDiscreteLaplaceHalfDecay
  -> MobiusLaplaceCriticalAbelBound rho
  -> analyticOrderAt riemannZeta rho = 1
```

Principal declarations:

```text
MobiusLaplaceCriticalAbelBound
mobiusLaplaceCriticalAbelBound_of_halfDecay
deriv_riemannZeta_ne_zero_of_mobiusLaplaceCriticalAbelBound
deriv_riemannZeta_ne_zero_of_mobiusDiscreteLaplaceHalfDecay
analyticOrderAt_riemannZeta_eq_one_of_mobiusDiscreteLaplaceHalfDecay
mobiusDiscreteLaplaceHalfDecay_implies_riemannHypothesis_and_boundarySimplicity
```

The polylog-boundary module machine-checks the general radial-growth and multiplicity theorem:

```text
MobiusDiscreteLaplaceHalfPolylogDecay q
  -> MobiusLaplaceCriticalPolylogAbelBound q rho
  -> (analyticOrderAt riemannZeta rho).toNat <= q + 1,

MobiusDiscreteLaplaceHalfPolylogDecay q
  -> RiemannHypothesis /\
     every critical-line zeta-zero multiplicity <= q + 1.
```

Principal declarations:

```text
MobiusLaplaceCriticalPolylogAbelBound
mobiusLaplaceCriticalPolylogAbelBound_of_halfPolylogDecay
analyticOrderAt_riemannZeta_toNat_le_of_mobiusLaplaceCriticalPolylogAbelBound
analyticOrderAt_riemannZeta_toNat_le_of_mobiusDiscreteLaplaceHalfPolylogDecay
mobiusDiscreteLaplaceHalfPolylogDecay_implies_riemannHypothesis_and_multiplicityCap
```

The sharp-coefficient module machine-checks the remaining equality case.  It derives the exact
logarithmic Mellin moment `q! / r^(q+1)`, keeps the declared source constant through the radial
Abel estimate, extracts the maximal local zeta factor, and proves:

```text
MobiusDiscreteLaplaceHalfPolylogDecay q with witness C
  -> analyticOrderAt riemannZeta rho = q + 1
  -> exists p, riemannZeta(z) = (z-rho)^(q+1) p(z) locally /\
       p(rho) != 0 /\ ‖Gamma(rho) / p(rho)‖ <= C * q!.
```

Principal declarations:

```text
eventually_norm_scaled_mellin_le_halfPolylogConstant
exists_localFactor_with_Gamma_cap_of_halfPolylog_maximalOrder
```

Direct `lake env lean` checks pass for modified criterion, half-polylog, exact-boundary, and
polylog-boundary modules, and the new sharp-coefficient module compiles cleanly on its first
production check. Stage remains 2 until final build/lint/axiom gates pass.
