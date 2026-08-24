# The Euler pole is the exact four-unit anti-causal boundary budget

- **ID:** `euler-pole-four-unit-anti-causal-budget-law`
- **Stage:** 3-formalized/not_new_scientific_knowledge
- **Type:** THEOREM (paper), `[PROVED HERE; BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** `infinitesimal-euler-leakage-cauchy-energy-threshold.md`;
  `shifted-euler-error-floor-mobius-tail-coupling.md`
- **Statement:** At every finite prime cutoff, the critical completed logarithmic source has one
  and only one anti-causal channel: the uncancelled Euler pole at `s=1`.  Its profile is
  `2 exp(-t/2)` and its squared `L2(0,infinity)` norm is exactly `4`.  The all-prime completed
  limit cancels this pole and replaces it, if RH fails, by the transverse-zero residue profile.
  Thus the desired bound `C_E(0,0)<=4` is exactly a nonexpansive pole-to-divisor transfer law.

## 1. Finite-prime completed tangent

Put

```text
s=1/2-i z
```

and, for a finite set of primes `P`, define

```text
Q_P(z)
 =-2/s-2/(s-1)+log(pi)-psi(s/2)
  +2 sum_(p in P) sum_(r>=1)(log p)p^(-r s).             (1)
```

The prime-power sum converges locally uniformly on `Re s>0`, hence on the upper `z` half-plane.
Its boundary inverse Fourier transform is causal: it is the positive-frequency atomic measure
supported at the rates `r log p`.  The constant is supported at the boundary.  The poles of
`-2/s` and `-psi(s/2)` occur at

```text
s=0,-2,-4,...,
```

which correspond to the lower `z` half-plane.  They are causal in the same convention.

The only upper-half-plane pole of `(1)` is therefore

```text
z=i/2,
```

coming from `-2/(s-1)`.  Since `ds/dz=-i`,

```text
Res_(z=i/2)(-2/(s-1))=-2i.                              (2)
```

In the residue convention of the shifted-Xi leakage theorem, the reflected anti-causal profile is
`i` times the residue multiplied by `exp(-i z t)`.  Equations `(2)` and `z=i/2` give

```text
ell_pole(t)=2 exp(-t/2),          t>0.                   (3)
```

Consequently every finite-prime source has the exact boundary budget

```text
integral_0^infinity |ell_pole(t)|^2 dt
 =4 integral_0^infinity exp(-t)dt
 =4.                                                     (4)
```

This remains true when every power of every retained prime is kept.  A finite-prime Euler
logarithmic derivative is holomorphic on `Re s>0` and contributes only causal frequencies.

## 2. The all-prime replacement law

On the Euler half-plane, the full tangent is

```text
Q(z)=-2 Xi'(s)/Xi(s)
 =-2/s-2/(s-1)+log(pi)-psi(s/2)
  +2 sum_(n>=1)Lambda(n)n^(-s).                          (5)
```

The completed function `Xi` is regular and nonzero at `s=1`.  Therefore the meromorphic
continuation of the all-prime term in `(5)` cancels the pole channel `(3)` exactly.  The remaining
upper-half-plane poles are precisely the zeros

```text
rho=1/2+a+i gamma,       a>0,
```

of `Xi`.  For a finite right-half divisor, the residue theorem gives

```text
ell_E(t)
 =2 sum_j m_j exp(-(a_j+i gamma_j)t).                    (6)
```

Thus the cofinal all-prime operation does not add a correction to the four-unit channel.  It
removes that channel and replaces it by the complete transverse divisor channel.

## 3. Exact threshold and positive transfer statement

The Cauchy-energy theorem gives

```text
C_E(0,0)=||ell_E||_2^2
 >4
```

whenever the right-half divisor is nonempty; if it is infinite and the profile is not in `L2`, set
the energy to `+infinity`.  Under RH the profile `(6)` is zero.  Hence

```text
C_E(0,0)<=4
  <-> C_E(0,0)=0
  <-> RH.                                                 (7)
```

The constant in the proposed estimate is therefore forced, rather than chosen:

```text
4=||2 exp(-t/2)||_2^2.                                   (8)
```

The positive carrier theorem still required from the arithmetic source is:

> The coupled floor-discrepancy/Mobius-tail continuation transports the incoming Euler-pole
> channel `2 exp(-t/2)` to the completed transverse channel `ell_E` without increasing boundary
> energy.

Equivalently, it must construct a source-defined contraction `S_E` on the two-continuation graph
such that

```text
ell_E=S_E(2 exp(-t/2)),       ||S_E||<=1.                 (9)
```

Equation `(9)` immediately gives `C_E(0,0)<=4` and therefore RH.  It is a construction target, not
an assumed reformulation: `S_E` must be obtained from the coupled summatory source before the Xi
divisor is expanded.

At prime cutoff `N`, any autonomous algebraic-differential realization of this transport that
retains the rates `{log p:p<=N}` is forced by the singular Kolchin-frequency law to satisfy

```text
kappa(P_N)>=ceil(pi(N)/2).                               (10)
```

Thus a viable realization of `(9)` must have cofinally growing compatible jet variety, or place
the arithmetic state in an infinite-dimensional operator/test space, a nonautonomous coefficient
field, a determinant/divisor carrier, or a global non-flow constraint.

## 4. Why the theorem does not yet prove the bound

Finite Dirichlet sums converge to `(5)` only on the Euler half-plane.  Their anti-causal profiles
are all the fixed vector `(3)`, while the meromorphic all-prime continuation cancels `(3)` and may
create `(6)`.  Compact-open convergence on the Euler half-plane therefore does not pass the
boundary energy.  A proof of `(9)` needs a cofinal graph topology controlling the contour jump;
ordinary Hardy contractivity, boundary unimodularity, coefficient positivity, and separate bounds
on the two summatory terms do not supply it.

The critical derivative of the exact coupled summatory error is

```text
partial_omega E_omega(X)|_(0+)=2(psi(X)-X).              (11)
```

Here `2psi(X)` is the all-prime replacement and `2X` is the incoming Euler-pole channel.  Thus
`(11)` is the arithmetic coordinate of the replacement in `(3)`--`(6)`.  Passing `(11)` through
Suzuki's archimedean kernel with the graph-norm control required by `(9)` is the open RH-bearing
step.

## Scientific status

The residue calculation, Paley--Wiener support separation, and Cauchy threshold are standard
Hardy-space parent theory.  The result is retained as a bridge because it identifies the exact
origin of the constant `4` and converts the requested estimate into a positive nonexpansive
pole-to-divisor carrier theorem.  The new scientific content would be the unconditional
construction of `S_E` in `(9)`.

## Gates

- [x] finite-prime upper-half-plane poles classified
- [x] unique Euler-pole profile and exact energy `4` proved
- [x] incoming profile and exact norm formalized in `RHTower/EulerPoleBoundaryBudget.lean`
- [x] all-prime pole cancellation and divisor replacement identified
- [x] `C_E(0,0)<=4 <-> RH` proved in the extended-energy convention
- [x] singular-ADE capacity floor attached to finite-prime realizations
- [x] proved pole/divisor replacement law formalized unconditionally in Lean
- [x] open source-defined contraction `(9)` separated into the existing stage-1 RH producer
  `mobius-incidence-curvature-gamma-sonin-pole-divisor-transfer-rh.md`

## Lean status update (2026-08-23)

`RHTower/EulerPoleFourUnitCompletedWall.lean` now formalizes, without hypotheses, the exact
four-unit incoming norm together with the completed Suzuki-wall criterion

```text
(forall N, ||completedWall(-i,N+2)||_2^2 <= ||eulerPoleBoundaryProfile||_2^2) <-> RH.
```

It also formalizes the equivalent off-RH finite-aperture budget violation and packages the exact
incoming norm `4` with this completed-wall nonexpansiveness law.  Exact leaf build and axiom audit
pass; the new theorems use only `propext`, `Classical.choice`, and `Quot.sound`.

`RHTower/EulerPoleFinitePrimeTangent.lean` now additionally formalizes the literal finite-prime
tangent `(1)`, its unique upper-half-plane failure of holomorphy at `z=i/2`, residue `-2i`, and
all-prime cancellation at that node.  For every Xi zero `rho`, the affine centered node is proved
to lie in the upper half-plane exactly when `Re rho>1/2`; the all-prime tangent has punctured
residue

```text
-2i * analyticMultiplicity(Xi,rho),
```

and is holomorphic exactly away from the shifted Xi divisor.  Exact leaf build and axiom audit
pass; all new declarations use only `propext`, `Classical.choice`, and `Quot.sound`.

This closes every proved assertion of the bridge card.  Construction `(9)` remains open and is
not claimed here: it is already the explicit objective of
`pipeline/1-in-progress/mobius-incidence-curvature-gamma-sonin-pole-divisor-transfer-rh.md`.
The completed bridge theorem therefore advances to stage 3 without reclassifying its separate
RH-producing conjecture.
