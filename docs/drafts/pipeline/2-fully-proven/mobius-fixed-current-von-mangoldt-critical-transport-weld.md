# The Mobius multiplier fixed current is critically transport-equivalent to the Euler prime current

- **ID:** `mobius-fixed-current-von-mangoldt-critical-transport-weld`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / HT FIXED-CURRENT SOURCE WELD
- **Scientific status:** `[PROVED HERE] [LITERATURE NOVELTY OPEN] [NOT AN RH PROOF]`
- **Parents:**
  - `mobius-critical-fisher-tangent-hilbert-lift.md`
  - `mobius-incidence-clock-gini-fisher-four-unit-law.md`
  - `complementary-packet-critical-gini-isometry.md`
  - `new_scientific_knowledge/charged-scalar-core-fixed-current-torsor.md`
  - `../3-formalized/infinite-mobius-critical-boundary-layer-product.md`
  - `not_new_scientific_knowledge/infinitesimal-euler-leakage-cauchy-energy-threshold.md`
- **Statement:** The logarithmic current of the exact signed all-prime Mobius multiplier is the
  positive von Mangoldt prime-power law.  Its critical logarithmic clock and the squarefree
  Mobius clock converge in `W_1` to the same mean-one exponential law.  Their canonical monotone
  coupling therefore has vanishing critical complementary-packet cost, so the four-unit packet
  geometry transfers to the actual Euler current before Gamma/Sonin completion.

## Two source clocks

Let `sigma>1`, `epsilon=sigma-1`, and

```text
Z(sigma)=sum_d mu(d)^2d^(-sigma)=zeta(sigma)/zeta(2sigma),
P_sigma(d)=mu(d)^2d^(-sigma)/Z(sigma).                    (1)
```

Let

```text
A(s)=-zeta'(s)/zeta(s)=sum_(n>=2)Lambda(n)n^(-s),
nu_sigma(n)=Lambda(n)n^(-sigma)/A(sigma).                 (2)
```

Both `(1)` and `(2)` are probability laws.  Write `H_P=log d` under `P_sigma` and `H_E=log n`
under `nu_sigma`.

The exact moving-aperture signed Mobius multiplier is

```text
tau_sigma(u)
 =zeta(2sigma)/[zeta(sigma)zeta(sigma+u epsilon)],
u>=0.                                                     (3)
```

The parameter `epsilon` is the thermal/escape clock of `(1)`.  A second parameter `alpha` will
denote the normal Suzuki shift.  They must not be identified before taking the normal derivative.

## Exact fixed-current theorem `[PROVED HERE]`

The logarithmic current of `(3)` is

```text
J_sigma(u)
 =partial_u log tau_sigma(u)
 =epsilon A(sigma+u epsilon)
 =epsilon A(sigma) E_nu[exp(-u epsilon H_E)].             (4)
```

This is an exact identity on `sigma>1`.  In particular, scalar factors in `(3)` which are
independent of `u` disappear, while every nonconstant rational or Euler gauge contributes its
own logarithmic current.  Thus `(4)` is canonical under the multiplicative torsor freedom and is
not rational-gauge blind.

Equation `(4)` is the source-specific instance of the fixed-current mechanism proved for charged
scalar HT cores: a multiplicative amplitude has a gauge-invariant logarithmic current.  Here that
current is not abstract.  It is exactly the positive von Mangoldt law `(2)`.

The same current is the normal derivative of Suzuki's packet connection.  If

```text
c_alpha(n)=n^alpha product_(p|n)(1-p^(-2alpha)),          (5)
```

then the already proved coefficient identity gives

```text
partial_alpha c_alpha(n)|_(alpha=0)=2Lambda(n).           (6)
```

Consequently the logarithmic current of the signed multiplier and the normal current of the
complementary packet connection are the same arithmetic object.

## Diagonal-collapse no-go and positive two-clock law

For fixed `Re s>1`, absolute convergence gives

```text
C(alpha,s)=sum_n c_alpha(n)n^(-s)
          =zeta(s-alpha)/zeta(s+alpha),
partial_alpha C(alpha,s)|_(alpha=0)=2A(s).               (7)
```

On the old diagonal `s=1+2alpha`, however,

```text
C(alpha,1+2alpha)
 =zeta(1+alpha)/zeta(1+3alpha) ->3.                      (8)
```

Thus normal differentiation and critical diagonal summation do not commute.  In fact
`[C(alpha,1+2alpha)-1]/(2alpha)` diverges, whereas the correctly ordered normalized derivative is

```text
(epsilon/2) partial_alpha C(alpha,1+epsilon)|_(alpha=0)
 =epsilon A(1+epsilon) ->1.                              (9)
```

**No-go:** tying the normal Suzuki shift to the thermal critical parameter before differentiation
does not recover the von Mangoldt current.

**Positive theorem:** the HT source has two geometrically distinct clocks.  The normal fixed
current is obtained by `alpha->0` at fixed `epsilon`; only then may the escaping thermal limit
`epsilon->0` be taken.  This order is source-forced by `(7)`--`(9)`.

## Common exponential boundary law `[PROVED HERE]`

Set

```text
X_P=epsilon H_P,
X_E=epsilon H_E.                                         (10)
```

For every `u>=0`, the Laplace transforms are

```text
E[exp(-uX_P)]
 =Z(sigma+u epsilon)/Z(sigma) ->1/(1+u),

E[exp(-uX_E)]
 =A(sigma+u epsilon)/A(sigma) ->1/(1+u).                 (11)
```

The first limit is the proved squarefree critical boundary-layer theorem.  For the second, the
simple pole of zeta gives

```text
A(1+x)=1/x+O(1).                                         (12)
```

The limiting transform in `(11)` is that of `Exp(1)`, so both variables converge weakly to the
mean-one exponential law.  Their first moments also converge:

```text
E[X_P]=-epsilon Z'(sigma)/Z(sigma) ->1,
E[X_E]=-epsilon A'(sigma)/A(sigma) ->1.                  (13)
```

For `(13)`, use the residue-unit expansion of `Z` and differentiate `(12)`, which gives
`A'(1+x)=-x^(-2)+O(1)`.  Weak convergence on the half-line plus convergence of first moments is
equivalent to `W_1` convergence.  Therefore

```text
W_1(Law(X_P),Exp(1))->0,
W_1(Law(X_E),Exp(1))->0,
W_1(Law(X_P),Law(X_E))->0.                               (14)
```

Let `pi_sigma` be the monotone quantile coupling of the two laws.  It is determined by `(1)` and
`(2)` alone and satisfies

```text
epsilon E_(pi_sigma)|H_P-H_E|->0.                        (15)
```

The same argument at second order gives more.  The residue expansions imply

```text
E[X_P^2]->2,
E[X_E^2]=epsilon^2 A''(sigma)/A(sigma)->2.               (15a)
```

Hence both laws converge to `Exp(1)` in `W_2`.  For the same monotone coupling,

```text
epsilon^2 E_(pi_sigma)|H_P-H_E|^2->0.                    (15b)
```

In particular their centered thermal scores are coupled in `L2`:

```text
epsilon[(H_P-E H_P)-(H_E-E H_E)]->0                     (15c)
```

in the joint `L2` space.  The fixed-current transport therefore identifies the full critical
Fisher tangent, not only the ground clock distribution and its Gini energy.

## Prime-current four-unit law `[PROVED HERE]`

If `H_E'` is an independent copy of `H_E`, then `W_1` convergence and `(13)` imply uniform
integrability of the pairwise distance.  Hence

```text
epsilon E|H_E-H_E'|->E|Y-Y'|=1,
Y,Y' iid Exp(1).                                         (16)
```

Thus the von Mangoldt current has its own canonical four-unit incidence energy

```text
E^Euler_sigma=4epsilon E|H_E-H_E'|->4.                  (17)
```

This is not a fitted copy of the squarefree law.  It is obtained from the logarithmic current of
the exact signed multiplier `(3)` and independently calibrated by `(16)`.

## Vanishing complementary-packet transport cost `[PROVED HERE]`

Put `omega=epsilon/2` and let `B_h` be the complementary affine packet.  Its squared distance is

```text
||B_h-B_k||_2^2=D_omega(|h-k|),
D_omega(a)<=C+a/(1+omega)^2                              (18)
```

with `C` uniform near `omega=0`.  The monotone coupling `(15)` and `(18)` give

```text
epsilon E_(pi_sigma)||B_(H_P)-B_(H_E)||_2^2->0.          (19)
```

Take two independent copies of the coupling and define the two edge fields

```text
G_P=2(B_(H_P')-B_(H_P)),
G_E=2(B_(H_E')-B_(H_E)).                                 (20)
```

The elementary parallelogram bound and `(19)` imply

```text
epsilon E||G_P-G_E||_2^2->0.                             (21)
```

The squarefree packet theorem gives `epsilon E||G_P||^2->4`; equations `(16)` and `(18)` give the
same limit for `G_E`.  Hence `(21)` is an asymptotic isometry of the complete source packet
fields, not merely equality of two scalar limits.

Entrywise Gamma multiplication has norm tending to one and Sonin compression is contractive.
Applying them to the common coupling preserves `(21)` and the upper budget:

```text
limsup epsilon E||Q_Sonin G_Gamma G_E||_2^2<=4.          (22)
```

Thus the four-unit packet geometry has been transferred to the actual positive Euler current
before any Xi divisor expansion.

## RH contribution and exact remaining seam

The infinitesimal completed source is already known exactly:

```text
partial_alpha Theta_alpha(z)|_(alpha=0)
 =-2 Xi'(s)/Xi(s),
s=1/2-iz,                                                (23)
```

and `(6)` is its prime-power leg before Gamma completion.  Equations `(4)`, `(6)`, and `(19)`--`(22)`
therefore remove two ambiguities from the RH route:

1. the anti-causal normal readout must be the logarithmic fixed current, not an arbitrary
   contraction of the squarefree projection;
2. the metric source presented to that readout can be the Euler prime-current packet field with
   no loss of critical four-unit energy.

The remaining theorem is a single operator statement.  On the common Gamma/Sonin charged graph,
prove that the anti-causal fixed-current codifferential taking the completed Euler packet edge
field to the contour-jump part of `(23)` is closed and nonexpansive.  This is not proved here; its
output is the RH-bearing profile `ell_E`.

## No-go and positive HT consequences

### 1. One-clock diagonalization fails

Equation `(8)` disproves the diagonal shortcut.

**Positive HT statement:** tangential escape and normal constraint response can be independent
clocks even when a one-parameter specialization exists.  The invariant current is recovered only
by the ordered normal derivative.

### 2. Metric orientation is not enough

The squarefree and Euler laws are asymptotically indistinguishable in `W_1` and in packet energy,
but only the Euler law is the fixed current of the source multiplier.

**Positive HT statement:** a critical metric class may contain several asymptotically isometric
realizations, while a logarithmic current selects a distinguished source orientation inside that
class.

### 3. Bounded scalar overlap readouts collapse

The overlap `(3)` is of order `epsilon^2` on the moving aperture, while its logarithmic current has
a nonzero limit.  Extracting the current from the amplitude is therefore singular in the ordinary
Hilbert norm.

**Positive HT statement:** the charged graph is not optional decoration.  It is the natural
rigged norm in which a vanishing multiplicative torsor amplitude retains a finite fixed current.

## Novelty and anti-theatre gate

The ingredients `-zeta'/zeta=sum Lambda(n)n^(-s)`, Laplace-transform convergence, `W_1`
convergence by first moments, monotone coupling, and logarithmic-current invariance are standard
parents.  Targeted external searches found no statement combining the exact Mobius multiplier
current `(4)`, the two-clock noncommutation `(7)`--`(9)`, the squarefree/von-Mangoldt critical
transport `(14)`--`(15)`, and the complementary-packet asymptotic isometry `(19)`--`(22)`.

That negative search is not a novelty declaration.  The card remains `LITERATURE NOVELTY OPEN`.
The theorem is not an RH proof because it does not establish the charged anti-causal
codifferential estimate.

## Gates

- [x] exact Mobius multiplier logarithmic current computed
- [x] current identified with the positive von Mangoldt law
- [x] packet normal derivative identified with the same current
- [x] diagonal one-clock shortcut falsified exactly
- [x] ordered two-clock law proved
- [x] squarefree and Euler critical clocks proved `W_1`-equivalent
- [x] squarefree and Euler critical Fisher scores proved `W_2`-equivalent
- [x] canonical monotone coupling constructed
- [x] prime-current four-unit Gini law proved
- [x] complementary packet transport cost proved vanishing
- [x] Gamma/Sonin upper budget transferred to the Euler current
- [x] formalize the fixed-current identities in Lean
- [ ] formalize the transport identities `(14)`--`(22)` in Lean
- [ ] prove the charged anti-causal codifferential is nonexpansive
- [ ] identify its graph limit with `ell_E`
- [ ] independent specialist literature audit
- [ ] RH

## Lean formalization (fixed-current layer)

`formal/GaloisForLFunctions/RHTower/MobiusFixedCurrentVonMangoldt.lean` (imported by
`GaloisForLFunctions.RHTower`; builds clean; every result axiom-clean).

| Card item | Lean name |
|---|---|
| the von Mangoldt current `A(s) = -ζ′/ζ(s)` | `RHTower.vonMangoldtCurrent` |
| the moving multiplier `(3)` `τ_σ(u) = ζ(2σ)/[ζ(σ)ζ(σ+uε)]` | `RHTower.mobiusMovingMultiplier` |
| **`(4)`** the fixed current `∂_u τ = ε·A(σ+uε)·τ`, i.e. `logDeriv τ (u) = ε·A(σ+uε)` | `RHTower.hasDerivAt_mobiusMovingMultiplier`, `RHTower.logDeriv_mobiusMovingMultiplier` |
| the packet series `C(α,s) = ζ(s-α)/ζ(s+α)` | `RHTower.suzukiPacketDirichlet` |
| **`(7)`** `∂_α C(α,s)\|₀ = 2A(s)` on `re s > 1` | `RHTower.hasDerivAt_suzukiPacketDirichlet` |
| **`(8)`** the diagonal collapse `C(α,1+2α) → 3` | `RHTower.tendsto_suzukiPacketDirichlet_diagonal` |
| **`(9)`/`(12)`** `cε·A(1+cε) → 1` for every scale `c > 0` | `RHTower.tendsto_mul_vonMangoldtCurrent_scaled` |
| **`(11)`** `A(1+(1+u)ε)/A(1+ε) → 1/(1+u)` — the mean-one exponential Laplace transform | `RHTower.tendsto_eulerClockLaplace` |
| the derivative residue `(s-1)²A′(s) → -1` | `RHTower.tendsto_sub_one_sq_mul_deriv_vonMangoldtCurrent` |
| **`(13)`** `-εA′(1+ε)/A(1+ε) → 1` — the first moment of the critical Euler clock | `RHTower.tendsto_eulerClockFirstMoment` |
| the second derivative residue `(s-1)³A″(s) → 2` | `RHTower.tendsto_sub_one_cube_mul_deriv2_vonMangoldtCurrent` |
| **`(15a)`** `ε²A″(1+ε)/A(1+ε) → 2` — the second moment of the critical Euler clock | `RHTower.tendsto_eulerClockSecondMoment` |

`(6)` is already in the corpus as `RHTower.hasDerivAt_suzukiShiftedCoefficient`
(`∂_α c_α(n)\|₀ = 2Λ(n)`), and the squarefree half of `(11)` as
`RHTower.tendsto_squarefreeMobiusBoundaryLayerLaplace`.  The no-go `(8)` and the ordered two-clock
law `(7)`--`(9)` are therefore machine-checked in full.

### What remains for the Lean transport layer

`(14)`--`(22)`: `W₁`/`W₂` convergence of the two clocks (their moment inputs `(13)` and `(15a)` are proved above), the monotone quantile coupling, the
prime-current four-unit Gini law `(16)`--`(17)`, and the complementary-packet asymptotic isometry.
These need transport-distance and coupling infrastructure that mathlib does not yet carry; the
analytic inputs they consume — `(11)`, `(13)` and their squarefree counterparts — are now proved.
