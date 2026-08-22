# Orbit-sensitive continuation forces inverse-horizontal residue charge

- **ID:** `orbit-sensitive-continuation-horizontal-charge-norm-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent results:** Cauchy-kernel boundary norms, Laplace transforms of exponential modes, and
  the Xi rational-quartet gauge countermodel
- **Statement:** Ordinary Hardy size on a fixed Euler line cannot control orbit-sensitive
  meromorphic continuation uniformly near the critical line. A pole at horizontal depth `a` has
  bounded Euler-line norm but residue energy proportional to `1/a`. Hence every bounded
  orbit-sensitive continuation must put an explicit inverse-horizontal residue charge in its
  domain norm, or use an equivalent meromorphic graph coordinate.

## 1. One-pole model

Fix `Y>0`. For `0<a<Y`, `gamma in R`, and `c in C`, put

```text
w_(a,gamma)=-gamma+i a,
q_(a,gamma,c)(z)=c/(z-w_(a,gamma)).                       (1)
```

The fixed Euler-line norm is

```text
||q||_Y^2=integral_R |q(x+iY)|^2 dx.                     (2)
```

Define the reflected residue mode, with the harmless Fourier phase convention fixed once and for
all, by

```text
J q(t)=c exp(-a t) exp(i gamma t),       t>0.             (3)
```

Then

```text
||q_(a,gamma,c)||_Y^2=pi |c|^2/(Y-a),                    (4)

||J q_(a,gamma,c)||_2^2=|c|^2/(2a).                      (5)
```

Consequently

```text
||J q||_2^2/||q||_Y^2=(Y-a)/(2 pi a).                    (6)
```

In particular, the ratio tends to infinity as `a` decreases to zero, independently of the
ordinate `gamma`.

### Proof

On the line `Im z=Y`,

```text
|q(x+iY)|^2
 =|c|^2/((x+gamma)^2+(Y-a)^2).
```

The Cauchy integral

```text
integral_R dx/(x^2+b^2)=pi/b,       b>0,
```

gives `(4)`. Direct integration gives

```text
integral_0^infinity |c|^2 exp(-2a t)dt=|c|^2/(2a),
```

which is `(5)`. Division proves `(6)`.

## 2. No uniformly bounded orbit-sensitive continuation

Let `C_Y` be a linear map whose domain contains all pole generators `(1)` and which agrees with
the meromorphic contour jump:

```text
C_Y q_(a,gamma,c)=J q_(a,gamma,c).                        (7)
```

Then for every `0<a<Y`,

```text
||C_Y|| >=sqrt((Y-a)/(2 pi a)).                           (8)
```

Therefore no bounded map from the ordinary fixed-line Hardy norm can satisfy `(7)` for all
`a>0`.

The conclusion is not restricted to linear maps. Suppose a continuation rule `G` is covariant
under rational source gauges in the sense that

```text
G(S+q_(a,gamma,c))-G(S)=J q_(a,gamma,c)                   (9)
```

for a fixed pointed source `S`. If `G` is Lipschitz in the norm `(2)` with a constant independent
of `a`, equations `(6)` and `(9)` give the same contradiction. Thus a universal bounded or
uniformly Lipschitz gauge-covariant continuation is impossible.

## 3. Full FE--Schwarz orbit

The preceding divergence survives the completed-function symmetries. Let `m>=1`, `gamma>0`, and

```text
Q_(a,gamma)(s)
 =(((s-1/2)-a)^2+gamma^2)
  (((s-1/2)+a)^2+gamma^2).                               (10)
```

The zeros of `Q_(a,gamma)^m` form the FE--Schwarz quartet

```text
1/2+a+i gamma,  1/2+a-i gamma,
1/2-a+i gamma,  1/2-a-i gamma.                           (11)
```

In the coordinate `s=1/2-i z`, the completed logarithmic-source correction

```text
q_sym(z)=-2 Dlog(Q_(a,gamma)^m)(1/2-i z)                 (12)
```

has four simple pole terms, each with residue of modulus `2m`, at

```text
-gamma+i a,  gamma+i a,  -gamma-i a,  gamma-i a.         (13)
```

The contour jump sees the two upper poles and is, up to a fixed unit phase,

```text
J q_sym(t)
 =2m exp(-a t)(exp(i gamma t)+exp(-i gamma t)).           (14)
```

Its exact energy is

```text
||J q_sym||_2^2
 =4m^2/a+4m^2 a/(a^2+gamma^2)
 >=4m^2/a.                                                (15)
```

On the fixed line `Im z=Y`, the triangle inequality and the four Cauchy-kernel norms give

```text
||q_sym||_Y
 <=4m sqrt(pi)(1/sqrt(Y-a)+1/sqrt(Y+a)).                 (16)
```

For `0<a<=Y/2`, this yields the uniform bound

```text
||q_sym||_Y^2
 <=16m^2 pi(3+2sqrt(2))/Y.                               (17)
```

Combining `(15)` and `(17)`, every orbit-covariant continuation on the symmetric gauge family
obeys

```text
||C_Y||^2
 >=Y/(4 pi(3+2sqrt(2)) a).                               (18)
```

Hence the full symmetry orbit does not cancel the inverse-horizontal blow-up.

### Proof of the energy identity

Equation `(14)` is `4m exp(-a t) cos(gamma t)` up to a unit phase. Since

```text
integral_0^infinity exp(-2a t) cos(gamma t)^2 dt
 =1/(4a)+a/(4(a^2+gamma^2)),                             (19)
```

equation `(15)` follows. Each of the two upper pole terms in `(13)` has line norm
`2m sqrt(pi/(Y-a))`; each lower term has line norm `2m sqrt(pi/(Y+a))`. Their triangle bound is
`(16)`. If `a<=Y/2`, then

```text
1/sqrt(Y-a)<=sqrt(2/Y),
1/sqrt(Y+a)<=1/sqrt(Y),
```

and squaring gives `(17)`. Division proves `(18)`.

## 4. Positive carrier law

Let `D` be any Hilbert graph domain for meromorphic continuation and assume its residue map is
bounded:

```text
J:D->L2(0,infinity),       ||J||<=M.                     (20)
```

If `D` contains the symmetric orbit corrections `(12)`, then `(15)` forces

```text
||q_sym||_D^2>=4m^2/(M^2 a).                             (21)
```

Thus every successful orbit-sensitive continuation is forced to carry an
**inverse-horizontal residue charge**. Equivalently, it must possess at least one of the following
forms of state:

1. a domain norm containing the residue seminorm `||Jq||_2`;
2. an explicit meromorphic graph coordinate for every crossed pole, with its Cauchy Gram metric;
3. a Pontryagin/Krein state whose negative index and norm retain the same residue coordinates;
4. a genuinely pointed construction defined only on the exact Xi source, together with a
   source-specific estimate not asserted uniformly over rational gauges.

The first three descriptions are equivalent ways of paying the charge in `(21)`. The fourth is
the only escape from gauge covariance: it must use arithmetic information distinguishing Xi from
every symmetric orbit insertion.

For a finite right-half divisor `{a_j+i gamma_j}` with multiplicities `m_j`, the native charge is
the Cauchy Gram form

```text
R(q)=||Jq||_2^2
 =4 sum_(j,k) m_j m_k/(a_j+a_k+i(gamma_j-gamma_k)).       (22)
```

with the real value understood after the conjugate pairing. Its diagonal already contributes

```text
2 sum_j m_j^2/a_j.                                       (23)
```

Equation `(22)`, rather than the ordinary Euler-line Hardy norm, is the orbit-sensitive metric
that a continuation graph must transport.

## 5. Consequence for the CCM/Connes route

The signed Möbius multiplier is contractive on the Euler side, and the complete causal source has
a strong critical limit. This theorem proves that those facts cannot extend to the divisor side
through a universal bounded continuation on ordinary Hardy space. The missing arrow is necessarily
an unbounded meromorphic graph before it is renormalized.

The positive remaining target is therefore sharper than “construct a contraction”:

```text
exact Xi source
  -> closed orbit-marked graph carrying the charge R
  -> source-specific pole-to-divisor renormalization
  -> ||ell_E||_2<=2
  -> RH.                                                   (24)
```

Any contraction in `(24)` is a statement in the charged graph norm, not in the fixed Euler-line
Hardy norm. It must also explain why the incoming pole vector has graph charge `4` while every
nonempty off-line divisor would have energy greater than `4`. A generic FE--Schwarz carrier cannot
satisfy that estimate because the orbit family `(10)` has unbounded charge `(15)`.

This does not rule out a pointed Xi-specific theorem, the full Weil criterion, or an exact global
self-adjoint realization. It rules out the universal bounded-continuation implementation and
identifies the precise state a successful replacement must carry.

## 6. Scientific classification and Lean formalization

The proof is an elementary specialization of Cauchy-kernel and exponential-mode norm formulas.
It is a route bridge, not new scientific knowledge. Its value is to convert a failed bounded-map
proposal into the positive inverse-horizontal carrier law `(21)`.

`OrbitSensitiveContinuationCharge.lean` now formalizes the actual one-pole Hardy-line integral,
the actual crossed-residue integral, their exact ratio `(6)`, the quantified failure of every
uniform finite energy bound, and the positive domain-budget law `(21)`. It also identifies the two
right-half Cauchy modes with actual zeros of `centeredQuartetGauge` and proves their exact
`L^2` residue energy `(15)` and inverse-horizontal lower charge. The remaining paper-only analytic
piece is the four-pole fixed-line triangle estimate `(16)`--`(18)` for the complete symmetric
logarithmic correction. No pointed Xi graph or four-unit source-specific upper bound is asserted.

## Gates

- [x] exact one-pole source and residue norms
- [x] universal bounded-continuation obstruction
- [x] full FE--Schwarz quartet divergence
- [x] positive inverse-horizontal graph-charge law
- [x] consequence for the CCM continuation seam
- [x] exact one-pole obstruction and right-half quartet residue charge formalized in Lean
- [ ] full symmetric four-pole fixed-line estimate formalized in Lean
- [ ] construct the pointed Xi residue graph
- [ ] prove source-specific four-unit nonexpansive renormalization
- [ ] RH
