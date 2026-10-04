# The chronological theta cutoff commutator collapses to a Möbius Gaussian boundary source

- **ID:** `theta-deletion-cutoff-commutator-collapse`
- **Stage:** 3-formalized
- **Type:** exact shell identity, moving-boundary limit, cofinal Mellin classification
- **Routes:** STC, CSB, U; theta source transport
- **Status:** `[PROVED HERE ON PAPER] [FORMALIZED IN LEAN] [NOT AN RH PROOF]`
- **Lean:** `GaloisForLFunctions.RHTower.ThetaCutoffCommutatorShell`, `ThetaCutoffCommutatorCofinalLimit`, `ThetaCutoffCommutatorMellin`, `ThetaCofinalCurrentSignChanges`, `ThetaPrimeScheduleSpectralObservation`, `ThetaNaturalScheduleEulerOscillation`; certificate [theta-deletion-cutoff-commutator-collapse-formalized.md](theta-deletion-cutoff-commutator-collapse-formalized.md).
- **Dependencies:** [literal theta atom and boundary packet](../../3-formalized/theta/theta-euler-critical-boundary-mass-escape.md), [finite prime deletion](../../3-formalized/theta/theta-prime-deletion-spectral-escape.md), ordinary Euler product for `1/ζ(s)` when `Re s>1`.

## What actually fails to commute

Write the completed theta source as `k(x)=∑_(n≥1) a_n(x)`, where

```text
a_n(x)=n^(−1/2)h(x+log n),
e^(x/2)a_n(x)=e^x g(n e^x),
g(t)=−2π d/dt [t³ exp(−πt²)].
```

Let `K_N=∑_(1≤n≤N)a_n`, and let `D_S=∏_(p∈S)(1−p^(−1/2)T_(log p))` for a finite prime set `S`, with `P=∏_(p∈S)p`. Since `p^(−1/2)T_(log p)a_n=a_(pn)`, inclusion–exclusion gives the **exact cutoff commutator source**

```text
C_(S,N)(x):=D_S K_N(x)−∑_(1≤m≤N,(m,P)=1)a_m(x)
           =∑_(d|P) μ(d) ∑_(N<dn≤dN) a_(dn)(x).       (1)
```

The `d=1` shell is empty. Thus deletion operators commute with one another, but applying their shifts before an integer cutoff differs from cutting the already deleted source by precisely the atoms crossing `N`. For one prime, the difference is `−∑_(N<m≤pN,p|m)a_m`.

## Exact moving-boundary profile

Fix `S`, set `x=y−log N`, and weight by the critical half-density. For each `d|P`, the Riemann sum over `N<dn≤dN` has step `d/N`. Uniformly on compact `y`-intervals,

```text
e^((y−log N)/2) C_(S,N)(y−log N) → C_S(y)
  = ∑_(d|P) μ(d)/d ∫_(exp y)^(d exp y) g(t)dt
  = −2π exp(3y) [∑_(d|P) μ(d)d² exp(−πd²exp(2y))
                  − E_S(1)exp(−πexp(2y))],          (2)
E_S(s)=∏_(p∈S)(1−p^(−s)).
```

The primitive of `g` proves the second equality. Equation (2) is a finite, source-exact boundary law; no zero or analytic continuation enters it. Each `C_S` has zero ordinary integral, reflecting the zero critical moment of every finite shell atom.

For `Re z>−3`, the Mellin transform of (2) exists absolutely and is

```text
∫_ℝ exp(zy) C_S(y)dy
  = π^(−(z+1)/2) Γ((z+3)/2) [E_S(1)−E_S(1+z)].       (3)
```

Indeed `∫ exp((z+3)y)exp(−πd²exp(2y))dy` equals
`(1/2)d^(−z−3)π^(−(z+3)/2)Γ((z+3)/2)`. In particular, one fixed prime gives only the factor `(p^(−z)−1)/p`, whose zeros form an imaginary arithmetic lattice. Its moving shell has no Xi numerator.

## Universal joint-limit collapse: no critical prime breadth

The signed error has more structure than an absolute Riemann bound reveals. Set
`q_y(t)=exp(y)g(exp(y)t)` for `t≥0`. For a divisor `d|P`, use mesh
`h=d/N` on `(1,d]`. The corresponding term in the left side of (2) is
`(1/d)h∑_(1<nh≤d)q_y(nh)`, whereas its limit term is
`(1/d)∫_1^d q_y(t)dt`. Integration by parts against the step function
`h⌊t/h⌋−t=−h{t/h}` gives the **exact**, not asymptotic, error

```text
(1/d)[h∑_(1<nh≤d)q_y(nh)−∫_1^d q_y(t)dt]
 = (1/N)[{N/d}q_y(1)+∫_1^d {Nt/d}q_y'(t)dt].       (3a)
```

The upper endpoint has zero fractional part because `d/h=N` is an integer. Define the centered rough-number discrepancy

```text
A_S(X)=∑_(d|P) μ(d){X/d}
      =X E_S(1)−R_S(X),
R_S(X)=#{1≤m≤X:(m,P)=1}.                            (3b)
```

The second equality is finite inclusion–exclusion applied to the floor terms. Summing (3a) over `d|P` yields a source-weighted **sieve discrepancy identity** for the complete joint error:

```text
Δ_(S,N)(y):=e^((y−log N)/2)C_(S,N)(y−log N)−C_S(y)
 = q_y(1) A_S(N)/N
   + ∫_1^∞ q_y'(t) H_(S,N)(t)/N dt,
H_(S,N)(t)=∑_(d|P,d≥t) μ(d){Nt/d}.                (3c)
```

Now let `S_N` be **any** cofinal sequence of finite prime sets: each fixed prime belongs to `S_N` eventually. No bound on `|S_N|`, its product, or its growth rate is imposed. In fact the rough-number density vanishes **uniformly above the cutoff**:

```text
η_N:=E_(S_N)(1)+sup_(X≥N) R_(S_N)(X)/X → 0.          (3d)
```

Indeed `E_(S_N)(1)→0`. For any fixed finite prime set `F⊆S_N` eventually and any `X≥N`,
`R_(S_N)(X)≤R_F(X)≤X E_F(1)+∏_(p∈F)p`. Divide by `X`, take a supremum and limsup, then increase `F` through all primes. This uses only the periodic count of integers coprime to fixed `F` and Euler's reciprocal-prime divergence. Equation (3b) gives `|A_(S_N)(Nt)|/N≤tη_N`. Moreover
`H_(S_N,N)(t)=A_(S_N)(Nt)−∑_(d|P_N,d<t)μ(d){Nt/d}`; the second sum has fewer than `t` terms. Thus `|H_(S_N,N)(t)|/N≤t(η_N+1/N)` for **every** `t≥1`.

The literal Gaussian polynomial also gives two bounds independent of the moving coordinate `y`:
`sup_y|q_y(1)|<∞` and
`∫_1^∞t|q_y'(t)|dt=∫_(exp y)^∞u|g'(u)|du≤∫_0^∞u|g'(u)|du<∞`.
Equation (3c) therefore proves the stronger uniform estimate

```text
sup_(y∈ℝ)|Δ_(S_N,N)(y)| ≤ C_g(η_N+1/N) → 0.          (3e)
```

Since `C_(S_N)→C_∞` locally uniformly, the simultaneous prime/cutoff
moving-boundary limit is always `C_∞` locally uniformly. The discrete
Riemann error itself vanishes even when `y` moves arbitrarily with `N`.
The apparently critical `2^|S|≈N` regime from an absolute divisor count
does not retain a new phase: signed sieve density removes that error too.

There is a stronger observation-level consequence. The absolute Gaussian
sum bounds `sup_(S,y)|C_S(y)|<∞`: for `t=exp y≤1`, compare
`t³∑_(d≥1)d²exp(−πd²t²)` with its integral; for `t≥1`, Gaussian
decay is uniform. Equation (3e) and dominated convergence then give,
for every finite complex Borel measure `ν` on the moving coordinate,

```text
∫ e^((y−log N)/2) C_(S_N,N)(y−log N) dν(y)
   → ∫ C_∞(y)dν(y).                                (3f)
```

Thus every fixed finite-variation observation of this joint boundary
source sees the same reciprocal-zeta limit. A complex spectral test
that grows toward the negative cusp is outside (3f); its admission
and orientation remain separate hard questions.

The spectral observation can be kept exact at every finite stage. Put
`G(z)=π^(−(z+1)/2)Γ((z+3)/2)`, let
`H_N(s)=∑_(1≤n≤N)n^(−s)`, and let
`H_(S,N)^rough(s)=∑_(1≤n≤N,(n,P)=1)n^(−s)`.
The literal atom Mellin integral, valid when `Re z>−3`, gives

```text
∫_ℝ exp(zy)e^((y−log N)/2)C_(S,N)(y−log N)dy
 = z G(z) N^z [E_S(1+z)H_N(1+z)
                − H_(S,N)^rough(1+z)].            (3g)
```

To prove it, integrate (1) termwise, use
`∫ exp((z+1/2)x)a_m(x)dx=zG(z)m^(−1−z)`, and regroup
the shell as all `d|P,n≤N` minus all `m≤N,(m,P)=1`.
Equation (3g) is the exact **complex weighted rough-number discrepancy**.
It retains the completed theta atom factor and the incomplete arithmetic
phase before a limit. The real-line bounded-observation theorem (3f)
does not control (3g) at weights growing into the negative cusp.
Write `M_(S,N)(z)` for the left side of (3g).

### The complex spectral observation is schedule-dependent

Fix `s=σ+iτ` with `1/2<σ<1` and `τ≠0`, and put `z=s−1`.
Let `B_N=H_N(s)`. The corpus's partial-zeta asymptotic gives
`B_N=N^(1−s)/(1−s)+ζ(s)+o(1)`, so `B_N≠0` for all large `N`.
For either sign and any prescribed magnitude, there is a **finite**
set of primes above `N` whose Euler factors drive
`|∏(1−p^(−s))|` above or below that magnitude. Here is the
source-independent prime-supply proof. Choose narrow, periodically
repeated intervals of `|τ|log p` around `0` and around `π`.
On the first, `cos(τ log p)≥c>0`; on the second it is `≤−c`.
For sufficiently large `p`, respectively,

```text
log|1−p^(−s)| ≤ −c₁ p^(−σ),
log|1−p^(−s)| ≥  c₁ p^(−σ).
```

Each phase interval corresponds to a fixed-ratio multiplicative
prime interval `[x,Cx]`. The prime number theorem gives
`∑_(x≤p≤Cx)p^(−σ) ≫ x^(1−σ)/log x→∞` as the interval moves out.
Taking every prime in one sufficiently late interval therefore makes
the finite product arbitrarily small or large. No assumption about
the unknown zeta zeros enters this prime-supply argument.

Choose `S_N^−` to contain every prime `≤N` and enough later primes
from the first phase class that
`|E_(S_N^−)(s)B_N|≤1/N`. Choose `S_N^+` to contain the same
mandatory primes and enough later primes from the second class that
`|E_(S_N^+)(s)B_N|≥N^(2−σ)`. Both sequences are cofinal. Since
`H_(S_N^±,N)^rough(s)=1`, equation (3g) becomes

```text
M_(S_N^±,N)(s−1)
 = (s−1)G(s−1)N^(s−1)[E_(S_N^±)(s)B_N−1].       (3h)
```

The first sequence has `M_(S_N^−,N)(s−1)→0`, whereas the modulus
of the second tends to infinity. Thus **no schedule-independent
complex spectral limit exists** at any such nonreal strip point,
despite the uniform real-source error (3e) and the common local
limit (4). This does not rule out a law for one canonical prime
schedule. It proves that cofinality alone cannot be the missing
source-derived phase constraint.

Even the natural schedule `S_N^nat={p:p≤N}` has no ordinary complex
spectral limit there. The prime number theorem and Abel summation give

```text
∑_(p≤N) p^(−s)
  = N^(1−s)/((1−s)log N) + o(N^(1−σ)/log N).         (3i)
```

Explicitly, partial summation writes the left side as
`π(N)N^(−s)+s∫_2^N π(x)x^(−s−1)dx`.
Substitute `π(x)=x/log x+o(x/log x)`; the main integral is
`s N^(1−s)/((1−s)log N)+o(N^(1−σ)/log N)`, and the
PNT error integral is of the same little-o order.

Since `2σ>1`, the sum of the quadratic Euler-log errors
`∑_p O(p^(−2σ))` converges. Consequently

```text
log|E_(S_N^nat)(s)|
 = −Re[N^(1−s)/((1−s)log N)]
   + o(N^(1−σ)/log N).                              (3j)
```

The leading real part has amplitude
`N^(1−σ)/(|1−s|log N)→∞` and rotates with `τ log N`.
Choose integer subsequences whose logarithms approach the alternating
phase peaks; consecutive `log N` gaps tend to zero. Equation (3j)
gives subsequences with `|E_(S_N^nat)(s)|→0` faster than every power
and with `|E_(S_N^nat)(s)|→∞` faster than every power.
On the first, (3h) and the partial-zeta asymptotic give
`M_(S_N^nat,N)(s−1)→0`; on the second,
`M_(S_N^nat,N)(s−1)=−G(s−1)E_(S_N^nat)(s)(1+o(1))`,
so its modulus diverges. The raw canonical spectral observation
oscillates at **every** nonreal point of this strip, independently
of the Xi divisor. A proof cannot infer zero location from its
unrenormalized limit; a valid phase law would need a source-derived
renormalization retaining the signed arithmetic remainder.

There is one exact but **nonproductive** scalar renormalization. Since
`H_(S_N^nat,N)^rough(s)=1`, equation (3h) rearranges to

```text
[M_(S_N^nat,N)(s−1)/( (s−1)G(s−1)N^(s−1) )+1]
   / E_(S_N^nat)(s) = H_N(s).                       (3k)
```

Subtracting `N^(1−s)/(1−s)` from the right side converges to
`ζ(s)` by the already formalized partial-zeta asymptotic. Thus
normalizing away precisely the violent finite Euler envelope
recovers the ordinary zeta partial sum, with no new source inequality.
The Xi divisor is the first finite-size correction after this
normalization; locating it still needs an independent signed law.

## Cofinal classification

Let finite prime sets increase through all primes. The first sum in (2) converges absolutely and locally uniformly for every `y`. Euler's divergence of reciprocal primes gives `E_S(1)→0`. Therefore the canonical cofinal boundary source is

```text
C_∞(y)=−2π exp(3y)∑_(d≥1) μ(d)d² exp(−πd²exp(2y)). (4)
```

Absolute comparison with `∑ d² exp(−c d² exp(2y))` shows `C_∞(y)=O(1)` as `y→−∞`; it has Gaussian decay as `y→+∞`. For `Re z>0`, the absolute sum of the individual Mellin integrals is bounded by a constant times `∑d^(−1−Re z)`. Consequently

```text
∫_ℝ exp(zy) C_∞(y)dy
  = −π^(−(z+1)/2) Γ((z+3)/2) / ζ(1+z).             (5)
```

The same formula follows by taking the cofinal limit of (3) in this half-plane. Gamma has no zeros there. All arithmetic divisor data of this fixed-scale chronological boundary observation is therefore the reciprocal zeta factor; the Xi numerator of the completed theta source has disappeared.

The cofinal current also has **both signs arbitrarily far into the negative cusp**. If `C_∞(−t)` were eventually of one sign, remove a finite head and reverse its sign if necessary. The remaining nonnegative Laplace carrier has an abscissa `c≤0` by the bound above. Any nontrivial zeta zero `ρ` gives a genuine nonreal pole of (5) at `z=ρ−1`, so `c≥Re ρ−1>−1`. But (5) and the finite-head correction are holomorphic at every real `z∈(−1,0]`: zeta has no real zero on `(0,1)`, and its pole at `1` becomes a zero of the reciprocal. Landau's real-abscissa singularity theorem contradicts holomorphy at `c`. Thus no eventually positive or negative boundary-current model survives even before asking for RH-scale decay.

## Consequence for the proposed jump

The commutator identifies the genuine location of chronology: the *cutoff shell*, not the order of commuting prime deletions. Its signed Euler-summation error is exactly a rough-number discrepancy, and (3e) proves that **every** cofinal prime/cutoff schedule has the same smoothed Möbius limit (4). There is no hidden breadth threshold for this scalar boundary observation. A bound strong enough to place (5) past `Re z=−1/2` would itself require RH-scale Möbius cancellation. The commutator, at any cofinal schedule, supplies no independent zero-location law.

The positive survivor is the exact source-weighted sieve identity (3c) and its complex counterpart (3g). They locate arithmetic information before the scalar moving-boundary limit, in the full signed rough-number field across the `Nt` family. Equation (3h) shows that an unbounded spectral observer needs a **canonical, source-selected prime chronology**: arbitrary cofinal schedules can make its value vanish or diverge at the same spectral point. Equations (3i)–(3k) show that the natural chronology also has no raw spectral limit, while its elementary Euler normalization returns to the ordinary zeta partial sum. A future law must therefore control a nontrivial signed remainder of that canonical chronology and prove an independent orientation inequality. Literature novelty of the commutator interpretation has not been established.

## Log

- 2026-10-04: all displayed results formalized unconditionally (six modules, standard axioms only); moved to 3-formalized.
