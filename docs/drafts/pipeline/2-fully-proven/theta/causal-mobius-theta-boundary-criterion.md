# Causal Möbius–theta boundary criterion

- **ID:** L-PSRC-CMT
- **Stage:** 2-fully-proven (criterion only)
- **Type:** THEOREM (paper); source bound open
- **Routes:** L, PSRC, HDL
- **Statement:** Subpower growth of one literal one-sided Möbius–theta commutator tail is equivalent to RH.
- **Source geometry:** Completed theta reflection makes that tail a smooth
  wavelet coefficient of the Euler-deletion predictable drift. An exact
  flat gauge localizes all possible off-line growth to joint prime-power
  history clocks between approximately `N` and `N^(5/4)`; signed
  covariance there remains open.

## Source and boundary

Let `k = thetaCuspFullSource`. The corpus proves that `k` is even, positive,
strictly decreasing on the positive ray, and has an exponential bound there,
as does its derivative. For `t ≥ 1`, define the pointwise absolutely
convergent causal tail

```text
B(t) = sum_{n>t} μ(n) n^(-1/2) k(log(n/t)).                 (1)
```

With `T_n f(x)=n^(-1/2) f(x+log n)` and `P_+ f=1_{x>0}f`, equation (1) is
`-[P_+, sum_n μ(n)T_n]k(-log t)` away from boundary conventions. For a finite
prime set `P`, the corresponding sum over divisors of `prod(P)` is the literal
Euler-prime filter; those sums converge pointwise to the series in (1) on this
source. Thus (1) keeps the one-sided boundary discarded by full-line Möbius
inversion. It is a signed arithmetic observable, with no Xi value or zero in
its definition.

## Paper theorem [PROVED HERE]

```text
RH  ↔  for every ε>0, there is C_ε such that
        |B(t)| ≤ C_ε t^ε for all t≥1.                    (2)
```

Put `K(w)=integral_{0}^{∞} k(u)e^{wu} du`, initially for `Re w<1`, and
`F(w)=integral_{1}^{∞} B(t)t^(-w-1) dt` wherever admitted. For
`1/2<Re w<1`, absolute Fubini and `s=w+1/2` give the exact boundary identity

```text
F(w) = K(w)(1/ζ(s)-1) - E(w),
E(w) = sum_{n≥2} μ(n)n^(-s)
       integral_{log n}^{∞} k(u)e^{wu} du.              (3)
```

`E` is holomorphic throughout `Re w<1`: on a compact substrip, each
summand is `O(n^(-3/2))`, by the source's positive-ray exponential bound.
Under (2), `F` is holomorphic on `Re w>0`, since on each compact subset one
can choose `ε<Re w`. Multiplying (3) by `ζ(s)` and continuing meromorphically
across the connected strip `0<Re w<1` yields

```text
ζ(w+1/2) (F(w)+K(w)+E(w)) = K(w).                       (4)
```

At a hypothetical zeta zero `ρ` with `1/2<Re ρ<1`, set `w=ρ-1/2`.
Equation (4) forces `K(w)=0`. But evenness of `k` and its exact Xi transform
give `K(w)+K(-w)=ξ(1/2+w)=0`, so also `K(-w)=0`. This is impossible for
`Re w>0`: writing `ν(u)=-k'(u)≥0`, with `ν` nonzero and total mass `k(0)`, 

```text
Re(w K(-w))
  = integral_0^∞ [1-Re(e^(-wu))] ν(u) du > 0.         (5)
```

Here `1-Re(e^(-wu)) ≥ 1-e^(-Re(w)u)>0` for `u>0`. Thus (2) excludes all
right-of-centre zeros; the functional equation excludes left-of-centre
zeros.

More sharply, at **every** right-of-centre zero `ρ` of multiplicity `m`, the
meromorphic continuation forced by (3) has a pole of exact order `m`: the
numerator `K(ρ-1/2)=-K(1/2-ρ)` is nonzero by (5). The analytic correction
`K+E` cannot erase that pole. This identifies the full off-line divisor,
including multiplicity, as a causal boundary resonance.

Conversely RH gives `M(x)=sum_{n≤x}μ(n)=O_δ(x^(1/2+δ))` for every `δ>0`
by the corpus's closed Littlewood criterion. Apply Abel summation to (1)
with `f_t(u)=u^(-1/2)k(log(u/t))`:

```text
B(t) = -M(t)t^(-1/2)k(0)
       - integral_t^∞ M(u)u^(-3/2)
           [k'(log(u/t))-k(log(u/t))/2] du.             (6)
```

After `u=t e^v`, the integral is at most `C_δ t^δ` times
`integral_0^∞ e^(δv)(|k'(v)|+k(v)/2)dv`, finite for `0<δ<1`.
This proves (2); larger exponents follow from any smaller one.

## Meaning for the proof chain

The full-line inverse Euler filter cancels Xi and leaves only the Gaussian
seed. One-sided projection changes the problem: its commutator retains a
causal arithmetic tail. The half-line transform `K(-w)` is zero-free by
source monotonicity, so an off-line zero cannot hide through numerator
cancellation in (3). The remaining hard mathematical obstacle is precisely
the source-only subpower bound (2), rather than a value-level Xi identity.
An unconditional proof of (2), followed by formalization of (3)–(6), would
close RH in Lean. No such bound is claimed here.

The obvious absolute estimate is only `O(t^(1/2))`; the existing PNT-scale
Mertens saving remains `t^(1/2-o(1))`. Neither reaches (2). A next attack
must find signed cofinal cancellation in the actual moving window
`n/t>1`, potentially through Route L's prime–cofactor covariance or a
source-faithful singular completion. Local ordered-prime Schur positivity
alone gives no such estimate or current identification.

The source monotonicity gives an exact positive layer-cake bridge to Route L.
Since `k(v)=integral_v^∞ (-k'(y))dy` for `v>0`, absolute interchange in (1)
gives

```text
B(t) = integral_0^∞ (-k'(y)) W(t,y) dy,
W(t,y) = sum_{t<n≤t*exp(y)} μ(n)/sqrt(n).             (8)
```

Thus the sole analytic weight is a positive, source-defined measure; all
unresolved sign lives in multiplicative short-window Möbius sums. Applying
the corpus's arbitrary-weight finite Ramaré identity and then absolute
convergence gives a second exact form, with `ω(m)` the number of distinct
prime factors:

```text
B(t) = -sum_p sum_{m≥1, p∤m, p*m>t}
       μ(m)/(ω(m)+1) * k(log(p*m/t))/sqrt(p*m).        (9)
```

The double series in (9) is absolutely convergent for fixed `t`: each
squarefree integer `n>t` occurs once for every prime divisor, each time
with weight `1/ω(n)`. Equations (8)–(9) identify precisely where Route L's
signed prime–cofactor covariance must enter. The current corpus controls
finite incidence and some error sectors, but it has no RH-scale estimate
for this complete signed moving window.

There is already a **uniform diagonal energy law** for these exact blocks.
Write `a_t(n)=n^(-1/2)k(log(n/t))`. Counting the `ω(n)` representations in
(9) gives

```text
sum_p sum_{m≥1, p∤m, p*m>t}
  |μ(m) a_t(p*m)/(ω(m)+1)|²
    = sum_{n>t, squarefree} |a_t(n)|²/ω(n)
    ≤ sum_{n>t} k(log(n/t))²/n = O(1),               (10)
```

uniformly for `t≥1`. Indeed `k(v)≤C e^(-v)` makes the last expression at
most `C² t² sum_{n>t}n^(-3)`. Thus coefficient magnitude and diagonal
energy are paid **before** any RH assumption. A proof must control the
off-diagonal signed reconstruction covariance; estimating block magnitudes
separately loses the full critical power.

## Physical-source realization [PAPER-PROVED]

The causal tail is also a uniformly bounded observation of the **literal
Euler-deletion physical source**, so these two carriers share the same
unresolved signed drift. This is a one-way source comparison, not a bound on
either carrier.

Write the theta seed and the truncated divisor field as

```text
g(u) = (4*pi^2*u^4 - 6*pi*u^2)*exp(-pi*u^2),
D_N(r) = sum_(d|r, d<=N) mu(d),
H_N = sum_(d<=N) mu(d)/d,
C_N(r) = r*H_N - sum_(j<=r) D_N(j)
       = sum_(d<=N) mu(d)*{r/d},
E_N^2 = sum_(r>=1) C_N(r)^2/[r*(r+1)].
```

`E_N` is exactly the norm of the Möbius source in
`EulerDeletionPhysicalCellMoebiusIdentity.lean`; braces denote fractional
part. The theta atom formula gives
`k(log(n/N))/sqrt(n)=N^(-1/2)*sum_(m>=1)g(m*n/N)`.
Absolute Gaussian convergence permits regrouping by `r=m*n`. For `r>N`,
the complete divisor sum is zero, hence

```text
B(N) = -N^(-1/2) * sum_(r>N) g(r/N)*D_N(r).             (11)
```

This is the Gaussian observation of the *same* truncated Möbius-divisor
field that appears in the physical-cell formula. The decisive simplification
comes from extending the summation by parts across **all** physical cells.
For `1<=r<=N`, complete divisor inversion gives `D_N(r)=1_(r=1)`;
set `C_N(0)=0` and `g_r=g(r/N)`. Since
`D_N(r)=H_N-(C_N(r)-C_N(r-1))`, absolute summation by parts gives

```text
B(N) = N^(-1/2)*[
  g(1/N) - H_N*sum_(r>=1)g_r
  + sum_(r>=1)(g_r-g_(r+1))*C_N(r)].                 (12)
```

The apparent `sqrt(N)*H_N` background in a tail-only calculation is
**annihilated by the completed theta reflection**, before any arithmetic
estimate. Indeed, the atom formula for `k` and its proved evenness give

```text
sum_(r>=1)g(r/N) = N*sum_(m>=1)g(m*N).               (13)
```

The right side is Gaussian-small for `N>=1`; more precisely it is
`O_A(N^(-A))` for every `A>0`. This is the lattice-level zero-mean law
of the literal theta seed, not an assumed cancellation of Möbius signs.

Give sequences the physical inner product
`⟨u,v⟩_H=sum_(r>=1)u(r)*v(r)/[r*(r+1)]`, and define the **smooth complete-cell
wavelet**

```text
q_N(r) = r*(r+1)*(g(r/N)-g((r+1)/N))/sqrt(N),
e_N = g(1/N)/sqrt(N) - H_N*k(log N).                  (14)
```

Equations (12)--(13) prove the exact source identity

```text
B(N) = ⟨C_N,q_N⟩_H + e_N.                            (15)
```

The Gaussian polynomial has `g(u)=O(u^2)` near zero and rapid decay at
infinity. The mean-value theorem therefore gives
`sup_N ‖q_N‖_H<infinity`; for each fixed cell `r`, `q_N(r)=O_r(N^(-5/2))`.
Thus `q_N` tends weakly to zero in `H`. Moreover
the test has two exact discrete moment identities:

```text
sum_(r>=1) q_N(r)/[r*(r+1)] = g(1/N)/sqrt(N),
sum_(r>=1) r*q_N(r)/[r*(r+1)] = k(log N).
```

The second sum is absolutely convergent although the affine sequence
`r` itself is not in `H`. The first moment is `O(N^(-5/2))`; the second
is Gaussian-small by (13). The elementary bound
`|H_N|<=1+log N` and the Gaussian bound on `k(log N)` give
`e_N=O(N^(-5/2))`. Consequently

```text
|B(N)| <= C*(1+E_N)                 for every N>=1.   (16)
```

The source `C_N` is the corpus's exact Möbius residue vector. Its
martingale decomposition is `C_N=I_N+P_N`, with uniformly bounded
innovation norm `‖I_N‖_H<=sqrt(2)` and literal predictable drift `P_N`.
Thus (15) sharpens to

```text
B(N) = ⟨P_N,q_N⟩_H + O(1).                            (17)
```

This is a single, uniformly bounded moving coordinate of the predictable
arithmetic history; the completed theta symmetry has removed the bulk
harmonic mode. Its wavelet has no artificial seam at the causal cutoff.
At continuum scale its profile is `Q(u)=-u^2*g'(u)`. Both physical Mellin
moments vanish exactly:

```text
integral_0^infinity Q(u)/u^2 du = g(0)=0,
integral_0^infinity Q(u)/u du = integral_0^infinity g(u)du=0.
```

The second equality uses the explicit total derivative
`g(u)=-2*pi*(u^3*exp(-pi*u^2))'`. These two cancellations explain why
the complete-cell test rejects constant and affine physical backgrounds.
They do not cancel the Möbius predictable drift.

The existing nested-history decomposition localizes the remaining
coordinate. Set `K_N=5*(log2(N+1)+1)` and let `L_l` denote its orthogonal
history layer. The corpus bounds total squared drift norm in layers
`l>=K_N` by `110/(N+1)` and proves `L_l=0` unless `l+1` is a prime
power. Its base history is the constant vector. A telescoping residue
calculation gives

```text
sum_(r>=1) {r/d}/[r*(r+1)] = log(d)/d.               (18)
```

For proof, cut the sum at `r=d*K`, expand
`floor(r/d)=sum_(j=1)^K 1_(r>=d*j)`, and telescope the reciprocal cell
weights. The result is
`[H_(d*K+1)-1-H_K]/d + K/(d*K+1)`, which tends to
`log(d)/d`. Therefore the base projection of `C_N` and `P_N` is
`sum_(d<=N)mu(d)*log(d)/d` times `1`. The corpus's
`tendsto_moebiusLogHarmonicPartial_one` proves this scalar tends to `-1`;
its pairing with `q_N` is `O(N^(-5/2))`. The high-clock pairing is
`O(N^(-1/2))`. Hence

```text
B(N) = sum_(l<min(K_N,N), l+1 prime power) ⟨L_l P_N,q_N⟩_H
     + O(1).                                          (19)
```

An off-line divisor would therefore force polynomial growth in a joint
covariance of only `O(log N)` low prime-power history grades, although
the source includes all integers up to `N`. Each such grade contains the
complete joint history of smaller moduli; it is not an isolated-prime
estimate. Equation (19) localizes the hard signed producer without
bounding it.

### Smooth-gauge transition-clock theorem [PAPER-PROVED]

The test in (14) is not the only exact representative of its physical
observation. On the initial cells `r<=N`, the source is the affine line
`C_N(r)=r*H_N-1`. Hence any change `v_N` supported there with

```text
sum_(r<=N) v_N(r)/[r*(r+1)] = 0,
sum_(r<=N) r*v_N(r)/[r*(r+1)] = 0                 (21)
```

leaves `⟨C_N,q_N⟩_H` unchanged. Choose a smooth cutoff `chi` equal to
zero on `[0,1/4]` and one on `[1/2,infinity)`. Multiplying `q_N(r)` by
`chi(r/N)` changes it only on initial cells. Two fixed smooth bumps at
different points of `(1/4,1/2)` restore the two equalities (21). The
correction coefficients are uniformly bounded: after multiplying the
zeroth-moment row by `sqrt(N)` and dividing the first-moment row by
`sqrt(N)`, the two-by-two coefficient matrix tends to the matrix of
`integral phi(u)/u^2 du` and `integral phi(u)/u du`. Bumps around distinct
points make this matrix invertible. For the finitely many small `N`, keep
the original test. Denote the resulting exact test by `q_N^flat`. Then

```text
B(N)=⟨C_N,q_N^flat⟩_H+e_N,
q_N^flat(r)=0 for r<=N/4,
sup_N ‖q_N^flat‖_H<infinity.
```

The moment correction preserves the total test mean in (14). Writing
`w_r=1/[r*(r+1)]`, the weighted sequence has the form
`w_r*q_N^flat(r)=N^(-3/2)*G_N(r/N)`, where `G_N` vanishes on
`(-infinity,1/4]` and its Schwartz seminorms are uniform in `N`.
Its exact discrete sum is `g(1/N)/sqrt(N)`. Poisson summation for this
smooth family therefore gives `integral_R G_N=O(N^(-2))`.

Let `P_Q` be physical orthogonal projection onto sequences periodic
modulo positive integer `Q`. For each residue `a` modulo `Q`, the
projection numerator is the progression sum
`S_a=sum_(r=a mod Q)w_r*q_N^flat(r)`; its denominator is
`V_a=sum_(r=a mod Q)w_r >= 1/[Q*(Q+1)]`.
Progression Poisson summation and the uniform Schwartz bounds give, for
every `A>0`, uniformly in `a` and `1<=Q<=N`,

```text
|S_a| <= C_A/[Q*sqrt(N)] * [N^(-2)+(Q/N)^A],
‖P_Q q_N^flat‖_H
  <= C_A*sqrt(Q/N)*[N^(-2)+(Q/N)^A].                (22)
```

This is a source-derived, all-rate cancellation against periods shorter
than the physical scale. It is stronger than weak convergence of the
unflattened test; the affine initial-cell rigidity makes the flattening
exact on the literal Möbius source.

There is a complementary long-period estimate. Uniform Gaussian decay
gives `sum_(r>=1)|q_N^flat(r)| <= C*N^(3/2)` and
`sum_(r>=1)q_N^flat(r)^2 <= C*N^2`. For `Q>=N`, each conditional
periodic mean differs from its first-cell value only through later
copies in that residue fibre. The total weight of those copies is at
most `C/Q^2`. If `m_a` is that weighted mean, then
`sum_(k>=0)w_(a+kQ)*|q_(a+kQ)-m_a| <=
2*sum_(k>=1)w_(a+kQ)*|q_(a+kQ)-q_a|`. Sum this over fibres,
use `w_r<=Q^(-2)` for `r>Q`, and apply the displayed `ell^1`
bound to prove

```text
sum_(r>=1) w_r*|q_N^flat(r)-P_Q q_N^flat(r)|
  <= C*N^(3/2)/Q^2                           (Q>=N). (22a)
```

Thus very long periods also see almost the same wavelet in two nested
histories, so their **difference layer** has small overlap with the
literal source. Indeed `|C_N(r)|<=N` from its finite fractional-part
sum, and nested self-adjoint projections give

```text
|⟨C_N,L_l q_N^flat⟩_H|
  <= C*N^(5/2)/clock(l)^2       when clock(l)>=N.       (22b)
```

For a prime-power history step `l+1`, put `Q_l=clock(l+1)`. The clock
ratio `Q_l/clock(l)` is its underlying prime, at most `K_N` when
`l<K_N`. The corpus gives
`‖L_l P_N‖_H^2 <= (8*N^2+2)/(clock(l)+1)`.
Pair this with (22) on `Q_l<=N^(1-delta)`, choosing `A>1/delta`;
the whole short-clock sum is `O_delta(1)`. On
`Q_l>=N^(5/4+delta)`, (22b) and `Q_l/clock(l)<=K_N` make the
whole literal-source pairing `O_delta(1)`. Replacing that source by
the predictable drift changes the **sum** by at most
`‖I_N‖_H*‖q_N^flat‖_H=O(1)` through orthogonality of history layers.
High-clock and innovation errors remain bounded. Thus,
for every fixed `delta>0`,

```text
B(N) = sum_(l<min(K_N,N), l+1 prime power,
           N^(1-delta)<clock(l+1)<N^(5/4+delta))
          ⟨L_l P_N,q_N^flat⟩_H
       + O_delta(1).                                  (23)
```

Consequently the RH criterion (2) is equivalent to subpower growth of
the **transition-clock covariance in (23)**. A hypothetical off-line
zero must excite joint old-prime history at periods between approximately
`N` and `N^(5/4)`. This is a narrower source obligation than full drift energy;
it still requires a new signed estimate in that transition band.

A [primorial refinement](causal-mobius-theta-primorial-transition.md)
replaces the lcm filtration by the source's squarefree prime clock. Its
uniformly bounded innovations occur only at new primes, and the same
theta observation localizes to a prime-only signed transition
covariance. The bound on that covariance remains open.

On `N<=t<N+1`, the summation set in (1) is fixed. The established bound
`|k'(x)|<=C_1*exp(-x)` for `x>=0` gives
`|B(t)-B(N)|<=C_2*N^(-1/2)` by termwise differentiation and
`sum_(n>N)n^(-3/2)=O(N^(-1/2))`. Consequently **subpower physical-source
norm** `E_N=O_epsilon(N^epsilon)` for every epsilon is a source-only
sufficient condition for RH through (2). The bounded innovation part of
the existing Euler-deletion martingale shows the same implication with
`E_N` replaced by its predictable-drift norm, up to an additive constant.
Conversely (15)--(17), the interpolation bound, and the proved criterion
(2) give the sharper exact equivalence

```text
RH  ↔  for every epsilon>0,
        |⟨P_N,q_N⟩_H|=O_epsilon(N^epsilon).             (20)
```

At an off-line zero with horizontal displacement `beta>0`, this one
coordinate, and hence the physical norm and predictable drift, violates
every `O(N^epsilon)` bound with `epsilon<beta`.

The reinterpretation changes the unit of attack: (1) is one completed
theta wavelet coefficient of the physical signed source, while the EDQ
norm is its complete Hilbert energy. Theta reflection removes the
harmonic background, and the exact smooth gauge plus clock geometry
remove both the shorter and longer history scales. The remaining hard
producer is the **joint signed covariance in the transition corridor**
of (23); this paper theorem does not estimate it. The Gaussian bridge,
smooth-gauge construction and progression bounds have not yet been
formalized in Lean. Corpus searches found the physical-cell, high-clock
and prime-power ingredients, but no theta observation bridge; some deep
retrieval was partial, so this is an internal search conclusion only.

There is an exact finite-prime stability law. Let `B^(p)(t)` be (1) with
`p ∤ n`, defined also for `0<t<1`. Möbius multiplicativity gives

```text
B(t) = B^(p)(t) - p^(-1/2) B^(p)(t/p),
B^(p)(t) = sum_{j≥0} p^(-j/2) B(t/p^j).               (7)
```

The inverse series converges absolutely: for `u<1`, the source bound
`k(log(n/u)) ≤ C u/n` gives `B(u)=O(u)`. Equation (7) shows that (2) is
equivalent to the same subpower bound for `B^(p)`; iterate for any fixed
finite prime set. Hence a single prime packet cannot create the needed
regularity. The producer must control the cofinal all-prime limit or a
genuinely nonlocal source interaction.

## Corpus anchors and audit

- `HedenmalmThetaSourceUnconditional.lean`: positive even `k` and Xi landing.
- `PrimeArchThetaFlatWindowGramFloor.lean`: positive-ray antitonicity from a
  strict two-point source law.
- `HedenmalmThetaSourceUnconditional.lean` and
  `ThetaCuspFourierLaplace.lean`: strip-integrable source and exact transform.
- `XiThetaLogTranslationSeam.lean`: half-line translation commutator.
- `MobiusMertensLittlewood.lean`: RH iff all strict half-power Mertens bounds.
- `ThetaCuspFinitePrimeSource.lean` and `ThetaCuspFinitePrimeDerivatives.lean`:
  Gaussian atom formula and rapid source derivatives in (11)--(15).
- `EulerDeletionPhysicalCellMoebiusIdentity.lean`: exact truncated-divisor
  cells, physical norm and initial-cell harmonic control.
- `EulerDeletionResidueMartingale.lean`, `EulerDeletionLogClockLocalization.lean`
  and `EulerDeletionPrimePowerLayerSupport.lean`: bounded innovations,
  high-clock energy and prime-power history support used in (19)--(23).
- `Sieve/MoebiusLogarithmicNormalization.lean`: convergence of the base
  history scalar in (18).
- `MobiusHaarRamareFullPrimeCofactor.lean`: arbitrary-weight finite
  prime–cofactor identity used in (9).
- `MobiusThetaNativeMellinPole.lean` is a distinct native-collar tail: its
  numerator has a nonzero cofinal limit at every divisor, including line
  zeros. It does not contain (1) or (3).
- `MobiusLaplaceCriterionFrontier.lean` formalizes a different smoothed
  Möbius criterion with the zero-free Gamma numerator. Here the numerator
  is the physical half-theta transform; its noncancellation at off-line
  zeros requires **both** source reflection and positive-ray monotonicity.

Broad hybrid and mechanism-directed deep corpus searches on causal theta,
Möbius tails, Green current, Herglotz and Schur assembly found these
ingredients but not the criterion (2). Results were partial, so this is an
internal search conclusion, not an external novelty claim. The short broad
arXiv search for causal/Mellin, renewal/boundary and Wiener–Hopf/positive
methods supplied no usable source bound. This card is a paper proof, not a
Lean certificate.
