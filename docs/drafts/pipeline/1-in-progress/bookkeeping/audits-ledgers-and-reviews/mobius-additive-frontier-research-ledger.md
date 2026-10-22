# Möbius additive frontier — canonical research ledger

- **ID:** `mobius-additive-frontier-research-ledger`
- **Created:** 2026-07-22
- **Status:** ACTIVE SOURCE OF TRUTH
- **Scope:** Xi/Arakelov--Hurwitz dependence, Möbius--Laplace continuation, additive-convolution
  laws, and publication route outside Suzuki and CCM/Connes.
- **Terminal goal:** prove RH. Nothing weaker closes this ledger.

## Operating rule

This file prevents rediscovery. Before opening any branch, compare it against the theorem registry,
frozen collisions, and dead-route registry below. A branch may re-enter only if it supplies at least
one of:

1. a strictly stronger conclusion on the same hypotheses;
2. strictly weaker hypotheses for the same conclusion;
3. a new invariant that separates cases the recorded theorem cannot separate;
4. a falsifier of a recorded proof or classification;
5. a source estimate strong enough to cross the named RH wall.

Renaming an identity, changing notation, increasing convolution order, or restating a Mellin pole
as a Laplace singularity is not progress. Every candidate theorem receives a stable ID before it is
added to a paper. Superseded candidates remain here and are never silently recycled.

## Exact open core

`OPEN-SOURCE-001` is the only current RH-bearing analytic source on this route:

```text
For every epsilon>0,
  sum_(a+b=N) M(a)M(b) <= C_epsilon (N+1)^(2+epsilon),
```

or an explicitly proved source law that implies the equivalent strict-half-plane decay of

```text
Phi(x)=sum_(n>=1) mu(n)e^(-nx).
```

The decay-to-continuation bridge is already formalized. Higher even convolution order preserves,
rather than weakens, this wall. Lower bounds, sign recurrence, exact Abel identities, and zero-
abscissa reconstruction are scientific results only when genuinely new; none proves RH without a
new upper source.

## Theorem registry and dominance graph

| ID | Statement core | Status | Dominance / consequence | Reopen? |
|---|---|---|---|---|
| `AH-XI-CIRC-001` | Right-half Xi/Arakelov--Hurwitz source predicate collapses to the target RH obstruction under vacuity/collision audit. | corpus-proved no-go | Kills the advertised algebraic-character shortcut unless an independently constructed nonvacuous object is supplied. | No |
| `ML-WALL-001` | Strict-half-power Möbius--Laplace decay gives Mellin continuation and RH. | formalized bridge | Target of `OPEN-SOURCE-001`; not a source theorem. | No |
| `MERTENS-EVEN-001` | Positive-part order of every even Mertens additive convolution is `2k(1+Theta)-1`. | paper-proved; Lean algebraic bridge | Contains all higher-even Mertens criteria and unconditional positive excursions. | No |
| `DIRICHLET-MIXED-001` | Mixed Hermitian Mertens convolution for primitive `chi` has order `2k(1+Theta_chi)-1`. | paper-proved; novelty unverified | Strict generalization of `MERTENS-EVEN-001` to complex primitive characters. | No |
| `RAW-HERM-001` | Raw Hermitian reciprocal-coefficient convolution has positive recurrence and lower positive-part edge `2k Theta_chi-1`. | paper-proved; novelty unverified | New lower-side statement; does not dominate integrated exact law and does not imply RH. | Only for stronger arithmetic conclusion or matching upper edge |
| `PARITY-RAW-001` | Even-index projection of `RAW-HERM-001` is the average of the Hermitian Abel squares at `r` and `-r`; its lower pole edge is `2k theta-1` and positive even coefficients recur. | paper-proved; Lean algebraic core; novelty unverified | Strictly strengthens `RAW-HERM-001` by localizing every conclusion to even totals. | No, except stronger progression/source conclusion |
| `DYADIC-GRAM-001` | For every completely multiplicative `f`, the even binary convolution Abel series is `|F(r)-f(2)F(r^2)|^2+|f(2)F(r^2)|^2`. | paper-proved; Lean parallelogram core; novelty unverified | Refines `PARITY-RAW-001` by exposing the prime-2 local factor as two adjacent dyadic squares. | Active literature audit |
| `DYADIC-BLIND-001` | Every sequence with `a(2n)=ca(n)` is uniquely classified by its odd seed; Mellin factor is `1-c2^(-s)`. | paper-proved exact classification/no-go | Proves dyadic Gram alone cannot supply upper decay; for Liouville the multiplier is a unit on `Re(s)>0`. | No |
| `POWER-SIEVED-001` | De Camargo's known coefficients of `zeta(ms)/zeta(s)` obey the parity-projected raw recurrence and integrated zero-abscissa law. | paper-proved specialization; family known; consequence novelty unverified | Extends Möbius/Liouville conclusions through the known generalized-Liouville ladder. | No, except stronger uniform-in-m law |
| `VISIBLE-NOGO-001` | Visible-coprime identity has Mellin symbol `prod zeta(s_j)/zeta(sum s_j)`; zero modes lie in its radical and finite kernels have Mertens inertia. | paper-proved parent collision/no-go | Kills positive GCD-stationary kernels and positive diagonal completion as RH sources. | No |
| `DYADIC-COV-PREPRINT-NOGO-001` | A current claimed dyadic-covariance proof assumes false coefficient-blind affine shifted-convolution bounds; its formal toolkit is uninhabited. | dependency-closed external-claim no-go | Kills the strongest located claimed unconditional source; forces explicit cusp/main-term projection or genuinely Möbius-specific global cancellation. | No |
| `MERTENS-PRIME-TENT-001` | Removing one Euler prime rewrites every signed Mertens antidiagonal through a nonnegative tent kernel; prime `2` is pointwise optimal, while every second removed prime creates a negative lobe. | paper-proved; Lean connector/core | Classifies local-factor positivity depth as exactly one. Leaves global signed prime-free cancellation as `OPEN-SOURCE-001`. | No, except a global cancellation law using the negative lobes |
| `MOBIUS-TERNARY-INSERTION-NOGO-001` | Exact insertion of a third Möbius factor into constant or linear slack uniquely introduces `tau` or `sigma_1`; the latter has quadratic positive mass. | paper-proved classical no-go | Kills direct use of ternary Möbius estimates on the unweighted Mertens tent. A viable third variable must be geometric, not Dirichlet-inverted slack. | Only with power-saving weighted ternary theorem or lower-variation non-Dirichlet insertion |
| `MOBIUS-LAMBERT-TERNARY-NOGO-001` | Lambert dilation inserts a third Möbius factor exactly, but its divisor fibre sums to `delta_(ell,1)`. | paper-proved classical no-go | Joint fibre treatment is the original binary source; fixed-dilation ternary estimates lose two polynomial powers after the two slack integrations. | Only with a genuinely joint theorem that does not merely invoke the fibre collapse |
| `MOBIUS-LCM-CUBICAL-NOGO-001` | Every lcm block is an integrated cubical Euler characteristic and saturates to `mu(ell)(N-1)`, but positive semiprime blocks have total mass `>>N^3/log^2 N`. | paper-proved structural no-go | Localizes harmless bulk to `(N-1)M(floor(N/2))`; proves source requires cancellation across lcm parity ranks. The first adjacent-rank differential is exactly the prime-tent law. | Only with a nonlocal cross-rank cancellation theorem |
| `MOBIUS-GOWERS-NOGO-001` | Fourier duality gives `|U(N)|<<N^3||mu||_U2^2`; current fixed-order Gowers decay is only logarithmic/iterated-logarithmic. | classical literature no-go | Quantitative uniformity improves the cubic scale by logs, not the missing power. Short-interval higher uniformity is qualitative and almost-all. | Only with a polynomial-strength norm or a new low-frequency signed inequality |

Dominance chain currently certified:

```text
MERTENS-EVEN-001 < DIRICHLET-MIXED-001
RAW-HERM-001 < PARITY-RAW-001
PARITY-RAW-001 < DYADIC-GRAM-001          (completely multiplicative binary specialization)
ML-WALL-001 + OPEN-SOURCE-001 => RH
```

No other arrow to RH is certified.

## Frozen corpus collisions — do not rediscover

1. `sum_k Phi(kx)=e^(-x)` and its Mellin transform.
2. Visible primitive-lattice closure
   `sum_(gcd(a_1,...,a_r)=1) prod Phi(a_j x_j)=Phi(sum x_j)`.
3. Mellin quotient `prod zeta(s_j)/zeta(sum s_j)` for visible lattice points.
4. First nonzero Hermitian zero-jet orientation `sign(2 Re(rho)-1)`.
5. Finite coprimality-matrix signature encoded by signs of `mu(1),...,mu(N)`.
6. Exact even-order Abel hierarchy for Mertens convolutions.
7. Exact positive-part affine zero-abscissa law at every even order.
8. Dirichlet-character mixed Hermitian extension.
9. Raw radial identity `sum_N R_(chi,k)(N)r^N=|A_chi(r)|^(2k)`.
10. Mellin identity `int A_chi(e^(-x))x^(s-1)dx=Gamma(s)/L(s,chi)`.
11. Liouville dilation identity `sum lambda(n)n^(-s)=zeta(2s)/zeta(s)`.
12. Coefficient family with Dirichlet series `zeta(ms)/zeta(s)` is not presumed new.

## Frozen dead routes — require a new falsifier to reopen

| Route | Exact obstruction | Strongest survivor |
|---|---|---|
| Xi algebraic-character shortcut | Source predicate is circular/vacuous at right-half zeros. | Interface equivalence/no-go. |
| Positive norm or mean square | Absolute squaring destroys signed cancellation and overpays the critical exponent. | Gamma--Hankel wall identity. |
| Prime-removal norm | Low-frequency resonance survives removal. | Resonance classification. |
| Visible/GCD-stationary positivity | Critical zero lies in radical; negative index is unbounded. | Zero-jet/inertia law. |
| Positive diagonal completion | Adds a strictly positive even logarithmic moment at the zero jet. | Sharp completion no-go. |
| Raise additive order | Exact affine order law retains the same `Theta`; no automatic source appears. | `MERTENS-EVEN-001`. |
| Lower/omega/sign statement as RH source | Detects existing zeros but gives no upper half-power control. | `RAW-HERM-001`. |
| Dyadic Gram identity as automatic upper source | Odd-index seed is free and the Liouville multiplier `1+2^(-s)` is a unit on `Re(s)>0`. | `DYADIC-BLIND-001`: orbit classification and orthogonal odd/dilated decomposition. |
| Coefficient-blind affine spectral closure | Constant/Eisenstein packets violate the claimed square-root shifted-line envelope; Blomer--Harcos applies to cuspidal Hecke coefficients, not arbitrary divisor-bounded sieve coefficients. | Cusp-projection necessity law; exact audit in `5-failed/dyadic-covariance-affine-spectral-toolkit-no-go.md`. |
| Iterated local-factor positivity | After one prime the transfer kernel is a nonnegative tent, but every pair `p<q` has a strictly negative unit-seed coefficient at `max(q+1,2p-1)`. | `MERTENS-PRIME-TENT-001`: exact one-prime window/tent law, support shell, prime-2 optimality, and universal two-prime sign wall. |
| Ternary lift by Möbius inversion of tent slack | `1=mu*tau` and `id=mu*sigma_1` are the unique insertions; `sum_(n<=X)sigma_1(n)>=X(X+1)/2`, so the inverse weight erases the missing power. | `MOBIUS-TERNARY-INSERTION-NOGO-001`: exact inversion-cost theorem and routing rule. |
| Ternary lift by Lambert dilation | `sum_k F(z^k)=z`; retaining the divisor-fibre cancellation gives the original binary coefficient, while fixing the dilation makes current ternary estimates two powers too weak after slack integration. | `MOBIUS-LAMBERT-TERNARY-NOGO-001`: exact six-variable lift and collapse dichotomy. |
| LCM-block positivity / cubical Betti majorant | Saturated blocks are harmless, but positive semiprime blocks alone carry `Omega(N^3/log^2 N)` mass. Cancellation must cross lcm parity ranks; the first local rank differential is already the one-prime tent. | `MOBIUS-LCM-CUBICAL-NOGO-001`: persistent-Euler normal form, saturation law, and semiprime cancellation debt. |
| Fixed-order Gowers/nilsequence uniformity | Exact dual estimate is `|U(N)|<<N^3||mu||_U2^2`; known quantitative decay supplies only logarithmic suppression, and recent short-interval higher uniformity is qualitative/almost-all. | `MOBIUS-GOWERS-NOGO-001`: one-power exponent wall. |

### `MERTENS-PRIME-TENT-001` — proved local classification; source still open

For every prime `p`, coefficientwise Euler-factor removal gives

```text
M(n)=sum_(p∤r, r<=n<pr) mu(r),
U(N)=sum_(p∤r,p∤s) mu(r)mu(s) K_(p,N)(r,s),
```

where `K` is a nonnegative discrete tent supported exactly on
`r+s<=N<N+2<=p(r+s)`. These kernels increase pointwise with `p`, so `p=2` is optimal. For every
`2<=p<q`, the two-prime unit transfer polynomial has a negative coefficient at
`k=max(q+1,2p-1)`; at `(p,q,k)=(2,3,4)` it is `-2`. Thus local Euler stripping cannot be iterated
as a positive upper comparison. The unresolved source is global signed cancellation inside the
odd-seed tent sum, not another local identity.

## Active conjectures and proof obligations

### `PARITY-RAW-001` — proved; priority audit open

For `F_k(r)=|A(r)|^(2k)=sum_N R_k(N)r^N`, even projection gives the exact identity

```text
sum_(N>=0) R_k(2N)u^N
  = (|A(sqrt(u))|^(2k)+|A(-sqrt(u))|^(2k))/2 >= 0.       (P1)
```

Closed obligations:

- [x] prove coefficient reality and `(P1)` without a branch ambiguity;
- [x] prove the even-index positive-part lower edge `>=2k theta-1`;
- [x] handle the zero-exponent endpoint by Mellin continuation;
- [x] compare against `mobius-even-additive-zero-abscissa-order-law.md` and
  `mobius-even-additive-convolution-hierarchy.md` (these concern even convolution **order**, not
  yet known to concern even coefficient **index**);
- [x] exact-phrase and conceptual web/arXiv searches found no collision;
- [ ] specialist, MathSciNet, and Zentralblatt priority review.

### `DYADIC-GRAM-001` — proved; priority audit open

For a completely multiplicative complex sequence `f`, `c=f(2)`, and
`F(r)=sum f(n)r^n`, exact even-part extraction gives

```text
F(r)+F(-r)=2cF(r^2),
sum_q (sum_(a+b=2q) f(a)conjugate(f(b)))r^(2q)
  = |F(r)-cF(r^2)|^2+|cF(r^2)|^2.                            (D1)
```

For `f=lambda`, the structural pole of `zeta(2s)/zeta(s)` at `1/2` and `(D1)` prove
that same-sign Liouville pairs strictly outnumber opposite-sign pairs for infinitely many even
totals. This is unconditional but does not give cancellation or solve binary Chowla.

Exact source audit:

```text
F(r)=O(r)+cF(r^2),
F(r)=sum_(j>=0)c^j O(r^(2^j)),
D_odd(s)=(1-c2^(-s))D(s).
```

The odd seed `O` is arbitrary under the local dyadic recursion. For Liouville, `c=-1` and every
zero of `1+2^(-s)` lies on `Re(s)=0`. Hence this factor is an analytic unit on the entire
right-half pole domain. `DYADIC-GRAM-001` is a lower/sign theorem, not an upper source.

### `POWER-SIEVED-001` — proved specialization; family collision resolved

For integer `m>=2`, define multiplicative coefficients by

```text
D_m(s)=zeta(ms)/zeta(s)=sum_n a_m(n)n^(-s),
a_m(p^e)=1 if e=0 mod m, -1 if e=1 mod m, 0 otherwise.
```

Here `a_2=lambda`; fixed coefficients tend pointwise to `mu` as `m` tends to infinity. The family
is treated as known. Candidate new content is only a uniform additive/parity law and its exact pole
frontier. Obligations:

- classify every pole, including the structural pole at `s=1/m`;
- prove noncancellation at rightmost zeta zeros;
- separate exact universal identities from order estimates;
- check generalized-Liouville literature and the existing square-dilation card;
- state no major-open-problem claim unless a recognized open conclusion is actually closed.

## Literature collision ledger

| Source | Object/result | Collision verdict |
|---|---|---|
| Kaczorowski--Perelli (2015) | Omega theorems for Dirichlet coefficients of polynomial L-combinations. | Not ordinary-additive Cauchy convolution; neighboring method. |
| Mangerel (2024, final journal version) | `|sum_(n<N)lambda(n)lambda(N-n)|<N-1` for every `N>=11`; equality occurs exactly for `N in {2,3,5,10}`. | Strict nonmaximality ensures both pair types occur but does not determine aggregate sign; no collision with even-total majority recurrence. |
| Banks--Shparlinski (2026) | Multiple Möbius sums; binary cancellation remains out of reach. | Confirms `RAW-HERM-001` is weaker than the binary cancellation frontier. |
| Cantarini--Gambini--Zaccagnini (2026) | Weighted explicit formulas for Liouville/Möbius additive convolutions under RH-type hypotheses. | No located unconditional parity-positive recurrence; exact collision audit remains active. |
| de Camargo (2023), eq. (22) | Generalized Liouville `lambda_m` with Dirichlet series `zeta(ms)/zeta(s)`. | Exact collision for coefficient family; only additive parity consequences remain candidate new content. |
| Visible-lattice / gcd-matrix parent theory | Primitive-lattice zeta quotients and Möbius inertia. | `VISIBLE-NOGO-001` is not a novel parent identity. |

Negative search never certifies priority. Specialist review, MathSciNet, and Zentralblatt remain
publication gates.

## Paper admission rule

A result enters `one-sided-additive-zero-abscissa-law/main.tex` only if:

1. proof is dependency-closed on paper;
2. it strictly dominates a theorem row above or supplies a genuinely new specialization;
3. corpus comparison is recorded here;
4. primary-literature comparison is recorded here;
5. headline and abstract state exact significance without claiming RH or a solved major problem.

## Lean admission rule

Search existing modules first. Reuse generic Cauchy/Hermitian Abel machinery. Add only a connector
encoding genuinely new mathematical content. Batch edits; one direct `lake env lean <file>` check;
one final targeted `lake build <module>` audit; never rebuild the whole tree for exploration.

## Work log

- **2026-07-22 / L0:** Created canonical ledger after repeated route duplication. Froze known
  identities, dead mechanisms, exact RH source, theorem dominance, and publication/Lean admission
  gates. Flagged `PARITY-RAW-001` because corpus already contains similarly named even-additive
  results; novelty label suspended until index-vs-order comparison and literature audit finish.
- **2026-07-22 / L1:** Proved `PARITY-RAW-001`; corpus comparison confirmed prior cards concern
  even convolution order, not even output index. Proved `DYADIC-GRAM-001` and unconditional
  Liouville same-sign majority recurrence. Identified `POWER-SIEVED-001` coefficients exactly with
  de Camargo's known `lambda_m`; removed any family-novelty claim. Added dependency-closed card,
  strengthened manuscript, and formalized only the new projector/parallelogram connector in
  `DirichletLMixedAdditiveEvenIndexLaw.lean`. Direct cached Lean check passed.
- **2026-07-22 / L2:** Pushed dyadic route to its source boundary. Proved complete orbit
  classification by free odd-index seed and exact Mellin factorization. Froze
  `DYADIC-BLIND-001`: parity Gram exposes orthogonal channels but cannot generate a critical upper
  bound or alter the Mellin pole wall. Remaining source is now the odd-seed/even-coefficient upper
  law itself, not another dyadic identity.
- **2026-07-22 / L3:** Audited Zenodo `10.5281/zenodo.20082725`, the strongest located current
  claim of an unconditional `M(N) << N^(1/2+epsilon)` proof. Refuted its formal `BDHStatement` by
  a two-point finite instance and both decisive manuscript shifted-convolution inputs by the
  constant/Eisenstein packet. Primary Blomer--Harcos and Topacogullari statements do not cover
  arbitrary divisor-bounded sieve coefficients. Froze `DYADIC-COV-PREPRINT-NOGO-001`; no source
  theorem was imported.
- **2026-07-22 / L4:** Proved `MERTENS-PRIME-TENT-001`. One Euler-prime removal gives an exact
  nonnegative interval-overlap tent for the signed Mertens antidiagonal, with sharp shell support
  and prime-2 pointwise optimality. Proved every second removed factor forces a negative unit-seed
  lobe, so local-factor positivity has depth exactly one. Added dependency-closed paper card and
  Lean-checked coefficient, Mertens-window, antidiagonal connector, tent, monotonicity, and sign-wall
  theorems. `OPEN-SOURCE-001` remains global signed odd-seed cancellation.
- **2026-07-22 / L5:** Audited Banks--Shparlinski's exact ternary hypotheses and the 2026
  Cantarini--Gambini--Zaccagnini direct additive-convolution paper. Proved the unique
  Dirichlet-insertion cost law `1=mu*tau`, `id=mu*sigma_1`; quadratic `sigma_1` mass destroys the
  required power saving, while the direct zero-pair formula assumes RH and simple zeros. Retired
  the ternary-slack lift as `MOBIUS-TERNARY-INSERTION-NOGO-001`. Entropy decrement remains
  logarithmically averaged and does not supply the cutoff-pointwise `N^-1` tent bias.
- **2026-07-22 / L6:** Tested the only cost-free third-factor insertion missed by L5. Lambert
  inversion gives the exact lift
  `U(N)=sum_(m+n+kr+i+j=N+1)mu(m)mu(n)mu(r)`, but the `(k,r)` fibre is exactly
  `sum_(r|ell)mu(r)=delta_(ell,1)`. Joint treatment returns the binary source; fixed-`k`
  Banks--Shparlinski bounds, even granting separate-product and gcd repairs, are two polynomial
  powers short after the two slack integrations. Retired as
  `MOBIUS-LAMBERT-TERNARY-NOGO-001`.
- **2026-07-22 / L7:** Regrouped the antidiagonal by squarefree lcm and proved an exact cubical
  persistent-Euler law. Every block saturates to `mu(ell)(N-1)` once `N>=2ell`, so the complete
  bulk is the unconditionally `O(N^2)` term `(N-1)M(floor(N/2))`. The boundary is not positively
  controllable: semiprime lcms from two primes in `[N/5,N/4]` contribute
  `Omega(N^3/log^2 N)` positive mass. Required saving is cancellation across lcm parity ranks; the
  first adjacent-rank differential is precisely `MERTENS-PRIME-TENT-001`, and its iteration hits
  the recorded sign wall. Retired blockwise lcm positivity as `MOBIUS-LCM-CUBICAL-NOGO-001`.
- **2026-07-22 / L8:** Audited current global and short-interval Gowers uniformity at the exact
  antidiagonal norm interface. Parseval gives `|U(N)|<<N^3||mu||_U2^2`; the JEMS quantitative
  theorem supplies iterated-logarithmic decay, while the 2026 short-interval theorem is qualitative
  and almost-all. Both remain one polynomial power short of `OPEN-SOURCE-001`. Retired
  fixed-order uniformity as `MOBIUS-GOWERS-NOGO-001`.
