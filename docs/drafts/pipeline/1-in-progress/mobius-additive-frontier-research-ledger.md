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
| `PARITY-RAW-001` | Even-index projection of `RAW-HERM-001` remains a nonnegative radial square and may force positive recurrence on even indices. | proof candidate; **novelty suspended** | Would strictly strengthen `RAW-HERM-001` by localizing recurrence to even totals. Must first clear corpus and literature. | Active audit |
| `POWER-SIEVED-001` | For reciprocal coefficients of `zeta(ms)/zeta(s)`, parity-projected raw and integrated laws interpolate Liouville and Möbius behavior. | conjecture/proof candidate; family itself known | Potential universal specialization of abstract laws, not a new coefficient family. | Active audit |
| `VISIBLE-NOGO-001` | Visible-coprime identity has Mellin symbol `prod zeta(s_j)/zeta(sum s_j)`; zero modes lie in its radical and finite kernels have Mertens inertia. | paper-proved parent collision/no-go | Kills positive GCD-stationary kernels and positive diagonal completion as RH sources. | No |

Dominance chain currently certified:

```text
MERTENS-EVEN-001 < DIRICHLET-MIXED-001
RAW-HERM-001 < PARITY-RAW-001            (only if parity proof and audits pass)
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

## Active conjectures and proof obligations

### `PARITY-RAW-001`

For `F_k(r)=|A(r)|^(2k)=sum_N R_k(N)r^N`, even projection gives the exact identity

```text
sum_(N>=0) R_k(2N)u^N
  = (|A(sqrt(u))|^(2k)+|A(-sqrt(u))|^(2k))/2 >= 0.       (P1)
```

Obligations:

- prove coefficient reality and `(P1)` without a branch ambiguity;
- prove the even-index positive-part lower edge `>=2k theta-1`;
- handle the zero-exponent endpoint by Mellin continuation;
- compare against `mobius-even-additive-zero-abscissa-order-law.md` and
  `mobius-even-additive-convolution-hierarchy.md` (these concern even convolution **order**, not
  yet known to concern even coefficient **index**);
- run exact-phrase and conceptual literature searches before priority language.

### `POWER-SIEVED-001`

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
| Mangerel (2024/2025) | Liouville correlations, strict nonmaximality, conditional local sign patterns. | Does not yet match unconditional aggregate positive recurrence found in targeted search. |
| Banks--Shparlinski (2026) | Multiple Möbius sums; binary cancellation remains out of reach. | Confirms `RAW-HERM-001` is weaker than the binary cancellation frontier. |
| Cantarini--Gambini--Zaccagnini (2026) | Weighted explicit formulas for Liouville/Möbius additive convolutions under RH-type hypotheses. | No located unconditional parity-positive recurrence; exact collision audit remains active. |
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

