# First-order autonomous algebraic almost-periodicity forces periodicity

- **ID:** `first-order-autonomous-algebraic-ap-periodicity`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / CROSS-OPERATOR TRANSDUCTION
- **Scientific status:** `[PAPER-PROVED] [KNOWN-INGREDIENT SYNTHESIS]`
- **Novelty status:** no novelty claim; the proof combines algebraic-curve normalization with
  Schwartz's classical classification of minimal sets of `C^2` surface flows
- **Statement:** A nonconstant holomorphic uniformly almost-periodic strip function satisfying an
  implicit first-order autonomous algebraic differential equation is periodic. Equivalently, its
  Bohr-frequency group is a nonzero cyclic group.

## Setup

Let

```text
S_eta={z in C: |Im z|<eta},  eta>0.                         (1)
```

Let `f` be holomorphic on `S_eta` and suppose that its real translates are relatively compact in
the uniform norm on every closed smaller strip. Assume that `f` is nonconstant and that

```text
P(f,f')=0                                                   (2)
```

for a nonzero polynomial `P in C[X,Y]`.

## The theorem

`[PAPER-PROVED]` There is a nonzero real number `lambda` such that

```text
Gamma(f)=lambda Z.                                         (3)
```

Consequently `f` has real period `2pi/|lambda|`. In particular,

```text
rank_Q Gamma(f)=1.                                         (4)
```

The equation in `(2)` may be singular and implicit. No global choice of a branch `f'=R(f)` and no
initial-value uniqueness on the singular affine curve are assumed.

## 1. Reduction to one irreducible algebraic curve

Choose an irreducible factor of `P` that annihilates `(f,f')`, and denote it again by `P`. It must
depend on `Y`: otherwise the nonconstant holomorphic function `f` would take values in the finite
zero set of a one-variable polynomial. Let

```text
C={P(X,Y)=0} subset A^2_C.                                  (5)
```

Let

```text
nu:Ctilde -> Cbar                                           (6)
```

be the normalization of the projective closure of `C`. The affine coordinate functions pull back
to meromorphic functions `x,y` on the compact Riemann surface `Ctilde`.

For every member `g` of the Bohr hull `X_f`, local uniform convergence of translates and Cauchy's
formula give

```text
P(g,g')=0.                                                  (7)
```

No member of `X_f` is constant. Indeed, the hull is a minimal real-translation flow; if it
contained a constant, its singleton orbit closure would force the whole hull, and hence `f`, to be
constant.

Thus the holomorphic map

```text
J_g:S_eta -> C,       J_g(z)=(g(z),g'(z))                  (8)
```

is nonconstant and hence dominant onto the irreducible curve. Since the strip is normal, the
universal property of normalization gives a unique holomorphic lift

```text
Jtilde_g:S_eta -> Ctilde.                                   (9)
```

## 2. The normalized rational vector field is regular on the hull

Since `P` is irreducible, depends on `Y`, and the characteristic is zero, `P_Y` is nonzero in the
function field of `C`. The rules

```text
D(x)=y,
D(y)=-(P_X/P_Y)y                                           (10)
```

define a derivation of `C(C)` and hence a rational vector field `V` on `Ctilde`. Differentiating
`P(g,g')=0` where `P_Y(g,g')` is nonzero, then using analytic continuation, shows that every lift
in `(9)` is an integral curve:

```text
Jtilde_g'(z)=V(Jtilde_g(z)).                                (11)
```

Put

```text
p_g=Jtilde_g(0).                                            (12)
```

The vector field `V` has neither a pole nor a zero at any `p_g`. In a local coordinate `u` at
`p_g`, write `V=a(u)d/du`. If `a` has a pole and the nonconstant integral curve has
`u(z)=c z^m+...`, then the holomorphic function `u'` cannot equal the polar function `a(u)`.
If `a(0)=0`, local uniqueness for the regular equation `u'=a(u)` forces the integral curve through
`0` to be constant, again impossible.

Remove from `Ctilde` the poles of `x`, `y`, and `V` and the zeros of `V`; call the resulting open
Riemann surface `U`. All points `p_g` lie in `U`.

## 3. The normalized state is an embedding of the full hull

Define

```text
E:X_f -> U,       E(g)=p_g.                                (13)
```

This map is injective. If `p_g=p_h`, the regular local vector field has a unique integral curve
through that point, so the lifts in `(9)` agree near zero. Applying `x` gives `g=h` locally and the
identity theorem gives `g=h` on the strip.

The only delicate point is continuity at a singular point of the plane curve. Suppose `g_j->g` in
the hull. Evaluation of `(g_j,g_j')` converges locally uniformly by Cauchy's formula. The fibre of
the finite map `nu` over `J_g(0)` is finite. Choose disjoint neighbourhoods of its points and a
small plane neighbourhood `W` whose full inverse image lies in their union. On a sufficiently
small connected disc `D` about zero, all `J_{g_j}(D)` lie in `W`. Choose `z_0 in D` where `J_g(z_0)`
is in the smooth locus of `C`; such points exist because `J_g` is nonconstant and the singular
locus is finite. Near `z_0` the inverse branch of `nu` is unique, so the lifts of `J_{g_j}` lie in
the same component of `nu^(-1)(W)` as the lift of `J_g`. Properness of `nu` then forces

```text
p_(g_j) -> p_g.                                             (14)
```

Thus `E` is continuous. Since `X_f` is compact and `U` is Hausdorff, `(13)` is a topological
embedding. Write

```text
K=E(X_f) subset U.                                          (15)
```

Translation on the hull becomes the local holomorphic flow of `V` on `K`. The set `K` is compact,
connected, invariant, and every real orbit in it is dense.

## 4. Surface-flow rigidity forces a periodic orbit

Choose a relatively compact neighbourhood `W` of `K` in `U`. On `W`, the underlying real vector
field of the holomorphic field `V` is smooth and nonvanishing. Multiply it by a smooth cutoff that
is identically one on a neighbourhood of `K` and extend it by zero to the compact real surface
underlying `Ctilde`. This gives a global `C^2` flow whose restriction to `K` is exactly the
translation flow.

Schwartz's surface-flow theorem says that a minimal set of a `C^2` flow on a compact connected
surface is exactly one of:

```text
(a) a fixed point;
(b) a single periodic orbit homeomorphic to S^1;
(c) the entire surface, which is then a two-torus.           (16)
```

Case `(a)` is impossible because every hull member is nonconstant and `V` has no zero on `K`.
Case `(c)` is impossible because `K` lies in the affine normalization and avoids the nonempty
divisor at infinity, whereas the whole compact surface does not. Therefore

```text
K is one periodic orbit.                                    (17)
```

Since `(13)` conjugates the hull translation to this orbit, `X_f` is the circle and its character
group is infinite cyclic. The character group of `X_f` is precisely `Gamma(f)` with the discrete
topology, so `(3)` and `(4)` follow. Equivalently, the dense translation homomorphism
`R->X_f=S^1` has a nonzero discrete kernel; its positive generator is a period of every hull member
and in particular of `f`.

## Positive consequences

### Order-one hypertranscendence criterion

Every nonperiodic holomorphic uniformly almost-periodic strip function satisfies

```text
P(f,f') != 0                                               (17)
```

for every nonzero `P in C[X,Y]`. Thus nonperiodicity is an exact obstruction to every first-order
autonomous algebraic differential equation, including singular implicit equations.

### Divisor-frequency consequence

Every continuous translation-equivariant factor of the hull, including the zero-divisor hull, has
cyclic character group or a quotient thereof. Its frequency rank is therefore at most one.

### Sharp-conjecture consequence

The conjectural bound

```text
rank_Q Gamma(f)<=n                                         (18)
```

for minimal autonomous order `n` is proved, and strengthened to periodicity, when `n=1`. The open
case begins at order two, where normalization produces an `n`-dimensional variety rather than a
Riemann surface and non-circular higher-dimensional protori can embed in real dimension `2n`.

## Literature and novelty audit

1. A. J. Schwartz, *A generalization of a Poincare--Bendixson theorem to closed two-dimensional
   manifolds*, Amer. J. Math. **85** (1963), 453--458,
   <https://doi.org/10.2307/2373135>. Its minimal-set trichotomy gives the periodicity step after
   normalization.

2. G. C. O'Brien, *The frequencies of almost periodic solutions of almost periodic differential
   equations*, J. Austral. Math. Soc. **17** (1974), 332--344,
   <https://doi.org/10.1017/S1446788700017092>. Theorem 3 proves fewer than `p` basic frequencies
   for a regular autonomous first-order system in `R^p`. It is an adjacent classical consequence,
   but does not state the singular implicit algebraic-curve reduction.

3. M. L. Cartwright, *Almost periodic flows and the solutions of differential equations*, Proc.
   London Math. Soc. (3) **17** (1967), 355--380. This is the classical autonomous-flow source
   behind O'Brien's theorem and its integral-basis refinement.

4. The factorization through normalization is the standard universal property; see the Stacks
   Project, Tag 035Q, <https://stacks.math.columbia.edu/tag/035Q>.

The exact synthesis above was not found verbatim in the audited sources. It is nevertheless built
from classical ingredients with a short normalization argument, so this card makes no novelty
claim.

## Lean formalization (2026-09-28)

`[FORMALIZED]` Unconditional and axiom-clean (`propext`, `Classical.choice`, `Quot.sound`), wired
into `GaloisForLFunctions.HTGeometry`.  The strip is `imStrip η = {|Im z| < η}`; the hypothesis
"relatively compact real translates on every closed smaller strip" is
`IsImStripUniformlyAlmostPeriodic f η`, and `hasCompactImStripTranslates_iff_isCompact_closure`
proves it is literally compactness of the closure of the translates in the space of bounded
continuous functions on the closed strip.  `P(f, f') = 0` is `relEval P (f z) (deriv f z) = 0` for
`P : ℂ[X][Y]` nonzero, with no irreducibility, regularity or branch assumption.

| Card statement | Lean |
|---|---|
| `(3)`: `Γ(f) = λℤ`, `λ ≠ 0`; the period `2π/|λ|`; `(4)`: rank one | `firstOrderAlgebraic_stripAlmostPeriodic_frequencyGroup` |
| a nonzero real period | `exists_real_period_of_firstOrderRelation` |
| order-one hypertranscendence criterion `(17)` | `exists_relEval_ne_zero_of_not_periodic` |
| divisor-frequency consequence: every continuous translation-equivariant factor has cyclic frequency group, rank ≤ 1 | `observable_frequencyGroup_cyclic` |
| sharp-conjecture consequence at order one | the rank clause of the first theorem |

Modules (`formal/GaloisForLFunctions/HTGeometry/`): `FirstOrderRelationLocalUniqueness`,
`ImStripTranslateCompactness`, `FirstOrderAlgebraicStripPeriodicity`,
`FirstOrderAlgebraicStripFrequencyGroup`.

**The formal proof replaces both classical inputs of the paper route.**  Neither the normalization
of the algebraic curve nor Schwartz's minimal-set theorem is used.

1. A relation `Q` of least `Y`-degree has `∂_Y Q (f, f') ≢ 0`
   (`exists_relation_derivative_ne_zero`), so there is a real anchor `x₀` with `f'(x₀) ≠ 0` and
   `∂_Y Q (f(x₀), f'(x₀)) ≠ 0` (`exists_real_anchor`).
2. **Local uniqueness without a branch** (`eqOn_of_relEval_eq_zero`): divided differences write
   `0 = Q(v,v') − Q(w,w') = (v−w)E + (v'−w')D` with `D` near `∂_Y Q ≠ 0`, so `|v'−w'| ≤ K|v−w|`,
   and Grönwall along radii forces `v = w`.
3. An `ε`-almost period `τ` and the open mapping theorem give a small complex `c` with
   `f(x₀+c) = f(x₀+τ)`; local uniqueness makes `f(·+τ) = f(·+c)` on the half strip
   (`exists_translation_pair`).  If `c` is real, `τ − c` is a real period
   (`exists_period_of_real_translation_pair`).
4. Otherwise the pair transports the real line to the heights `k·Im c`
   (`exists_real_eq_of_translation_pair`); as `Im c → 0` these are dense, so `|f|` never exceeds
   its supremum on the line (`norm_le_iSup_of_translation_pairs`).  The **maximum principle for
   translates** (`HasCompactImStripTranslates.exists_const_of_norm_le_iSup`: a limit of translates
   realising the supremum attains its maximum modulus at an interior point) makes `f` constant,
   contradicting `f'(x₀) ≠ 0`.
5. A period confines the Bohr spectrum to `(2π/p)ℤ` (`mem_zmultiples_of_bohrCoefficient_ne_zero`);
   a nonconstant function has a nonzero frequency (`exists_ne_zero_mem_bohrSpectrum`); subgroups
   of a cyclic subgroup of `ℝ` are cyclic (`exists_eq_zmultiples_of_le_zmultiples`); the corpus
   uniqueness theorem gives the period `2π/|λ|` (`periodic_of_bohrSpectrum_subset`).

## Gates

- [x] exact theorem and hypotheses
- [x] singular implicit equation handled on the normalization
- [x] continuity at multiple branches audited
- [x] rank-two and noncyclic-rank-one alternatives excluded
- [x] positive order-one hypertranscendence statement extracted
- [x] primary-source literature audit
- [x] conservative no-novelty classification
- [x] unconditional Lean formalization

## Log

- 2026-07-17 -- Proved during programme-2 research. The first pass gave only
  `rank_Q Gamma(f)=1`; the surface non-embedding theorem sharpened this to cyclic spectrum and
  periodicity.
- 2026-09-28 -- Formalized unconditionally in Lean by an elementary route (local uniqueness + maximum
  principle for translates) that needs neither curve normalization nor Schwartz's theorem; moved to
  stage 3.
