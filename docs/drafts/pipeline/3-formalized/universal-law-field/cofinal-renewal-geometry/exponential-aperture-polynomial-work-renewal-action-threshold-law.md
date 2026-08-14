# Exponential-aperture / polynomial-work renewal-action threshold law

- **ID:** ULF-CRG-1
- **Stage:** 3-formalized
- **Type:** THEOREM / SHARP CLASSIFICATION / GLOBAL PROPERNESS LAW
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [UNCONDITIONAL] [BRIDGE]`
  `[NOVELTY UNVERIFIED] [LEAN NOT YET WRITTEN] [NOT RH]`
- **Programme:** `cofinal-renewal-geometry`
- **Source frontier:** `../../../1-in-progress/rh-current-frontier-map.md`, information-evacuation seam

## Result in one sentence

If a source aperture has baseline mass at most `C exp(-beta n)`, an admitted observer has work at
most `K n^d`, and renewal keeps their mass-weighted current at least `c > 0`, then the least
relative-entropy renewal cost is asymptotically at least

```text
(c beta / K) n^(1-d).
```

Consequently total renewal action diverges for `d <= 2`; for `d > 2` a two-point
information projection has finite total action.  Cubic growth is therefore the first integer
polynomial degree not excluded by finite-action formation.

## 1. Setup

For every integer `n >= n0`, let `(Omega_n,F_n,mu_n)` be a probability space and let
`A_n in F_n` be an admitted aperture with

```text
epsilon_n := mu_n(A_n),        0 < epsilon_n < 1.
```

A **renewal** is another probability measure `nu_n` with `nu_n << mu_n`.  Write

```text
alpha_n := nu_n(A_n).
```

Let `W_n > 0` be observer work available inside the aperture.  Its admitted current is

```text
J_n := alpha_n W_n.
```

The renewal action at scale `n` is

```text
I_n := D(nu_n || mu_n),
```

and total action is the extended series

```text
A(nu | mu) := sum_{n >= n0} I_n.
```

No independence between the spaces is needed for the lower theorem.  The series is a cofinal
formation action: it records information injected at each scale rather than pretending that a
vanishing aperture remains an admitted source.

This action is canonical only when the source supplies independently charged increments or a
path-space KL chain rule.  One global intervention could otherwise share information across
scales.  The stronger companion
`disjoint-aperture-global-renewal-moment-properness-and-cubic-threshold-law.md` removes that
possible overcount by using one source law and one KL divergence.

For `0 <= x <= 1` and `0 < y < 1`, put

```text
d_B(x || y) = x log(x/y) + (1-x) log((1-x)/(1-y)),
```

with `0 log 0 = 0`, and put

```text
h(x) = -x log x - (1-x) log(1-x).
```

## 2. Exact formation-conservation law

### Theorem 2.1 — aperture disintegration and minimal renewal

Let `mu,nu` be probability measures, `nu << mu`, and let `A` satisfy
`0 < mu(A) < 1`.  Write `epsilon=mu(A)` and `alpha=nu(A)`.  Then

```text
D(nu || mu)
  = d_B(alpha || epsilon)
    + alpha D(nu_A || mu_A)
    + (1-alpha) D(nu_Ac || mu_Ac).                 (CRG.1)
```

Here conditional terms with zero coefficients are interpreted as zero.  In particular,

```text
D(nu || mu) >= d_B(alpha || epsilon).              (CRG.2)
```

For fixed `alpha`, equality holds exactly when renewal changes only aperture mass:

```text
d nu^(alpha) / d mu
  = alpha/epsilon                    on A,
  = (1-alpha)/(1-epsilon)            on A^c.        (CRG.3)
```

Thus `d_B(alpha || epsilon)` is not a chosen penalty.  It is the least possible information influx
capable of changing admission from `epsilon` to `alpha`.

### Proof

On `A`, factor the Radon--Nikodym derivative as

```text
dnu/dmu = (alpha/epsilon) (dnu_A/dmu_A),
```

and use the analogous factorization on `A^c`.  Integrating `log(dnu/dmu)` over the two pieces gives
`(CRG.1)`.  Nonnegativity of conditional relative entropy gives `(CRG.2)`.  Equality holds exactly
when both conditional laws agree, which gives `(CRG.3)`.  If `nu` is not absolutely continuous,
the left side is `+infinity` and the lower bound remains true.

## 3. Cofinal threshold

### Theorem 3.1 — exponential evacuation forces polynomial renewal action

Fix constants

```text
C > 0, beta > 0, K > 0, c > 0,
```

and an integer `d >= 0`.  Assume, for every sufficiently large `n`,

```text
epsilon_n <= C exp(-beta n),
W_n <= K n^d,
alpha_n W_n >= c.                                  (CRG.4)
```

Then

```text
liminf_{n -> infinity} n^(d-1) D(nu_n || mu_n)
  >= c beta / K.                                   (CRG.5)
```

Consequently:

1. if `d = 0`, per-scale renewal cost grows at least linearly;
2. if `d = 1`, per-scale cost is bounded away from zero;
3. if `d = 2`, per-scale cost is at least harmonic order;
4. for every `d <= 2`, total action is infinite:

```text
sum_n D(nu_n || mu_n) = +infinity.                 (CRG.6)
```

### Proof

Set

```text
b_n = c / (K n^d).
```

The current constraint and work upper bound give `alpha_n >= b_n`.  Exponential decay beats every
polynomial, so eventually

```text
epsilon_n <= b_n <= alpha_n <= 1.
```

For fixed `epsilon`, binary relative entropy is increasing in `alpha` on
`[epsilon,1]`, because

```text
d/dalpha d_B(alpha || epsilon)
  = log(alpha(1-epsilon)/(epsilon(1-alpha))) >= 0.
```

Theorem 2.1 therefore gives

```text
D(nu_n || mu_n) >= d_B(b_n || epsilon_n).
```

Expanding binary relative entropy yields the elementary lower bound

```text
d_B(b || epsilon)
  = b log(1/epsilon) - h(b) - (1-b) log(1-epsilon)
  >= b log(1/epsilon) - h(b).                       (CRG.7)
```

Since `log(1/epsilon_n) >= beta n - log C`, we obtain

```text
n^(d-1) D(nu_n || mu_n)
  >= (c/K)(beta - (log C)/n) - n^(d-1) h(b_n).      (CRG.8)
```

If `d=0`, the last entropy term divided by `n` tends to zero.  If `d>0`, the standard bound

```text
h(x) <= x log(1/x) + x
```

shows

```text
n^(d-1) h(b_n) = O((log n)/n) -> 0.
```

Taking `liminf` proves `(CRG.5)`.  Hence, for large `n`,

```text
D(nu_n || mu_n) >= (c beta/(2K)) n^(1-d).
```

The comparison series diverges exactly when `d <= 2`, proving `(CRG.6)`.

### Theorem 3.2 — sharpness above the quadratic wall

Let `d > 2`, `beta,K,c > 0`, and assume `c < K`.  There are two-point probability spaces,
apertures, works, and renewals satisfying

```text
epsilon_n = exp(-beta n),
W_n = K n^d,
alpha_n W_n = c,
sum_n D(nu_n || mu_n) < infinity.                  (CRG.9)
```

Thus neither exponential aperture decay nor positive admitted current alone forces infinite
action above degree two.

### Proof

Take `Omega_n={0,1}`, `A_n={1}`, and let

```text
mu_n(1)=epsilon_n=exp(-beta n),
nu_n(1)=alpha_n=c/(K n^d).
```

For large `n`, `epsilon_n < alpha_n < 1`.  This renewal is exactly the information projection
`(CRG.3)`, so

```text
D(nu_n || mu_n)=d_B(alpha_n || epsilon_n).
```

Because `alpha_n > epsilon_n`, the complementary term in binary KL is nonpositive.  Hence

```text
d_B(alpha_n || epsilon_n)
  <= alpha_n log(alpha_n/epsilon_n)
  <= alpha_n log(1/epsilon_n)
  = (c beta/K) n^(1-d).
```

The last series converges for `d>2`, while `alpha_n W_n=c` exactly.

## 4. Global formation properness

Let

```text
X = product_{n >= n0} [0,1]
```

with product topology and define the minimal renewal action

```text
S(alpha) = sum_n d_B(alpha_n || epsilon_n).         (CRG.10)
```

### Theorem 4.1 — compact action sublevels and the cubic entrance wall

The functional `S:X->[0,+infinity]` is lower semicontinuous and every sublevel

```text
{alpha : S(alpha) <= M}
```

is compact.  For fixed work sequence `W_n`, the persistent-current locus

```text
C_c = {alpha : alpha_n W_n >= c for every n}
```

is closed.  Under `(CRG.4)`, if `d <= 2`, `C_c` has empty intersection with every finite-action
sublevel.  Conversely, for every integer `d > 2` there exists an exponentially evacuated
two-point system—the one in Theorem 3.2—whose persistent-current locus meets a finite-action
sublevel.

Hence finite-action formation is globally proper.  Across the class of exponentially evacuated
systems, polynomial degree three is the first integer degree at which a persistent current can
enter a finite-action history space.  An upper exponential bound alone does not guarantee entrance
for every particular baseline: a superexponentially smaller aperture can still force infinite
action above degree two.

### Proof

Each binary-KL coordinate is continuous on `[0,1]` because `0 log 0=0`.  The partial sums in
`(CRG.10)` are continuous and increase to `S`, so `S` is lower semicontinuous.  Tychonoff compactness
of `X` makes each closed sublevel compact.  Each inequality `alpha_n W_n >= c` defines a closed
coordinate cylinder, so `C_c` is closed.  Universal exclusion for `d<=2` is Theorem 3.1.  The
existential sharpness statement for `d>2` is Theorem 3.2.

## 5. Exact source-horizontal consequence

The formalized canonical abelian aperture has, after reindexing `n=N+1`, exact unnormalized
forward/reverse masses

```text
W_+(n) = p^(-(2-a)n) + p^(-2n+1+a),
W_-(n) = p^(-(2+a)n) + p^(-2n+1-a).
```

Multiplication by the fixed positive class-law normalizer does not change exponential rate.  The
elementary bounds

```text
W_+(n) <= (1+p^(1+a)) p^(-(2-a)n),
W_-(n) <= (1+p^(1-a)) p^(-2n)                       (CRG.11)
```

therefore give forward rate `(2-a) log p` and reverse rate `2 log p`.  Adaptive reflected
Jeffreys work satisfies

```text
W_n <= 2 a (log p) n,          0 < a < 1.
```

### Corollary 5.1 — orientation-resolved renewal price

Suppose renewals of the forward and reverse apertures have masses `alpha_n^+`, `alpha_n^-` and
preserve currents

```text
alpha_n^+ W_n >= c > 0,
alpha_n^- W_n >= c > 0.
```

Then

```text
liminf_n D(nu_n^+ || mu_n^+) >= c(2-a)/(2a),
liminf_n D(nu_n^- || mu_n^-) >= c/a,               (CRG.12)

sum_n D(nu_n^+ || mu_n^+) = +infinity,
sum_n D(nu_n^- || mu_n^-) = +infinity.             (CRG.13)
```

### Proof

Apply Theorem 3.1 with `d=1` and `K=2a log p`.  For the forward orientation use
`beta=(2-a)log p`; for the reverse use `beta=2log p`.  The prime logarithm cancels, leaving
`(CRG.12)`.  The bounds `(CRG.11)` follow directly from the two displayed exact masses: divide the
second forward term by `p^(-(2-a)n)` and the two reverse terms by `p^(-2n)`.

This is new unconditional leverage on the current frontier: the exact source aperture cannot be
replenished by a finite-total-KL perturbation while retaining nonzero admitted adaptive current.
Moreover the two functional-equation orientations have different compulsory information prices;
forward strip slack contributes the factor `2-a`, while reverse renewal pays the full exponent
two.
The result does not assume an RH zero and does not construct the missing source renewal.

## 6. Four-organ fusion and prediction

One conservation/properness package now couples four structurally different organs:

| organ | variable | exact role |
|---|---:|---|
| source admission | `epsilon_n` | evacuated aperture mass |
| observer/information | `W_n` | work available after admission |
| intervention/formation | `nu_n`, `alpha_n` | renewed source law and admitted mass |
| cofinal topology | `sum D`, product topology | proper history action and completion boundary |

The exact conservation identity is `(CRG.1)`.  The route-independent prediction in the fourth
organ is the sharp degree wall:

> Exponential evacuation plus persistent admitted current excludes every finite-action polynomial
> observer of degree at most two.  Cubic response is the first polynomial rate not excluded.

This does **not** assert that any existing cubic corpus observable supplies a source renewal.  It
predicts what growth class a successful finite-action compensator must reach, and it explains why
linear Fisher/Jeffreys amplification and quadratic metric amplification cannot repair the current
aperture theorem.

## 7. Hostile conjecture / proof / failure loops

1. **KL disintegration is the missing producer.** Failed.  `(CRG.1)` consumes `nu`; it does not
   construct it.  Survivor: once a renewal is proposed, its minimal source price is forced.
2. **Any unbounded polynomial work can defeat exponential evacuation.** Failed.  Degrees zero,
   one, and two have infinite total action.
3. **Exponential evacuation always forces infinite renewal action.** Failed.  Theorem 3.2 gives a
   finite-action two-point countermodel for every `d>2`.
4. **The quadratic wall is an artefact of an estimate.** Failed.  Lower and upper constructions
   have the same `n^(1-d)` order.
5. **Compactness of the schedule space itself selects neutrality.** Failed.  Compactness is cheap;
   the lower-semicontinuous action and current constraint produce the exclusion.
6. **This proves RH.** Failed.  The missing arithmetic theorem remains construction of a canonical
   pre-zero finite-action renewal/current.  This card proves what such a theorem would have to pay
   and why lower-degree replacements cannot work.

## 8. Literature and priority boundary

- Csiszar's classical I-divergence geometry supplies information projections and Pythagorean
  decompositions: <https://doi.org/10.1214/aop/1176996454>.
- Schroedinger bridges minimize path-space relative entropy under endpoint constraints; a current
  2026 survey is <https://arxiv.org/abs/2603.18992>.
- Modern rare-event importance sampling studies likelihood-ratio instability and marginal
  reweighting: <https://arxiv.org/abs/2504.13982>.
- Esscher transforms are constrained minimum-relative-entropy updates; quantum generalizations are
  <https://arxiv.org/abs/2401.07561> and <https://arxiv.org/abs/2608.04055>.

These sources occupy every local ingredient of Theorem 2.1.  Broad searches found no statement of
the sharp cofinal `d=2` total-action boundary coupling exponentially evacuated event mass,
polynomial observer work, persistent mass-weighted current, and compact action sublevels.  Priority
is therefore **unverified**, not claimed.

The corpus's existing global-formation-properness theorem proves a different mechanism: a fixed
positive reporter makes a nonneutral scale orbit leave every bounded-work sublevel.  It does not
price renewal of a reporter whose admitted mass itself tends to zero.  The present theorem begins
exactly at that evacuation wall and classifies cumulative intervention action; it neither replaces
nor renames the earlier coercivity theorem.

## 9. Lean status

No Lean was written or built in this research phase.  The current corpus was audited read-only.
Exact reusable parents already indexed are
`HTGeometry.ConstitutiveGlobalFormationInformationProperness.toReal_klDiv_bernoulli`,
`HTGeometry.ConstitutiveTimeReversalLikelihoodCocycle.klDiv_eq_map_add_cond`,
`RHTower.sourceHorizontalPrimeAdaptiveJeffreysWork_le_linear`, the canonical forward/reverse
admission identities and bounds in `SourceHorizontalAbelianClassLawApertureEvacuation`, and the
existing real p-series/geometric-limit infrastructure.  The only substantial new formal layer is
the cofinal lower-bound assembly and compact product-sublevel wrapper.
Formalization must wait for a separate dependency-closed Lean pass and must enter pipeline 3 only
after direct check, module build, lint, axiom audit, and umbrella wiring.

## Log

- 2026-08-12 — exact current frontier re-audited; information disintegration already present,
  source renewal still missing.
- 2026-08-12 — exponential/polynomial threshold conjectured, attacked at `d>2`, and sharpened to
  an if-and-only-if finite-action classification by two-point I-projection.
- 2026-08-12 — global compact-sublevel theorem and source-horizontal linear-action corollary closed
  on paper.
- 2026-08-14 — Full unconditional Lean closure: exact aperture KL disintegration and piecewise information projection, sharp EReal liminf/divergence through degree two, compact action sublevels, exact superquadratic two-point witness/entrance, and source-horizontal orientation prices; targeted builds, umbrella, scoped scan, and standard-only axiom audits pass.
