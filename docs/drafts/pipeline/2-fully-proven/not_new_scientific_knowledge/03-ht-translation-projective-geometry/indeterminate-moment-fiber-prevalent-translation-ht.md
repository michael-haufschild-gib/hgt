# Indeterminate moment fibers are locally prevalent in maximal translation HT

- **ID:** `indeterminate-moment-fiber-prevalent-translation-ht`
- **Stage:** 2-fully-proven on paper / needs audit
- **Type:** THEOREM / MEASURE-THEORETIC MOMENT-FIBER PHASE LAW
- **Lane:** general hypertranscendence; Hamburger moment geometry; prevalence
- **Scientific status:** `[PROVED HERE] [BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent:** `indeterminate-moment-fiber-maximal-translation-ht.md`
- **Statement:** In every bounded positive barycentric chart inside an indeterminate
  Hamburger moment fiber, maximal differential-algebraic independence of the full complex
  translation family is locally prevalent, not merely residual. More precisely, one compact
  product probe of moment-preserving extremal-mixture directions makes the full-translation-HT
  locus have probability one after every deterministic recentering in a smaller chart ball.

## Exact target

Use the parent card's pairwise mutually singular `N`-extremal measures `(mu_(tau_n))`, weights
`eta_n>0`, mean-zero Banach space

```text
E_eta={v in ell-infinity(R):sum_n eta_n v_n=0},
X_delta={1+v:v in E_eta, ||v||_infinity<delta},  0<delta<1.  (1)
```

Let `G_delta^full subset X_delta` be the densities whose Cauchy transforms have differentially
algebraically independent translates for every finite tuple of distinct complex shifts.

`[PROVED HERE]` For every closed ball `B` whose positive distance from the boundary of `X_delta` is
`r>0`, there is a compactly supported Borel probability measure `Pi_B` on `E_eta`, supported in the
ball of radius `r`, such that

```text
Pi_B({w:x+w in G_delta^full})=1                             (2)
```

for every `x in B`. The probe is required to be an explicit convergent product random series of
finite-support moment-preserving directions, with each coordinate law absolutely continuous.

The corresponding full-fiber statement is: for every `mu_0 in M(s)` and every weak neighborhood
`W` of `mu_0`, there is a compactly supported probability cloud inside `W` whose measures have
maximal full-complex-translation HT almost surely, obtained by an arbitrarily small convex
insertion of the same probe simplex.

## Finite-support control blocks `[PROVED HERE]`

The mean-zero controllability theorem remains true when its domain is restricted to finitely
supported directions

```text
E_eta^fin={v in E_eta:v_n=0 for all but finitely many n}.    (3)
```

Indeed, suppose a real functional on one finite Cauchy-jet target annihilates the image of
`E_eta^fin`. Writing its value on the `n`th extremal parameter as `F_n`, test against the two-point
direction

```text
v_p=1/eta_p,  v_q=-1/eta_q,  v_n=0 otherwise.               (4)
```

This gives `F_p=F_q` for every pair, so `(F_n)` is constant. The parent card's reflected rational
principal-part argument then forces every coefficient of the functional to vanish. The image has
zero real annihilator and lies in a finite-dimensional target, hence it is the whole target.

Consequently every finite translated jet packet has a finite family of normalized directions in
`E_eta^fin` whose images span it.

## Compact product-probe construction `[PROVED HERE]`

Enumerate the countable collection of triples consisting of:

1. a differential-relation support and coefficient-degree bound;
2. a number of shifts and a compact local patch in its configuration space;
3. a separated evaluation packet with rank-defect codimension larger than the patch dimension.

For the `j`th triple, finite-support mean-zero controllability supplies finitely many directions
`v_(j,1),...,v_(j,d_j) in E_eta` whose Cauchy-jet images span the full evaluation packet throughout
the patch after shrinking it. Normalize these directions and choose positive amplitudes `a_j` with

```text
sum_j a_j d_j < r.                                         (5)
```

For independent uniform variables `X_(j,k) in [-1,1]`, put

```text
V=sum_j a_j sum_(k=1)^(d_j) X_(j,k) v_(j,k).               (6)
```

The series converges absolutely and uniformly in `E_eta`. Let

```text
Omega=product_j [-1,1]^(d_j)                                (7)
```

with product Lebesgue probability. The partial-sum maps from `Omega` to `E_eta` are continuous and
their tails converge uniformly by (5). Hence (6) is a continuous map from compact `Omega` into
`E_eta`; its pushforward `Pi_B` is compactly supported. Every direction has weighted mean zero, and
`||V||_infinity<r`, so `x+V` remains in `X_delta` for every `x in B`.

## Conditional transversality has probability one `[PROVED HERE]`

Fix a deterministic recentering `x in B` and one enumerated relation patch `j`. Condition on every
random block except

```text
xi_j=(X_(j,1),...,X_(j,d_j)).                               (8)
```

The conditioned blocks give one fixed bounded mean-zero background `w`. On the open Euclidean
parameter space containing `[-1,1]^(d_j)`, the row-jet map is

```text
Psi_j(xi_j,h)
 =E_j(m_(x+w+a_j sum_k xi_(j,k)v_(j,k)),h).                 (9)
```

The Cauchy transform is affine in the density. Therefore the derivative of (9) in `xi_j` is
`a_j` times the fixed controllability matrix of the chosen directions. It is onto throughout the
local shift patch after the patch was shrunk in the enumeration. This derivative is independent of
`x`, `w`, and the values of every other random block. Thus `Psi_j` is a real-analytic submersion for
every conditioning.

Stratify the finite-dimensional algebraic rank-defect set `D_j` by finitely many Whitney strata.
The almost-everywhere form of finite-dimensional parametric transversality says that for Lebesgue-
almost every `xi_j`, the partial map `h |-> Psi_j(xi_j,h)` is transverse to every stratum. The
evaluation-row count was chosen so every stratum has real codimension strictly larger than the
real dimension of the shift patch. Every transverse preimage is therefore empty. Hence, for every
fixed conditioning, the exceptional set of `xi_j` has Lebesgue measure zero.

Fubini gives

```text
Pi_B({V:the jth relation occurs somewhere on its patch})=0. (10)
```

This conclusion holds for the fixed deterministic `x`, and the proof uses the same probe for every
`x in B`; only the null set is allowed to depend on `x`, exactly as in the definition of
prevalence. Taking the countable union of (10) over all relation patches proves (2).

Conditioning on infinitely many other blocks causes no regularity gap: their series converges in
`E_eta` to one bounded background before (9) is considered, while the dependence on the remaining
finite block and on `h` is still affine-holomorphic and real-analytic respectively.

## Local-prevalence theorem `[PROVED HERE]`

Let a Borel set `G` in a Banach space be prevalent if some compactly supported probability `Pi`
satisfies `Pi(G-x)=1` for every deterministic `x`. Since `X_delta` is open, use the local version on
balls compactly contained in it.

The construction above proves:

> **Every compactly contained closed ball in `X_delta` admits one compact product probe `Pi_B`
> such that maximal full-complex-translation differential independence has probability one after
> every deterministic recentering in the ball.**

Thus `G_delta^full` is locally prevalent throughout `X_delta`. Its complement is simultaneously
meagre and locally Haar-null under explicit finite-support extremal-mixture probes.

## Full moment-fiber probability clouds `[PROVED HERE]`

Fix `mu_0 in M(s)` and a weak neighborhood `W`. Choose `epsilon>0` small enough that every measure

```text
nu_(x,V)=(1-epsilon)mu_0+epsilon mu_(x+V)                  (11)
```

with `x+V` in the compact probe support belongs to `W`. Such an `epsilon` exists because a basic
weak neighborhood uses finitely many bounded continuous test functions and all measures involved
are probabilities.

The previous conditional proof applies verbatim to (11). Its deterministic background is now
`(1-epsilon)m_(mu_0)`, while every control derivative is multiplied by the nonzero scalar
`epsilon`; surjectivity and the codimension argument are unchanged. Therefore the pushforward of
`Pi_B` under (11) is a compactly supported probability measure inside `W`, and its sampled Cauchy
transform has maximal full-complex-translation differential rank almost surely.

This is stronger than choosing a probability supported on an already known residual set: the cloud
is an explicit affine product of finite-support moment-preserving directions, has nondegenerate
absolutely continuous conditional laws in every relation-killing block, and works after every
deterministic recentering. `QED`

## Positive carrier consequence

> A differential-rigid marked subfiber must be thin under every moment-preserving extremal probe,
> not only meagre. Any selector stable under one full product aperture inherits maximal translation
> HT almost surely and therefore cannot impose a universal finite-shift differential law.

This makes the formal-collapse/global-explosion phase robust in both Baire category and local
prevalence. It still does not identify a canonical RH selector; it sharpens the geometry that such
a selector must violate.

## Attack and boundary audit

1. `[BRIDGE]` A dense residual set can trivially support an artificial probability-one measure.
   That is not the theorem: the same compact product probe works after every deterministic
   recentering and is built from absolutely continuous control blocks.
2. `[PROVED]` Finite support of the moment measure remains the sharp dead boundary. Its Cauchy
   transforms are rational, so no probe can create one HT translate.
3. `[PROVED]` Strict positivity is preserved because the probe norm is smaller than the chart's
   boundary margin. No signed-measure excursion is used.
4. `[PROVED]` Uncountably many complex shifts are handled before probability enters: codimension
   makes the transverse preimage of each rank-defect stratum empty over a whole compact patch.
5. `[BOUNDARY]` The probe is source-intrinsic only after a countable extremal palette and an
   enumeration are fixed. The theorem proves local prevalence, not a canonical probability law on
   the full moment fiber.

## Parent-theory and significance verdict

The theorem does **not** raise the combined moment-fiber route above its existing `84/100` estimate.
Hunt--Sauer--Yorke prevalence and prevalent parametric transversality already provide the general
measure-theoretic framework, while `fixed-taylor-modulus-ht-real-rootedness-nonselection.md` already
uses product-Haar nullity to make HT phase completions almost sure. The recentering-uniform
extremal-mixture probe and the exact all-moment/full-complex-translation application are useful,
but they are a direct bridge from those parents plus the existing moment-fiber controllability
theorem. They are not a new proof engine or a new scientific obstruction.

The exact theorem remains worth retaining because it closes a possible escape hatch: the residual
explosion is not an artifact of Baire category. It is also full measure under explicit local probe
clouds. But the honest scientific classification is `[BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]`.

A true crossing above 90 for the parent route still requires at least one of:

- a normalization-independent canonical probability or explicit point in the prevalent phase;
- a converse classifying all jet-deficient source markings;
- a theorem placing a concrete Euler/functional-equation carrier on one side of the phase law.

## Gates

- [x] residual full-fiber parent theorem available on paper
- [x] countable relation-patch enumeration available
- [x] mean-zero finite Cauchy-jet controllability available
- [x] finite-support mean-zero control blocks proved
- [x] compact product probe constructed rigorously
- [x] conditional parametric transversality proved for every deterministic recentering
- [x] full-fiber convex-insertion corollary proved
- [x] preliminary prevalence and generic-hypertranscendence parent audit
- [ ] independent specialist proof audit
- [ ] unconditional Lean formalization of the exact theorem

## Log

- 2026-07-12 -- Proved a recentering-uniform compact product-probe theorem and the full-fiber
  probability-cloud corollary. Parent audit then reduced the mechanism to established prevalence
  and prevalent transversality, with an existing project tail-Haar HT precedent. Retained the
  theorem as a bridge and did not raise the scientific score.
