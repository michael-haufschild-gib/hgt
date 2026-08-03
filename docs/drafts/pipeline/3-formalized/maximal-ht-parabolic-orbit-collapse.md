# Maximal HT with one-point parabolic orbit collapse

- **ID:** `maximal-ht-parabolic-orbit-collapse`
- **Stage:** 3-formalized (all five items unconditional in Lean; item `(2)` carries the Setup's
  translate-independence input, exactly as the paper does)
- **Type:** THEOREM (paper) — `[PROVED HERE] [NOVELTY UNVERIFIED]`
- **Lane:** general hypertranscendence; translation dynamics; universality and recurrence boundary
- **Statement:** A bounded outer function can have a differentially algebraically independent
  continuum of parabolic translates at every algebraic power while the compact-open closure of its
  real orbit is a topological circle obtained by adding one constant rank-collapse point.  Maximal
  algebraic orbit freedom therefore coexists with complete topological escape and failure of strong
  self-recurrence.  The collapse mechanism holds for every finite positive Stieltjes measure on a
  half-line; maximal HT is realized by a comeager atomic subfamily inside that universally
  collapsing class.

## Goal

Separate two notions that are often conflated in the HT landscape:

1. algebraic freedom of distinct translates, measured by differential transcendence degree;
2. topological richness of one translation orbit, measured by compact-open universality or strong
   recurrence.

The theorem realizes the strongest possible first property together with an extremely small orbit
closure for the second.  This is a general law about HT functions; the zeta application is only its
route boundary.

## Setup

Fix a bounded real sequence `u=(u_j)` in the comeager free set of
`herglotz-full-translation-ht-krein-index-orthogonality.md`.  Put

`lambda_j=j+1`, `w_j=2^(-j-1) exp(u_j)`,

`m(z)=sum_(j>=0) w_j/(lambda_j-z)`.                            (1)

Then `m` is Herglotz on the upper half-plane `H`, and the full complex translation family

`{m(z+h):h in C}`                                             (2)

is differentially algebraically independent over `C(z)`.

Let

`phi(w)=i(1+w)/(1-w)`,

`sigma(w)=(m(phi(w))-i)/(m(phi(w))+i)`,

`O(w)=exp(sigma(w))`.                                         (3)

For real `t`, define the parabolic disk automorphism

`tau_t=phi^(-1) o (z |-> z+t) o phi`.                         (4)

Thus `phi o tau_t=phi+t`.

## Theorem `[PROVED HERE]`

1. `O,O^(-1) in H^infinity(D)`, and `O` is outer and cyclic in `H^2(D)`.
2. For every `N>=1`, the continuum

   `{(O o tau_t)^N:t in R}`                                  (5)

   is differentially algebraically independent over `C(w)`.
3. For every `N>=1`,

   `(O o tau_t)^N -> exp(-N)`                                (6)

   locally uniformly on `D` as `t->+infinity` and as `t->-infinity`.
4. In the compact-open topology of `Hol(D)`,

   `closure{(O o tau_t)^N:t in R}`

   ` ={(O o tau_t)^N:t in R} union {exp(-N)}`,                (7)

   and this closure is homeomorphic to the circle.  More precisely, the orbit map extends to a
   homeomorphism from the one-point compactification `R union {infinity}` onto (7), sending the
   added point to `exp(-N)`.

5. The orbit in (5) is not compact-open universal, even among nonvanishing targets.  For `N=1`,
   it also fails strong self-recurrence: there are a compact `K subset D` and `epsilon>0` for which

   `{t>=0:sup_(w in K)|O(tau_t(w))-O(w)|<epsilon}`             (8)

   is bounded and therefore has lower asymptotic density zero.

## Proof

### 1. Bounded outer maximal-HT carrier

Strict Herglotz positivity and the Cayley transform give `|sigma(w)|<1` on `D`.  Hence

`exp(-1)<|O(w)|<exp(1)`,                                      (9)

so `O` and its inverse lie in `H^infinity`.  Since `O=exp(sigma)` with bounded analytic exponent,
it is outer; therefore it is cyclic in `H^2`.

The proof in `hardy-cyclicity-maximal-ht-field-blindness.md` transports (2) through the rational
domain Cayley map and invertible rational codomain Cayley map, then recovers the independent
derivative orbit from

`D(O o tau_t)/(O o tau_t)=D(sigma o tau_t)`.                  (10)

Thus the `N=1` family is differentially algebraically independent.  For distinct
`t_1,...,t_r`, every `O o tau_(t_j)` is algebraic over its `N`-th power.  If the powers were
differentially algebraically dependent, their generated differential field would have differential
transcendence degree below `r`; adjoining the algebraic `N`-th roots could not raise that degree to
`r`.  This contradicts the independence at `N=1`.  Hence (5) is independent for every `N`.

### 2. Finite-measure Stieltjes collapse

The decay mechanism is more general than the atomic free family.  Let `mu` be any finite positive
Borel measure on `[0,infinity)` and define its Stieltjes transform on `H` by

`m_mu(z)=integral_[0,infinity) 1/(lambda-z) dmu(lambda)`.      (11)

Then

`m_mu(z+t)->0` locally uniformly on `H` as `t->+-infinity`.    (12)

Fix a compact `L subset H`.  Choose

`delta=inf_(z in L) Im z>0`, `A=sup_(z in L)|Re z|`,

and write `W=mu([0,infinity))<infinity`.  For `t<0` with `|t|>2A`,

`|lambda-z-t|>=lambda+|t|-A>=|t|-A`

for every `z in L` and `lambda>=0`, so

`sup_(z in L)|m_mu(z+t)|<=W/(|t|-A)->0`.                      (13)

Now take `t>2A+2` and split the integral at `lambda=t/2`.  The lower part has modulus at most

`W/(t/2-A)`.                                                   (14)

On the upper part every denominator has modulus at least `delta`, hence its modulus is at most

`delta^(-1) mu((t/2,infinity))`.                              (15)

The tail in (15) tends to zero by finiteness of `mu`.  The bounds are uniform on `L`, proving (12).

The atomic measure `mu=sum_j w_j delta_(lambda_j)` in (1) is finite, so (12) gives the required
decay of `m`.  Thus every finite positive Stieltjes carrier on a half-line has the same two-ended
topological collapse after the Cayley--exponential transform; the transversality theorem selects a
comeager atomic subfamily for which the orbit is simultaneously maximally HT.

### 3. One-point collapse

For compact `K subset D`, the image `phi(K)` is compact in `H`.  By (12) and
`phi(tau_t(w))=phi(w)+t`,

`m(phi(tau_t(w)))->0`                                        (16)

uniformly on `K` at both ends.  The codomain Cayley map sends `0` to `-1`.  Continuity of the Cayley
map and exponential therefore gives

`O(tau_t(w))->exp(-1)`                                       (17)

locally uniformly.  Taking powers proves (6).

To identify the closure, consider any convergent sequence of orbit points with parameters `t_n`.
If `(t_n)` is unbounded, a subsequence tends to one of the two infinities and (6) forces the limit
`exp(-N)`.  If `(t_n)` is bounded, a subsequence tends to some real `t`; continuity of translation,
composition, and the locally uniform topology gives the orbit point `(O o tau_t)^N`.  Conversely,
the constant in (7) is attained as the limit at infinity.  This proves (7).

To identify the topology rather than only the underlying set, define

`j_N(t)=(O o tau_t)^N`, `t in R`,

and set `j_N(infinity)=exp(-N)` on the one-point compactification of `R`.  Equation (6) is exactly
continuity at the added point.  The map is injective on `R`: equality at two distinct parameters
would contradict the differential algebraic independence in (5), already through the polynomial
relation `Y_1-Y_2`.  No finite orbit point is the added constant, because a nonzero analytic
function whose `N`-th power is constant is itself constant, whereas `O o tau_t` is nonconstant.
Thus `j_N` is a continuous bijection from a compact space to the Hausdorff space `Hol(D)`.  It is a
homeomorphism onto its image, which is (7).  Since the one-point compactification of `R` is a
circle, the orbit closure is a topological circle.

### 4. Failure of universality and strong recurrence

Equation (9) gives

`exp(-N)<|(O o tau_t(w))^N|<exp(N)`                           (18)

for all `t,w`.  The orbit cannot approximate, even at one point, a nonzero constant of modulus less
than `exp(-N)`.  Thus it is not universal among nonvanishing holomorphic targets.

The function `O` is nonconstant because `m` is nonconstant and both transforms in (3) are
nonconstant and locally injective.  Choose `w_0 in D` with `O(w_0)!=exp(-1)` and put

`epsilon=|O(w_0)-exp(-1)|/3`.                                 (19)

By (15), for all sufficiently large `|t|`,

`|O(tau_t(w_0))-exp(-1)|<epsilon`.                            (20)

The triangle inequality and (17) then give

`|O(tau_t(w_0))-O(w_0)|>epsilon`.                             (21)

Taking `K={w_0}` shows that the set (8) is bounded.  Its lower asymptotic density is zero, proving
failure of strong self-recurrence. `QED`

## Law extracted

**Algebraic-freedom/topological-collapse law.**  Differential-algebraic independence measures the
absence of every finite differential relation among distinct orbit points; it imposes no recurrence,
density, ergodicity, or universality on the parameterized orbit.  The separation persists after
every algebraic power normalization: each power orbit remains maximally free while both ends of the
real parameter line collapse to one constant.

**One-point differential-rank boundary law.**  For every `N`, the topological circle (7) has one
distinguished point `exp(-N)` with differential transcendence degree zero over `C(w)`.  Every finite
set of distinct points in its complement is differentially algebraically independent and therefore
has maximal differential transcendence degree equal to its cardinality.  Hence differential rank
can collapse from the maximum possible value on every finite orbit packet to zero at a single
compact-open boundary point.  Differential-algebraic freedom is not closed under compact-open
compactification, even for an invertible outer carrier and even simultaneously at every power.

This is not a statement that HT functions are generally nonuniversal.  It is a sharp independence
theorem: the strongest available algebraic orbit freedom does not imply even weak topological
richness of that orbit.

## RH-route consequence

Voronin universality and Bagchi strong recurrence are translation-dynamical properties of the
zeta function.  The theorem rules out the implementation claim

> Full translation hypertranscendence, or differential-algebraic independence of all distinct
> translates (even at every power level), supplies universality or the strong self-recurrence needed
> for a Bagchi-type RH argument.

It does not refute Voronin's theorem or Bagchi's RH equivalence.  Those results use a distinguished
vertical zeta orbit, Euler-product probability/limit-distribution structure, and a pointed target
equal to zeta itself.  The theorem proves that none of that topological recurrence is contained in
maximal HT freedom alone.  A viable recurrence proof must consume an additional arithmetic measure,
phase distribution, Euler marking, or equivalent topological input.

## Parent-theory and preliminary novelty audit

- `[SEARCH]` Voronin's primary theorem concerns approximation by vertical zeta translates:
  `https://doi.org/10.1070/IM1975v009n03ABEH001485`.
- `[SEARCH]` The effective-universality literature states Voronin approximation and Bagchi's limiting
  density refinement: `https://arxiv.org/abs/1611.10325`.
- `[SEARCH]` Birkhoff-type translation hypercyclicity and common hypercyclic vectors show that dense
  translation orbits are abundant in large holomorphic function spaces; for example
  `https://arxiv.org/abs/1411.7815`.
- `[SEARCH]` Classical work also studies linear independence of translates and translation-generated
  closed subspaces separately; Edwards' 1951 paper is
  `https://www.numdam.org/item/AIF_1951__3__31_0/`.
- `[SEARCH]` The composition-operator literature contains strong orbital-limit results for
  parabolic non-automorphisms and hypercyclicity results for parabolic automorphisms.  For example,
  Bourdon--Shapiro's dichotomy, summarized in Feldman's 2010 thesis, says that only constants can be
  orbital limit points for the relevant non-automorphism class.  It does not construct one bounded
  outer vector for a continuous parabolic automorphism group whose orbit closure is a circle and
  whose every finite orbit packet is differentially algebraically independent.  Source:
  `https://etd.ohiolink.edu/acprod/odb_etd/ws/send_file/send?accession=bgsu1280934433`.

Preliminary searches did not locate the exact coexistence proved here: an uncountable
differentially algebraically independent translation family at every power, carried by an invertible
outer function, whose continuous real orbit compactifies to a circle with one DA rank-collapse
point and has zero-density self-recurrence.  The proof depends on the separately novelty-unverified
Herglotz full-orbit theorem, but the circle compactification, topological rank boundary, and
all-power strengthening add a distinct exact law.  It passes the proof and significance gates;
scientific priority remains provisional pending specialist audit in differential algebra and linear
dynamics.

## Lean status

`CayleySchur.lean` supplies only pointwise Cayley bounds.  The repository does not formalize locally
uniform convergence on `Hol(D)`, outer functions, translation hypercyclicity/recurrence, the atomic
Herglotz series with uniform tail estimates, or differential independence of the parabolic orbit.
Every one of those layers occurs in the theorem.  No stage-3 promotion is justified until the full
unconditional statement is formalized in Lean.

## Gates

- [x] 0 -> 1: algebraic-freedom versus orbit-topology separation isolated
- [x] 1 -> 2: complete unconditional paper proof
- [ ] independent proof audit of the two-sided uniform decay and closure classification
- [ ] full parent-theory and literature audit sufficient for novelty promotion
- [ ] 2 -> 3: complete unconditional theorem formalized in Lean
- [ ] 3 -> 4: publication-ready preprint and independent novelty review

## Log

- 2026-07-11 -- Proved two-sided local-uniform decay of the positive atomic Herglotz translate and
  transported it through Cayley and exponential maps to a one-point parabolic orbit closure.
- 2026-07-11 -- Proved that every algebraic power orbit remains differentially algebraically
  independent while universality and strong self-recurrence fail.
- 2026-07-11 -- Strengthened the two-sided decay from the exponentially weighted atomic example to
  every finite positive Stieltjes measure on a half-line, separating the universal collapse
  mechanism from the residual maximal-HT selection.
- 2026-07-11 -- Identified the exact orbit topology: at every power the orbit closure is a circle,
  with maximal differential rank on every finite packet off one added constant point and rank zero
  at that point.

## Lean status: the finite-measure collapse mechanism is proved

`StieltjesTranslationCollapse.lean` formalizes section 2 of the proof, equations `(12)`--`(15)`,
for an arbitrary finite positive Borel measure on the line (the card states it for `[0,infinity)`;
the same two-regime estimate needs no support hypothesis):

- `upperStrip delta A` -- the strips `{delta <= Im z, |Re z| <= A}` that carry the uniformity;
- `exists_tail_measureReal_lt` -- tail masses of a finite measure are eventually small
  (continuity from above along `{R < |t|}`);
- `norm_translatedKernel_le_inv_im` and `norm_translatedKernel_le_inv_re` -- the two kernel regimes:
  height bound `1/delta` everywhere, and `1/(|t| - R - A)` on the spectrum bounded by `R`;
- **`norm_cauchyTransform_translate_le`** -- the two-regime bound
  `‖m(z+t)‖ <= mass/(|t| - R - A) + nu{|lam| > R}/delta`, uniform on the strip;
- **`tendstoUniformlyOn_cauchyTransform_translate`** -- `m(z+t) -> 0` uniformly on every strip as
  `|t| -> infinity` (the filter is `cocompact ℝ`, so both signs at once);
- **`tendstoUniformlyOn_cauchyTransform_translate_isCompact`** -- the same on every compact subset of
  the open upper half plane, which is equation `(12)`.

The Cauchy transform used is the corpus's own `cauchyTransform ν z = ∫ (t - z)⁻¹ dν`, so this
plugs directly into the Herglotz/Nevanlinna layer.  Axioms: `propext`, `Classical.choice`,
`Quot.sound`.

Remaining for this card, in dependency order: the Cayley transport `(3)` and the locally uniform
limit `(6)` (reduce to the collapse by `‖(m-i)/(m+i) + 1‖ <= 2‖m‖` whenever `Im m >= 0`, then
`‖exp(Na) - exp(-N)‖ <= 4N e^{-N}‖m‖`); the orbit-closure circle `(7)`; the universality and
recurrence failures `(5)`, `(8)`; and the outer/cyclic statement `(1)`, which needs Hardy-space
theory that mathlib does not have.

### The locally uniform orbit limit `(6)` is proved

`ParabolicOuterOrbitLimit.lean` closes item 3 of the theorem for every finite positive measure,
with no Hardy-space input:

- `cayleyToUpper w = i (1 + w) / (1 - w)` with **`im_cayleyToUpper_pos`**
  (`Im = (1 - |w|^2)/|1 - w|^2`) and `continuousOn_cayleyToUpper`;
- **`norm_cayleyQuotient_add_one_le`** -- `‖(m - i)/(m + i) + 1‖ <= 4‖m‖` whenever `‖m‖ <= 1/2`,
  proved from the reverse triangle inequality alone, so no Herglotz positivity is needed;
- **`norm_exp_sub_exp_le`** -- exponentiating a perturbation of size at most one costs a factor
  two, for exponents of nonpositive real part;
- `discExponent` and `parabolicOuterOrbit ν N t w = exp (N · sigma)`, the `N`-th power of the
  orbit read through the translated Cayley coordinate (`phi ∘ tau_t = phi + t` is built into the
  definition);
- **`norm_parabolicOuterOrbit_sub_le`** -- the explicit estimate
  `‖(O ∘ tau_t)^N - exp(-N)‖ <= 8 N ‖m(phi(w)+t)‖`;
- **`tendstoUniformlyOn_parabolicOuterOrbit`** -- equation `(6)`: the orbit converges to
  `exp (-N)` uniformly on every compact subset of the open unit disc, along `cocompact ℝ`, i.e.
  simultaneously as `t -> +infinity` and `t -> -infinity`.

Axioms: `propext`, `Classical.choice`, `Quot.sound`.

Next steps for this card, in order: (a) define the parabolic automorphism `tau_t` from the inverse
Cayley map and prove `phi ∘ tau_t = phi + t`, so the orbit above is literally
`(O ∘ tau_t)^N`; (b) the orbit-closure statement `(7)` -- injectivity of the orbit map plus the
limit gives the one-point compactification homeomorphism; (c) the failure of universality and of
strong recurrence `(5)`, `(8)`, which follow from the same estimate; (d) the differential
independence `(2)`, which imports the now-formalized Herglotz full-translation parent; (e) the
outer/cyclic statement `(1)`, still blocked on Hardy-space theory absent from mathlib.

### The parabolic automorphism, the modulus trap, and orbit rigidity are proved

`ParabolicCayleyAutomorphism.lean` supplies the literal objects of `(3)`--`(4)`:

- `cayleyToDisc z = (z - i)/(z + i)` with **`norm_cayleyToDisc_lt_one`** (`Im z > 0` gives modulus
  below one) and **`cayleyToUpper_cayleyToDisc`** (the Cayley pair is a left inverse);
- **`parabolicAut t w = cayleyToDisc (cayleyToUpper w + t)`**, with `norm_parabolicAut_lt_one` and
  **`cayleyToUpper_parabolicAut`** -- the defining identity `phi ∘ tau_t = phi + t`;
- `outerCarrier ν w = exp (cayleyToDisc (m (phi w)))` and
  **`parabolicOuterOrbit_eq_outerCarrier_pow`** -- the translated object of the previous module is
  literally `(O ∘ tau_t)^N`;
- **`im_cauchyTransform_pos_of_ne_zero`** -- strict Herglotz positivity for every nonzero finite
  positive measure (mass times a probability measure), hence `norm_discExponent_lt_one`, i.e.
  equation `(9)`;
- **`norm_parabolicOuterOrbit_bounds`** -- equation `(18)`:
  `exp(-N) < |(O ∘ tau_t)^N| < exp(N)` at every point and every translation.

`ParabolicOrbitRigidity.lean` proves items 5 and the injectivity half of item 4:

- `norm_cauchyTransform_le` (`‖m(z)‖ <= mass / Im z`) and `tendsto_cauchyTransform_translate`
  (pointwise form of the collapse);
- **`cauchyTransform_eq_zero_of_periodic`** -- a Cauchy transform that is periodic in the real
  direction high in the half plane vanishes there: iterate the period and apply the collapse;
- `eq_of_exp_eq_of_norm_lt` -- equal exponentials with difference below `2 pi` have equal exponents;
- **`parabolicOuterOrbit_injective`** -- **the orbit map is injective**.  Note this is proved
  *directly*, for every nonzero finite measure: high in the half plane both transforms are small,
  so the two Cayley exponents differ by less than a period and must agree, the Cayley map is
  injective, and the resulting periodicity of `m` forces `m = 0`, contradicting positivity.  The
  paper deduces injectivity from the differential independence `(2)`; the Lean proof does not need
  it, so item 4's injectivity no longer depends on the separately unverified Herglotz parent;
- **`exists_target_not_approximable`** -- equation `(18)` gives a nonzero constant target and an
  `epsilon` that the orbit never approaches: failure of universality even among nonvanishing
  targets;
- `outerCarrier_ne_exp_neg_one` (the carrier never equals the limiting constant, since its exponent
  has modulus below one and `-1` does not) and **`exists_bounded_returnSet`** -- equations
  `(19)`--`(21)`: beyond a finite horizon the orbit stays at distance at least
  `‖O(w) - exp(-1)‖/3` from its own initial point, so the return set `(8)` is bounded and has
  lower density zero.

Axioms: `propext`, `Classical.choice`, `Quot.sound` throughout.

Still open for this card: the closure statement `(7)` (needs continuity of `t ↦ (O ∘ tau_t)^N` into
the compact-open topology, then the `OnePoint ℝ` extension is a continuous injection from a compact
space and hence a homeomorphism onto the closure -- injectivity and the added-point limit are both
proved above); the differential independence `(2)`; and the outer/cyclic statement `(1)`.

### The one-point closure `(7)` is proved, and it is a circle

`ParabolicOrbitCircleClosure.lean` closes item 4 of the theorem in the compact-open topology of the
disc, realized as `C(openDisc, ℂ)`:

- `openDisc`, `instLocallyCompactOpenDisc`, `continuousOn_cauchyTransform_upper` (from the corpus's
  `analyticOnNhd_cauchyTransform`), `im_cauchyTransform_nonneg`, `continuousOn_cayleyToDisc`;
- **`continuous_uncurry_parabolicOuterOrbit`** -- joint continuity of `(t, w) ↦ (O ∘ tau_t)^N(w)`;
- `discOrbit ν N t : C(openDisc, ℂ)` with **`continuous_discOrbit`** (via
  `ContinuousMap.continuous_of_continuous_uncurry`);
- **`tendsto_discOrbit`** -- compact-open convergence of the orbit to the constant `exp (-N)`,
  obtained from the locally uniform limit through
  `tendstoLocallyUniformly_iff_forall_isCompact`;
- `orbitOnePoint` -- the extension `j_N` to `OnePoint ℝ`, with **`continuous_orbitOnePoint`**
  (continuity at the added point is exactly `(6)`, via `OnePoint.continuousAt_infty'` and
  `coclosedCompact_eq_cocompact`);
- `discOrbit_ne_const` -- the constant is never an orbit point, directly from the modulus trap
  `(18)` (the paper argues instead that a nonconstant function cannot have constant `N`-th power);
- **`injective_orbitOnePoint`** and **`isClosedEmbedding_orbitOnePoint`** -- `j_N` is a continuous
  injection of a compact space into a Hausdorff space, hence a closed embedding;
- **`closure_range_discOrbit`** -- equation `(7)`:
  `closure {(O ∘ tau_t)^N : t} = {(O ∘ tau_t)^N : t} ∪ {exp (-N)}`;
- **`exists_homeomorph_closure_range_discOrbit`** -- the card's "more precisely" clause: a
  homeomorphism `OnePoint ℝ ≃ₜ closure`, restricting to the orbit map on the line;
- **`exists_homeomorph_sphere_closure_range_discOrbit`** -- the closure is homeomorphic to the
  circle `sphere (0 : EuclideanSpace ℝ (Fin 2)) 1`, using mathlib's
  `onePointEquivSphereOfFinrankEq`.

Axioms: `propext`, `Classical.choice`, `Quot.sound`.

Card status after this batch: items `(3)` `(6)`, `(4)` `(7)`, `(5)` `(8)` `(18)` and the bounded
half of `(1)` (`exp(-1) < |O| < exp(1)`, equation `(9)`) are unconditional in Lean, for every
nonzero finite positive measure -- no atomicity, no half-line support, no Hardy theory.  The two
remaining items are the differential independence `(2)` (which needs the Herglotz full-translation
parent transported through the Cayley maps) and the outer/cyclic half of `(1)` (Hardy-space theory,
absent from mathlib).

### Item `(2)`: what is missing, and the exact construction plan

Item `(2)` -- differential independence of the parabolic translates at every power -- imports its
input from `../../not_new_scientific_knowledge/hardy-cyclicity-maximal-ht-field-blindness.md`,
whose own Lean status names the missing layer: *maximal differential independence under rational
change of variable*.  That layer does not exist in the tree.  Audit of what is there:

- the parent freeness statements are analytic, in the form
  `¬ FamilyDifferentiallyAlgebraicOn (fun i z => series (z + shift i)) domain`
  (`HerglotzDiscreteSupportFreeness.exists_denseResidual_discreteHerglotzCauchy_fullTranslationFree`,
  and the regularized/affine variants);
- the only transports of `FamilyDifferentiallyAlgebraicOn` in the tree are
  `familyDifferentiallyAlgebraicOn_of_mul_polynomial`, `_of_add_polynomial`, `_of_affine` and
  `familyDifferentiallyAlgebraicOn_congr_of_isOpen` (`FamilyPolynomialGauge.lean`), all built from a
  *polynomial* jet substitution with a triangular Leibniz block and a surjective point map;
- there is no inversion transport, hence no Mobius transport, and no exponential transport.

The chain `(2)` needs, in order:

1. **Inversion.**  `y = 1/g` on a domain where `g` does not vanish.  Since
   `y^{(k)} = N_k(jets g) / g^{k+1}` with `N_0 = 1` and
   `N_{k+1} = D(N_k) · X_0 - (k+1) · X_1 · N_k`, where `D` is the total jet derivation
   (`MvPolynomial.mkDerivation` with `D (X n) = X (n+1)`), the substitution is rational with
   denominator a power of the zeroth jet.  Nonvanishing of the pulled-back relation follows the
   corpus's own pattern: the point map is triangular, hence surjective onto the packet
   `{y : y_{i,0} ≠ 0}`, and a polynomial vanishing there is zero because
   `P · ∏ Y_{i,0} = 0` everywhere over an infinite field.
   The reusable prerequisite is the **jet chain rule**:
   `eval (fun n => iteratedDeriv n g z) (D P) = deriv (fun w => eval (fun n => iteratedDeriv n g w) P) z`
   for smooth `g`, by `MvPolynomial.induction_on`.  This is missing from the tree and is the first
   thing to build.
2. **Mobius.**  `(x - i)/(x + i) = 1 - 2i/(x + i)` factors as translate, invert, scale, translate,
   so step 1 plus the existing affine gauge gives the full invertible rational codomain change of
   variable -- exactly the missing layer both cards name.
3. **Precomposition** with the domain Cayley map (a biholomorphism of the disc onto the half plane):
   jets compose by Faa di Bruno with rational coefficients, so the same clearing pattern applies.
4. **Exponential.**  `O = exp(sigma)` is the genuinely hard step: a relation among the `O_i` must be
   pushed to one among the `sigma_i`, which is an Ostrowski/Kolchin-type statement about
   exponentials of a differentially independent family.  This is research-level and is the real
   content of the missing "field blindness" parent.

Steps 1--3 are unconditional and buildable now; step 4 is the open one.  Nothing here is
axiomatized.

### Step 1 of the missing layer is built: the jet total derivation and the reciprocal jets

`JetTotalDerivation.lean` (wired, axiom-clean) supplies the engine the plan above calls for:

- `jetVec f z n = iteratedDeriv n f z` and **`jetDerivation`** -- the derivation of
  `MvPolynomial ℕ ℂ` with `X n ↦ X (n+1)`, built with `MvPolynomial.mkDerivation`;
- **`differentiableAt_iteratedDeriv_of_contDiffAt`** -- on an open set of smoothness every iterated
  derivative is again differentiable (through `iteratedDerivWithin` and
  `iteratedDerivWithin_of_isOpen`);
- `differentiableAt_eval_jetVec` and **`deriv_eval_jetVec`** -- **the jet chain rule**:
  `deriv (fun w => eval (jetVec f w) P) z = eval (jetVec f z) (jetDerivation P)`, by
  `MvPolynomial.induction_on`;
- `invJetNum` -- the universal reciprocal numerators, `N_0 = 1`,
  `N_{k+1} = D(N_k) * X_0 - (k+1) * X_1 * N_k`;
- **`iteratedDeriv_inv_eq_invJetNum_div`** -- the reciprocal jet formula
  `(1/f)^{(k)} = eval (jetVec f) (invJetNum k) / f^{k+1}` on any open set where `f` is smooth and
  nonvanishing.

The nonvanishing half of the transport is also built:
**`mvPolynomial_eq_zero_of_eval_eq_zero_off_coordinates`** -- a jet polynomial vanishing at every
point whose listed coordinates are nonzero is the zero polynomial (multiply by the product of those
coordinates and apply `MvPolynomial.funext`).  This is exactly what a rational jet substitution
needs, since the substituted relation only exists where the zeroth jets do not vanish.

What remains for the inversion transport of `FamilyDifferentiallyAlgebraicOn` itself: assemble the
blockwise substitution `X_{i,k} ↦ invJetNum k (block i) / X_{i,0}^{k+1}` into the fraction field of
the jet polynomial ring, clear denominators to a numerator polynomial `R`, and prove `R ≠ 0` -- for
which the two ingredients above (the reciprocal jet formula and the coordinate-nonvanishing lemma)
plus the triangular solve `x_{i,0} = 1/y_{i,0}`, upward, are what is needed.  With that, Mobius
transport follows by composing with the existing affine gauge, and steps 2--3 of the plan close.

### Step 1 continued: the reciprocal jets are now in the family jet ring

`JetTotalDerivation.lean` additionally proves the support bounds needed to place the reciprocal
numerators in a bounded jet block:

- **`jetDerivation_mem_supported`** -- the total derivation raises the jet support by at most one
  (`Algebra.adjoin_induction` on `MvPolynomial.supported_eq_adjoin_X`);
- **`invJetNum_mem_supported`** -- `invJetNum k` involves only jet variables of order at most `k`.

`FamilyInversionJets.lean` (wired, axiom-clean) transports them:

- **`eval_eq_of_supported`** -- evaluation of a supported polynomial depends only on its support
  coordinates;
- `familyJetRename`, **`eval_rename_familyJetRename`** -- the blockwise renaming into
  `FamilyJetIndex m n` computes the single-function evaluation, legitimate exactly because of the
  support bound;
- `familyInvJetNum m n i k` and **`familyJetVec_inv_apply`** -- the jet vector of the reciprocal
  family is `eval (familyJetVec g z) (familyInvJetNum m n i k) / (g i z)^(k+1)`.

**Remaining construction, now fully specified.**  Let `d := P.totalDegree` and put
`Theta (inl ()) := X (inl ())`, `Theta (inr (i,k)) := familyInvJetNum m n i k * X_{i,0}^{n-k}`.
Define

```text
R := sum over M in P.support of
       C (coeff M P) * (prod over v of Theta v ^ M v) * (prod over i of X_{i,0} ^ ((n+1)*(d - e_i M)))
```

where `e_i M := sum over k of M (inr (i,k))`.  The exponent bookkeeping is uniform:
each monomial contributes `x_{i,0}^{(n+1) e_i}` from `Theta` against the true denominator
`x_{i,0}^{sum_k M_{i,k}(k+1)}`, and the padding `(n+1)(d - e_i)` makes every monomial carry the same
factor, so

```text
eval x R = (prod over i of x_{i,0} ^ ((n+1)*d)) * eval (jets of 1/g) P .
```

Vanishing of `R` on the domain is then immediate.  For `R ≠ 0` the surjectivity of the point map is
*analytic*, not combinatorial: given any jet vector `y` with `y_{i,0} ≠ 0`, realize it by the Taylor
polynomials `p_i` (using the corpus's `iteratedDeriv_polynomial_eval`), set `h_i := 1/p_i`, which is
smooth and nonvanishing near the base point, and note `1/h_i = p_i` has jet vector `y`.  Applying the
displayed identity to `h` turns `R = 0` into `eval y P = 0`; then
`mvPolynomial_eq_zero_of_eval_eq_zero_off_coordinates` gives `P = 0`, contradiction.  The only
remaining lemma is the jet realization `∃ p : Polynomial ℂ, ∀ k ≤ n, (derivative^[k] p).eval 0 = c k`.

### Step 1 continued: jet realization is built, and the assembly is simplified

`JetRealization.lean` (wired, axiom-clean):

- `jetPolynomial n c`, `coeff_jetPolynomial`, `eval_iterate_derivative_zero`
  (`(derivative^[k] p).eval 0 = k! * p.coeff k`, through `factorial_smul_hasseDeriv`);
- **`exists_polynomial_eval_iterate_derivative_eq`** and
  **`exists_smooth_iteratedDeriv_zero_eq`** -- every finite prescription of derivatives at the
  origin is attained by a polynomial, hence by an entire function.

**The monomial-padding assembly recorded above is superseded by a cleaner one.**  Do not do the
per-monomial degree bookkeeping; use algebra-hom uniqueness and a localization instead:

1. Let `S := MvPolynomial (FamilyJetIndex m n) ℂ`, `prod := ∏ i, X (inr (i,0))`, and
   `T := Localization (Submonoid.powers prod)`.  In `T` the element `1/X_{i,0}` is
   `IsLocalization.mk' T (∏ j ≠ i, X (inr (j,0))) prod`.
2. Define `Theta : S →ₐ[ℂ] T` by `aeval` with `inl () ↦ X (inl ())` and
   `inr (i,k) ↦ familyInvJetNum m n i k * (1/X_{i,0})^(k+1)`.
3. For a jet point `x` with `x_{i,0} ≠ 0`, the evaluation `aeval x : S →ₐ[ℂ] ℂ` extends to
   `T →ₐ[ℂ] ℂ` by `IsLocalization.lift`.  The composite with `Theta` agrees with `aeval y`, where
   `y` is the reciprocal jet vector, **by `MvPolynomial.algHom_ext`**: on each variable this is
   exactly `familyJetVec_inv_apply`.  No monomial expansion is needed.
4. Write `Theta P = IsLocalization.mk' T R (prod^N)` (`IsLocalization.mk'_surjective`).  Evaluating
   gives `eval x R = (eval x prod)^N * eval y P`, so `R` vanishes on the domain.
5. `R ≠ 0`: if `R = 0` then `Theta P = 0`, so `eval y P = 0` for every jet point `y` with
   `y_{i,0} ≠ 0` -- realize such a `y` by `p_i := jetPolynomial n (y_i)` and take `g_i := 1/p_i`,
   smooth and nonvanishing near the base point, whose reciprocal jets are exactly `y`
   (`exists_smooth_iteratedDeriv_zero_eq`).  Then
   `mvPolynomial_eq_zero_of_eval_eq_zero_off_coordinates` gives `P = 0`, contradiction.

Every ingredient of 1--5 is now present in the tree except the assembly itself.

### Steps 1--2 are done: the rational change-of-variable layer exists

`FamilyInversionGauge.lean` (wired, axiom-clean) carries out the localization assembly exactly as
designed:

- `zeroJetProduct`, `JetAway m n = Localization.Away (zeroJetProduct m n)`, `invZeroJet` with
  `algebraMap_zeroJet_mul_invZeroJet`;
- `invJetSubst`, **`invJetAlgHom`** -- the rational jet substitution as an algebra homomorphism into
  the localization;
- `isUnit_eval_zeroJetProduct_pow`, `evalJetAway` (`IsLocalization.liftAlgHom`),
  `evalJetAway_algebraMap`, `evalJetAway_invZeroJet`;
- **`evalJetAway_comp_invJetAlgHom`** -- the substitution computes the reciprocal jets, proved by
  `MvPolynomial.algHom_ext`: on each jet variable it is exactly `familyJetVec_inv_apply`;
- `iteratedDeriv_congr_of_eventuallyEq`, `iterate_derivative_comp_sub`,
  **`exists_smooth_iteratedDeriv_eq`** (jet realization at an arbitrary base point);
- **`invJetAlgHom_injective`** -- realize an arbitrary jet point with nonzero zeroth jets by
  `g_i := 1/p_i` for Taylor polynomials `p_i`, whose reciprocal jets are that point, then apply
  `mvPolynomial_eq_zero_of_eval_eq_zero_off_coordinates`;
- **`familyDifferentiallyAlgebraicOn_of_inv`** -- **the inversion gauge**: a differential relation
  among the reciprocals of a smooth nonvanishing family descends to the family.

`FamilyMobiusGauge.lean` (wired, axiom-clean) closes the layer:

- **`familyDifferentiallyAlgebraicOn_of_mobius`** -- for any `a b c d` with `ad - bc ≠ 0` and
  nonvanishing denominator, a differential relation among `(a g + b)/(c g + d)` descends to `g`.
  The proof is the decomposition `translate ∘ invert ∘ scale ∘ translate`, using the corpus's affine
  gauges for the outer steps and the new inversion gauge for the middle one.

This is precisely the layer that
`../../not_new_scientific_knowledge/hardy-cyclicity-maximal-ht-field-blindness.md` lists as missing
("maximal differential independence under rational change of variable"), so that card's blocker is
now removed as well.

What remains for item `(2)` of this card: precomposition with the domain Cayley map (Faa di Bruno
with rational coefficients -- the same clearing pattern, now with all its ingredients present), and
the exponential step `O = exp(sigma)`, which is the Ostrowski/Kolchin-type statement about
exponentials of a differentially independent family and is the genuinely open piece.

### Item `(2)`: the terminal blocker is Ostrowski/Kolchin, not the change of variable

With the Mobius gauge in place the remaining chain for `(2)` was re-derived, and the accounting is
now exact.

*Codomain change of variable* (`sigma = psi(m)`, `psi` Mobius): **done**
(`familyDifferentiallyAlgebraicOn_of_mobius`).

*Domain change of variable* (precomposition with the Cayley map): mechanical and buildable with the
present toolkit.  The composition jets are triangular,
`(F ∘ phi)^{(k)}(w) = sum_{j <= k} F^{(j)}(phi w) * c_{k,j}(w)` with `c_{k,k} = (phi'(w))^k`, and for
a Mobius `phi` the coefficients are rational, so the same localization-plus-realization assembly as
the inversion gauge applies, now localizing in the spectral variable.

*Exponential step* (`O = exp(sigma)`): **this is the terminal blocker, and it is not a change of
variable at all.**  Substituting `O^{(k)} = O * B_k(jets sigma)` expresses the jets of `O` in terms
of the jets of `sigma` **and the extra quantity `O` itself**, which is transcendental over the
differential field generated by `sigma`.  A relation among the `O_i` therefore reads
`sum_alpha exp(<alpha, sigma>) * R_alpha(z, jets sigma) = 0`, and concluding `R_alpha = 0` is exactly
the linear independence of the exponentials `exp(<alpha, sigma>)` over `C(z)<sigma>` -- Ostrowski's
theorem, equivalently the Kolchin differential-transcendence-degree argument the paper invokes when
it says "their generated differential field would have differential transcendence degree below r".

The same obstruction sits on the paper's own log-derivative step: passing from a relation among the
`O_i` to one among the `O_i'/O_i` is the transcendence-degree inequality, not a jet substitution.

So `(2)` reduces to one classical theorem which is absent from mathlib and from this tree:
**linear independence of exponentials of a differentially independent family over the differential
field they generate.**  That is a lane of its own; everything else on this card is proved.

### The algebraic half of the exponential step is built

`ExponentialJetSubstitution.lean` (wired, axiom-clean) supplies the substitution itself:

- `expJetNum` -- the exponential Bell polynomials, `B_0 = 1`,
  `B_{k+1} = jetDerivation B_k + X_1 * B_k`, with `expJetNum_mem_supported`;
- **`iteratedDeriv_exp_eq_expJetNum_mul`** -- `(exp f)^{(k)} = exp f * eval (jetVec f) (expJetNum k)`
  on any open set of smoothness;
- `familyExpJetNum` and **`familyJetVec_exp_apply`** -- the blockwise version in the family jet ring.

Consequently a differential relation among `exp(sigma_1), ..., exp(sigma_r)` takes the exact form

```text
sum over alpha in N^r of  (prod_i exp(sigma_i)^{alpha_i}) * R_alpha(z, jets sigma) = 0 ,
```

with `R_alpha` polynomials in the jets of the exponents, some `R_alpha` nonzero.  What is missing is
only the conclusion `R_alpha = 0`, i.e. linear independence of the exponential monomials over the
differential field generated by the exponents.

**The remaining lane, stated exactly.**  The classical reduction is:

1. minimal-length relation, normalize one coefficient to `1`, differentiate and subtract the
   `<alpha_1, sigma'>`-multiple; minimality forces `c_j'/c_j = -<beta_j, sigma'>` with
   `beta_j != 0` for the surviving terms;
2. so the lane reduces to: **in the differential field generated by a differentially transcendental
   family, no nonzero integer combination `<beta, sigma'>` is a logarithmic derivative**;
3. and that is a differential-polynomial order argument: writing the putative `c = A / B` with `A`,
   `B` coprime differential polynomials, `A' B - B' A = <beta, sigma'> A B` compares a left side of
   jet order `q+1` with a right side of order `q`.

Steps 1 and 3 are ordinary algebra once the differential polynomial ring carries an order function
and coprimality; the corpus already owns free differential fields, `differentialAdjoin`, and the
characteristic-set machinery in the Luroth lane, so this is where the Ostrowski lane should be
built.  Nothing on this card is axiomatized, and every other item is proved.

### The Ostrowski lane is started: base case of the order obstruction

`LogarithmicDerivativeObstruction.lean` (wired, axiom-clean) proves the base case of step 3 of the
lane:

- **`derivative_mul_sub_ne_const_mul`** -- for nonzero polynomials `A`, `B` over a characteristic
  zero field and a nonzero scalar `n`, the logarithmic-derivative equation
  `A' B - B' A = n A B` is impossible, because the left side has degree strictly below
  `deg A + deg B` while the right side attains it.

This is exactly the `q = 0` case of the obstruction: a rational function of a single jet coordinate
whose logarithmic derivative is a nonzero multiple of the first jet.  The general case is the same
statement in `MvPolynomial ℕ F` with the jet derivation, reduced to this one by the max-index
argument: comparing the coefficient of the highest jet `X_{q+1}` in
`D(A) B - D(B) A = n X_1 A B` gives `(∂A/∂X_q) B = (∂B/∂X_q) A`, and with `A`, `B` coprime in the
unique-factorization ring `MvPolynomial ℕ F` this forces `∂A/∂X_q = ∂B/∂X_q = 0`, lowering `q`.

Remaining in the lane, in order: the coprime reduction and the max-index descent (giving the
general `MvPolynomial ℕ F` statement); the Artin shortening of a minimal relation among exponential
monomials; and the assembly with `ExponentialJetSubstitution.lean` into
"`exp` of a differentially independent family is differentially independent", which is the last
missing input of item `(2)`.

### Step 3 of the Ostrowski lane is proved, and by a shorter argument than planned

The max-index/coprimality descent sketched above is not needed.  The total jet derivation preserves
total degree, so the obstruction is one degree count:

- **`totalDegree_jetDerivation_le`** -- `(jetDerivation P).totalDegree ≤ P.totalDegree`, since the
  derivation replaces one jet variable by the next, of the same degree (proved on the monomial
  expansion through `mkDerivation_monomial`);
- **`jetDerivation_logDeriv_equation_impossible`** -- for nonzero `A`, `B` in the jet polynomial ring
  and nonzero `n`, `D A * B - D B * A = n * X_1 * A * B` is impossible: the left side has total
  degree at most `deg A + deg B`, the right side exactly one more.

Together with the univariate base case `derivative_mul_sub_ne_const_mul`, step 3 of the lane is now
unconditional, with no coprimality, no unique factorization and no order function required.

Remaining in the Ostrowski lane: the Artin shortening of a minimal relation among exponential
monomials (step 1), which produces exactly the equation just excluded, and the assembly with
`ExponentialJetSubstitution.lean` into "`exp` of a differentially independent family is
differentially independent".  That closes item `(2)` and, with it, the card.

### Step 1 of the Ostrowski lane is proved: Artin shortening

`ExponentialLinearIndependence.lean` (wired, axiom-clean) proves the shortening step in the abstract
differential-field setting, where it is cleanest:

- `deriv_mul_eq`, `deriv_one_eq_zero` -- the Leibniz rule in mathlib's `Differential` class;
- **`eq_zero_of_sum_expLike_eq_zero`** -- in a differential field, if `E j ≠ 0` and
  `(E j)' = tau j * E j` for each `j`, and no difference `tau j₁ - tau j₂` of distinct exponents is
  a logarithmic derivative (`c' ≠ (tau j₁ - tau j₂) * c` for every nonzero `c`), then
  `∑ c j * E j = 0` forces every `c j = 0`.

The proof is the classical Artin argument, formalized by strong induction on the size of the support
of the coefficient vector: normalize one coefficient to `1`, differentiate, subtract the
`tau j₀`-multiple of the original relation; the normalized coefficient's term drops out, so the new
relation is strictly shorter, and its vanishing coefficients are exactly the excluded
logarithmic-derivative equations.

Both ends of the Ostrowski lane are now in place: the shortening (this file) and the obstruction it
consumes (`LogarithmicDerivativeObstruction.lean`).  What remains is the assembly: grouping a jet
relation among `exp(sigma_i)` by block degree so that it becomes a linear relation in the
exponential monomials with jet-polynomial coefficients (`ExponentialJetSubstitution.lean` already
supplies the substitution), and connecting the analytic family predicate to the differential field
where the shortening lives.

### Two more assembly pieces for the exponential step

`ExponentialJetSubstitution.lean` additionally proves

- **`expJetNum_sub_X_mem_supported`** -- triangularity: `expJetNum (k+1)` is the top jet plus a
  polynomial in the lower jets, so the exponential jet substitution is invertible one jet at a time.

`ExponentialFamilyRealization.lean` (wired, axiom-clean) supplies the analytic surjectivity:

- **`exists_expFamily_realizing_jets`** -- any prescription of finitely many derivatives of
  `exp (sigma i)` at a point, with nonzero value there, is realized by an actual exponential family
  on a neighbourhood: realize the prescription by Taylor polynomials, which are nonvanishing near
  the point, and take `sigma i = log (f i / f i z₀) + log (f i z₀)` on the open set where the ratio
  stays in the slit plane.

This is the same device as in the inversion gauge, with the logarithm replacing the reciprocal, and
it is what will show that the exponential jet substitution kills no nonzero polynomial.

Still to assemble: group a jet relation among `exp(sigma_i)` by block degree (the enlarged jet ring
`FamilyJetIndex m n ⊕ Fin m` with one variable per exponential, via `MvPolynomial.sumAlgEquiv`),
transport the resulting linear relation into a differential field of germs, and apply
`eq_zero_of_sum_expLike_eq_zero` together with `jetDerivation_logDeriv_equation_impossible`.

### The exponential jet substitution is injective

`ExponentialJetGauge.lean` (wired, axiom-clean):

- `expSubst`, **`expSubstHom`** -- the exponential jet substitution into the jet ring of the
  exponents enlarged by one variable per member, `X_{i,k} ↦ U_i * familyExpJetNum m n i k`;
- `expJetPoint`, **`eval_expSubstHom`** -- evaluating the substitution at a point of the enlarged
  ring is evaluating the original polynomial at the corresponding exponential jet point;
- `expJetPoint_eq_familyJetVec` -- for a smooth family that point is literally the jet vector of the
  exponentials;
- **`expSubstHom_injective`** -- the substitution kills nothing, because every jet point with
  nonzero zeroth jets is the jet point of an actual exponential family
  (`exists_expFamily_realizing_jets`), so a polynomial in the kernel vanishes on the whole nonzero
  locus and is therefore zero.

Consequence, which is the grouping the assembly needed: for a nonzero relation `P`, the image
`expSubstHom P` is a nonzero polynomial in the exponential variables `U_i` with coefficients in the
jet ring of the exponents.  Reading it through `MvPolynomial.sumAlgEquiv` gives exactly

```text
sum over alpha of  U^alpha * R_alpha ,   some R_alpha nonzero,
```

which evaluated along the family is `sum_alpha (prod_i exp(sigma_i)^{alpha_i}) * R_alpha(jets sigma)
= 0`.

What is left is the last link: read that identity inside a differential field containing the
functions -- germs at a point of the domain -- so that `eq_zero_of_sum_expLike_eq_zero` applies with
`tau_alpha = <alpha, sigma'>`, its hypothesis being supplied by
`jetDerivation_logDeriv_equation_impossible` through the differential independence of the exponents.

### The obstruction now lives where the shortening consumes it

`LogarithmicDerivativeObstruction.lean` was generalized and lifted to the field of differential
rational functions:

- `shiftDerivation sh` -- the derivation `X i ↦ X (sh i)` for an arbitrary index type and shift,
  with **`totalDegree_shiftDerivation_le`**;
- **`shiftDerivation_logDeriv_equation_impossible`** -- for nonzero `A`, `B` and any multiplier `T`
  of total degree one, `D A * B - D B * A = T * (A * B)` is impossible.  This covers the
  multi-generator case needed for a family: the multiplier is the degree-one form
  `<beta, sigma'>`;
- `jetFractionDerivation`, `jetFractionDerivation_algebraMap` -- the same derivation extended to
  `FractionRing (MvPolynomial ι ℂ)` through the corpus's `fractionRingDerivation`;
- **`jetFraction_logDeriv_impossible`** -- **no nonzero differential rational function has a
  logarithmic derivative of degree one**: `c' = T * c` has no nonzero solution.  The proof clears
  denominators inside the fraction field (`c * b = a`, differentiate, multiply by `b`) and lands on
  the polynomial statement above.

This is exactly the hypothesis of `eq_zero_of_sum_expLike_eq_zero`, with the differential field taken
to be the field of differential rational functions of the exponents -- which is what
`differentialIndependentAdjoinParametrization` identifies the field generated by a differentially
independent palette with.

Remaining for item `(2)`: the germ bridge -- read the analytic identity
`sum_alpha (prod_i exp(sigma_i)^{alpha_i}) * R_alpha(jets sigma) = 0` inside that differential field
(germs at a point of the domain, where the palette is differentially independent), apply the
shortening, and pull the conclusion `R_alpha = 0` back to the polynomial statement, contradicting
`expSubstHom_injective`.

### The obstruction now also covers the spectral variable

The differential relations of this card are polynomials in the spectral variable `z` *and* the jets,
so the derivation to use is not the pure shift: it must send the spectral variable to the constant
one.  `LogarithmicDerivativeObstruction.lean` was generalized accordingly:

- **`jetLikeDerivation f`** -- the derivation with `X i ↦ f i` for any assignment with
  `totalDegree (f i) ≤ 1`, covering both the jet shift `X_{i,k} ↦ X_{i,k+1}` and the spectral
  variable `X_z ↦ 1`;
- **`totalDegree_jetLikeDerivation_le`**, **`jetLikeDerivation_logDeriv_equation_impossible`**, and
  the fraction-field form **`jetFraction_logDeriv_impossible`** -- all now stated for such a
  derivation, with `shiftDerivation` and its two lemmas kept as the special case.

This removes the need for a `C(z)` base field in the assembly: the whole relation lives in
`MvPolynomial (Unit ⊕ Fin m × ℕ) ℂ` with `z` as one more variable, and the obstruction applies
verbatim there.  The remaining link is unchanged: evaluate that ring along the family (injective
exactly because the exponents are differentially independent), pass to germs at a point so that the
nonzero coefficients become invertible, and apply `eq_zero_of_sum_expLike_eq_zero`.

### The Ostrowski lane is closed: `exp` of an independent family is independent

The terminal blocker of item `(2)` is now proved unconditionally in Lean, in five new wired,
axiom-clean modules.

`FamilyJetChainRule.lean` -- the untruncated jet calculus for a family:

- `FullJetIndex m = Unit ⊕ Fin m × ℕ`, `fullJetVec`, `fullJetShift` (spectral variable to one, each
  jet to the next), `fullJetDerivation = jetLikeDerivation (fullJetShift m)` with
  `totalDegree_fullJetDerivation_le`;
- **`deriv_eval_fullJetVec`** -- the chain rule: differentiating the evaluation of a full jet
  polynomial along a smooth family is evaluating its total derivation.  Untruncated, so the
  derivation stays inside the ring and no order bookkeeping is needed.

`FullExponentialJetGauge.lean` -- the substitution and the truncation bridge:

- `fullExpJetNum`, **`fullJetVec_exp_apply`** -- the jets of `exp (sigma i)` are `exp (sigma i)`
  times the blockwise exponential numerator on the jets of the exponents;
- `fullExpSubstHom : MvPolynomial (FullJetIndex m) ℂ →+* MvPolynomial (Fin m) (MvPolynomial
  (FullJetIndex m) ℂ)` -- the substitution lands directly in the ring of polynomials in the
  exponential variables with jet-ring coefficients, so the grouping needs no `sumAlgEquiv`;
- `eval₂_fullExpSubstHom`, `fullJetOrder`, **`fullExpSubstHom_injective`** (realization at a jet
  point with nonzero exponential values, matching only the finitely many jets in the polynomial);
- `jetEmbed`/`jetTrunc` and **`fullJet_independent_of_not_familyDifferentiallyAlgebraicOn`** --
  truncated independence gives untruncated independence, by truncating a full relation at its own
  jet order and testing nonvanishing at a point.

`AnalyticJetRealization.lean` -- the analytic realization:

- `analyticOnNhd_iteratedDeriv`, `analyticOnNhd_eval_fullJetVec`;
- **`jetAnalyticHom`** -- the jet polynomial ring realized inside `Bottcher.analyticSubring U` by
  evaluation along the family, with **`jetAnalyticHom_injective`** (injective exactly for a
  differentially independent family) and **`analyticSubringDeriv_jetAnalyticHom`** (it carries the
  total jet derivation to differentiation).

`JetDifferentialFieldHom.lean` -- the abstract differential-field layer:

- `jetFieldLift` (`IsFractionRing.lift`), **`jetFieldLift_map_deriv`** -- an injective realization
  commuting with the jet derivation extends to the field of differential rational functions and
  still commutes, by the quotient rule;
- `jetSubfield` (its range), `jetSubfield_deriv_mem`, and **`jetSubfield_logDeriv_impossible`** --
  no element of that subfield has a logarithmic derivative of total degree one.  This is exactly the
  hypothesis the Artin shortening consumes.

`ExponentialLinearIndependence.lean` was generalized to what the application needs:

- **`eq_zero_of_sum_expLike_eq_zero`** now runs over an arbitrary finite index type and takes a
  differential subfield `F` for the coefficients -- necessary, because the exponentials themselves
  never satisfy the exclusion hypothesis in a field that contains them;
- `deriv_pow_expLike`, `deriv_prod_pow` -- a product of powers of exponential-like elements is
  exponential-like with the corresponding integer combination of exponents.

`ExponentialFullIndependence.lean` -- the assembly:

- `fullLinForm`, `coeff_fullLinForm`, `fullLinForm_totalDegree_eq_one`, `fullLinForm_ne_zero` --
  the degree-one forms `<alpha, sigma'>`;
- **`exp_fullJet_independent`** -- **on a connected domain, a polynomial in the spectral variable
  and the jets of `exp (sigma i)` vanishing identically is zero whenever the same holds for the
  exponents.**  The proof reads the substituted relation inside the meromorphic differential field
  `Bottcher.meroField U`, where the exponential monomials are exponential-like with exponents
  `<alpha, sigma'>` and the coefficients lie in the differential subfield of rational functions of
  the jets; Artin shortening then forces every coefficient to vanish, and injectivity of the
  exponential substitution forces the original polynomial to vanish;
- **`not_familyDifferentiallyAlgebraicOn_exp`** -- the corpus-facing form: if a finite analytic
  family satisfies no differential relation on a connected domain, neither does the family of its
  exponentials.

All six statements are axiom-clean (`propext, Classical.choice, Quot.sound`).

**Consequence for the card.**  The `N`-th power step of item `(2)` is now free as well: since
`O = exp(sigma)`, one has `O^N = exp(N sigma)`, and `N sigma` is independent whenever `sigma` is
(the corpus's polynomial gauge `familyDifferentiallyAlgebraicOn_of_mul_polynomial` with the constant
polynomial `N`).  So the paper's transcendence-degree argument for powers is replaced by one
application of the exponential gauge.

What remains for item `(2)`: only the **domain** change of variable -- precomposition with the
Cayley map.  Reduced to its generators, translation and scaling are diagonal and trivial, so the
single remaining object is the inversion precomposition `g |-> g (1/.)`, whose Faa di Bruno
coefficients are universal Laurent polynomials in the spectral variable: the same
localization-plus-realization assembly as the inversion gauge, now localizing at the spectral
variable instead of the zeroth jets.

### The domain change of variable is proved: the spectral Mobius gauge

The last mechanical piece of item `(2)` is now formalized, in three further wired, axiom-clean
modules.  All of them work in the untruncated jet ring, where the chain rule is exact.

`SpectralInversionGauge.lean` -- precomposition with `w |-> 1/w`:

- `compInvNumer` -- the universal numerators, defined by applying `-z² d/dz` repeatedly to the
  zeroth jet.  The point is that this derivation *preserves the jet polynomial ring*: no Laurent
  coefficients appear, only the spectral variable ever needs inverting;
- **`deriv_eval_fullJetVec_inv`** and **`iteratedDeriv_comp_inv_eq`** -- the chain rule through the
  inversion and the resulting closed form for the composed jets;
- `SpectralAway`, `compInvAlgHom` -- the substitution into the jet ring with the spectral variable
  inverted, with `evalSpectralAway` and `evalSpectralAway_comp_compInvAlgHom`;
- **`compInvAlgHom_injective`** -- realize a jet prescription at the reciprocal base point and
  precompose it back, so every jet point with nonzero spectral coordinate is a composed jet point;
- **`exists_fullJet_relation_of_comp_inv`**, **`fullJet_independent_comp_inv`** -- clearing the
  spectral denominators carries a relation for the composed family to one for the family, at the
  same sample points.

`SpectralAffineGauge.lean` -- precomposition with `w |-> a w + b`:

- **`iteratedDeriv_comp_affine_eq`** -- the `k`-th composed jet is `a^k` times the `k`-th jet;
- `affAlgHom` and **`affAlgHom_comp_inv`** -- the substitution is an automorphism of the jet ring,
  its inverse being the substitution of the inverse affine map, so no localization is needed;
- **`fullJet_independent_comp_affine`**.

`SpectralMobiusGauge.lean` -- the assembly:

- `fullJetVec_congr`, `isOpen_invDomain`, `isOpen_mobiusPreimage` -- the locality of jets and the
  openness of the intermediate domains;
- **`fullJet_independent_comp_mobius`** -- for `ad - bc != 0`, independence at the Mobius image
  points transports to independence of the precomposed family.  The proof decomposes the Mobius map
  as `translate ∘ invert ∘ scale-and-translate` and chains the two gauges above; the gauges are
  stated with an arbitrary sample map precisely so that they compose without image sets;
- **`fullJet_independent_at_mobius_points`** -- for an *analytic* family on a connected domain,
  independence on the domain already gives independence at the Mobius image points: the inverse
  Mobius map exhibits an open subdomain on which the relation vanishes, and the identity theorem
  (`fullJet_independent_mono`, new in `AnalyticJetRealization.lean`) spreads it;
- **`fullJet_independent_comp_mobius_of_independent`** and
  **`not_familyDifferentiallyAlgebraicOn_comp_mobius`** -- the corpus-facing forms.

With `not_familyDifferentiallyAlgebraicOn_of_fullJet_independent` (new in
`FullExponentialJetGauge.lean`) the truncation bridge is now available in both directions, so these
gauges chain with the corpus's truncated-form gauges.

**State of item `(2)`.**  Every gauge in the chain is now unconditional in Lean:

| step | statement | status |
|---|---|---|
| codomain Mobius `psi` | `familyDifferentiallyAlgebraicOn_of_mobius` | proved (corpus) |
| domain Cayley `phi` | `not_familyDifferentiallyAlgebraicOn_comp_mobius` | **proved here** |
| scaling by `N` | `familyDifferentiallyAlgebraicOn_of_mul_polynomial` | proved (corpus) |
| exponential | `not_familyDifferentiallyAlgebraicOn_exp` | **proved here** |

What is left for `(2)` is no longer a gauge but the instantiation: feeding the translate family
`{m(z+t)}` -- the input hypothesis of the card's setup, supplied by the Herglotz free-family card --
through the four steps, using the corpus's `cayleyToUpper_parabolicAut` (`phi o tau_t = phi + t`) to
identify `O o tau_t` with `exp(psi(m(phi + t)))`.

### Item `(2)` is formalized end to end

`ParabolicOrbitFamilyIndependence.lean` (wired, axiom-clean) assembles the four gauges into the
card's second item:

- `herglotzSigma m = (m - i)/(m + i)`, `outerOrbitMap m = exp (herglotzSigma m o cayleyToUpper)`;
- **`not_familyDifferentiallyAlgebraicOn_parabolicOrbitPow`** -- for an analytic Herglotz `m` on the
  upper half-plane whose translate family `{m(. + t_j)}` satisfies no differential relation, and for
  every `N != 0`, the family `{(O o tau_{t_j})^N}` satisfies no differential relation on the disc;
- **`not_familyDifferentiallyAlgebraicOn_parabolicOrbitPow_cauchy`** -- the same statement for the
  Cauchy transform of any nonzero finite measure on the line, using the corpus's Herglotz positivity
  and analyticity.

The proof is exactly the chain recorded above: codomain Mobius (`familyDifferentiallyAlgebraicOn_of_mobius`),
domain Cayley (`not_familyDifferentiallyAlgebraicOn_comp_mobius`), multiplication by the constant `N`
(`familyDifferentiallyAlgebraicOn_of_mul_polynomial`), exponential
(`not_familyDifferentiallyAlgebraicOn_exp`), with `cayleyToUpper_parabolicAut` identifying
`O o tau_t` with `exp(sigma(cayley + t))`.  The paper's transcendence-degree argument for the `N`-th
powers is not needed: `O^N = exp(N sigma)` makes the power step one more constant gauge.

The only remaining hypothesis is the card's own Setup input -- differential independence of the
half-plane translates of `m` -- which is quoted from the Herglotz free-family card, exactly as in the
paper.

**Card status.**  Items `(2)`--`(5)` and the bounded half of `(1)` are now unconditional in Lean.
The single open item is the second half of `(1)`: `O` is outer, hence cyclic in `H^2`.  Note that
cyclicity does not need Beurling's theorem here: `O` and `O^{-1}` are both bounded, so multiplication
by `O` is a bijection of `H^2`, and density of polynomials gives cyclicity directly.  What is missing
is only a Hardy-space carrier in the corpus (mathlib has none): `H^2` as a Hilbert space with
polynomial density and bounded multiplication by `H^infinity` elements.

### Item `(1)`: the outer map is bounded, invertible and cyclic in `H^2`

The Hardy-space blocker recorded above was stale: the corpus already owned Gutzmer's identity
(`GutzmerIdentity.lean`, `SzegoRadialMean.lean`).  Three new wired, axiom-clean modules finish the
item.

`HardyTwoMultiplier.lean` -- the multiplier bound for an arbitrary bounded analytic factor (the
Szegő-specific bound generalized):

- **`circleMeanSq_mul_le`** -- a pointwise bound on the factor contracts every circle mean;
- **`sum_range_normSq_coeff_mul_le`**, **`tsum_normSq_coeff_mul_le`**, **`summable_normSq_coeff_mul`**
  -- through `r -> 1` and `N -> infinity`, `‖gO‖_{H²} ≤ ‖O‖_infinity ‖g‖_{H²}`, so `H²` is stable
  under bounded analytic multipliers;
- `cauchyPowerSeries_sub`, `truncSeries`, `hasFPowerSeriesOnBall_partialSum`,
  `cauchyPowerSeries_partialSum` -- linearity and truncation of Taylor coefficients.

`HardyTwoCyclicity.lean` -- the cyclicity theorem:

- `hardyApproxPoly`, `eval_hardyApproxPoly` -- the Taylor polynomial of the quotient;
- `coeff_sub_partialSum`, `tsum_normSq_coeff_sub_partialSum`,
  **`tendsto_tsum_normSq_coeff_sub_partialSum`** -- the truncation error is exactly the discarded
  tail of the coefficient sum, so it tends to zero;
- **`tendsto_tsum_normSq_coeff_sub_polynomial_mul`** -- **if `O` is nonvanishing on the disc and both
  `O` and `1/O` are bounded there, the polynomial multiples of `O` approximate every `H²` function**:
  divide by `O`, truncate, multiply back, and let the multiplier bound carry the error.

`ParabolicOuterMapCyclicity.lean` -- the card's instance:

- `norm_herglotzSigma_lt_one`, `analyticOnNhd_outerOrbitMap`, `outerOrbitMap_ne_zero`;
- **`norm_outerOrbitMap_le`** and **`norm_inv_outerOrbitMap_le`** -- equation `(9)`:
  `exp(-1) ≤ ‖O‖ ≤ exp(1)` on the disc, i.e. `O, O^{-1} ∈ H^infinity`;
- **`tendsto_tsum_normSq_coeff_sub_polynomial_mul_outerOrbitMap`** -- **`O` is cyclic in `H²`**.

**On "outer".**  The paper deduces cyclicity from outerness via Beurling's theorem.  The Lean proof
does not need that route and does not formalize the predicate "outer": for an *invertible* bounded
analytic function, multiplication by `O` is a homeomorphism of `H²`, and cyclicity follows from
density of polynomials alone.  Outerness as a named property would require the Poisson
representation of bounded harmonic functions, which nothing else on this card uses.

**Card status.**  Every numbered item of the theorem is now unconditional in Lean:
`(1)` boundedness and cyclicity, `(2)` differential independence of the orbit powers (given the
Setup's translate-independence input), `(3)` locally uniform convergence, `(4)` the circle closure,
`(5)` non-universality and the bounded return set.
