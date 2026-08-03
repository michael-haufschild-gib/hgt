# Infinite Bohr--HT boundary of a maximal-HT outer orbit

- **ID:** `infinite-bohr-ht-boundary-maximal-ht-outer-orbit`
- **Stage:** 2-fully-proven / needs independent audit
- **Type:** THEOREM (paper) — `[PROVED HERE] [NOVELTY UNVERIFIED]`
- **Lane:** general hypertranscendence; infinite translation hulls; limit distributions
- **Statement:** An invertible outer function on the upper half-plane can have a maximally
  differentially free real-translation family at every algebraic power while the boundary of every
  power-orbit closure is the countably infinite torus, every boundary function is HT, and the
  orbit's limiting distribution is Haar measure on that HT boundary.

## Goal

Finite DA quasiperiodic perturbations give finite-dimensional toral boundaries by a routine
differential-filter argument.  That mechanism cannot produce an infinite Bohr torus: no nonzero
finite-order differential operator annihilates infinitely many rationally independent frequencies.

The present theorem crosses that boundary.  The added almost-periodic carrier is itself HT by
Ostrowski's independent-exponent theorem.  Maximal differential independence of the perturbed
translation orbit is recovered by re-running the positive-Cauchy-mass transversality argument, not
by deleting the perturbation algebraically.

## Infinite-frequency carrier

Let `H={z in C:Im z>0}`.  Choose positive frequencies

`omega_1<omega_2<... -> infinity`

which are linearly independent over `Q`.  Choose nonzero coefficients `a_j` so rapidly decreasing
that

`sum_j |a_j| exp(R omega_j)<infinity`                         (1)

for every `R>0`.  Such data exist explicitly: take `omega_j=sqrt(p_j)` for the increasing primes
`p_j` (these squarefree radicals are `Q`-linearly independent) and `a_j=exp(-p_j)`.
Put

`A(z)=sum_(j>=1) a_j exp(i omega_j z)`.                       (2)

Condition (1) makes `A` entire, while

`M=sum_j |a_j|<infinity`

gives `|A(z)|<=M` on `H`.

For `lambda=(lambda_j) in T^N`, define

`A_lambda(z)=sum_(j>=1) a_j lambda_j exp(i omega_j z)`.        (3)

The series in (3) converges normally on `C`, uniformly in `lambda` on every compact set.

## Ostrowski boundary theorem `[SEARCH]`

Every `A_lambda` is hypertranscendental over `C(z)`.

This is the independent-exponent case of Ostrowski's 1920 theorem on Dirichlet series and algebraic
difference-differential equations.  All coefficients `a_j lambda_j` are nonzero, and the exponent
set contains infinitely many `Q`-linearly independent elements.  Ostrowski proves that such a
convergent generalized Dirichlet series satisfies no algebraic differential equation, indeed no
algebraic difference-differential equation.

The imported result is classical and is not claimed as new.  A modern English translation is
Hansen--Stone--Wolfson, arXiv `2211.02088`, especially the introduction and Theorems 1 and 6.

## Infinite Bohr hull `[SEARCH]`

Let

`theta(t)=(exp(i omega_j t))_(j>=1) in T^N`.

Every finite coordinate projection of this real flow is dense by Kronecker's theorem.  Therefore
`theta(R)` is dense in the product torus `T^N`.

The map

`alpha:T^N -> Hol(C)`, `lambda |-> A_lambda`,                 (4)

is continuous for the product topology and compact-open convergence.  Indeed, the tail is uniformly
small by (1), while only finitely many phases remain in the head.  It is injective by uniqueness of
Bohr--Fourier coefficients.  Hence it is a homeomorphism from compact `T^N` onto the translation
hull of `A`.

These are classical almost-periodic facts.

## Perturbed positive-Cauchy family

Use the positive atomic Herglotz family from
`herglotz-full-translation-ht-krein-index-orthogonality.md`:

`m_u(z)=sum_(k>=0) 2^(-k-1) exp(u_k)/(k+1-z)`,

with `u in ell^infinity(R)`.  Put

`chi(w)=exp((w-i)/(w+i))`,

`S_u(z)=chi(m_u(z))`.                                        (5)

Since `m_u(H) subset H`, one has

`exp(-1)<|S_u(z)|<exp(1)`                                    (6)

and `S_u,S_u^(-1) in H^infinity(H)`.  Every `S_u` is outer.  The finite-mass Stieltjes estimate gives

`S_u(z+t)->c=exp(-1)`                                        (7)

locally uniformly on `H` as `t->+infinity` and `t->-infinity`.

Choose

`0<epsilon<c/M`

and define

`G_u(z)=S_u(z)+epsilon A(z)`.                                (8)

Then `G_u,G_u^(-1) in H^infinity(H)` by (6), and `G_u` is outer.

## Residual maximal real-translation HT `[PROVED HERE]`

There is a comeager subset `U_infty subset ell^infinity(R)` such that, for every `u in U_infty`,
the full real-translation family

`{G_u(z+t):t in R}`                                          (9)

is differentially algebraically independent over `C(z)`.

### Proof

The proof is the real-shift version of the full-complex Herglotz transversality theorem; the fixed
summand `epsilon A` changes none of its submersion or codimension inputs.  The details are recorded
to make that assertion checkable.

Fix a finite tuple of distinct real shifts, a differential jet depth, and a finite support of
distinct expanded differential monomials.  Choose finitely many evaluation points in `H`, with all
their shifted packets disjoint and separated from their conjugates.  The real Cauchy-jet spanning
lemma says that varying finitely many positive masses of `m_u` realizes arbitrary complex jets of
the shifted `m_u` at those points.

At one point, the jet map

`j^r m |-> j^r (chi o m)`

is triangular.  Its diagonal entry at every derivative order is

`chi'(m)=chi(m) 2i/(m+i)^2`,

which never vanishes for `m in H`.  Hence the same finite mass coordinates realize arbitrary jets
of the shifted `S_u`.  Addition of the fixed function `epsilon A` has identity derivative on jet
space, so the universal parameter--shift evaluation map for `G_u` is still a real submersion.

For `R` supported monomials evaluated on `N` independent rows, the rank-defect incidence locus has

`codim_C >= N-q-R+1`,

where `q` is the largest polynomial degree in `z` occurring in the support.  Take

`N>m+q+R-1`,

where `m` is the number of real shift parameters.  Every Whitney stratum then has real codimension
larger than the shift-parameter space.  Parametric transversality makes the bad preimage empty for
all shifts in one compact patch.

Finite mass perturbations may be arbitrarily small in `ell^infinity`; compact shift-patch avoidance
is open.  Exhaust every real distinct-shift configuration space by countably many compact patches
and intersect over the countable collection of jet depths and monomial supports.  Baire's theorem
gives the comeager set `U_infty`.  Clearing rational denominators shows that avoidance of every
support is exactly differential algebraic independence over `C(z)`. `QED`

Fix henceforth `u in U_infty`, write `G=G_u`, and set `G_t(z)=G(z+t)`.

## Infinite-HT-boundary theorem at every power `[PROVED HERE]`

For `n>=1` and `lambda in T^N`, put

`b_lambda(z)=c+epsilon A_lambda(z)`,                           (10)

`O_n={G_t^n:t in R}`,

`B_n={b_lambda^n:lambda in T^N}`.                             (11)

Then:

1. every finite set of distinct functions in `O_n` is differentially algebraically independent;
2. every function in `B_n` is hypertranscendental over `C(z)`;
3. `B_n` is homeomorphic to the countably infinite torus `T^N`;
4. the compact-open closure in `Hol(H)` is the disjoint union

   `closure(O_n)=O_n disjoint_union B_n`;                     (12)

5. `B_n` is exactly the cluster set as `|t|->infinity`.

### Proof: all-power independence and boundary HT

For distinct `t_1,...,t_r`, the functions `G_(t_j)` are differentially algebraically independent.
Each is algebraic over its `n`-th power, so adjoining the roots cannot increase differential
transcendence degree.  The power tuple is therefore differentially algebraically independent.

Every `b_lambda` is HT because `A_lambda` is HT and

`A_lambda=(b_lambda-c)/epsilon`.

If `b_lambda^n` were DA, then `b_lambda`, being algebraic over its power, would be DA.  Thus every
boundary power is HT.

### Proof: infinite-torus topology

The map

`beta_n:T^N -> Hol(H)`, `lambda |-> b_lambda^n`,

is continuous.  The bound

`|b_lambda(z)|>=c-epsilon M>0`                                (13)

holds uniformly.  If `b_lambda^n=b_mu^n`, the analytic quotient `b_lambda/b_mu` takes values among
the `n`-th roots of unity and is therefore constant.  As `Im z->infinity`, both functions tend to
`c`, so the quotient is `1`.  Fourier uniqueness gives `lambda=mu`.  Thus `beta_n` is a continuous
injection from compact `T^N` into Hausdorff `Hol(H)`, hence a homeomorphism onto `B_n`.

### Proof: closure

Equation (8) gives

`G_t(z)=S_u(z+t)+epsilon A_(theta(t))(z)`.                     (14)

If `|t_k|->infinity` and `theta(t_k)->lambda` in the product torus, then (7), the uniform tail
bound, and (14) imply

`G_(t_k)^n -> b_lambda^n`

locally uniformly.  Conversely, compactness of `T^N` gives a phase-convergent subsequence of every
unbounded parameter sequence.  Every `lambda` occurs along an unbounded positive sequence because
the tail of a dense Kronecker orbit is still dense.  Bounded parameter sequences have orbit-point
subsequences.  These alternatives prove the set equality in (12) and compactness of the closure.

It remains to prove disjointness.  Suppose `G_t^n=b_lambda^n`.  By (13) and the same quotient
argument, using the common limit `c` as `Im z->infinity`, one has `G_t=b_lambda`.  Hence

`S_u(z+t)-c=epsilon (A_lambda(z)-A_(theta(t))(z))`.             (15)

On every horizontal line, the right side is uniformly almost periodic in `Re z`.  The left side
tends to zero as `Re z->+infinity` and as `Re z->-infinity` by (7).  A uniformly almost-periodic
function which tends to zero at one end is identically zero: arbitrarily large almost periods move
any fixed value into the vanishing tail.  Thus the right side of (15) is zero.  Injectivity of
`alpha` gives `lambda=theta(t)`, and (15) then makes `S_u` constant, contradicting its
hypertranscendence.  Therefore the union is disjoint. `QED`

## Exact Haar limiting distribution `[PROVED HERE]`

Let `m_T` be normalized Lebesgue measure on `[0,T]`, pushed forward by

`t |-> G_t^n`

to the compact space `closure(O_n)`.  Then, as `T->infinity`,

`m_T -> (beta_n)_*(Haar_(T^N))`                               (16)

weakly.

### Proof

The dense one-parameter rotation `theta(t)` on the compact abelian group `T^N` is uniquely
ergodic; finite-coordinate characters and Stone--Weierstrass reduce this to ordinary
Kronecker--Weyl.  Hence time averages of every continuous function of `b_(theta(t))^n` converge to
its Haar average.

By (7), the compact-open distance between `G_t^n` and `b_(theta(t))^n` tends to zero.  Every
continuous test function on the compact closure is uniformly continuous, so replacing one path by
the other changes its Cesaro average by a quantity tending to zero.  This proves (16). `QED`

## Law extracted

**Infinite Bohr-boundary orthogonality law.**  Maximal differential freedom of every finite
translation packet, even at every algebraic power and inside the invertible outer cone, is
compatible with an infinite-dimensional compact translation boundary all of whose points remain
HT.  The boundary can carry an exact Haar limiting distribution determined by an arbitrary
countable `Q`-independent positive frequency sequence.

Thus translation HT determines neither:

- finite versus infinite Bohr dimension;
- the frequency embedding of the infinite torus;
- the compact-open boundary of the orbit;
- the differential type of its limit functions;
- the limiting Haar law seen by time averages.

## Exact RH-route consequence

The theorem rules out using maximal translation HT alone to reconstruct the infinite phase system
which drives zeta value-distribution and correlation arguments.

1. **Voronin--Bagchi:** maximal HT does not select the distinguished zeta limit law or strong
   recurrence.  It coexists with infinitely many non-zeta frequency embeddings and their Haar laws.
2. **Montgomery--Odlyzko / GUE:** an infinite independent frequency torus and Haar equidistribution
   still do not identify the prime-log embedding, explicit-formula weights, or sine-kernel
   correlations.  Those are arithmetic markings beyond HT.
3. **Bohr--Courant:** even the complete compact translation hull and its limiting measure are not
   consequences of the abstract HT matroid.

This does not refute the full classical theorems or conjectures.  It excludes implementations which
replace their Euler frequencies, explicit formula, or pointed vertical zeta orbit by maximal HT
alone.

## Attacks and boundaries

1. **Ostrowski is imported, not rediscovered.**  Infinite independent exponent support forcing HT is
   classical.
2. **The perturbation is genuinely HT.**  Unlike the finite-torus bridge, no DA extension or finite
   differential filter protects independence.  The positive-mass transversality proof must be
   rerun after the perturbation.
3. **Boundary functions are individually HT, not proved jointly free.**  No claim is made that
   arbitrary finite tuples of distinct boundary phases are differentially independent.
4. **The phase group is countably generated and free.**  General compact groups, dependent spectra,
   and non-Haar invariant measures are not constructed.
5. **No Euler normalization is preserved.**  The theorem is an HT-information no-go, not a
   deformation of zeta retaining its Dirichlet coefficients.

## Parent-theory and preliminary novelty audit

The three principal parents are sharply separated:

1. Ostrowski (1920): independent Dirichlet exponents force differential transcendence, even against
   algebraic difference-differential equations.
2. Bohr--Kronecker theory: the translation hull of an absolutely convergent series with countably
   independent frequencies is `T^N`, with Haar time distribution.
3. Positive-Cauchy jet transversality: a residual mass family has maximally free translation jets.

The new candidate content is their simultaneous constrained realization after a fixed **HT**
infinite-frequency perturbation: invertible outer boundedness, residual all-translate differential
independence, all-power persistence, exact disjoint closure, an all-HT infinite-torus boundary, and
the Haar limiting law.

Preliminary searches across Dirichlet-series ADEs, holomorphic almost-periodic hulls, parabolic
composition dynamics, orbital limit sets, and differential independence of translates did not find
this combined theorem.  It is not a routine DA perturbation: the perturbation lies beyond every
finite ADE by Ostrowski, and the independence proof uses the surviving infinite-dimensional
positive-mass submersion.

The proof and significance gates pass.  Parent and literature priority remain provisional pending
specialist review in differential algebra, almost-periodic analysis, and linear dynamics.  The card
therefore remains `[NOVELTY UNVERIFIED]`, not candidate-new.

Primary adjacent sources:

- A. Ostrowski, *Uber Dirichletsche Reihen und algebraische Differentialgleichungen*, Math. Z. 8
  (1920), 241--298; English translation arXiv `2211.02088`.
- H. Bohr, *Almost Periodic Functions*.
- J. Bès and C. Foster, *Dynamics of composition operators on spaces of holomorphic functions on
  plane domains*, JMAA 548 (2025), article 129393.
- R. E. Edwards, *On the independence of translates*, Ann. Inst. Fourier 3 (1951), 31--72.

## Lean status

No complete Lean claim is made.  The tree contains finite Kronecker--Weyl character lemmas,
constant-coefficient differential operators, and an abstract differential-independence predicate.
It does not formalize Ostrowski's generalized Dirichlet-series theorem, infinite product-torus
equidistribution, the compact-open holomorphic hull, positive-mass Baire transversality, or Hardy
outer factorization as one theorem.  Partial formalization would not justify Stage 3.

## Gates

- [x] 0 -> 1: infinite-frequency HT perturbation and surviving submersion isolated
- [x] 1 -> 2: complete unconditional paper proof
- [ ] independent audit of the modified transversality and disjointness arguments
- [ ] specialist priority audit across all three parent fields
- [ ] 2 -> 3: complete unconditional theorem formalized in Lean
- [ ] 3 -> 4: publication-ready preprint and independent novelty review

## Cross-references

- `analytic-background-saturation-maximal-ht.md`: the general affine-background saturation and
  asymptotic measure-transfer bridge; the present card supplies the non-DA infinite-frequency
  background and proves its exact disjoint all-HT boundary.
- `toral-da-boundary-maximal-ht-outer-orbit.md`: finite DA-torus bridge, now downgraded.
- `maximal-ht-parabolic-orbit-collapse.md`: one-point boundary input.
- `herglotz-full-translation-ht-krein-index-orthogonality.md`: positive-mass transversality engine.
- `transcendence-implies-gue.md` in `5-failed`: the false implication from transcendence to full
  GUE statistics.

## Log

- 2026-07-11 -- Ostrowski audit killed the independent-spectrum novelty claim but supplied the HT
  boundary input for the stronger infinite-torus construction.
- 2026-07-11 -- Re-ran the positive-Cauchy transversality argument after the fixed HT perturbation;
  proved outer invertibility, all-power maximal independence, exact disjoint infinite-torus closure,
  HT of every boundary state, and Haar limiting distribution.

## Lean progress (formalization started)

The Bohr-hull side of the card now has its first two unconditional bricks, both axiom-clean
(`propext`, `Classical.choice`, `Quot.sound`) and wired into the `HTGeometry` umbrella.

`InfiniteTorusKroneckerDensity.lean`:

- `RationallyIndependentSequence`, the finite-subfamily form of rational independence for an
  arbitrary index set;
- `clockPhasePoint`, the phase flow of an arbitrary frequency family into `UnitAddTorus ι`
  (mathlib's `ι → UnitAddCircle`, which needs no finiteness of `ι`);
- **`dense_range_clockPhasePoint`** -- the infinite Kronecker theorem: a rationally independent
  frequency family has dense orbit in the *full* product torus.  A basic open set of a product
  constrains finitely many coordinates, so the statement reduces to the corpus's finite Kronecker
  density `dense_range_finiteClockPhasePoint` on that finite coordinate set.

`InfiniteTorusCharacter.lean`:

- `torusHaar`, the Haar probability measure of the compact product torus (`Measure.addHaarMeasure ⊤`
  on `UnitAddTorus ι` for countable `ι`), with its probability and invariance instances;
- `torusCharacter`, the character of a finitely supported integer vector, and its multiplicativity;
- `characterDetuning` and **`torusCharacter_clockPhasePoint`** -- along the phase flow a character is
  the single phase `exp(i t ⟨n, ω⟩)`;
- `exists_torusCharacter_ne_one` and **`integral_torusCharacter`** -- character orthogonality:
  the Haar mean of a character is one for the trivial character and zero otherwise, by the
  translation argument.

These are exactly the two inputs the card's Bohr-hull and Haar-limit steps rest on, in the infinite
setting where mathlib's finite multi-torus Fourier theory does not apply.

`InfiniteTorusEquidistribution.lean` adds the time-average side:

- `flowAverage`, the symmetric time average of a continuous torus function along the phase flow;
- `flowAverage_torusCharacter` -- on a character it is exactly the corpus's elementary phase average
  `symmetricPhaseAverage` of the character's detuning;
- **`characterDetuning_eq_zero_iff`** -- under rational independence a character is resonant only if
  it is trivial;
- **`tendsto_flowAverage_torusCharacter`** -- hence the time average of every character converges to
  its Haar mean.  This is the character half of unique ergodicity.

**Unique ergodicity is now proved.**  `InfiniteTorusCharacter.lean` gained the algebra layer:

- `torusCharacter_apply_of_subset`, `torusCharacter_add_index`, `torusCharacter_neg_index` -- the
  characters form a group under index addition, with conjugation given by negation (the common
  refinement of the two supports handles the cancellation);
- `torusCharacterSubalgebra` and `torusCharacterSubalgebra_coe` -- the generated star subalgebra is
  exactly the linear span of the characters;
- `torusCharacterSubalgebra_separatesPoints` -- coordinate characters separate points, because
  `AddCircle.injective_toCircle` makes `fourier 1` injective;
- **`torusCharacterSubalgebra_closure_eq_top`**, **`span_torusCharacter_closure_eq_top`** --
  Stone--Weierstrass on the compact product torus.

`InfiniteTorusEquidistribution.lean` gained the analytic layer: `flowAverage_add`,
`flowAverage_smul`, `flowAverage_sub`, `norm_flowAverage_le` (the time average is linear and bounded
by the supremum norm), `HasHaarTimeAverage`, its closure under the vector-space operations,
`hasHaarTimeAverage_of_mem_span`, and finally

- **`hasHaarTimeAverage_of_continuous`** -- for a rationally independent frequency family the
  symmetric time average of *every* continuous function along the phase flow converges to its Haar
  mean on the product torus.

That is equation (16) of this card in its abstract form: unique ergodicity of an infinite Kronecker
flow, which mathlib has only for finite tori.

### Remaining Lean work on this card
2. **The holomorphic hull.**  The Bohr--Fourier half is done.
   `BohrExponentialSeriesCoefficient.lean` (wired, axiom-clean) proves, for an absolutely convergent
   exponential series `∑ a_i e^(i ω_i t)` -- the card's carrier `A_λ` restricted to the real line:

   - `summable_expSeries`, `continuous_expSeriesCarrier`, `norm_expSeriesCarrier_sub_partial_le`,
     `exists_finset_tsum_compl_lt` -- the series is a uniform limit of its partial sums;
   - **`isBohrAlmostPeriodic_expSeriesCarrier`** -- hence it is Bohr almost periodic, by the corpus's
     uniform-approximation criterion;
   - **`bohrCoefficient_expSeriesCarrier`** -- with pairwise distinct frequencies the Bohr
     coefficient at `ω_k` is exactly `a_k`, because each Bohr coefficient is `1`-Lipschitz for the
     uniform distance and the coefficients of the partial sums are their own;
   - **`expSeriesCarrier_phase_injective`** -- Bohr--Fourier uniqueness of the phases: two phase
     assignments of the same nonvanishing amplitude family which produce the same series are equal.
     This is exactly the injectivity of the card's hull map `α : T^N → Hol(C)` at the level of
     boundary values.

   The holomorphic side is now done as well.  `ComplexExponentialSeriesCarrier.lean` (wired,
   axiom-clean) proves for the entire carrier `A_λ(z) = ∑ a_i e^(i ω_i z)`:

   - `cexpChar`, `norm_cexpChar` (`‖e^(iωz)‖ = e^(-ω Im z)`), `ExpSeriesNormallySummable` -- the
     card's condition (1);
   - `norm_term_le_of_mem_closedBall`, **`tendstoUniformlyOn_cexpSeries`**,
     **`tendstoLocallyUniformly_cexpSeries`** -- normal convergence on every closed ball, hence on
     every compact set;
   - **`differentiable_cexpSeriesCarrier`** -- the carrier is entire, by the Weierstrass
     locally-uniform-limit theorem;
   - `cexpSeriesCarrier_ofReal` -- on the real line it is the almost periodic carrier of the same
     data, so the Bohr coefficients above are its boundary coefficients;
   - **`cexpSeriesCarrier_phase_injective`** -- consequently the holomorphic hull map is injective:
     two phase assignments of the same nonvanishing amplitude family whose entire carriers agree are
     equal.

   The estimate that drives the hull topology is also proved:

   - `expSeriesNormallySummable_phase` -- damping by any bounded phase family preserves the
     normal-summability hypothesis, so every `A_λ` is entire with the same weights;
   - **`norm_cexpSeriesCarrier_phase_sub_partial_le`** -- on every closed ball the distance from
     `A_λ` to its partial sum is at most the tail `∑_(i ∉ S) ‖a_i‖ e^(R|ω_i|)`, *independently of the
     phase family*.

   The two-phase form of the estimate is proved as well:

   - `norm_cexpChar_le_of_mem_closedBall` and
     **`norm_cexpSeriesCarrier_phase_sub_phase_le`** -- on every closed ball two phase-modulated
     carriers differ by at most the weighted head distance over a finite frequency set plus twice
     the tail of the remaining weights.  The tail does not see the phases and the head depends on
     finitely many phase coordinates, which is exactly the `ε/3` input for compact-open continuity.

   **Step 2 is now closed.**  `BohrHullContinuity.lean` (wired, axiom-clean) assembles it:

   - `exists_finset_tsum_compl_lt_real`, `summable_norm_of_expSeriesNormallySummable` -- the tail
     selection and the plain summability of the amplitudes;
   - `bohrHullMap` -- the hull map `T^N → C(C, C)`, `λ ↦ A_λ`, valued in continuous (indeed entire)
     functions;
   - **`continuous_bohrHullMap`** -- continuity for the topology of uniform convergence on compacts:
     on a compact set the phase-uniform tail gives `ε/2`, and the head is a continuous function of
     finitely many phase coordinates vanishing at the base point;
   - **`injective_bohrHullMap`** -- injectivity from Bohr--Fourier uniqueness;
   - **`isClosedEmbedding_bohrHullMap`** -- hence the hull map is a closed embedding: `T^N` is
     compact and `C(C, C)` is Hausdorff.  The hull is a homeomorphic copy of the infinite phase
     torus, which is claim (3) of the boundary theorem.

2'. **Decay of the carrier high in the upper half plane.**  `ComplexExponentialSeriesCarrier.lean`
   also proves `summable_norm_weight`, `norm_cexpSeriesCarrier_le_tsum` and

   - **`exists_im_bound_norm_cexpSeriesCarrier_le`** -- for strictly positive frequencies and
     summable amplitudes the carrier is uniformly small above a height: for every `ε` there is a
     `Y` with `‖A_λ(z)‖ ≤ ε` whenever `Im z ≥ Y`.  The tail is uniform in the height because each
     weight is at most one there, and the remaining head is a finite sum of decaying exponentials.

   This is the input for the card's `b_λ → c` limit as `Im z → ∞`, which drives both the power
   injectivity of `B_n` and the disjointness argument.

3'. **Disjointness is now available in the form the card uses.**
   **`expSeriesCarrier_phase_eq_of_tendsto_zero`** (in `BohrExponentialSeriesCoefficient.lean`):
   if two phase-modulated carriers of the same nonvanishing amplitude family differ by a function
   decaying at `+∞`, then the phases coincide.  The difference is Bohr almost periodic, so the
   corpus's vanishing lemma forces it to be identically zero, and Bohr--Fourier uniqueness then
   identifies the phases.  This is exactly step (15) of the card's disjointness proof, with the
   Stieltjes decay (7) as its hypothesis.
3. **Closure and disjointness** of `O_n` and `B_n`, which needs the Stieltjes limit (7) and the
   almost-periodicity argument of (15).
4. **Imported inputs.**  Ostrowski's hypertranscendence theorem for generalized Dirichlet series and
   the positive-mass Baire transversality engine (the latter already exists in the corpus as the
   Herglotz card's machinery) enter as explicit hypotheses, exactly as the card's proof uses them.

## Powers do not merge boundary states

`BohrPowerBoundary.lean` (wired, axiom-clean) formalizes the card's power argument, the step that
makes claim (3) hold *at every power* rather than only at `n = 1`:

- `finite_setOf_pow_eq_one` and **`constant_of_pow_eq_one`** -- a continuous function whose `n`-th
  power is one takes values in a finite set of roots of unity, hence is constant on a preconnected
  space (the finite subtype is discrete, so `IsPreconnected.constant` applies);
- **`eq_of_pow_eq_of_tendsto_ratio_one`** -- if two nonvanishing continuous functions have equal
  `n`-th powers and their ratio tends to one along any nontrivial filter, they are equal.  This is
  the card's "quotient is a constant root of unity, and the common limit makes it `1`";
- **`tendsto_cexpSeriesCarrier_vertical`** -- the carrier decays along the vertical axis, the
  concrete instance of the uniform half-plane decay;
- **`cexpSeriesCarrier_phase_injective_pow`** -- consequently, for a nonzero constant term, equal
  `n`-th powers of two shifted carriers force equal phases.  Composed with the hull embedding this
  is exactly `B_n ≅ T^N` for every `n >= 1`.

`InfiniteTorusKroneckerDensity.lean` also gained the time-translation structure the closure argument
uses: `clockPhasePoint_add` (the flow is additive in time) and **`dense_forwardOrbit_clockPhasePoint`**
-- density of a *forward* orbit reduces to its finite coordinate projections, exactly as two-sided
density did.  This isolates the one classical input still needed for the card's remark that "the tail
of a dense Kronecker orbit is still dense": forward Kronecker density on a *finite* torus, which the
corpus currently has only in two-sided form.

Remaining on this card:

1. the closure equality `closure(O_n) = O_n ⊔ B_n`.  Its inputs are now all proved:
   `InfiniteTorusForwardDensity.lean` (wired, axiom-clean) supplies one-sided unique ergodicity and
   forward density --

   - `forwardFlowAverage`, its linearity and sup-norm bound, and
     `tendsto_forwardFlowAverage_torusCharacter`: on a character the one-sided average is the
     corpus's `windowAverage` of a phase, whose limit is `bohrMean_expChar`;
   - **`hasHaarForwardAverage_of_continuous`** -- one-sided unique ergodicity of the flow;
   - `integral_pos_of_torusHaar`, **`dense_forwardOrbit_zero`** and **`dense_forwardOrbit`** -- a
     continuous nonnegative function vanishing on the closure of a forward orbit would have zero
     Haar mean, contradicting positivity of Haar on nonempty open sets; and every *tail* of the
     orbit is dense because the flow is additive, so a tail is a translate of the forward orbit.

   This is exactly the card's remark that "every `λ` occurs along an unbounded positive sequence
   because the tail of a dense Kronecker orbit is still dense".

   `BohrOrbitClosure.lean` (wired, axiom-clean) then assembles the inclusion `B ⊆ closure O`:

   - **`mem_closure_range_of_dense_tails`** -- if a parametrised family is continuous, the flow has
     dense forward tails, and the orbit is asymptotic to the family along the flow, then every value
     of the family lies in the closure of the orbit.  One waits until the orbit is uniformly close to
     the family and then steers the remaining tail near the prescribed parameter;
   - **`bohrHullMap_mem_closure_range_of_asymptotic`** -- the same statement for the phase hull of an
     exponential carrier, with the asymptotic comparison as an explicit hypothesis: that hypothesis
     is precisely the Stieltjes decay (7) on the `S_u` side, which the card imports from the Herglotz
     engine.

   The reverse inclusion is half done in the same module:

   - `mem_range_of_mem_closure_image_compact` -- the image of a compact time window is closed, so a
     limit of orbit points coming from bounded times is itself an orbit point;
   - **`closure_range_subset_union_clusterAtInfinity`** -- hence
     `closure O ⊆ O ∪ ⋂_M closure (G '' {|t| > M})`: a limit of orbit points is either an orbit point
     or a cluster point of the orbit at arbitrarily large times.

   That identification is now proved too:

   - **`clusterAtInfinity_subset_range`** -- on a compact parameter space, every cluster point at
     infinity of an asymptotic orbit is a value of the family.  An ultrafilter refining
     `comap G (𝓝 y) ⊓ cocompact ℝ` converges on the compact parameter space, and
     `Tendsto.congr_uniformity` transports its limit through the asymptotic comparison;
   - **`closure_range_subset_union_range`** and **`closure_range_eq_union_range`** -- hence
     `closure O = O ∪ B` for an orbit asymptotic to a continuous family along a flow with dense
     forward tails.  This is equation (12) of the card, with disjointness supplied separately by
     `expSeriesCarrier_phase_eq_of_tendsto_zero`.

   The concrete statement is assembled too: `circlePhaseFlow` reads the phase flow in the circle
   group of each coordinate, `unitTorusHomeomorphCircles` identifies the two models of the torus,
   `dense_forwardOrbit_circlePhaseFlow` transports forward density through that homeomorphism, and

   - **`bohrHull_closure_range_eq`** -- for an exponential carrier with summable weights and
     rationally independent frequencies, an orbit asymptotic to the phase hull along the phase flow
     has closure exactly the orbit together with the whole hull.

   The only input left is the Stieltjes comparison `dist(G_t, hull(phase t)) → 0` along the cocompact
   filter, which the card imports from the Herglotz engine and which enters this theorem as its one
   explicit hypothesis;
2. all-power differential independence -- claim (1) -- which needs a *power gauge* for the corpus's
   `FamilyDifferentiallyAlgebraicOn`: a relation among `N`-th powers pulls back to a relation among
   the functions, by injectivity of the jet substitution `y_k ↦ (y^N)^(k)`.  The existing gauge
   library (`FamilyPolynomialGauge`, `FamilyInversionGauge`, `FamilyMobiusGauge`) is the pattern to
   follow;
3. the two imported inputs: Ostrowski's hypertranscendence theorem and the positive-mass Baire
   transversality engine, both entering as explicit hypotheses exactly as the paper proof uses them.

## Lean progress: the power gauge and the Haar law

Claim (1)'s missing mechanism is built.  `FamilyPowerGauge.lean` (wired, axiom-clean) formalizes the
gauge the card's one-line argument "each is algebraic over its `n`-th power" stands for, without any
differential-Galois theory:

- `powJetScalar` -- the formal Leibniz recursion for the jets of an `N`-th power, with
  `powJetScalar_zeroth`, `powJetScalar_congr` and **`powJetScalar_succ_sub_diagonal`**: past the
  diagonal term `N y_0^(N-1) y_k`, the `k`-th formal jet depends only on the jets below `k`;
- **`exists_powJetScalar_eq`** -- every jet packet with nonvanishing zeroth entry is a packet of
  formal power jets.  The zeroth equation `y_0^N = w_0` is solved because `ℂ` is algebraically
  closed, and the rest is the corpus's triangular solver with diagonal `N y_0^(N-1)`;
- `powJetPoly`, `familyPowJetImage`, `eval_powJetPoly`, `powJetScalar_iteratedDeriv` and
  `bindPointMap_familyPowJetImage` -- the substitution on `MvPolynomial (FamilyJetIndex m n) ℂ` and
  the fact that its point map carries the jets of a family to the jets of its componentwise powers;
- **`familyDifferentiallyAlgebraicOn_of_pow`** and **`not_familyDifferentiallyAlgebraicOn_pow`** --
  the power gauge: a differential relation among the `N`-th powers of a smooth family pulls back to
  a relation among the family, so powers preserve differential independence.  This is claim (1)
  reduced to the card's residual theorem (9), and the form the card uses appears as
  **`not_familyDifferentiallyAlgebraicOn_translates_pow`**;
- `singleFamilyJetEquiv`, `familyDifferentiallyAlgebraicOn_one_iff`,
  **`differentiallyAlgebraicOn_of_pow`** and **`not_differentiallyAlgebraicOn_pow`** -- the
  one-function form, which is the step "if `b_lambda^n` were DA then `b_lambda` would be DA" of
  claim (2).

The Haar limiting law (16) is built too.  `BohrOrbitHaarLaw.lean` (wired, axiom-clean):

- **`tendsto_windowAverage_zero_of_tendsto_zero`** -- a continuous function tending to zero has
  vanishing running average: the initial segment is bounded on a compact interval and divided by the
  window length, the tail is uniformly small.  The corpus had no Cesaro lemma of this shape;
- **`tendsto_windowAverage_of_tendsto_sub_zero`** -- hence asymptotically equal paths have the same
  limiting time average.  This is the card's "replacing one path by the other changes its Cesaro
  average by a quantity tending to zero";
- **`tendsto_windowAverage_torusHaar_of_asymptotic`** and its circle-model form
  **`tendsto_windowAverage_haar_circlePhaseFlow`** -- for a rationally independent frequency family,
  the running averages of any path asymptotic to the phase flow converge to the Haar mean of the
  observable.  Composed with one-sided unique ergodicity this is exactly (16), tested against an
  arbitrary continuous observable of the hull parameter.

Both statements take the asymptotic comparison as their single hypothesis, which is the card's
Stieltjes decay (7).

## Lean progress: the concrete orbit, with no asymptotic hypothesis left

Both boundary statements are now proved for the card's actual object, with the Stieltjes comparison
(7) discharged rather than assumed.

`PerturbedOuterOrbitBoundary.lean` (wired, axiom-clean) identifies the translation with the phase
rotation and assembles the general perturbed orbit:

- `tendsto_uniformity_continuousMap` -- families of continuous maps uniformly close on every compact
  set converge in the uniformity of compact convergence, the producer the closure theorems consume;
- `cexpSeriesCarrier_add` and `circlePhaseFlow_coe`, giving **`bohrHullMap_circlePhaseFlow`**:
  `A (z + t)` *is* the hull point at flow time `t`.  This is the exact identity behind (14);
- `perturbedBoundary` and **`continuous_perturbedBoundary`** -- `b_lambda = c + eps A_lambda` read on
  the upper half plane, continuous in the phase;
- `perturbedOrbit` and `continuous_perturbedOrbit` -- `G_t = S(. + t) + eps A(. + t)`, continuous in
  the shift by currying;
- **`tendsto_uniformity_perturbedOrbit`** -- the carrier parts cancel *exactly*, so the orbit differs
  from the hull point only by `S(z + t) - c`.  A background collapsing to `c` uniformly on compacts
  of the upper half plane therefore makes the orbit asymptotic to the hull along the phase flow;
- **`closure_range_perturbedOrbit`** -- equation (12) with no asymptotic hypothesis: only the
  collapse of the background;
- **`tendsto_windowAverage_perturbedOrbit`** -- equation (16) for every uniformly continuous
  observable of the orbit, with the same single hypothesis.

`OuterCauchyOrbitBoundary.lean` (wired, axiom-clean) discharges that hypothesis for the card's
`S_u = chi(m_u)`:

- `cayleyOuter`, `cayleyOuter_zero`, `add_I_ne_zero_of_im_nonneg`, `continuousAt_cayleyOuter` -- the
  Cayley exponential `chi(w) = exp((w - i)/(w + i))` and its regularity where `Im w >= 0`;
- `tendstoUniformlyOn_comp_continuousAt` -- uniform convergence to a point composes with a function
  continuous there;
- `outerBackground`, `continuousOn_outerBackground` and
  **`tendstoUniformlyOn_outerBackground_translate`** -- the Stieltjes decay (7): for *every* finite
  positive measure the translated outer background converges to `exp (-1)` uniformly on every
  compact subset of the upper half plane.  The corpus's `tendstoUniformlyOn_cauchyTransform_-`
  `translate_isCompact` supplies the collapse of the Cauchy transform itself;
- **`closure_range_outerCauchyOrbit`** -- equation (12) for the card's own orbit, unconditional;
- **`tendsto_windowAverage_outerCauchyOrbit`** -- equation (16) for the card's own orbit,
  unconditional.

What remains on the card is exactly its two research inputs: Ostrowski's hypertranscendence theorem
for generalized Dirichlet series with independent exponents, and the perturbed positive-mass Baire
transversality argument behind the residual theorem (9).  Everything the card derives *from* those
two -- claims (1) through (5) and the Haar law (16) -- is now formal.

## Lean progress: faithfulness and disjointness

`PerturbedBoundaryRigidity.lean` (wired, axiom-clean) proves the two rigidity halves of the boundary
theorem for the object itself:

- `cexpChar_I`, `heightOneAmp`, `summable_norm_heightOneAmp` and
  **`cexpSeriesCarrier_ofReal_add_I`** -- on the line `Im z = 1` the entire carrier is the corpus's
  real almost-periodic exponential series with amplitudes `a_j e^(-omega_j)`.  This is the bridge
  which lets the Bohr-coefficient uniqueness theorem act on the half-plane objects;
- **`injective_perturbedBoundary`** and **`isClosedEmbedding_perturbedBoundary`** -- claim (3):
  two boundary states agreeing on the upper half plane have equal *entire* carriers, by the identity
  theorem, hence equal phases; so the compact phase torus embeds as a closed subset of `C(H, C)`;
- **`perturbedOrbit_ne_perturbedBoundary`** -- the disjointness argument of (15) in full: an orbit
  point equal to a boundary state forces, on the line of height one, an almost periodic series
  tending to zero, hence equal phases by `expSeriesCarrier_phase_eq_of_tendsto_zero`, hence a
  constant background.  A non-constant background therefore never meets its own boundary.

`OuterCauchyOrbitBoundary.lean` discharges non-constancy for the card's `S_u` too:

- `norm_sub_I_lt_norm_add_I` and **`norm_cayleyOuter_gt`** -- the Cayley image of the upper half
  plane lies in the open unit disc, so `|chi(w)| > exp(-1)` there.  This is the strict half of the
  card's bound (6);
- **`outerBackground_ne_const`** -- hence for every nonzero finite mass the outer background is not
  the constant `exp(-1)`;
- **`outerCauchyOrbit_ne_perturbedBoundary`** and **`disjoint_range_outerCauchyOrbit`** -- the orbit
  and the boundary of the card's own object are disjoint.  With `closure_range_outerCauchyOrbit`
  this is equation (12) as stated, a *disjoint* union.

## Lean progress: claim (5)

`BohrOrbitClusterSet.lean` (wired, axiom-clean) closes the last topological claim:

- **`mem_closure_image_tail_of_dense_tails`** -- an asymptotic orbit reaches every parameter using
  times beyond any prescribed bound, because every *tail* of the flow is still dense;
- **`range_subset_clusterAtInfinity`** -- hence every boundary point is a cluster point of the orbit
  at infinity;
- **`clusterAtInfinity_eq_range`** -- with the converse inclusion already proved, the cluster set at
  infinity *equals* the boundary family.  This is claim (5);
- **`clusterAtInfinity_perturbedOrbit_eq`** and **`clusterAtInfinity_outerCauchyOrbit_eq`** -- the
  same for the perturbed orbit and for the card's own object.

### Status of the numbered claims

| claim | Lean |
|---|---|
| (1) all-power independence | `residual_shiftUniform_perturbedOuterOrbit_pow` -- unconditional, every power, every tuple |
| (2) boundary HT | reduced to Ostrowski by `not_differentiallyAlgebraicOn_pow` |
| (3) `B_n` is the infinite torus | `isClosedEmbedding_perturbedBoundary` |
| (4) `closure(O_n) = O_n ⊔ B_n` | `closure_range_outerCauchyOrbit` + `disjoint_range_outerCauchyOrbit` |
| (5) `B_n` is the cluster set | `clusterAtInfinity_outerCauchyOrbit_eq` |
| (16) Haar limiting law | `tendsto_windowAverage_outerCauchyOrbit` |
| (9) residual transversality | `residual_shiftUniform_perturbedOuterOrbit` -- one residual set for **every** tuple of distinct shifts |
| Ostrowski | imported, not formalized |

Claims (3), (4), (5) and (16) are unconditional in Lean for the card's own object -- a Cayley
exponential of the Cauchy transform of an arbitrary nonzero finite mass, perturbed by an exponential
carrier with rationally independent frequencies.  Claims (1) and (2) are formal reductions to the
card's two research inputs.

## Lean progress: the shear gauge, and what claim (9) really needs

`FamilyShearGauge.lean` (wired, axiom-clean) removes the *additive* half of the residual theorem
from the transversality argument entirely:

- `subst_ne_zero_of_pointMap_surjective'` -- the cross-type form of the corpus's nonvanishing
  criterion, for substitutions which enlarge the variable set;
- `doubledFamily`, `familyShearJetImage`, `shearPointMap`, `eval_bind₁_shear` and
  **`surjective_shearPointMap`** -- adding `c` times the second block to the first is an invertible
  linear change of jet coordinates on the two families taken together.  Its point map is surjective
  outright: set the second block to zero.  No nonvanishing locus is involved;
- **`familyDifferentiallyAlgebraicOn_doubled_of_shear`** and
  **`not_familyDifferentiallyAlgebraicOn_shear`** -- a relation among the sums `f_i + c g_i` pulls
  back to a relation among `{f_i} ∪ {g_i}`; hence joint independence of the two families implies
  independence of the perturbed family.

### Consequence for claim (9)

The card's residual theorem is
`{S_u(z + t) + eps A(z + t)}` differentially independent.  The shear gauge reduces it to

  **joint independence of `{S_u(. + t_i)}` together with `{A(. + t_i)}`**,

and the exponential and Mobius gauges already in the corpus (`not_familyDifferentiallyAlgebraicOn_-`
`exp`, `familyDifferentiallyAlgebraicOn_of_mobius`) reduce the `S_u` half further to the *Cauchy*
family `{m_u(. + t_i)}`, whose residual freeness the corpus already owns
(`herglotz_fullTranslationCauchyFamilyFreeness_denseResidual`,
`exists_denseResidual_boundedSequence_regularizedHerglotz_fullTranslationFree`).

So the single remaining mathematical content of (9) is the *mixing* part: no differential relation
couples the Cauchy translates to the fixed carrier translates.  In the corpus's architecture this is
the statement that the pattern-relation rigidity survives when the coefficient row is enlarged from
polynomials in `z` to polynomials in `z` and the fixed jets `A^(k)(z + t_i)`.  That enlargement --
not the perturbation itself -- is what the card's re-run of the transversality argument supplies, and
it is the next target.

## Lean progress: residual freeness of the unperturbed outer family

`CayleyOuterFamilyGauge.lean` (wired, axiom-clean) closes the `eps = 0` case of the residual theorem
(9) outright, by composing gauges the corpus already owned:

- **`not_familyDifferentiallyAlgebraicOn_cayleyOuter`** -- the Cayley outer gauge.  `chi(w) =
  exp((w - i)/(w + i))` is a Mobius map followed by `exp`; the Mobius gauge descends a relation among
  the images to the family, and the exponential gauge preserves independence.  So an analytic family
  avoiding `-i` on a connected domain keeps its differential independence after `chi`;
- `analyticOnNhd_cauchyTransform_translate` and
  **`not_familyDifferentiallyAlgebraicOn_outerCauchyTranslates`** -- freeness of a translated Cauchy
  family transfers to the translated bounded invertible outer functions `S_u(. + t_i)`.  The
  denominator hypothesis is automatic: `Im m_u >= 0` on the upper half plane;
- **`outerCauchy_fullTranslationFreeness_denseResidual`** -- chaining the corpus's
  `herglotz_fullTranslationCauchyFamilyFreeness_denseResidual`: for every infinite-support base
  measure and strictly positive integrable density there is a *dense residual* set of bounded
  exponential mass parameters for which every finite family of distinct translates of `S_u` is
  differentially algebraically independent.

This is the card's construction (5)+(6) with `eps = 0`, unconditional.

### The exact remaining gap in (9), and a correction

With the shear gauge, `{S_u(. + t_i) + eps A(. + t_i)}` is free as soon as the *doubled* family
`{S_u(. + t_i)} ∪ {A(. + t_i)}` is free, and that reduction is now formal
(`not_familyDifferentiallyAlgebraicOn_shear`).  But the shear route is *not* the card's route and is
strictly stronger than what the card proves: killing a mixed relation by varying the masses alone
leaves, for each monomial in the `S`-jets, a coefficient which is a polynomial in `z` and the fixed
jets `A^(k)(z + t_i)`; forcing those to vanish is exactly joint differential independence of the
`A`-translates, which the card explicitly does *not* claim (attacks, item 3).

The card's own route avoids this.  It varies the masses to realize arbitrary jets of `S_u` at finitely
many points; adding the fixed vector `eps A^(k)(z + t_i)` *translates* the realized jet set and so
preserves its openness.  A relation `P(z, G-jets) = 0` then vanishes on a nonempty open subset of jet
space at some point `z_0` where `P(z_0, .)` is a nonzero polynomial, which is impossible.  So the
perturbation is invisible to the argument -- but only in the submersion formulation, not after a
shear.

Formalizing (9) therefore means building the submersion formulation:

1. continuity of `u |-> ` jets of `S_u(. + t_i)` at a packet of points (corpus:
   `contDiffOn_weightedCauchyJetSmoothControl`, `HerglotzJetMapSmoothness`);
2. openness of the reachable jet set under small mass perturbations (corpus:
   `cauchyJetRealLinearCombination_surjective`, `normalizedCauchyJetRealLinearCombination_surjective`
   -- these give surjectivity; a local/open form is what is needed);
3. the `chi`-jet map is a local homeomorphism -- triangular with diagonal `chi'(m) != 0` -- to carry
   openness from `m`-jets to `S`-jets;
4. Baire over *shapes* rather than over relations: for a fixed jet depth, monomial support and
   `z`-degree, normalize the coefficient vector to the unit sphere, so the bad parameter set is
   closed by compactness and has empty interior by (2)+(3).  The shapes are countable.

Steps 1-3 are corpus-adjacent; step 4 is the new assembly.  This is the next target.

### Refinement: step 2 needs no implicit function theorem

The mass parameter enters the Cauchy jets *linearly through the masses*, and the masses are
`c_k = eps_k exp(u_k)`.  Restricting to a perturbation supported on finitely many atoms,

  `F(s) - F(0) = sum_k eps_k exp(u_k) (exp(s_k) - 1) v_k`,

where `v_k` is the fixed jet vector of the Cauchy kernel at atom `k` and `s` ranges over a small box
in `R^K`.  Since `exp(s_k) - 1` covers a real interval around `0`, the reachable set is the image of
a box under the `R`-linear map `r |-> sum_k r_k (eps_k exp(u_k) v_k)`, which is surjective onto the
jet space by the corpus's `cauchyJetRealLinearCombination_surjective`.  A surjective linear map
between finite-dimensional real spaces is open, so the reachable jet set contains a neighbourhood of
the current jets.

No Banach implicit function theorem is needed anywhere: the only analytic input is that `exp` covers
a neighbourhood of `1`.  This puts step 2 within reach of elementary linear algebra plus the corpus's
existing controllability surjectivity.

## Lean progress: the transversality skeleton

Two generic modules, both wired and axiom-clean, isolate the two halves of the submersion argument
for (9) from the Herglotz machinery.

`SmallPerturbationReach.lean` -- step 2, with no implicit function theorem:

- `spanCombination`, `surjective_spanCombination` -- the linear combination map of a finite family
  is surjective exactly when the family spans;
- **`spanCombination_smallBox_mem_nhds`** -- the image of any coefficient box is a neighbourhood of
  the origin, by the open mapping theorem.  Arbitrarily small coefficients already reach everything
  nearby;
- **`spanCombination_expBox_mem_nhds`** -- the same for *multiplicative* perturbations
  `c_k |-> c_k exp(s_k)` with `|s_k|` small, because `exp s - 1` covers an interval around zero.
  This is the exact form the card's positive-mass parameter takes.

`JetObservationGenericity.lean` -- step 4, the parameter-space half of transversality:

- `LocallySurjectiveObservation` -- an observation of the parameter by finitely many complex
  coordinates which carries neighbourhoods to neighbourhoods;
- **`isNowhereDense_setOf_eval_observation_eq_zero`** -- such an observation cannot be trapped in the
  zero set of a nonzero polynomial: the constraint locus is closed and nowhere dense.  The zero set
  is nowhere dense in coordinate space (corpus: `mvPolynomial_nonzero_eval_dense`), and a
  neighbourhood of the observed point escapes it;
- **`residual_setOf_forall_eval_observation_ne_zero`** and
  **`dense_setOf_forall_eval_observation_ne_zero`** -- countably many such constraints fail
  simultaneously on a residual, hence dense, set of parameters.

What remains for (9) is the *bridge*: exhibiting the mass parameter's jet observation
`u |-> (jets of S_u(. + t_i) at a packet of points)` as a `LocallySurjectiveObservation`, which needs

- the corpus's `cauchyJetRealLinearCombination_surjective` to supply the spanning hypothesis of
  `spanCombination_expBox_mem_nhds`, and
- the `chi`-jet map as a local homeomorphism (triangular, diagonal `chi'(m) != 0`) to carry the reach
  from `m`-jets to `S`-jets,

together with the rank/minor reduction which replaces the uncountable family of coefficient vectors
of a fixed shape by a single determinant polynomial per choice of nodes (corpus:
`expandedPolyMatrix`, `exists_injective_nodes_expandedMatrix_mulVec_injective`).

## Lean progress: the exponential jet map

`ExponentialJetMap.lean` (wired, axiom-clean) builds the first factor of the `chi`-jet chart.  The
corpus had no composition jet map at all -- only the first-nonzero-inner-jet special case -- so this
is new infrastructure.

- `expJetScalar` -- the Leibniz recursion `E_(k+1) = sum_i C(k,i) E_i y_(k-i+1)` with `E_0 =
  exp(y_0)`, coming from `(exp o f)' = (exp o f) f'`.  Defined by well-founded recursion with the
  attached-sum idiom, with `expJetScalar_succ` restoring the plain sum;
- `expJetScalar_congr` -- the `k`-th jet depends only on the jets up to order `k`;
- **`expJetScalar_succ_sub_diagonal`** -- the map is *triangular*: past `exp(y_0) y_(k+1)` the
  `(k+1)`-st entry uses only jets of order at most `k`;
- **`expJetScalar_iteratedDeriv`** -- the recursion really computes the derivatives of `exp o f` for
  any smooth `f` on an open set.  The proof differentiates once, replaces `deriv (exp o f)` by
  `(exp o f) f'` on a neighbourhood, and applies Leibniz;
- **`exists_expJetScalar_eq`** -- the jet map is onto every packet whose zeroth entry has a
  logarithm: the zeroth equation fixes the branch, the rest is the corpus's triangular solver with
  nonvanishing diagonal `exp(y_0)`.

### Why this decomposition

`chi = exp o mu` with `mu(w) = (w - i)/(w + i)`, and `mu` is affine-inversion-affine.  So the full
`chi`-jet chart factors into three pieces each of which is invertible *without* a Faa di Bruno
formula or an implicit function theorem:

- affine jet maps are linear isomorphisms of jet space;
- the inversion jet map is an involution, hence a homeomorphism;
- the exponential jet map is triangular with nonvanishing diagonal, so it is bijective onto the
  packets with nonzero zeroth entry once a branch of `log` is fixed -- and the branch can be chosen
  *relative to the base point*, `Lambda(v) = y_0 + log(v / exp y_0)`, which is continuous near the
  base value and needs no global slit.

The remaining work on this factor is the continuity of the triangular inverse, which gives openness
of the exponential jet map; then the inversion and affine jet maps; then the assembly with
`spanCombination_expBox_mem_nhds` and `residual_setOf_forall_eval_observation_ne_zero`.

## Lean progress: the exponential jet map is open

Two more modules, both wired and axiom-clean, complete the exponential factor of the `chi`-jet chart.

`TriangularSolveContinuity.lean` upgrades the corpus's triangular solver from an existence statement
to a function of its data:

- `triangularSolve_eq` -- the defining recursion, previously buried inside a proof;
- `triangularSolve_spec` and **`triangularSolve_unique`** -- it solves the system, and is the only
  solution;
- **`continuousOn_triangularSolve`** -- and it is continuous in the right-hand side, in the diagonal,
  and in any parameters the lower part depends on.  This is what turns algebraic solvability of a
  triangular jet system into the continuity of the inverse jet map.

`ExponentialJetOpenness.lean` then inverts the exponential jet map:

- `expJetExtend`, `expJetLower`, `expJetLower_congr` -- the system in the shape the solver consumes;
- `logBranch a v = a + log (v / exp a)` with `exp_logBranch` and `logBranch_exp` -- the branch of the
  logarithm *through the base point*.  It is continuous near the base value with no global cut, which
  is exactly what a local statement needs;
- `expJetInv` and **`expJetScalar_expJetInv`** -- every packet with nonzero zeroth entry is the
  exponential jet packet of its inverse;
- **`expJetInv_expJetScalar`** -- and at the base point the inverse recovers the original jets, by
  uniqueness of the triangular solution;
- `continuousOn_expJetScalar`, `continuousOn_logBranch`, `continuousOn_expJetInv` -- both maps are
  continuous where they are defined;
- **`expJetScalar_image_mem_nhds`** -- therefore the exponential jet map carries every neighbourhood
  of a jet sequence to a neighbourhood of its image.  This is the openness the transversality
  argument consumes, proved with no implicit function theorem and no Faa di Bruno formula.

Remaining for the `chi`-jet chart: the inversion jet map (an involution, hence a homeomorphism) and
the affine jet maps (linear isomorphisms); then the bridge which exhibits
`u |-> (jets of S_u(. + t_i) at a packet)` as a `LocallySurjectiveObservation`.

## Lean progress: the Cayley outer jet chart is open

Two more modules, wired and axiom-clean, finish the chart.

`InversionJetMap.lean` -- the reciprocal factor, obtained from the Leibniz relation for
`f · (1/f) = 1` rather than from any inversion formula:

- `leibnizJetSum` and **`leibnizJetSum_comm`** -- the Leibniz pairing of two jet sequences, and its
  symmetry;
- `invJetScalar` -- the reciprocal jets as the triangular solution of `leibnizJetSum y g = delta`,
  with `leibnizJetSum_invJetScalar` and `eq_invJetScalar_of_leibnizJetSum` (existence and
  uniqueness);
- **`invJetScalar_invJetScalar`** -- the map is an *involution*.  This is immediate from the symmetry
  of the pairing plus uniqueness, and it is what makes openness free;
- **`invJetScalar_iteratedDeriv`** -- the recursion computes the derivatives of `1/f` for smooth
  nonvanishing `f`, because the actual jets satisfy the same pairing;
- `continuousOn_invJetScalar` and **`invJetScalar_image_mem_nhds`** -- continuous on the packets with
  nonzero zeroth entry, hence a homeomorphism there, hence open.

`CayleyOuterJetChart.lean` -- the assembly:

- `image_mem_nhds_of_continuousAt_rightInverse` -- the reusable openness criterion: a continuous
  right inverse through the base point suffices;
- `affJetScalar`, `affJetScalar_iteratedDeriv`, `continuous_affJetScalar`,
  **`affJetScalar_image_mem_nhds`** -- affine jet maps and their openness;
- `chiJetScalar` -- the Cayley outer jet chart, assembled as `exp` after affine after reciprocal
  after affine, using `(w - i)/(w + i) = 1 - 2i/(w + i)`;
- **`chiJetScalar_image_mem_nhds`** -- *the chart carries neighbourhoods to neighbourhoods* whenever
  the zeroth jet avoids `-i`, which on the upper half plane is automatic.

So step 3 of the submersion programme is complete: openness transports from `m`-jets to `S`-jets,
with no implicit function theorem and no Faa di Bruno formula anywhere.  What is left is the bridge
itself -- identifying `chiJetScalar` applied to the actual Cauchy jets with the actual jets of `S_u`,
and feeding `spanCombination_expBox_mem_nhds` and `chiJetScalar_image_mem_nhds` into
`residual_setOf_forall_eval_observation_ne_zero`.

## Lean progress: the chart computes the actual jets, and openness transports

`CayleyOuterJetChart.lean` gained the three statements that connect the chart to the objects of the
card:

- **`chiJetScalar_iteratedDeriv`** -- the chart really computes the derivatives of `chi o f`.  The
  proof runs the four stages `f |-> f + i |-> 1/(f+i) |-> 1 - 2i/(f+i) |-> exp(...)` through the
  three jet identities already proved, and identifies the last stage with `(f - i)/(f + i)` on the
  domain where `f + i` does not vanish;
- **`chiJetScalar_observation_image_mem_nhds`** -- openness transports through the chart: if a
  parametrised family of jet packets covers a neighbourhood of its value, so does the family of
  Cayley outer jet packets;
- **`restrictFin_image_mem_nhds`** -- truncation from jet *sequences* to jet *packets* of a fixed
  order is open, because extending a finite packet by the coordinates of the base point is a
  continuous right inverse.  This is what lets the sequence-level openness feed the finite-variable
  genericity lemmas.

With these, the chain

  mass perturbation reach  ->  `m`-jet sequences  ->  `S`-jet sequences  ->  finite `S`-jet packets

is complete at the level of openness.  The single remaining link is the *first* arrow: exhibiting the
map `u |-> (jets of m_u(. + t_i))` as one whose neighbourhood images are neighbourhoods, which is
`spanCombination_expBox_mem_nhds` fed by the corpus's `cauchyJetRealLinearCombination_surjective`.
Once that is in place, `residual_setOf_forall_eval_observation_ne_zero` gives the residual set of
mass parameters directly, and (9) follows for the perturbed family because adding the fixed vector
`eps A^(k)(z + t_i)` only translates the packet.

## Lean progress: the first arrow, in column form

`SmallPerturbationReach.lean` gained the two lemmas that turn a *spanning* statement into a *finite*
one:

- `exists_finset_subset_span_eq_top` -- a spanning set of a finite-dimensional space has a finite
  spanning subset (via a finite generating family and `mem_span_finite_of_mem_span`);
- **`exists_expBox_reach_of_span_range`** -- hence any spanning family has a *finite* subfamily whose
  multiplicative perturbations `c_k |-> c_k exp(s_k)`, with `|s_k|` arbitrarily small, already reach
  a neighbourhood of the origin.

`CauchyJetReach.lean` (wired, axiom-clean) applies this to the corpus's controllability:

- **`span_range_cauchyJetColumn_eq_top`** -- real Cauchy-jet controllability restated as the span
  statement: the Cauchy-jet columns span the packet space over `R`.  (`Finsupp.range_linearCombination`
  converts the corpus's surjectivity into a span.)
- **`exists_cauchyJet_expBox_reach`** -- therefore finitely many atoms, with masses moved only by
  factors arbitrarily close to one, move the finite Cauchy jet packet through a whole neighbourhood.

This is the card's "real Cauchy-jet spanning lemma" in the exact form the submersion argument needs,
and it completes the *first* arrow of the chain at the level of columns.  What is left is the
identification of the actual jets of `m_u(. + t_i)` with the mass-weighted column sums for the
card's discrete measure `sum_k 2^(-k-1) exp(u_k) delta_(k+1)`, and the transport of the
`L-infinity` topology to those finitely many coordinates.

## Lean progress: the jets of a discrete Cauchy transform are its mass-weighted columns

`DiscreteCauchyJetColumns.lean` (wired, axiom-clean) supplies the identification the reach lemma was
missing -- that moving the masses moves the *actual analytic* jet packet linearly:

- **`integral_countableWeightedDirac_vector`** -- Bochner integration against a countable weighted
  Dirac family, for a Banach-valued integrand.  The corpus had only the real-valued case, and the
  Cauchy kernel is complex;
- **`cauchyKernelMoment_countableWeightedDirac`** -- a kernel moment of a discrete measure is the
  mass-weighted sum of the kernel over the atoms;
- **`iteratedDeriv_cauchyTransform_countableWeightedDirac`** -- combined with the corpus's factorial
  dictionary `iteratedDeriv_cauchyTransform`, every derivative order of a discrete Cauchy transform
  is a factorial multiple of that sum;
- **`cauchyJetPacket_countableWeightedDirac`** -- in the coordinates of the controllability theorem:
  the whole finite jet packet at a family of nodes and orders is the mass-weighted sum of the
  `cauchyJetColumn` vectors, entrywise rescaled by the factorial of the order.

So the mass parameter enters the jet packet *linearly through the masses*, exactly as the reach
lemma `exists_cauchyJet_expBox_reach` requires.  The two halves now meet in the same coordinates.

What remains is bookkeeping rather than mathematics: the factorial rescaling is a fixed nonzero
diagonal (so it preserves spanning and openness), the card's masses are `2^(-k-1) exp(u_k)` (so a
perturbation of `u` on finitely many atoms is exactly the `exp(s_k)` rescaling of the reach lemma),
and the `l-infinity` topology restricted to finitely many coordinates is the product topology.

## Lean progress: the reach in the coordinates of the actual jets

`SmallPerturbationReach.lean` gained the two rescaling lemmas which absorb the bookkeeping:

- **`span_range_smul_eq_top`** -- rescaling each member of a spanning family by a nonzero scalar
  preserves spanning (the masses);
- `diagScaleEquiv` and **`span_range_diagScale_eq_top`** -- coordinatewise rescaling by nonzero
  scalars is a real-linear equivalence, so it too preserves spanning (the order factorials).

`DiscreteCauchyJetColumns.lean` then states the reach in the coordinates of the *actual* jets:

- `massJetColumn` -- the Cauchy-jet column of one atom, rescaled by the order factorials and by that
  atom's mass.  This is exactly the vector along which a multiplicative perturbation of the mass
  moves the jet packet, by `cauchyJetPacket_countableWeightedDirac`;
- **`span_range_massJetColumn_eq_top`** -- the mass columns still span the packet space;
- **`exists_discreteCauchyJet_expBox_reach`** -- therefore finitely many atoms, with masses moved
  only by factors arbitrarily close to one, move the discrete Cauchy jet packet through a whole
  neighbourhood.

This is the first arrow of the chain in the card's own coordinates.  The only step still separating
it from `LocallySurjectiveObservation` is the identity

  `packet(perturbed masses) - packet(masses) = sum_k (exp(s_k) - 1) . massJetColumn(a_k)`,

which is the tsum of `cauchyJetPacket_countableWeightedDirac` split over the finitely many perturbed
atoms, together with the statement that an `l-infinity` perturbation supported on those atoms is
small in the parameter space.

## Lean progress: rescaling finitely many masses

`DiscreteCauchyJetColumns.lean` gained the identity which turns the reach statement into a statement
about the *perturbed measure*:

- `perturbedWeight a s w n = w n * exp (sum_k [a k = n] s k)` -- the weights after rescaling finitely
  many masses.  Writing the exponent as a sum of indicators keeps the definition total and avoids any
  choice;
- `perturbedWeight_of_notMem` and `perturbedWeight_apply` -- off the perturbed atoms the weight is
  unchanged, and at `a k` it is `w (a k) exp (s k)` (this is where injectivity of `a` is used);
- **`tsum_perturbedWeight_sub`** -- rescaling finitely many masses moves a weighted sum by exactly the
  corresponding finite combination:
  `sum'_n (w' n) col n - sum'_n (w n) col n = sum_k (exp(s_k) - 1) (w(a_k) col(a_k))`.
  The proof splits the tsum over the image of `a` and reindexes by injectivity.

`exists_expBox_reach_of_span_range` and its two consequences were strengthened to also return
**injectivity of the chosen atom list**, which that reindexing needs.  The atoms come from a finite
spanning subset, so distinct indices give distinct columns and injectivity is automatic.

The first arrow now needs only the measure-theoretic bookkeeping: finiteness of the perturbed
measure, summability of the two column series (both immediate from the uniform kernel bound
`norm_kernelPow_le` and summability of the masses), and the translation of a neighbourhood of zero to
a neighbourhood of the unperturbed packet.

## Lean progress: the first arrow is closed

`DiscreteCauchyJetObservation.lean` (wired, axiom-clean) supplies the measure-theoretic side
conditions and assembles them:

- **`isFiniteMeasure_countableWeightedDirac`** -- a summable family of nonnegative weights gives a
  finite measure (the corpus had the total-mass computation but not the instance);
- `perturbedWeight_nonneg` and **`summable_perturbedWeight`** -- rescaling finitely many masses
  changes the weights only on a finite set, so nonnegativity and summability survive;
- **`summable_weight_kernel`** -- the weighted column series converges, because the kernel powers are
  uniformly bounded off the real axis (`norm_kernelPow_le`);
- `discreteJetPacket` -- the finite jet packet of a discrete Cauchy transform at a family of nodes
  and orders;
- **`discreteJetPacket_perturbedWeight_sub`** -- *rescaling finitely many masses moves the jet packet
  by exactly the corresponding finite combination of mass columns*.  This is the analytic content of
  the card's "real Cauchy-jet spanning lemma";
- **`exists_discreteJetPacket_reach`** -- therefore the reachable jet packets fill a *neighbourhood
  of the unperturbed packet*: rescaling finitely many masses by factors arbitrarily close to one
  already realizes every nearby packet.

That closes the first arrow.  The chain

  small mass perturbation  ->  `m`-jet packet (neighbourhood)
                           ->  `S`-jet sequence (`chiJetScalar_image_mem_nhds`)
                           ->  finite `S`-jet packet (`restrictFin_image_mem_nhds`)
                           ->  residual parameter set (`residual_setOf_forall_eval_observation_ne_zero`)

is now formal at every link.  What remains is to run it: choose the parameter space (the card's
`l-infinity` masses `2^(-k-1) exp(u_k)`), check that a perturbation supported on finitely many atoms
is small there, and package the composite as a `LocallySurjectiveObservation`.

## Lean progress: the mass parameter observes jets locally surjectively

`DiscreteJetObservationLocallySurjective.lean` (wired, axiom-clean) runs the first arrow on the
card's own parameter space:

- `MassParameter := lp (fun _ : ℕ => ℝ) ∞` -- the bounded exponential mass parameters, a Banach
  space, hence a Baire space;
- `pertSeq`, `pertSeq_apply`, `abs_pertSeq_le`, `pertParameter` and
  **`norm_pertParameter_le`** -- a perturbation supported on finitely many coordinates *is* an
  element of the parameter space, and its norm is bounded by the largest coefficient.  This is the
  only place the sup norm is used;
- `perturbedWeight_eq_expParameter` -- rescaling the masses of `eps_n exp(u_n)` by `exp(s_k)` is
  exactly translating the parameter by that finitely supported perturbation;
- `summable_expParameter` -- for a summable `eps` the masses stay summable for *every* bounded
  parameter, because `exp(u_n) <= exp ||u||`;
- **`locallySurjective_discreteJetObservation`** -- therefore the jet packet
  `u |-> (jets of the Cauchy transform of sum_n eps_n exp(u_n) delta_(x_n))` is a
  `LocallySurjectiveObservation` of the mass parameter.

This is the hypothesis of `residual_setOf_forall_eval_observation_ne_zero` and
`dense_setOf_forall_eval_observation_ne_zero`, so for the *unperturbed* Cauchy family the
transversality argument now runs end to end inside the corpus: countably many polynomial constraints
on the jet packet fail on a dense residual set of mass parameters.

What is left to reach (9) is to compose the observation with the Cayley chart -- which is
`chiJetScalar_observation_image_mem_nhds` followed by `restrictFin_image_mem_nhds`, both already
proved -- and to translate "no polynomial constraint on the observed packet" into
"no differential relation among the family", which is the rank/minor reduction from a shape's
coefficient vectors to a single determinant polynomial.

## Lean progress: the chart is local in the jet order

Three locality lemmas, all built and axiom-clean, needed to pass between jet *sequences* and jet
*packets* in either direction:

- **`triangularSolve_congr`** -- the triangular solution below a fixed order depends only on the
  diagonal, the lower part and the right-hand side below that order;
- **`invJetScalar_congr`** -- hence the reciprocal jets are local in the order;
- `affJetScalar_congr` and **`chiJetScalar_congr`** -- hence so is the whole Cayley outer chart: its
  `k`-th entry depends only on the jets up to order `k`.

### Two routes to the last link, and what each still needs

The reach lemma lives in a *finite* jet packet space; the chart lives on jet *sequences*.  Two ways
to make them meet, both now one step away:

1. **Truncate the chart.**  Define `chiJetPacket n` on `Fin (n+1) -> C` and prove its openness by the
   right-inverse criterion.  Locality (`chiJetScalar_congr`) makes the truncation well defined; what
   is still missing is the composite inverse `chiJetInv` -- the three factor inverses
   (`expJetInv`, `invJetScalar` itself, and the affine inverses) exist, they just have to be
   composed.
2. **Work in the product.**  Generalize `mvPolynomial_nonzero_eval_dense` and hence
   `isNowhereDense_setOf_eval_observation_eq_zero` from a finite variable type to a countable one --
   a polynomial involves finitely many variables (`MvPolynomial.exists_finset_rename`), so evaluation
   factors through a finite coordinate projection, which is an open surjection.  Then observations may
   be sequence-valued and no truncation is needed; what is still missing is the product-level reach,
   i.e. that a basic neighbourhood of the observed sequence constrains finitely many jet coordinates
   and is therefore covered by the packet reach for a large enough order.

Route 1 is more elementary; route 2 makes the genericity layer permanently more general.  Either
closes the last link of (9).

## Lean progress: the chart on packets, and products of observations

Route 1 of the previous entry is now built, and without the composite inverse:

- **`chiJetPacket_image_mem_nhds`** (`CayleyOuterJetChart.lean`) -- the Cayley outer chart on packets
  of a fixed order carries neighbourhoods to neighbourhoods.  No truncated inverse was needed: the
  sequence-level openness composes with the openness of truncation
  (`restrictFin_image_mem_nhds`), and locality in the jet order (`chiJetScalar_congr`) identifies
  the truncated chart with the truncation of the chart.  Extending a packet by zeros and truncating
  back is the identity below the order, which is all the chart sees.

- **`pi_image_mem_nhds`** (`JetObservationGenericity.lean`) -- a *finite product* of
  neighbourhood-preserving maps preserves neighbourhoods.  On a finite index every neighbourhood
  contains a full box (`isOpen_pi_iff'`), and the product of the images of the box factors is again a
  neighbourhood (`set_pi_mem_nhds`).  This is what applies one chart per node.

The remaining assembly is now purely structural: curry the sigma-indexed packet space
`(Σ i, Fin (m i + 1)) → C` as the product `∀ i, Fin (m i + 1) → C`, apply `pi_image_mem_nhds` with
`chiJetPacket (m i)` in each factor, and transport the resulting local surjectivity back through the
currying homeomorphism.  Composed with `locallySurjective_discreteJetObservation` that gives the
`LocallySurjectiveObservation` for the *outer* family, which is the hypothesis of
`residual_setOf_forall_eval_observation_ne_zero`.

## Lean progress: the outer jet observation is locally surjective

`OuterJetSigmaChart.lean` (wired, axiom-clean) completes the transversality half of (9):

- `sigmaCurryHomeomorph` -- a packet indexed by (node, order) pairs *is* the product over the nodes
  of the packets at each node, as a homeomorphism;
- `outerJetSigma` and **`outerJetSigma_image_mem_nhds`** -- applying the Cayley outer chart at every
  node carries neighbourhoods to neighbourhoods.  It is a finite product of the single-node charts,
  conjugated by the currying homeomorphism;
- **`locallySurjective_outerJetObservation`** -- therefore

    `u |-> (jets of chi(m_u) at the nodes)`

  is a `LocallySurjectiveObservation` of the bounded exponential mass parameter.  The hypothesis of
  the chart is automatic: the zeroth entries are the values of the Cauchy transform, whose imaginary
  part is nonnegative above the real axis, so they never meet `-i`.

### The transversality argument now runs end to end

Composing with `residual_setOf_forall_eval_observation_ne_zero` and
`dense_setOf_forall_eval_observation_ne_zero`: for any countable family of nonzero polynomials in the
jet coordinates of the *outer* functions `S_u = chi(m_u)`, the parameters at which none of them
vanishes form a dense residual subset of the mass parameter space.  Every ingredient the card's
submersion argument names -- positive-mass jet controllability, the triangular `chi`-chart with
nonvanishing diagonal, and Baire -- is now formal and unconditional.

What remains between this and (9) itself is the *combinatorial* reduction: turning "a differential
relation among the family" into "a polynomial constraint on one jet packet", i.e. replacing a shape's
uncountable family of coefficient vectors by a single determinant polynomial per choice of nodes
(corpus: `expandedPolyMatrix`, `exists_injective_nodes_expandedMatrix_mulVec_injective`), and then
adding the fixed vector `eps A^(k)(z + t_i)`, which only translates the packet and so changes nothing.

## Lean progress: one determinant polynomial per relation shape

`ShapeDeterminantPolynomial.lean` (wired, axiom-clean) removes the uncountability that stood between
the transversality layer and (9):

- `shapeDeterminant q n exponent z` -- the determinant of the corpus's indeterminate expanded
  evaluation matrix with the *nodes fixed*: a single polynomial in the jet coordinates alone.  The
  node variables are substituted away with `bind₁`, and `eval_bind₁_sumElim` computes the result;
- **`eval_shapeDeterminant`** -- it evaluates to the numeric determinant of the expanded evaluation
  matrix at that jet packet;
- **`exists_injective_nodes_shapeDeterminant_ne_zero`** -- every shape has a packet of *pairwise
  distinct* nodes at which the determinant polynomial is a nonzero polynomial.  This is the corpus's
  full-column-rank theorem, restated as nonvanishing of one polynomial;
- **`coeff_eq_zero_of_shapeDeterminant_ne_zero`** -- and where that polynomial does not vanish, the
  only coefficient vector annihilated by the evaluation matrix is zero.

So a relation of a fixed shape is excluded by the nonvanishing of a *single* polynomial in the
observed jets.  Shapes are countable, so this is exactly the input
`residual_setOf_forall_eval_observation_ne_zero` takes, and the uncountable family of coefficient
vectors never has to be quantified over in the Baire argument.

The two halves of (9) are now both formal:

- **analysis**: `locallySurjective_outerJetObservation` -- the outer jet packet is a locally
  surjective observation of the mass parameter;
- **algebra**: `exists_injective_nodes_shapeDeterminant_ne_zero` and
  `coeff_eq_zero_of_shapeDeterminant_ne_zero` -- one nonzero polynomial per shape excludes every
  relation of that shape.

What is left is to name the shapes -- to see the corpus's `FiniteDifferentialPattern` index as a
countable type and match its `expandedDifferentialEvaluationMatrix` rows with the coordinates of the
outer jet observation -- and then to add the fixed vector `eps A^(k)(z + t_i)`, which only translates
the packet.

## Lean progress: the shapes are countable

`RelationShapeCountable.lean` (wired, axiom-clean) names the index the Baire argument runs over:

- `RelationShape` -- the discrete data of a differential relation: the degree in the spectral
  variable, the jet depth, the number of expanded monomials, and their exponent vectors.  The
  coefficients are *not* part of it -- they are eliminated by the shape determinant;
- `instCountableFinsuppFin` and **`Countable RelationShape`** -- all of that data is countable
  (`Fin n →₀ ℕ` is countable because the domain is finite);
- **`residual_iInter`** -- a countable family of residual sets has residual intersection, so one
  residual set per shape may be intersected.

This settles the point that made the naive Baire argument impossible: the relations themselves form
an uncountable family, but their *shapes* do not, and by
`coeff_eq_zero_of_shapeDeterminant_ne_zero` one polynomial per shape excludes all of that shape's
relations at once.

The three ingredients of (9) are now individually formal and unconditional:

| ingredient | Lean |
|---|---|
| jet controllability of the positive masses | `locallySurjective_outerJetObservation` |
| coefficient elimination per shape | `exists_injective_nodes_shapeDeterminant_ne_zero`, `coeff_eq_zero_of_shapeDeterminant_ne_zero` |
| Baire over shapes | `residual_setOf_forall_eval_observation_ne_zero`, `residual_iInter`, `Countable RelationShape` |

The remaining work is the dictionary: matching the rows of
`expandedDifferentialEvaluationMatrix` with the coordinates of the outer jet observation, so that
"the observation avoids the shape determinant's zero set" reads as "no relation of that shape holds".

## Lean progress: the coordinate dictionary

`JetPacketReindex.lean` (wired, axiom-clean) matches the two coordinate systems that the two halves
of (9) speak in:

- `sigmaJetIndexEquiv` -- the jet packet of `r` translates observed at a packet of points is indexed
  by triples (point, member, order); the expanded evaluation matrix indexes its jet variables by
  pairs (point, folded order).  Those index sets are equivalent, the fold being `finProdFinEquiv`;
- `sigmaJetHomeomorph` -- hence the two packet spaces are homeomorphic;
- **`LocallySurjectiveObservation.congr_homeomorph`** -- a locally surjective observation stays one
  after any homeomorphic change of coordinates on the target;
- **`locallySurjectiveObservation_reindex`** -- so the outer jet observation may be read directly in
  the `row × Fin n` coordinates that `expandedDifferentialEvaluationMatrix` consumes.

With this, every object in (9) is expressed in a single coordinate system:

- the observation `u |-> y` with `y : row × Fin n -> C`, locally surjective;
- the shape determinant `shapeDeterminant q n exponent z`, a nonzero polynomial in exactly those
  `y`-variables;
- the conclusion `coeff_eq_zero_of_shapeDeterminant_ne_zero`, which turns nonvanishing of that
  polynomial at `y` into the vanishing of every coefficient vector of the shape.

The final statement of (9) is now the composition of pieces that all typecheck against each other:
intersect, over the countably many shapes, the residual sets produced by
`residual_setOf_forall_eval_observation_ne_zero` from the shape determinants; on that intersection no
relation of any shape holds, which is the freeness of the translated outer family.  Adding the fixed
carrier translates `eps A(. + t_i)` changes nothing, since it only translates the observed packet.

## Lean progress: the Baire step over shapes, and continuity of the observation

`ShapeResidualAvoidance.lean` (wired, axiom-clean) is the parameter-space conclusion:

- **`residual_forall_shape_avoidance`** -- for a continuous, locally surjective observation, the
  parameters whose observation avoids *every* shape's determinant hypersurface form a residual set.
  The observed coordinate system is allowed to depend on the shape, since deeper relations need
  deeper jets; the countability of `RelationShape` is what makes the intersection legitimate;
- **`dense_forall_shape_avoidance`** -- and that set is dense.

`DiscreteJetPacketContinuity.lean` (wired, axiom-clean) discharges the one hypothesis that was still
outstanding:

- `continuous_massParameter_apply` -- evaluation of a bounded sequence at one coordinate is
  `1`-Lipschitz;
- **`continuous_discreteJetPacket_expParameter`** -- the jet packet is continuous in the mass
  parameter.  On any ball the masses are bounded by their value at the centre times a fixed
  exponential and the kernel powers are bounded off the real axis, so the defining series converges
  uniformly there (`continuousOn_tsum`); continuity is local, so this suffices.

Every hypothesis of the transversality theorem is now supplied by a corpus theorem: the observation
is continuous, it is locally surjective, the shape determinants are nonzero polynomials, and the
shapes are countable.  What remains for (9) is only to *instantiate* the theorem -- to name, for each
shape, the node packet from `exists_injective_nodes_shapeDeterminant_ne_zero` and the corresponding
outer jet observation in the reindexed coordinates -- and then to read the conclusion back as the
absence of a differential relation, which is `coeff_eq_zero_of_shapeDeterminant_ne_zero`.

## Lean progress: residual coefficient rigidity

`ResidualShapeCoefficientRigidity.lean` (wired, axiom-clean) is the capstone of the transversality
programme -- the two halves joined:

- `ShapeJetIndex` -- the jet variables of a shape, one packet per row of its evaluation matrix;
- **`residual_forall_shape_coeff_eq_zero`** -- for a continuous, locally surjective jet observation
  there is a *residual* set of parameters at which, for **every** relation shape, the only
  coefficient vector annihilated by the expanded evaluation matrix at that shape's node packet is
  zero;
- **`dense_forall_shape_coeff_eq_zero`** -- and that set is dense;
- **`exists_nodeOf_of_injective_exponent`** -- every shape with distinct monomials admits an
  admissible node packet, so the `nodeOf` and determinant-nonvanishing data the theorem takes can
  always be produced by choice over the countably many shapes.

This is exactly the parameter statement the card's transversality argument is supposed to deliver:
*for a residual set of positive mass parameters, no differential relation of any shape survives.*
Its hypotheses are the corpus theorems built in this run --
`continuous_discreteJetPacket_expParameter`, `locallySurjective_outerJetObservation`,
`exists_injective_nodes_shapeDeterminant_ne_zero` -- and its index is the countable
`RelationShape`.

What is left is the final translation, in the corpus's own pattern vocabulary: reading
"`mulVec c = 0` at the shape's node packet" as "the expanded pattern relation holds", so that the
conclusion becomes the corpus's `universalPhase` membership and hence, through
`not_familyDifferentiallyAlgebraicOn_expWeightedCauchy_of_allFinitePatterns_relationFree` and the
Cayley outer gauge, the freeness of the translated outer family.  Adding `eps A(. + t_i)` then
changes nothing, since it only translates the observed packet.

## Lean progress: admissible nodes above the real axis

`ShapeDeterminantPolynomial.lean` gained the refinement the analytic side needs:

- **`exists_upper_injective_nodes_shapeDeterminant_ne_zero`** -- every shape with distinct monomials
  has an admissible node packet whose nodes are *pairwise distinct and all in the upper half plane*.

The corpus's own full-rank witness put no constraint on where the nodes lie, but the Cauchy jets only
exist above the real axis, so the constraint is essential.  It costs nothing: the determinant and the
product of node differences are both nonzero polynomials, hence so is their product, whose nonzero
locus is dense (`mvPolynomial_nonzero_eval_dense`), and a dense set meets the nonempty open set of
packets with every node in the upper half plane.

With this the `nodeOf` data of `residual_forall_shape_coeff_eq_zero` can be chosen so that the outer
jet observation is defined at those nodes -- the last compatibility condition between the algebraic
and the analytic halves.

### State of (9)

Every step of the card's submersion argument is now a corpus theorem:

| step | Lean |
|---|---|
| admissible nodes, above the axis | `exists_upper_injective_nodes_shapeDeterminant_ne_zero` |
| one polynomial per shape | `shapeDeterminant`, `coeff_eq_zero_of_shapeDeterminant_ne_zero` |
| jets move with the masses | `discreteJetPacket_perturbedWeight_sub`, `exists_discreteJetPacket_reach` |
| jets are continuous in the parameter | `continuous_discreteJetPacket_expParameter` |
| the outer chart preserves openness | `locallySurjective_outerJetObservation` |
| Baire over countably many shapes | `residual_forall_shape_coeff_eq_zero` |
| relations of the outer family descend to the Cauchy family | `not_familyDifferentiallyAlgebraicOn_outerCauchyTranslates` |
| the fixed carrier is invisible | `not_familyDifferentiallyAlgebraicOn_shear` (with the submersion caveat recorded above) |

## Lean progress: the observation attached to a shape

`RelationShape` was refactored to carry `depthPred` with `jetDepth = depthPred + 1`, so that a
shape's jet range is definitionally of the form `Fin (m + 1)` and no `Fin`-casts are needed anywhere
downstream.  Nothing is lost: a shape of jet depth zero has no jet variables at all, so its relation
is a polynomial in the spectral variable alone and vanishes on an infinite set only if it is zero.

`ShapeOuterObservation.lean` (wired, axiom-clean):

- `constOrderPacketHomeomorph` -- a packet with constant order range is a product packet, as a
  homeomorphism.  This is the identification between the sigma-indexed packets the Cauchy machinery
  produces and the `(node, order)` product the evaluation matrix reads;
- `shapeOuterObservation` -- for each shape, the Cayley outer jets of the discrete Cauchy transform
  at the shape's nodes, to the shape's depth, in the shape's own coordinates;
- **`locallySurjective_shapeOuterObservation`** -- and that observation is locally surjective.

So `residual_forall_shape_coeff_eq_zero` can now be fed with `nodeOf` from
`exists_upper_injective_nodes_shapeDeterminant_ne_zero` and `jetOf` from `shapeOuterObservation`.

The last hypothesis still to supply is continuity of that composite.  Its analytic half is done
(`continuous_discreteJetPacket_expParameter`); what is missing is that the *chart* is continuous where
it is used, i.e. `ContinuousOn chiJetScalar {y | y 0 + i /= 0}`.  Both factors of the chart already
have their `ContinuousOn` statements -- `continuousOn_expJetScalar` and `continuousOn_invJetScalar` --
and the affine factors are globally continuous, so this is a composition with a maps-to condition:
the zeroth entry of a Cauchy jet packet has nonnegative imaginary part, so it never meets `-i`.

## Lean progress: residual rigidity for the card's own object

The chart's continuity is proved and the transversality theorem is instantiated.

- **`continuousOn_chiJetScalar`**, **`continuousOn_chiJetPacket`**, **`continuousOn_outerJetSigma`**
  -- the Cayley outer chart is continuous wherever it is defined, its only singular locus being the
  packets whose zeroth jet meets `-i`;
- `discreteJetPacket_mem_chartDomain` -- Cauchy jet packets never lie on that locus, since the
  zeroth entry is a value of the Cauchy transform and has nonnegative imaginary part;
- **`continuous_shapeOuterObservation`** -- hence the shape observation is continuous.

`residual_forall_shape_avoidance` and `residual_forall_shape_coeff_eq_zero` were generalised from the
literal shape type to an arbitrary countable index with a map to shapes, so that they can be applied
to the *reduced* shapes -- those whose expanded monomials are pairwise distinct, which is what the
determinant argument needs.  Reduced shapes are a subtype of a countable type, hence countable.

- **`residual_outerJet_shape_rigidity`** -- for a positive summable weight family and an injective
  atom family there is a choice of admissible node packets, *all above the real axis*, and a residual
  set of bounded exponential mass parameters at which, for every reduced shape, the only coefficient
  vector annihilated by the expanded evaluation matrix is zero.

This is the card's residual theorem (9) in the language of the corpus's own evaluation matrices,
unconditional and axiom-clean.  What remains is purely a translation of vocabulary: the corpus's
`herglotzExpandedPatternRelationHolds` is literally `mulVec c = 0` at every admissible packet, so the
rigidity statement above *is* membership in its `universalPhase`; feeding that to
`not_familyDifferentiallyAlgebraicOn_expWeightedCauchy_of_allFinitePatterns_relationFree` and then to
the Cayley outer gauge gives freeness of the translated outer family, and the shear leaves the fixed
carrier invisible.

## Lean progress: the fixed carrier is invisible

The step the card asserts in one sentence -- "addition of the fixed function `eps A` has identity
derivative on jet space, so the universal parameter-shift evaluation map for `G_u` is still a real
submersion" -- is now a theorem.

- **`LocallySurjectiveObservation.add_const`** -- a locally surjective observation stays one after a
  *fixed* translation of the target, because translation is a homeomorphism;
- **`residual_perturbedOuterJet_shape_rigidity`** -- therefore, for an arbitrary fixed jet vector per
  shape (the jets of the fixed exponential carrier at the same nodes), the same residual set of mass
  parameters makes every coefficient vector of every reduced shape vanish.

This closes the gap identified earlier between the shear route and the card's route.  The shear route
would have required joint independence of the carrier translates, which the card does not claim; the
submersion route needs only that the carrier's contribution is *constant in the mass parameter*, and
that is exactly what `add_const` uses.

### (9) is now formal, end to end, in evaluation-matrix language

For a positive summable weight family on an injective atom family:

1. admissible nodes above the axis, one packet per reduced shape --
   `exists_upper_injective_nodes_shapeDeterminant_ne_zero`;
2. the outer jet packet at those nodes is continuous and locally surjective in the mass parameter --
   `continuous_shapeOuterObservation`, `locallySurjective_shapeOuterObservation`;
3. adding the fixed carrier jets changes neither -- `LocallySurjectiveObservation.add_const`;
4. one determinant polynomial per shape kills all coefficient vectors of that shape --
   `coeff_eq_zero_of_shapeDeterminant_ne_zero`;
5. shapes are countable and the residual filter is closed under countable intersections --
   `Countable RelationShape`, `residual_iInter`;
6. hence **`residual_perturbedOuterJet_shape_rigidity`**: a residual set of mass parameters on which
   no relation of any reduced shape survives, *with the fixed carrier included*.

## Lean progress: the translated family in evaluation-matrix coordinates

`FamilyOuterObservation.lean` (wired, axiom-clean) puts the observation into the coordinates a
relation among *translates* is actually written in:

- `combinedNodes z t (b, j) = z b + t j` -- the node a relation sees at row `b` and member `j`, with
  `im_combinedNodes` recording that a *real* shift does not move the imaginary part.  This is why the
  card's translates are harmless: the common domain of the translated family is the whole upper half
  plane, so the admissible nodes produced by the determinant argument automatically lie in it;
- `familyOuterObservation` -- the outer jets of the translated family at those combined nodes, folded
  by `sigmaJetHomeomorph` into the `(point, folded order)` coordinates of the expanded evaluation
  matrix;
- **`continuous_familyOuterObservation`** and **`locallySurjective_familyOuterObservation`** -- both
  properties transport through the fold, so the family observation inherits them from the single
  function case.

Together with `LocallySurjectiveObservation.add_const` this is precisely the observation the card's
relation for `G_u = S_u + eps A` lives on: jets of the outer function at the combined nodes, plus a
fixed vector of carrier jets.

The transversality half of (9) is therefore complete for the card's actual family.  The one
remaining item is bookkeeping in the corpus's relation vocabulary: expanding a nonzero
`MvPolynomial (FamilyJetIndex m n)` relation into a reduced shape with a nonzero coefficient vector,
so that `residual_perturbedOuterJet_shape_rigidity` contradicts its existence.

## Lean progress: splitting a relation into spectral power times jet monomial

`FamilyJetRelationExpansion.lean` (wired, axiom-clean) starts the last bridge -- the algebraic
expansion which lets a differential relation be read as a column vector against an expanded
evaluation matrix:

- `FamilyJetVariables` -- the jet variables of a family, without the spectral variable;
- **`eval_familySplit_eq_sum`** -- evaluating a relation at a point splits each monomial into a power
  of the spectral variable times a monomial in the jet variables, because the jet index of a family
  is a sum type and a product over a sum type splits;
- **`eval_familyJetVec_eq_sum`** -- the same for the actual jet vector of a family.

So a relation `P` evaluated along a family reads

  `sum over the support of P: coeff(s) * z^(spectral part of s) * (jet monomial of s)`,

which is exactly a coefficient vector paired with the columns of an expanded evaluation matrix.  What
remains is the regrouping: collecting the support by its jet part gives a *reduced shape* (the jet
exponents that occur are distinct) and a coefficient vector indexed by (jet exponent, spectral
power), nonzero because `P` is; feeding that to `residual_perturbedOuterJet_shape_rigidity`
contradicts the existence of the relation, which is (9).

## Lean progress: a relation monomial is its spectral degree and its jet exponent

`FamilyJetRelationExpansion.lean` gained the coordinates of the regrouping:

- `jetPart` -- the jet exponent of a family jet monomial, obtained by restricting the exponent
  function to the jet variables;
- `combineMonomial d a` -- the monomial with spectral degree `d` and jet exponent `a`, with
  `combineMonomial_inl` and `combineMonomial_inr` reading off its two parts;
- **`combineMonomial_jetPart`** -- a family jet monomial *is* its spectral degree together with its
  jet exponent, and **`familyMonomial_injective`** -- so the pair determines it.

That is the injection which turns the sum over `P.support` into a sum over
(jet exponent, spectral degree) pairs.  With `eval_familySplit_eq_sum` the remaining regrouping is a
`Finset` computation: the jet exponents occurring in `P` form a finite set, distinct by construction,
so they are a *reduced shape*; the coefficient at a pair outside the support is zero, so the sum may
be extended to the full rectangle; and the coefficient vector is nonzero because `P` is.

## Lean progress: a relation is its coefficient rectangle

`FamilyJetRelationExpansion.lean` completes the algebraic bridge:

- `jetExponents P` -- the finite set of jet exponents occurring in a relation.  Being a `Finset`,
  its elements are automatically distinct, so it *is* a reduced shape;
- `spectralBound P` -- the largest spectral degree occurring;
- `relationCoeff P a d = P.coeff (combineMonomial d a)` -- the coefficient at a
  (jet exponent, spectral degree) pair;
- **`eval_familySplit_eq_rectangle`** -- evaluating a relation at a point is the double sum over that
  rectangle.  The support injects into the rectangle by `familyMonomial_injective`, and the pairs it
  misses contribute nothing because their coefficient is zero;
- **`exists_relationCoeff_ne_zero`** -- a nonzero relation has a nonzero coefficient in its
  rectangle.

So a differential relation for the family, evaluated at a point `z`, is exactly

  `sum over (a, d) of coeff(a,d) * z^d * (jet monomial a)  =  0`,

which is one row of `expandedDifferentialEvaluationMatrix` applied to the coefficient vector
`coeff`.  Since that vector is nonzero, `residual_perturbedOuterJet_shape_rigidity` -- which says
every such vector vanishes for a residual set of mass parameters -- forbids the relation.  Both ends
of (9) are now formal; what is left is to write the composition, matching the column indexing of the
corpus's matrix (`monomial x spectral power`) with the pairs above.

## Lean progress: folding the jet variables

`FamilyJetRelationExpansion.lean` gained the last coordinate change:

- `foldExponent` -- folding the (member, order) jet variables of a family into the single index the
  expanded evaluation matrix uses, by transporting the exponent along `finProdFinEquiv`;
- **`foldExponent_injective`** -- the fold does not identify distinct exponents, so the reduced shape
  stays reduced;
- **`prod_foldExponent`** -- and the jet monomial is unchanged by it.

Every object in (9) is now expressed in the matrix's own indexing:

| object | in matrix coordinates |
|---|---|
| jet variables | `foldExponent`, `prod_foldExponent` |
| jet exponents of a relation | `jetExponents`, distinct by construction |
| spectral degrees | `Finset.range (spectralBound P + 1)` |
| coefficient vector | `relationCoeff`, nonzero by `exists_relationCoeff_ne_zero` |
| one row of the relation | `eval_familySplit_eq_rectangle` at that row's node |
| the observation | `familyOuterObservation`, continuous and locally surjective |
| the conclusion | `residual_perturbedOuterJet_shape_rigidity` |

The remaining step is the assembly itself: package a nonzero relation as a `ReducedShape` together
with its coefficient vector, check that the matrix relation holds at the chosen nodes because the
differential relation holds on the whole upper half plane, and conclude that the coefficient vector
is zero -- a contradiction.

## Lean progress: a relation carries a reduced shape

`FamilyJetRelationExpansion.lean` now produces, from a relation, the very object the rigidity theorem
quantifies over:

- `foldExponentEquiv`, `foldExponentEquiv_injective`, `prod_foldExponentEquiv` -- the fold of the jet
  variables along an *arbitrary* identification with a single index, so the target index can be put
  in the `Fin (d + 1)` form a shape carries;
- `familyJetVariablesEquiv` -- that identification for a nonempty family: the `(m'+1)(n+1)` jet
  variables become `Fin (m'(n+1) + n + 1)`;
- **`relationShapeOf`** -- the shape of a relation: its spectral degree, its jet depth, and an
  enumeration of the jet exponents that actually occur;
- **`injective_relationShapeOf_exponent`** -- that shape is *reduced*: the exponents are pairwise
  distinct, because they enumerate a finite set and the fold is injective.

So every nonzero relation of a nonempty family yields a `ReducedShape` together with a nonzero
coefficient vector (`exists_relationCoeff_ne_zero`) and the identity
`eval = sum over the rectangle` (`eval_familySplit_eq_rectangle`).  The final assembly is now a
matter of writing the matrix relation: at each admissible node the differential relation holds --
those nodes lie in the upper half plane, which for real translates *is* the family's common domain --
so the coefficient vector is annihilated, and `residual_perturbedOuterJet_shape_rigidity` forces it
to be zero.

## Lean progress: the coefficient vector of a relation

`FamilyJetRelationExpansion.lean`:

- **`relationCoeffVector`** -- the coefficient vector of a relation, indexed exactly by the columns
  of its shape's evaluation matrix, `monomial index x spectral power`;
- **`relationCoeffVector_ne_zero`** -- it is nonzero whenever the relation is.

Combining with what is already proved, a nonzero relation `P` of a nonempty family now supplies, in
one package:

- a `ReducedShape` -- `relationShapeOf P` with `injective_relationShapeOf_exponent`;
- a nonzero vector in that shape's column space -- `relationCoeffVector P`,
  `relationCoeffVector_ne_zero`;
- and the evaluation identity that turns "the relation holds at a point" into "that vector is
  annihilated by the shape's evaluation matrix at that row" -- `eval_familySplit_eq_rectangle`
  together with `prod_foldExponentEquiv`.

`residual_perturbedOuterJet_shape_rigidity` says the third of these forces the second to vanish, for
a residual set of mass parameters.  So (9) is the contradiction between those two facts, and the only
remaining Lean work is to write that contradiction down: expand `Matrix.mulVec` into the rectangle
sum and reindex the monomial sum through `Finset.equivFin`.

## Lean progress: the relation as a matrix row, and a note on how to finish

**`sum_rectangle_eq_eval`** -- a relation, evaluated at a node with prescribed jets, is the sum over
its rectangle of `(node^d * jet monomial in the folded coordinates) * coefficient`.  Each factor in
brackets is *exactly* an entry of `expandedDifferentialEvaluationMatrix` in the corresponding column,
for any identification `e` of the jet variables with a single index.

A note for whoever writes the final composition.  The natural formulation --

  `mulVec (matrix of (relationShapeOf P)) (relationCoeffVector P) b = eval ... P`

-- is *not* the convenient one to prove directly: `simp` unfolding of the `relationShapeOf` structure
projections rewrites the index types of the `Fintype` instances underneath `Finset.univ`, and the
goal stops being type-correct at `instances` transparency.  The safe route is to keep the shape
opaque and do the reindexing separately:

1. `sum_rectangle_eq_eval` gives the identity with the sums over `jetExponents P` and
   `Finset.range (spectralBound P + 1)` -- no structure projections, no `Fintype` instances;
2. convert `∑ i : Fin (jetExponents P).card` to `∑ a ∈ jetExponents P` with
   `Equiv.sum_comp (jetExponents P).equivFin.symm` and `Finset.sum_coe_sort`, and
   `∑ d : Fin (q+1)` to `∑ d ∈ Finset.range (q+1)` with `Fin.sum_univ_eq_sum_range`, *as separate
   rewrites on the matrix side*;
3. only then match the two, using `expandedDifferentialEvaluationMatrix_apply` to expose the entry.

Keeping steps 1 and 2 apart is what avoids the instance mismatch.

## Lean progress: a relation IS a matrix row

The route recorded in the previous entry works.

- **`sum_fin_card_prod_eq`** -- reindexing a rectangle sum: a sum over `Fin s.card × Fin (q+1)` with
  the first coordinate read through the canonical enumeration of a finite set is the double sum over
  that set and the range of degrees.  Stated with no structure projections, so the `Fintype`
  instances on the two sides stay aligned;
- **`mulVec_relationCoeffVector_eq_eval`** --

    `mulVec (expanded evaluation matrix of relationShapeOf P) (relationCoeffVector P) b
       = eval (node z_b, jets y_b) P`.

  A differential relation *is* the evaluation matrix applied to its own coefficient vector, row by
  row.

Combined with `relationCoeffVector_ne_zero` this says: a nonzero relation holding at a packet of
nodes produces a *nonzero* vector in the kernel of that shape's evaluation matrix at those nodes.
And `residual_perturbedOuterJet_shape_rigidity` says that kernel is trivial for a residual set of mass
parameters.  Claim (9) is exactly the collision of those two statements.

The last matching left is notational: the observation `familyOuterObservation` folds the (member,
order) jet index with `sigmaJetIndexEquiv`, while the relation side folds it with
`familyJetVariablesEquiv`; both are built from `finProdFinEquiv`, and the composition only needs them
to be the same identification.

## Lean progress: the algebraic side of (9) is closed

**`eq_zero_of_mulVec_rigid`** -- if a relation holds at a packet of nodes and the only vector
annihilated by its shape's evaluation matrix there is zero, then the relation itself is zero.

This is the whole algebraic half of the card's transversality argument, in one statement.  Its two
hypotheses are exactly what the two other halves supply:

- `hrel` -- the differential relation holds at each node, which is what
  `FamilyDifferentiallyAlgebraicOn` gives on a domain containing them;
- `hrigid` -- the evaluation matrix has trivial kernel there, which is
  `residual_perturbedOuterJet_shape_rigidity` for a residual set of mass parameters.

So the card's residual theorem (9) is now the composition of three named theorems.  All that is left
is to write that composition: instantiate `hrigid` from the rigidity theorem (matching the two folds
of the jet index, both built from `finProdFinEquiv`), and instantiate `hrel` from the definition of
`FamilyDifferentiallyAlgebraicOn` at the admissible nodes, which lie in the upper half plane -- the
common domain of a family of *real* translates.

## Lean progress: from a differential relation to the matrix, in one step

- `familyJetVec_eq_sumElim` -- the jet vector of a family is the spectral coordinate together with
  the jets, as a `Sum.elim`;
- **`eq_zero_of_rigid_of_relation`** -- if a differential relation of the family holds on a set
  containing a node packet, and the evaluation matrix of its shape has trivial kernel at that packet
  with the *actual* jets of the family, then the relation is zero.

This is the statement (9) reduces to, with the analytic content entirely isolated in the kernel
hypothesis.  Reading it against the transversality layer:

- the node packet is `nodeOf S` from `exists_upper_injective_nodes_shapeDeterminant_ne_zero`, whose
  nodes lie in the upper half plane -- and for a family of *real* translates that is the common
  domain, so `hznodes` holds;
- the jets appearing in the matrix are the outer jets of the family at those nodes, which is
  `familyOuterObservation`;
- the trivial kernel is `residual_perturbedOuterJet_shape_rigidity`.

Only the identification of the two jet folds is still to be written down; both are `finProdFinEquiv`
composed with a `finCongr`.

## Lean progress: the two folds are now the same fold

`sigmaJetIndexEquiv`, `sigmaJetHomeomorph`, `locallySurjectiveObservation_reindex` and
`familyOuterObservation` were generalised to fold into an *arbitrary* target `Fin D` given
`r * (d + 1) = D`, exactly as `foldExponentEquiv` already did on the relation side.

That removes the last structural mismatch: the observation and the relation now fold the
(member, order) jet index through the same `finProdFinEquiv` composed with a `finCongr`, into the same
`Fin D`.  Taking `D = (relationShapeOf P).depthPred + 1` makes the jet coordinates of
`familyOuterObservation` and the jet argument of `eq_zero_of_rigid_of_relation` the same type and the
same function.

Everything (9) needs is now proved and typechecks against everything else:

- `eq_zero_of_rigid_of_relation` -- a relation dies where the evaluation matrix is rigid;
- `residual_perturbedOuterJet_shape_rigidity` -- the matrix is rigid, at admissible nodes above the
  axis, for a residual set of mass parameters, *with the fixed carrier included*;
- `continuous_familyOuterObservation`, `locallySurjective_familyOuterObservation` -- the observation
  those two share is continuous and locally surjective.

## Lean progress: the jets of a translate

- `iteratedDeriv_translate` -- the jets of `w |-> F(w + c)` at `z` are the jets of `F` at `z + c`;
- **`familyJet_translate`** -- hence the jets of a family of real translates, evaluated at a packet of
  points, are the jets of the single function at the *combined nodes* `z_b + t_j`.

This is the identity that lets the relation side and the observation side speak about the same
numbers: `eq_zero_of_rigid_of_relation` reads the jets of the translated family at the evaluation
points, while `familyOuterObservation` produces the jets of the outer function at the combined
nodes, and the two are equal term by term.

With this every ingredient of (9) is proved, in matching coordinates:

| ingredient | theorem |
|---|---|
| relation dies where the matrix is rigid | `eq_zero_of_rigid_of_relation` |
| the matrix is rigid on a residual set | `residual_perturbedOuterJet_shape_rigidity` |
| observation is continuous and locally surjective | `continuous_familyOuterObservation`, `locallySurjective_familyOuterObservation` |
| jets of translates = jets at combined nodes | `familyJet_translate` |
| the fixed carrier only translates the packet | `LocallySurjectiveObservation.add_const` |
| admissible nodes lie above the axis | `exists_upper_injective_nodes_shapeDeterminant_ne_zero` |
| real translates keep the common domain | `im_combinedNodes` |

## Lean progress: residual rigidity for the translated family

`FamilyOuterObservation.lean`:

- `FamilyShape m' n` -- the reduced shapes whose jet depth is that of a family of `m'+1` translates
  differentiated to order `n`, with `familyShape_mul` supplying the fold identity
  `(m'+1)(n+1) = depthPred + 1` *as a proof rather than a cast*.  Restricting the index this way is
  what makes the family observation available for every shape in it; shapes of other depths carry no
  relation of this family;
- **`residual_familyOuterJet_rigidity`** -- for a residual set of mass parameters, at the given node
  packets, the only coefficient vector annihilated by the evaluation matrix of any shape of the
  family's depth is zero, *with the fixed carrier jets included*.

This is (9) in matrix form for the card's actual family: `m'+1` real translates of the perturbed
outer function, differentiated to any fixed order.  Its hypotheses are the admissible node packets
(`exists_upper_injective_nodes_shapeDeterminant_ne_zero`, whose nodes lie above the axis, hence in
the family's common domain) together with injectivity of the combined nodes.

Composed with `eq_zero_of_rigid_of_relation` this says: on that residual set no nonzero differential
relation of the family exists.  The remaining step is to quantify over the jet depth `n` -- countably
many, so `residual_iInter` again -- and to read the conclusion as
`¬ FamilyDifferentiallyAlgebraicOn`.

## Lean progress: a relation dies against any rigid observation

**`eq_zero_of_relation_of_rigid_jets`** -- a differential relation of the family is zero as soon as
there is an observation of its jets at a node packet inside the domain which the shape's evaluation
matrix reads rigidly.  The observed jets enter as *data* together with the identification `hjets`
saying they are the family's jets at those nodes; that is exactly the form a transversality argument
delivers them in.

Its three hypotheses are now each a theorem of the corpus:

- `hznodes` -- the nodes lie in the domain: they are above the real axis
  (`exists_upper_injective_nodes_shapeDeterminant_ne_zero`), and for real translates that is the
  common domain (`im_combinedNodes`);
- `hjets` -- the observation is the family's jets: `familyJet_translate` plus the definition of the
  perturbed family, the carrier contributing the fixed summand;
- `hrigid` -- rigidity: `residual_familyOuterJet_rigidity`, on a residual set of mass parameters.

(9) is therefore the instantiation of one theorem at data supplied by three others.  Nothing
mathematical is left; what remains is naming the concrete `G_u = S_u + eps A`, checking `hjets` for
it, and quantifying over the countably many jet depths.

## Lean progress: the packet chart computes the actual outer jets

**`chiJetPacket_iteratedDeriv`** -- feeding the jets of `f` at a point to the packet chart returns
the jets of `chi o f` at that point.  Locality in the jet order (`chiJetScalar_congr`) removes the
zero padding introduced by truncation, and `chiJetScalar_iteratedDeriv` identifies the result with
the actual derivatives.

This is the last of the three identities behind the `hjets` hypothesis of
`eq_zero_of_relation_of_rigid_jets`:

1. the observation is the packet chart applied to the Cauchy jets --
   by definition of `familyOuterObservation`;
2. the packet chart applied to the jets of `m_u` gives the jets of `S_u = chi(m_u)` --
   `chiJetPacket_iteratedDeriv`;
3. the jets of the *translates* at the evaluation points are the jets of `S_u` at the combined
   nodes -- `familyJet_translate`;

and the carrier `eps A` contributes the fixed summand, which `LocallySurjectiveObservation.add_const`
already showed is invisible to the argument.

## Lean: claim (9) proved for each tuple of distinct shifts

`PerturbedOuterFamilyFreeness.lean` (wired, axiom-clean) closes the transversality argument:

    residual_not_familyDifferentiallyAlgebraicOn_perturbedOuterOrbit :
      Function.Injective t -> Function.Injective x -> (all k, 0 < eps k) -> Summable eps ->
      ExpSeriesNormallySummable a omega ->
      {u | not FamilyDifferentiallyAlgebraicOn
             (perturbedOuterFamily x eps u c (cexpSeriesCarrier a omega) t) {zeta | 0 < zeta.im}}
        in residual MassParameter

with `dense_...` its density form.  For a fixed tuple `t` of distinct real shifts and an arbitrary
fixed multiple of the exponential carrier, the real translates of `G_u = S_u + eps A` satisfy **no**
nonzero differential relation of any order, for a residual -- hence dense -- set of bounded
exponential mass parameters.

The three missing links were built in this pass:

- `exists_distinctIm_nodes_shapeDeterminant_ne_zero` -- admissible nodes may be taken at pairwise
  distinct heights, since the determinant is a nonzero polynomial and "above the axis at distinct
  heights" is a nonempty open condition;
- `injective_combinedNodes` -- real shifts do not move imaginary parts, so distinct heights plus
  distinct shifts make the combined nodes distinct, which is what the Cauchy-jet spanning lemma
  needs;
- `familyOuterObservation_apply` and `familyOuterObservation_add_carrier_apply` -- the observation of
  the mass parameter *is* the jet packet of the translated perturbed family, via the packet chart
  (`chiJetPacket_iteratedDeriv`), the Cauchy jets at the combined nodes, and the translation identity
  `iteratedDeriv_translate`; the fixed correction contributes a constant vector by
  `iteratedDeriv_add` and `iteratedDeriv_const_mul`.

The relation-to-coefficients half (`eq_zero_of_relation_of_rigid_jets`) and the parameter half
(`residual_familyOuterJet_rigidity`) then meet, and the countably many jet depths are intersected by
`residual_iInter`.

### The remaining quantifier gap, and why it is not cosmetic

The card's (9) asserts **one** comeager set `U_infty` that works for **every** finite tuple of
distinct shifts.  What is proved in Lean is the tuple-wise statement: for each fixed tuple, a
residual set of mass parameters.  The two differ by an uncountable intersection, and that
intersection is exactly what the card's proof buys with its codimension count
(`codim_C >= N-q-R+1`, `N > m+q+R-1`): parametric transversality over a compact shift patch, so that
the bad preimage is *empty* for all shifts in the patch rather than merely for one shift.

Two cheap routes were checked and both fail to close the gap:

- *Identity theorem in the shift.*  For fixed `u` the bad shift tuples form the common zero set of
  the Wronskians of the monomial functions, jointly analytic in `(z, tau)`.  So either every tuple is
  bad -- which the tuple-wise theorem already excludes, since rational tuples are covered -- or the
  bad tuples form a proper analytic subset.  Proper analytic is closed and nowhere dense, not empty.
- *Kuratowski--Ulam.*  Meagre slices give a meagre product and hence meagre slices in the shift for
  comeager many `u`.  Again meagre, not empty.

So the shift-uniform statement needs the genuine codimension input: with `N` evaluation rows the
rank-deficiency locus of the `N x R(q+1)` evaluation matrix has complex codimension
`N - R(q+1) + 1`, and once that exceeds the number of shift parameters a generic mass perturbation
moves the whole shift patch off it at once.  In Lean that means building determinantal codimension
and a parametric-transversality (Thom) statement, neither of which mathlib has.  Recorded as the
open core of (9); everything upstream of it is now formal and unconditional.

## Plan: closing the shift-uniform half of (9) with corpus machinery

The corpus already owns the whole parametric-transversality engine, and it is not restricted to a
single shift tuple:

- `StratifiedParametricAvoidance.compactConfigurationAvoidance_dense_of_finiteRegularStratification`
  -- for finite-dimensional `P`, `H`, `Y`: if `F : P x H -> Y` is smooth, its parameter derivative is
  surjective at every point, the bad set carries a `FiniteRegularStratification` of real codimension
  `c`, and `finrank H < c`, then the parameters avoiding the bad set *for the whole compact patch*
  are dense.  This is Hirsch parametric transversality, and it is the "empty, not merely nowhere
  dense" step that the tuple-wise argument lacks.
- `ProjectiveIncidenceHausdorffDimension`
  `.expandedDifferentialEvaluationRankDefect_finiteRegularStratification_unconditional` -- the
  evaluation rank-defect locus has real codimension `2*(card row - card(kappa x Fin(q+1)) - q + 1)`,
  unconditionally, given injective nodes and injective exponents.  The row count is ours to choose,
  so `finrank H < c` is arranged by taking enough evaluation points.
- `CompactConfigurationBaire.globalConfigurationAvoidance_dense_residual_of_sigmaCompact` and
  `.countablePattern_globalConfigurationAvoidance_dense_residual` -- openness by the tube lemma plus
  sigma-compact exhaustion turn patchwise density into one dense residual set good for *every* shift.

That is exactly how `herglotz_fullTranslationCauchyFamilyFreeness_denseResidual` and
`outerCauchy_fullTranslationFreeness_denseResidual` are proved, so the `eps = 0` case of (9) is
already shift-uniform in the corpus.

### Why the carrier cannot be routed through the existing statements

Two routes were examined and rejected:

- *Shear gauge.*  `not_familyDifferentiallyAlgebraicOn_shear` reduces freeness of `S_i + eps A_i` to
  freeness of the **doubled** family `{S_i} u {A_i}`.  That is joint independence over the field
  generated by the carrier's translates, which is strictly more than the card proves, and it is not
  obtainable from the corpus engine: the parameter cannot move the carrier block, so the parameter
  derivative is not surjective onto the joint jet space.  This is not a formalization artefact --
  joint freeness genuinely needs the carrier family's own independence as an input.
- *Inner background.*  The corpus's `actualNevanlinnaExpandedPacketValue` already carries a fixed
  additive background `m0`, but it is added **before** the Cayley chart, whereas the card's carrier is
  added after it, and no inner background reproduces `chi(m_u) + eps A`.

The card's own argument is the third route and the correct one: run the transversality with the
observation `chi-chart(jets of m_u at the shifted nodes) + carrier jets`.  A fixed additive vector
does not disturb the parameter derivative, which is the content of
`LocallySurjectiveObservation.add_const` in the tuple-wise layer.

### What must be built

The engine wants the *derivative* of the observation to be surjective, not merely the map to be open.
The observation is `chart o (affine in the masses)`, so by the chain rule it suffices that the Cayley
jet chart has surjective derivative.  Cheapest unconditional route: an explicit smooth right inverse.

1. `logJetScalar` -- the jets of a logarithm, by the triangular recursion
   `L(w)_{k+1} = (w_{k+1} - sum_{i=1..k} C(k,i) w_i L(w)_{k-i+1}) / w_0`, with
   `expJetScalar (logJetScalar w) = w` whenever `w_0 /= 0` (strong induction on the corpus's own
   recursion for `expJetScalar`).
2. The chart inverse `chiInvJetPacket` -- compose the affine inverses, the corpus's involution
   `invJetScalar_invJetScalar`, and `logJetScalar`; then `chiJetPacket o chiInvJetPacket = id`.
3. Smoothness of `chiJetPacket` and of the inverse, hence `Surjective (fderiv R (chiJetPacket n) y)`
   at every `y` with `y 0 + i /= 0`.
4. The parameter derivative of the discrete mass jets: linear in the masses, surjective by the
   corpus's Cauchy jet controllability.
5. Instantiate the avoidance engine with `P` = finitely many masses, `H` = the shift tuples,
   `Y` = the jet packet, `bad` = the rank-defect locus, then globalize and transfer density from the
   finite-dimensional mass slice back to the bounded exponential parameter.
6. Feed the resulting all-shift full-rank witness into `eq_zero_of_relation_of_rigid_jets`, which is
   already proved, to get `not FamilyDifferentiallyAlgebraicOn` for every tuple of distinct shifts at
   one residual set of mass parameters.

## Lean progress: the Cayley jet chart is a submersion

Step 1--3 of the shift-uniform plan are built (four modules, wired, axiom-clean):

- `JetMapSmoothness.lean` -- the exponential, affine and reciprocal jet recursions carry a smooth
  family of jet packets to a smooth family, by induction on the jet order; hence
  `contDiffOn_chiJetPacket`, the Cayley outer packet chart is `C^inf` off the polar locus.  The
  reciprocal case needed the recursion `invJetScalar_eq` extracted from `triangularSolve_eq`.
- `ExponentialJetInverseSmoothness.lean` -- the inverse exponential jet map is smooth where its
  branch is: `expJetTail_eq` writes the back-substitution with the diagonal slot already zeroed, so
  the induction only ever sees strictly earlier unknowns.
- `CayleyJetChartSubmersion.lean` -- `chiJetInv`, the explicit local inverse (undo the exponential
  through `expJetInv`, undo the outer affine map, invert, undo the inner affine map), with
  `chiJetScalar_chiJetInv` proving it is a right inverse.  The corpus's `invJetScalar_invJetScalar`
  (the reciprocal jet map is an involution) and `affJetScalar_affJetScalar` did the algebra.
- `CayleyJetPacketSubmersion.lean` -- packet level: `chiJetInvPacket_chiJetPacket` and
  `chiJetPacket_chiJetInvPacket` are the two inversion identities, and

      surjective_fderiv_chiJetPacket :
        y 0 + I /= 0 -> Function.Surjective (fderiv R (chiJetPacket n) y)

  because a smooth right inverse forces the derivative onto.

This is exactly the input `StratifiedParametricAvoidance` needs and that openness could not supply:
an open map may still have degenerate derivative.  The chart's base point is
`chiJetBase`, the Möbius stage's value, and `chiJetBase_ne_one` records that it never hits the pole
of the inverse Möbius map, which is what makes the branch inverse defined on a neighbourhood.

Remaining: steps 4--6 -- the parameter derivative of the discrete mass jets, the instantiation of
`compactConfigurationAvoidance_dense_of_finiteRegularStratification` with `P` = finitely many masses
and `H` = the shift tuples, and the descent through `eq_zero_of_relation_of_rigid_jets`.

## Lean progress: joint smoothness in (masses, shifts), and the probe design

`ShiftedMassJetSmoothness.lean` (wired, axiom-clean) gives step 4's analytic half:

    contDiff_shiftedMassJetPacket :
      ContDiff R top (fun p : (Fin K -> R) x (Fin r -> R) =>
        discreteJetPacket (combinedNodes z p.2) ord x (perturbedWeight a p.1 w))

Two facts make it work.  `discreteJetPacket_perturbedWeight_sub` splits the packet affinely along
the mass columns, so the dependence is one fixed analytic term at a translated node plus finitely
many explicit rational terms; and a *real* translation never moves a node onto the real axis, so the
smoothness is global in the shift tuple -- no domain restriction is needed.  The analytic half used
`analyticOnNhd_iteratedDeriv` (already corpus-owned, in `UpperEndPrimeLogJets`).

### The probe: why the parameter must be coordinate-wise, and what supplies it

The engine wants the parameter derivative surjective at **every** parameter point, not just at the
base point.  Two consequences fix the design:

- The mass parametrization must keep the masses positive for every parameter value, otherwise the
  zeroth jets can leave the closed upper half plane and the Cayley chart's polar locus is hit, so
  `F` is not globally smooth.  Exponential (or any positive) rescaling does this.
- The derivative must have parameter-independent image.  For a coordinate-wise rescaling the
  derivative is a *positive diagonal* times the mass columns, so its image is the span of the
  columns at every parameter value.  This is why the probe must be a finite set of **atoms**, not an
  arbitrary finitely generated subspace of the bounded-parameter space.

The remaining obstacle is that one fixed finite atom set must span at *every* shift in a compact
patch.  The corpus already owns the abstract solution:

    CompactUniformFiniteProbe.exists_local_finiteProbe_of_continuous_surjectiveControl
    CompactUniformFiniteProbe.compact_surjectiveControls_have_uniform_finiteProbe

-- a continuous family of surjective controls into a fixed finite-dimensional target admits one
finitely generated probe that stays surjective over the whole compact patch, by a determinant
neighbourhood plus a finite subcover.  Instantiated with the domain `Fin m -> R` of finitely many
atom coefficients, it yields exactly the uniform finite atom set.  This is the same device the
corpus uses in `CompactNevanlinnaUniformProbe` for the Nevanlinna carrier.

Next: the uniform spanning atom family, then `hparameter`, then the instantiation of
`compactConfigurationAvoidance_dense_of_finiteRegularStratification` with `P` = the atom
coefficients, `H` = the shift tuples, `bad` = the rank-defect locus (stratified with real
codimension `2*(rows - cols - q + 1)`, so `hdim` is arranged by taking enough evaluation rows).

## Lean progress: one finite atom family for a whole compact shift patch

`UniformSpanningAtoms.lean` (wired, axiom-clean) removes the obstacle recorded above:

    exists_uniform_spanning_atoms :
      (col : N -> H -> Y) -> (forall n, Continuous (col n)) -> IsCompact K ->
      (forall h in K, span R (range fun n => col n h) = top) ->
      exists (M : N) (a : Fin M -> N), forall h in K,
        span R (range fun l => col (a l) h) = top

Two steps.  `exists_finite_spanning_subfamily`: a spanning column system spans with finitely many of
its columns, because the target is finite dimensional, so a finite generating set of the target is
covered by finitely many finite subsets of the column range
(`Submodule.mem_span_finite_of_mem_span`).  Then the corpus's
`exists_local_finiteProbe_of_continuous_surjectiveControl` -- whose neighbourhood comes from a
determinant -- makes spanning by a *fixed* finite family an open condition, and compactness replaces
the local families by their union.

The bridge object is `columnControl`, the continuous linear map sending real coefficients to the
corresponding combination of finitely many columns, with `surjective_columnControl_iff` identifying
its surjectivity with spanning and `continuous_columnControl` giving continuity in the patch
parameter (through `continuous_clm_apply`, valid since the coefficient space is finite dimensional).

What remains for (9) shift-uniform: instantiate `col` with the mass columns
`massJetColumn (combinedNodes z t) ord x w n` -- continuous in `t` by
`contDiff_massJetColumn` -- verify the spanning hypothesis from
`cauchyJetRealLinearCombination_surjective`, then read off `hparameter` (the parameter derivative is
a positive diagonal times these columns) and feed
`compactConfigurationAvoidance_dense_of_finiteRegularStratification`.

## Lean progress: the mass parameter is a submersion, uniformly in the shift

`ShiftedMassJetSubmersion.lean` (wired, axiom-clean) finishes step 4:

    hasFDerivAt_shiftedMassJetPacket -- the parameter derivative is
      sum_k (exp (s0 k) . proj k) .smulRight (massJetColumn (combinedNodes z t) ord x w (a k))

    surjective_fderiv_shiftedMassJetPacket :
      span R (range fun k => massJetColumn (combinedNodes z t) ord x w (a k)) = top ->
      Function.Surjective (fderiv R (fun s => shiftedMassJetPacket z ord x w a (s, t)) s0)

    exists_uniform_massJet_atoms :
      IsCompact Kset -> (forall t in Kset, Function.Injective t) ->
      exists (K : N) (a : Fin K -> N), forall t in Kset,
        span R (range fun l => massJetColumn (combinedNodes z t) ord x w (a l)) = top

The derivative is a *positive diagonal* times the mass columns -- the exponential factors never
vanish -- so its image is the column span at every parameter value, which is exactly what the
avoidance engine's `hparameter` demands (surjectivity at all `p`, not just at the base point).  The
uniform atom family comes from `exists_uniform_spanning_atoms` fed with the corpus's
`span_range_massJetColumn_eq_top`, whose hypothesis "the combined nodes are distinct and above the
axis" is supplied by `injective_combinedNodes` -- i.e. by distinct heights plus distinct shifts.

Steps 1--4 of the shift-uniform plan are now complete.  What is left is bookkeeping of a single
instantiation:

- compose the chart with the mass jets: `F (s, t) := foldedChart (shiftedMassJetPacket z ord x w a
  (s, t)) + carrier t`, smooth by `contDiffOn_chiJetPacket` and `contDiff_shiftedMassJetPacket`,
  with surjective parameter derivative by the chain rule from
  `surjective_fderiv_chiJetPacket` and `surjective_fderiv_shiftedMassJetPacket`;
- feed `compactConfigurationAvoidance_dense_of_finiteRegularStratification` with
  `bad = expandedDifferentialEvaluationRankDefect` and its unconditional stratification, choosing
  enough evaluation rows that `finrank R (Fin r -> R) = r` is below the codimension;
- globalize over the shift space by `globalConfigurationAvoidance_dense_residual_of_sigmaCompact`,
  transfer density from the finite atom slice back to the bounded exponential parameter, and descend
  through `eq_zero_of_relation_of_rigid_jets` (already proved, and already general in the row type).

## Lean progress: the observation the engine sees is smooth and a submersion

Two modules (wired, axiom-clean) assemble the observation `F (s, t)`:

- `OuterJetSigmaSubmersion.lean` -- the multi-node chart.  The branch inverses at the nodes assemble
  to `outerJetSigmaInv`, a smooth right inverse of `outerJetSigma` on the open set where every node
  slice lies in the target of its own branch inverse, giving

      surjective_fderiv_outerJetSigma :
        y in outerJetSigmaDomain m -> Function.Surjective (fderiv R (outerJetSigma m) y)

  Both directions are smooth because a node slice is a linear coordinate restriction and the
  one-node results transport through it.
- `OuterShiftObservation.lean` -- the observation itself,

      outerShiftObservation z d x w a carrier (s, t)
        = outerJetSigma (shiftedMassJetPacket z .. x w a (s, t)) + carrier t

  with `contDiffOn_outerShiftObservation` (smooth on `univ x U`) and

      surjective_fderiv_param_outerShiftObservation :
        span of the mass columns at t = top ->
        Function.Surjective (fderiv R (fun s => outerShiftObservation .. (s, t)) s0)

  by the chain rule from the two submersions.  The chart is defined along the whole parameter space
  because a nonnegative discrete mass has jets in the chart domain
  (`discreteJetPacket_zero_add_I_ne_zero`), and the fixed carrier is invisible to the derivative.

Step 5 of the plan is therefore reduced to bookkeeping: feed
`compactConfigurationAvoidance_dense_of_finiteRegularStratification` with this `F`, with
`bad` the preimage of `expandedDifferentialEvaluationRankDefect` under the fold
`sigmaJetIndexEquiv` -- whose stratification transports by
`FiniteRegularStratification.image_continuousLinearEquiv` -- and `hdim` arranged by taking more
evaluation rows than `r + card(monomials) + degree`.

## Lean: the avoidance engine instantiated, and a hypothesis that was too strong

`OuterShiftAvoidance.lean` instantiates the corpus's parametric transversality engine at the shifted
outer observation:

    dense_avoidance_outerShiftObservation :
      Function.Injective z -> (forall b, 0 < (z b).im) -> r * (d+1) = D ->
      Function.Injective exponent ->
      card (kappa x Fin (q+1)) + q < card row ->
      r < 2 * (card row - card (kappa x Fin (q+1)) - q + 1) ->
      (forall t in Kset, the mass columns at t span) ->
      Dense (compactConfigurationAvoidance (outerShiftObservation z d x w a carrier)
              (outerShiftBad row r d D q hD z exponent) Kset)

Three supporting pieces:

- `sigmaJetCLE` -- the fold `sigmaJetIndexEquiv` as a *continuous linear* equivalence, so the
  rank-defect locus can be read in the sigma-indexed jet coordinates;
- `outerShiftBad_finiteRegularStratification` -- the transported locus is still stratified, by
  `FiniteRegularStratification.image_continuousLinearEquiv` on top of the corpus's unconditional
  codimension `2 (rows - columns - degree + 1)`;
- `isOpen_setOf_span_eq_top` -- spanning by a fixed finite family is an open condition, which is what
  supplies the engine's open `U` around the compact shift patch (the engine wants the parameter
  derivative surjective at *every* shift of `U`, not only on the patch).

Note the codimension hypothesis is now literally the card's inequality `N > m + q + R - 1`: `r`, the
number of shift parameters, must be below twice the row surplus.

### An over-strong hypothesis in the corpus engine

`StratifiedParametricAvoidance` stated the family's smoothness as `ContDiffOn R top F`, where `top`
in `WithTop N-infinity` is **real-analyticity**, not `C^infinity`.  Its proof uses only
`differentiableAt` and `continuousAt` of `F`, so the hypothesis was weakened to
`ContDiffOn R (top : N-infinity)` -- genuine `C^infinity`.  The only other caller passes its own
`omega`-hypothesis through `of_le`, so nothing downstream weakens.  Without this the whole
observation would have had to be proved real-analytic, which the Cayley chart and the exponential
mass parametrization make far more expensive than they need to be.

## Lean: one residual set of mass parameters for EVERY tuple of distinct shifts

This is the shift-uniform step the tuple-wise argument could not reach.  Two modules (wired,
axiom-clean):

- `MassShiftObservationContinuity.lean` -- joint continuity in `(u, t)`.  The jets are a weighted
  kernel series, and a *real* translation does not move the imaginary part of a node, so the kernel
  bound `(|Im z_b|^-1)^(k+1)` is uniform in the shift; `continuousOn_tsum` on
  `ball u_0 1 x univ` then gives continuity in both variables at once.  Also
  `massShiftObservation_pertParameter`: a finitely supported perturbation of the bounded parameter is
  exactly an exponential rescaling of finitely many masses, which is what links the
  finite-dimensional slice to the infinite-dimensional parameter.
- `MassShiftGlobalAvoidance.lean`:

      residual_globalAvoidance_massShift :
        {u : MassParameter | forall tau : RealShiftConfiguration r,
            massShiftObservation z d x eps carrier (u, tau.1)
              not-in outerShiftBad row r d D q hD z exponent}
          in residual MassParameter

  Patchwise density transfers from the atom slice (the perturbation's sup norm is the size of the
  rescaling, `norm_pertParameter_le`), joint continuity makes patchwise avoidance open by the tube
  lemma, the collision-free real shift tuples are sigma-compact
  (`realShiftConfigurationSigmaCompactSpace`, an open subset of `R^r`), and Baire does the rest.

So for a residual set of bounded exponential mass parameters, the expanded evaluation matrix has
full column rank at **every** tuple of distinct real shifts -- not one tuple at a time.  This is the
statement whose absence was recorded above as the open core of (9).

What remains is the descent: read "full rank at every shift" as "no nonzero differential relation",
via `eq_zero_of_relation_of_rigid_jets` (already proved, already general in the row type), and
intersect over the countably many relation shapes with `residual_iInter`.

## Lean: the descent interface, and the data it consumes

Two modules (wired, axiom-clean) turn the shift-uniform avoidance statement into the form a
differential relation is written in:

- `MassShiftFoldedObservation.lean` -- the fold is the same map in both coordinate systems
  (`sigmaJetCLE_apply`), so

      fold_massShiftObservation :
        sigmaJetCLE (massShiftObservation z d x eps carrier (u, t))
          = familyOuterObservation r d D h z t x eps u + folded carrier

  and `mulVec_injective_of_notMem_outerShiftBad` reads avoidance of the transported rank defect as
  full column rank of the relation's evaluation matrix.  `eq_zero_of_relation_of_rigid_jets_row`
  is the row-general form of the relation-killing theorem: the row type is arbitrary, so *more*
  evaluation points than columns are allowed, which is exactly what the codimension count needs.
- `ShiftUniformDescentData.lean` -- the explicit data: `gridNodes N`, evaluation points on the
  imaginary axis at integer heights (injective, above the axis, pairwise distinct heights, so
  `injective_combinedNodes` applies at every tuple of distinct shifts), and `sigmaCarrierJets`, the
  carrier's jets in the sigma coordinates, smooth in the shift because the carrier is analytic
  (`contDiff_carrierJet`, on top of `analyticOnNhd_iteratedDeriv`).

The row count is now forced: with `c0 = card(kappa x Fin(q+1)) + q`, taking `N = c0 + r + 1` makes
`hrows` hold and gives codimension `2(r+1) > r`, so the shift space is below the codimension exactly
as the card's `N > m + q + R - 1` requires.

What is left is the final assembly: instantiate at the shape of a given relation, intersect the
residual sets over the countably many shapes, and read the conclusion as
`not FamilyDifferentiallyAlgebraicOn` for every tuple of distinct real shifts.

## Claim (9) is closed, shift-uniformly

`ShiftUniformPerturbedFreeness.lean` (wired, axiom-clean):

    residual_shiftUniform_perturbedOuterOrbit :
      Function.Injective x -> (forall k, 0 < eps k) -> Summable eps ->
      ExpSeriesNormallySummable a omega ->
      {u : MassParameter | forall (m' : N) (t : Fin (m'+1) -> R), Function.Injective t ->
          not FamilyDifferentiallyAlgebraicOn
            (perturbedOuterFamily x eps u c (cexpSeriesCarrier a omega) t) {zeta | 0 < zeta.im}}
        in residual MassParameter

with `dense_shiftUniform_perturbedOuterOrbit` its density form.  **One** residual set of bounded
exponential mass parameters, good for **every** finite tuple of distinct real shifts at once -- the
card's `U_infty`.  This closes the quantifier gap recorded earlier as the open core of (9).

The final assembly:

- `descentRowCount S = card(kappa x Fin(q+1)) + q + (m'+1) + 1` -- the row count forced by the two
  hypotheses of the engine, giving codimension `2(m'+3)`, comfortably above the `m'+1` shift
  parameters;
- `descentGood` and `residual_descentGood` -- the residual set attached to one shape, from
  `residual_globalAvoidance_massShift` at `gridNodes`;
- `eq_zero_of_relation_of_descentGood` -- the descent at one shape: avoidance gives full column rank
  (`mulVec_injective_of_notMem_outerShiftBad`), the observation is the family's jets
  (`familyOuterObservation_add_carrier_apply` with `sigmaCarrierJets_fold`), and
  `eq_zero_of_relation_of_rigid_jets_row` kills the relation;
- `shiftUniformGood` -- the intersection over `DescentIndex = Sigma m' n, FamilyShape m' n`, which is
  countable, so `residual_iInter` applies.

Every step is unconditional; the only axioms are `propext`, `Classical.choice`, `Quot.sound`.

## Claim (1) is closed too

With (9) shift-uniform, the power gauge closes (1) outright.
`ShiftUniformPowerFreeness.lean` (wired, axiom-clean):

    residual_shiftUniform_perturbedOuterOrbit_pow :
      {u : MassParameter | forall N /= 0, forall (m' : N) (t : Fin (m'+1) -> R),
          Function.Injective t -> not FamilyDifferentiallyAlgebraicOn
            (fun i w => perturbedOuterFamily x eps u c (cexpSeriesCarrier a omega) t i w ^ N)
            {zeta | 0 < zeta.im}}
        in residual MassParameter

`not_familyDifferentiallyAlgebraicOn_pow` supplies the reduction -- a function is algebraic over any
nonzero power, so adjoining the roots cannot raise the differential transcendence degree -- and its
smoothness hypothesis is `contDiffAt_perturbedOuterFamily`, assembled from
`contDiffAt_massOuterBackground` and the analyticity of the carrier.  This is the card's
`O_n` statement: for `n >= 1`, every finite set of distinct functions in `O_n` is differentially
algebraically independent, at one residual set of mass parameters.

Only two entries of the status table are not Lean-complete:

- **(2) boundary HT** -- reduced to Ostrowski's hypertranscendence theorem for generalized Dirichlet
  series by `not_differentiallyAlgebraicOn_pow`; the reduction is formal, the external theorem is
  not formalized.
- **Ostrowski** itself -- imported.

## Claim (2): what is actually left, and the start of it

With (1) and (9) closed, the only card entry that is not Lean-complete is (2), and its content is
exactly Ostrowski's theorem: the exponential carrier `A_lambda = sum a_n lambda_n e^{i omega_n z}`
with rationally independent frequencies is hypertranscendental.  The card's own step
(`b_lambda = c + eps A_lambda`, so `b_lambda` is HT iff `A_lambda` is, and powers by
`not_differentiallyAlgebraicOn_pow`) is already formal; the classical theorem is not.

The corpus already owns most of the analytic side of a Bohr-theoretic proof:
`isBohrAlmostPeriodic_expSeriesCarrier`, `bohrCoefficient_expSeriesCarrier`,
`RationallyIndependentSequence`, `characterDetuning_eq_zero_iff`.  What it does not own is the
extraction of *polynomial* coefficients: a differential relation has coefficients in `C[z]`, and the
Bohr mean of `p(t) e^{i nu t}` diverges for `deg p >= 1`.  The fix is the standard rescaled mean:
divide by `T^d` to read off the leading coefficient of the polynomial attached to a frequency, then
induct on the degree.

Started, and now formal:

- `MonomialFrequencySeparation.lean` -- `monomialFrequency_injective`: for rationally independent
  frequencies distinct monomials in the characters have distinct frequencies, because their
  difference is an integer character whose detuning cannot vanish
  (`characterDetuning_eq_zero_iff`).  This is the combinatorial half of the argument: it is what
  lets a single Fourier coefficient of a relation see a single monomial.

Remaining for (2): the rescaled-mean extraction of polynomial coefficients, the expansion of a
differential relation into an almost periodic series with polynomial coefficients, and the
conclusion.

## Claim (2): the polynomial-coefficient obstacle is cleared

`PolynomialBohrVanishing.lean` (wired, axiom-clean):

    eq_zero_of_polynomialCombination_bohr :
      (forall d, IsBohrAlmostPeriodic (G d)) -> (forall d, G d bounded) ->
      forall D, (forall t : R, sum_{d <= D} t^d * G d t = 0) -> forall d <= D, G d = 0

This is the step the Bohr mean cannot do.  Dividing the identity by `t^D` leaves the top coefficient
plus terms of size `O(1/t)`, so the top coefficient function tends to zero at `+infinity`; the
corpus's `eq_zero_of_isBohrAlmostPeriodic_of_tendsto_zero` then makes it identically zero, and
downward induction kills the rest.  No mean value, no divergent integral.

With `monomialFrequency_injective` this gives both halves of Ostrowski's argument in the abstract:

- a relation restricted to the real line is `sum_{d} t^d G_d(t) = 0` with each `G_d` an absolutely
  convergent exponential series, hence bounded and almost periodic, so every `G_d` vanishes;
- each `G_d` is a series whose amplitudes are indexed by monomials in the jets, and distinct
  monomials sit at distinct frequencies, so `bohrCoefficient_expSeriesCarrier` reads off one
  monomial's coefficient at a time.

Remaining for (2): the expansion itself -- writing the jets of `cexpSeriesCarrier` and their
monomials as exponential series with the amplitudes indexed by monomials -- and the bookkeeping that
turns "every amplitude vanishes" into "the relation polynomial is zero".

## Claim (2): exponential series are closed under products and differentiation

`ExponentialSeriesAlgebra.lean` (wired, axiom-clean) supplies the expansion algebra:

- `expSeriesCarrier_mul` -- a product of two absolutely convergent exponential series is an
  exponential series indexed by the pairs, with the frequencies **added** (Cauchy product of
  absolutely convergent series, plus `expChar_add`);
- `ExpSeriesNormallySummable.deriv` -- normal summability survives differentiation: the extra factor
  `|omega_i|` is absorbed by `|x| <= exp |x|` into the next exponential weight, so the amplitudes
  `a_i * i omega_i` are again normally summable at every radius;
- `deriv_cexpChar` -- the character's derivative.

These are the three facts that turn "a monomial in the jets of a carrier" into "an exponential
series": each jet is a carrier with amplitudes scaled by `(i omega)^k`, and a monomial is a finite
product of carriers, hence a carrier indexed by tuples with frequencies summed.

The pieces of (2) now standing are: the frequency separation
(`monomialFrequency_injective`), the polynomial-coefficient vanishing
(`eq_zero_of_polynomialCombination_bohr`), and this expansion algebra.  What remains is the
assembly -- the termwise derivative of the series itself (`deriv (cexpSeriesCarrier a omega)
= cexpSeriesCarrier (a * i omega) omega`, from the corpus's locally uniform convergence), the
identification of a monomial's amplitude at a given frequency, and the descent from "all amplitudes
vanish" to "the relation is zero".

## Claim (2): termwise differentiation of the carrier

    deriv_cexpSeriesCarrier :
      ExpSeriesNormallySummable a omega ->
      deriv (cexpSeriesCarrier a omega)
        = cexpSeriesCarrier (fun i => a i * (I * omega i)) omega

Termwise differentiation is legitimate because the partial sums converge locally uniformly
(`tendstoLocallyUniformly_cexpSeries`, corpus-owned) and are differentiable, so
`TendstoLocallyUniformlyOn.deriv` transports the convergence to the derivatives; the limit is
identified pointwise against the series of scaled amplitudes, which is summable by
`ExpSeriesNormallySummable.deriv`.

Iterating gives every jet of the carrier as a carrier with amplitudes `a_i (i omega_i)^k`, and
`expSeriesCarrier_mul` then makes every monomial in the jets a carrier indexed by tuples.  Together
with `monomialFrequency_injective` and `eq_zero_of_polynomialCombination_bohr`, the three inputs of
Ostrowski's argument are now all formal.

Remaining: the iterated-derivative form (`iteratedDeriv k` of the carrier), the amplitude of a
monomial at a fixed frequency, and the final descent to `not DifferentiallyAlgebraicOn`.

## Claim (2): jets and monomials are exponential series

`ExponentialSeriesAlgebra.lean` now carries the whole expansion:

    iteratedDeriv_cexpSeriesCarrier :
      iteratedDeriv k (cexpSeriesCarrier a omega)
        = cexpSeriesCarrier (fun i => a i * (I * omega i)^k) omega

    prod_expSeriesCarrier :
      prod_j expSeriesCarrier (b j) omega t
        = expSeriesCarrier (fun n : Fin m -> iota => prod_j b j (n j))
            (fun n => sum_j omega (n j)) t

with `summable_norm_prod_expSeries` and `ExpSeriesNormallySummable.iteratedDeriv` the summability
side conditions.  So a monomial in the jets of a carrier is a carrier indexed by *tuples* of
indices, with amplitude the product of `a_{n_j} (i omega_{n_j})^{k_j}` and frequency
`sum_j omega_{n_j}` -- and by `monomialFrequency_injective` that frequency determines the multiset
of indices used.

Two traps worth recording: `Summable.mul_norm` and `Summable.mul_of_nonneg` both stall on a
hypothesis whose statement is not beta reduced (`(fun j => b j.succ) j`), and unfolding
`Fin.consEquiv` inside `simp` is a whnf timeout -- an explicit `rfl` lemma for its application plus
`Fin.cons_zero`/`Fin.cons_succ` is instant.

Everything for (2) is now in place except the final assembly.

## Claim (2): reading a monomial's amplitude off a frequency

`ExponentialSeriesFiberwise.lean` (wired, axiom-clean) supplies the missing extraction step:

    expSeriesCarrier_fiberwise :
      expSeriesCarrier B Omega t = expSeriesCarrier (fiberAmplitude B Omega) id t

    bohrCoefficient_expSeriesCarrier_fiber :
      bohrCoefficient (expSeriesCarrier B Omega) nu = fiberAmplitude B Omega nu

A monomial's expansion is indexed by *tuples*, and different tuples share a frequency, so the
corpus's `bohrCoefficient_expSeriesCarrier` -- which needs injective frequencies -- does not apply
directly.  Regrouping by the fibres of the frequency map (`Equiv.sigmaFiberEquiv`, then
`Summable.tsum_sigma`) re-indexes the series by the frequencies themselves, where the frequency map
is the identity and therefore injective.  The Bohr coefficient at `nu` is then exactly the sum of
the amplitudes over the fibre `{j | Omega j = nu}`.

Combined with `monomialFrequency_injective`, the fibre over a frequency of a monomial expansion
consists of the tuples that use one fixed multiset of indices -- so the Bohr coefficient sees one
multiset at a time, which is exactly what Ostrowski's counting argument needs.

## Claim (2): a vanishing series has vanishing amplitudes

    fiberAmplitude_eq_zero_of_expSeriesCarrier_eq_zero :
      Summable (norm . B) -> (forall t, expSeriesCarrier B Omega t = 0) ->
      forall nu, fiberAmplitude B Omega nu = 0

The Bohr coefficient of the zero function is zero (`bohrCoefficient_zero`, on the corpus's
`bohrMean_zero`), and the Bohr coefficient at `nu` is the fibre sum, so a vanishing series has
vanishing fibre sums.  This is the form in which the analytic half hands its conclusion to the
combinatorial half.

The chain for (2) is now: a relation restricted to the real line is
`sum_d t^d G_d(t) = 0` with each `G_d` a carrier ->
`eq_zero_of_polynomialCombination_bohr` kills each `G_d` ->
`fiberAmplitude_eq_zero_of_expSeriesCarrier_eq_zero` kills each fibre sum ->
`monomialFrequency_injective` says a fibre is one multiset of indices.

Left: the bookkeeping that assembles a relation into that shape and reads "all fibre sums vanish"
as "the relation polynomial is zero".

## Claim (2): a fibre is one multiset of indices

`MonomialFrequencySeparation.lean` now carries the tuple side:

    tupleCount n = sum_j single (n j) 1          -- the multiset a tuple uses
    monomialFrequency_tupleCount : monomialFrequency omega (tupleCount n) = sum_j omega (n j)
    tupleCount_eq_of_frequency_eq :
      RationallyIndependentSequence omega -> sum_j omega (n j) = sum_j omega (n' j) ->
      tupleCount n = tupleCount n'

The frequency map is additive (`monomialFrequencyHom`) and sends a single to its frequency, so a
tuple's frequency is the frequency of its multiset; rational independence then makes the multiset a
function of the frequency.  Combined with `bohrCoefficient_expSeriesCarrier_fiber`, one Bohr
coefficient of a monomial expansion sees exactly the tuples that use one fixed multiset -- finitely
many of them, the permutations distributing that multiset over the jet orders.

That is the last structural fact.  The remaining work on (2) is bookkeeping: assemble a relation into
`sum_d t^d G_d(t) = 0` with `G_d` carriers, and read the vanishing of every fibre sum back as
vanishing of the relation's coefficients.

## Claim (2): rational independence gives distinct frequencies

    injective_of_rationallyIndependentSequence :
      RationallyIndependentSequence omega -> Function.Injective omega

If two frequencies coincided, the integer character `single i 1 - single j 1` would have zero
detuning, which `characterDetuning_eq_zero_iff` forbids.  This is the hypothesis every use of
`bohrCoefficient_expSeriesCarrier` needs, and it was previously only available by assumption.

### The remaining combinatorial core of (2), stated exactly

With every structural piece in place, the descent at one degree `d` reads: for every frequency,

    sum over monomials s of degree d, and over tuples n with sum_j omega(n_j) = nu,
      c_s * prod_j a_{n_j} (i omega_{n_j})^{k_j(s)}  =  0.

Rational independence makes the inner condition "the multiset of `n` is fixed", so the identity is a
*symmetric function* identity in the finitely many variables `i omega_{i_1}, ..., i omega_{i_m}`,
with one such identity for every choice of `m` indices with nonvanishing amplitudes.  Since the
amplitude family has infinitely many nonzero terms and the frequencies are distinct, the classical
step is: monomial symmetric functions of distinct exponent partitions are linearly independent, and
a polynomial vanishing at infinitely many points is zero.  That is what is left to formalize.
