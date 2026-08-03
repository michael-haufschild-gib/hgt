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
