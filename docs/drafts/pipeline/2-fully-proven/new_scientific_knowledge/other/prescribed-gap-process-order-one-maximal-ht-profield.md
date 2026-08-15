# Prescribed gap-process law in an order-one maximal-HT profield

- **ID:** `prescribed-gap-process-order-one-maximal-ht-profield`
- **Stage:** 2-fully-proven / needs independent audit
- **Type:** THEOREM (paper) — `[PROVED HERE] [NOVELTY UNVERIFIED]`
- **Lane:** general hypertranscendence; order-one canonical products; zero statistics
- **Statement:** Every stationary ergodic positive gap process of mean one is realized by the
  positive zeros of an even real order-one Laguerre--Polya function whose full complex translation
  family is differentially algebraically independent at every power; the same power profield and
  exactly the same real-zero statistics also contain a representative with an off-real quartet.

## Goal

The arbitrary-divisor HT theorems lose finite order, while rational quartet surgery preserves order
but changes only finitely many zeros.  The missing statistical question is sharper:

> Inside the exact order-one FE/Schwarz cage, does maximal translation HT constrain the asymptotic
> local statistics of the real divisor?

The answer is no.  Shrinking zero-location parameters preserve every finite-block gap statistic but
remain nonzero in the finite coordinate directions used by the Cauchy-jet transversality proof.

## Prescribed stationary gap process

Let `P` be a shift-invariant ergodic Borel probability measure on

`(0,infinity)^N`

whose first coordinate has finite mean one.  Birkhoff's theorem and a countable determining family
of bounded Lipschitz cylinder functions give a `P`-generic sequence

`g=(g_1,g_2,...)`, `g_j>0`,                                   (1)

such that:

1. `N^(-1) sum_(j<=N) g_j ->1`;
2. for every block length `k>=1` and every bounded Lipschitz
   `Phi:(0,infinity)^k -> R`,

   `N^(-1) sum_(j=1)^N Phi(g_j,...,g_(j+k-1))`

   ` -> integral Phi dP_k`,                                  (2)

   where `P_k` is the first-`k` marginal of `P`.

Set `Lambda_1=1` and

`Lambda_(j+1)=Lambda_j+g_j`.                                 (3)

Then `Lambda_j/j->1`.

Choose positive radii `r_j` satisfying

`r_j<2^(-j) min(1,g_(j-1),g_j)/16`,                          (4)

with `g_0=1`.  In particular `r_j->0`.  For

`theta=(theta_j) in ell^infinity(R)`, put

`lambda_j(theta)=Lambda_j+r_j tanh(theta_j)`.                 (5)

The sequence remains strictly increasing.  Indeed,

`lambda_(j+1)-lambda_j`

` =g_j+r_(j+1)tanh(theta_(j+1))-r_j tanh(theta_j)>3g_j/4`.    (6)

Moreover `lambda_j(theta)/j->1`, uniformly in the sense needed for the canonical-product estimates.

## Exact preservation of the gap-process law `[PROVED HERE]`

Let

`d_j(theta)=lambda_(j+1)(theta)-lambda_j(theta)`.

Then

`d_j(theta)-g_j ->0`.                                        (7)

For every fixed block length `k`, the distance between

`(d_j(theta),...,d_(j+k-1)(theta))`

and the corresponding `g`-block tends to zero.  A bounded Lipschitz test changes by a quantity
tending to zero, and its Cesaro mean also tends to zero.  Combining with (2) gives

`N^(-1) sum_(j=1)^N Phi(d_j(theta),...,d_(j+k-1)(theta))`

` -> integral Phi dP_k`                                      (8)

for every `theta`, every `k`, and every bounded Lipschitz `Phi`.

Thus every perturbed divisor has exactly the prescribed stationary finite-block gap law `P`.

Special cases include:

- the clock law (`g_j=1`);
- the Poisson-renewal law (iid exponential gaps of mean one);
- any stationary ergodic Palm gap-process model of intensity one.  In particular, any
  sine-process/GUE target encoded by such a stationary ergodic gap law is admissible.

No random sample is used in the theorem after the generic sequence has been selected; probability
only supplies existence of one deterministic base divisor.

## Order-one even canonical products

Define

`E_theta(z)=prod_(j>=1) (1-z^2/lambda_j(theta)^2)`.            (9)

Because `lambda_j(theta) asymp j`, the product converges normally.  It is a real even entire
function of exact order one, with simple zeros

`{+-lambda_j(theta):j>=1}`.

It belongs to the Laguerre--Polya class.  Its negative logarithmic derivative is

`H_theta(z)=-E_theta'(z)/E_theta(z)`

` =sum_(j>=1) [1/(lambda_j(theta)-z)+1/(-lambda_j(theta)-z)]`. (10)

The function `H_theta` is Herglotz on the upper half-plane and odd under `z |-> -z`.

## Residual maximal complex-translation HT `[PROVED HERE]`

There is a comeager set

`Theta_P subset ell^infinity(R)`

such that, for every `theta in Theta_P`, the full complex translation family

`{H_theta(z+h):h in C}`                                      (11)

is differentially algebraically independent over `C(z)`.

### Proof: shrinking location coordinates still span every finite jet packet

Fix a finite packet of evaluation nodes whose full sign/conjugation orbits are disjoint, and fix a
jet depth.  Differentiate one paired atom in (10) with respect to its location `lambda`.  The
resulting jet column is a rational function of the real parameter `lambda`, with poles only at the
evaluation nodes and their negatives.

Suppose a real-linear functional annihilates the location-variation columns at every
`lambda_j(theta)`.  Adding its conjugate gives a rational function of `lambda` which vanishes at the
infinite unbounded sequence `lambda_j(theta)`.  It is therefore identically zero.  Principal parts
at the separated poles `+-x` force every coefficient of the functional to vanish.  Thus the real
span of all location columns is the complete complex jet space.

The actual parameter derivative is

`partial_(theta_j) lambda_j=r_j sech(theta_j)^2>0`.            (12)

Multiplication of each column by this nonzero scalar does not change its span.  Hence finitely many
theta coordinates give a real jet isomorphism at any prescribed finite packet, despite `r_j->0`.

### Proof: remove every uncountable shift relation

For a fixed finite support of `R` expanded differential monomials and a compact patch of `m`
distinct complex shifts, use `N` separated evaluation rows.  The rank-defect incidence locus has

`codim_C >= N-q-R+1`,                                        (13)

where `q` is the largest polynomial coefficient degree in `z`.  Choose

`N>m+q+R-1`.

Then every Whitney stratum has real codimension greater than the `2m`-dimensional real shift patch.
The finite theta coordinates from the preceding lemma make the universal parameter--shift map a
real submersion.  Parametric transversality therefore makes every bad preimage empty.

Finite-coordinate perturbations can be arbitrarily small in `ell^infinity`; compact-patch
avoidance is open.  Exhaust all complex distinct-shift configuration spaces by countably many
compact patches, and intersect over the countable jet depths and finite monomial supports.  Baire's
theorem yields `Theta_P`.  Clearing rational denominators converts support avoidance into
differential algebraic independence over `C(z)`. `QED`

## Entire-carrier and all-power maximal HT `[PROVED HERE]`

Fix `theta in Theta_P` and write `E=E_theta`, `H=H_theta`.

For every complex shift `h`,

`H(z+h)=-D E(z+h)/E(z+h)`

belongs to the differential field generated by `E(z+h)`.  Therefore differential independence of
the `H` translates forces differential independence of the corresponding `E` translates.

For every `n>=1`, the family

`{E(z+h)^n:h in C}`                                          (14)

is also differentially algebraically independent: adjoining the algebraic `n`-th roots cannot
increase differential transcendence degree.

Define the complete positive-power translation profield

`T_n(E)=C(z)(D^q(E(z+h)^n):h in C,q>=0)`, `n>=1`.             (15)

## Same-profield opposite-divisor theorem `[PROVED HERE]`

Choose `tau in C` with

`Re(tau) Im(tau)!=0`

and put

`Q_tau(z)=(z^2-tau^2)(z^2-conj(tau)^2)`.                     (16)

The polynomial is real and even.  For real `x`,

`Q_tau(x)=|x^2-tau^2|^2>0`,                                  (17)

so it has no real zeros.  Its zeros are exactly the off-real quartet

`{+-tau,+-conj(tau)}`.

Set

`F=Q_tau E`.                                                  (18)

Then:

1. `E` and `F` are real even entire functions of exact order one;
2. `E` has only real zeros, whereas `F` has the designated off-real quartet;
3. their positive real zero sequences are identical, hence both have the complete prescribed gap
   process `P` in the sense of (8);
4. both are hypertranscendental and have maximally independent full complex translation families;
5. for every `n>=1`,

   `T_n(F)=T_n(E)`.                                           (19)

For (19), use

`F(z+h)^n=Q_tau(z+h)^n E(z+h)^n`.

The nonzero polynomial factor and its inverse lie in `C(z)`, so the translated order-zero
generators on either side recover one another; differential closure gives equality.  The HT and
independence assertions follow from the same rational-gauge substitution. `QED`

## Law extracted

**Order-one zero-statistics/HT orthogonality law.**  Exact order one, scalar functional-equation
symmetry, Schwarz reality, the complete stationary local gap process, and maximal differential
freedom of every complex translation packet at every positive power are independent coordinates.

Even after all those data are fixed, one exact profield contains a Laguerre--Polya representative
and a representative violating the real-zero predicate.

## Exact RH-route consequence

In the spectral variable `z`, real zeros correspond to critical-line zeros of the completed
function.  The theorem excludes the following implementations:

1. **Montgomery--Odlyzko / GUE:** maximal HT cannot force one distinguished gap process.  Every
   stationary ergodic local gap law, including clock, Poisson, or any stationary ergodic target
   used to encode sine-process statistics, is compatible with the same strongest translation-HT
   conclusion in the order-one FE cage.
2. **Hilbert--Polya / Connes:** real spectral location plus any prescribed local spectral statistics
   do not arise canonically from the unpointed HT profield.  A distinguished operator/measure is
   additional data.
3. **Li / Weil / de Branges:** even a complete real-zero gap process cannot replace their global
   all-zero positivity or kernel selector.  A finite off-real quartet leaves the entire real gap
   process and profield unchanged.

The full criteria are not refuted.  They use the complete pointed divisor, Euler normalization,
global positivity cone, or actual spectral realization.  What is ruled out is promoting HT plus
asymptotic zero statistics into the missing global selector.

## Attacks and boundaries

1. **This is stronger than prescribing one marginal.**  Every finite consecutive-gap block law is
   retained.
2. **Pair correlation is not separately axiomatized.**  A stationary Palm gap process determines
   the local point configuration through partial sums, but the theorem is stated only in the
   bounded-Lipschitz block language actually proved.
3. **The off-real surgery is finite.**  It suffices to reverse the all-real predicate but does not
   prescribe a positive density of off-real zeros.
4. **The real divisor is not the zeta divisor.**  No Euler product, Riemann--von Mangoldt secondary
   term, or gamma normalization is retained.
5. **Shrinking radii are essential.**  They preserve statistics.  Their nonvanishing, not their
   size, is what preserves finite jet surjectivity.

## Parent-theory and preliminary novelty audit

The imported mechanisms are classical separately:

- existence of deterministic generic sequences for stationary ergodic processes;
- canonical products and Laguerre--Polya theory;
- stability of empirical block laws under coordinatewise `o(1)` perturbations;
- rational finite-divisor gauges.

The candidate-new content, if any, is the simultaneous arbitrary-gap-process realization inside
the exact order-one even canonical-product cone with residual full **complex** translation
differential independence, all-power persistence, and same-profield reversal of the real-zero
predicate.

Targeted searches across prescribed zero spacings, canonical products, Laguerre--Polya functions,
generic Herglotz pole locations, translate independence, and hypertranscendence did not locate this
combined theorem.  Nearby hypertranscendental interpolation results prescribe values and growth,
not a full stationary divisor process plus a maximal translation matroid.  Random-matrix
universality results derive specific gap laws from ensembles and do not address HT orthogonality.

The proof and significance gates pass.  Parent-theory priority remains open because the proof
extends the separately novelty-unverified positive-Herglotz transversality engine.  Scientific
novelty is therefore provisional and the card remains `[NOVELTY UNVERIFIED]` pending specialist
review in differential algebra, entire-function theory, and point-process statistics.

## Lean status

No complete Lean claim is made.  The current tree has finite canonical-product, rational-quartet,
and differential-independence components, but not stationary ergodic generic-sequence selection,
infinite location-parameter Baire transversality, empirical block-law convergence, or the complete
analytic canonical product in one theorem.  Partial formalization would not justify Stage 3.

## Gates

- [x] 0 -> 1: prescribed process and shrinking-location mechanism isolated
- [x] 1 -> 2: complete unconditional paper proof
- [ ] independent audit of shrinking-coordinate transversality and process preservation
- [ ] specialist novelty audit across three parent fields
- [ ] 2 -> 3: complete unconditional theorem formalized in Lean
- [ ] 3 -> 4: publication-ready preprint and independent novelty review

## Cross-references

- `herglotz-full-translation-ht-krein-index-orthogonality.md`: location-jet transversality parent.
- `laguerre-polya-jensen-profield-blindness.md`: fixed-lattice LP/profield bridge.
- `fixed-divisor-maximal-translation-ht-genericity.md`: arbitrary divisors but uncontrolled order.
- `transcendence-implies-gue.md` in `5-failed`: false implication from transcendence to full GUE.

## Log

- 2026-07-11 -- Used an ergodic generic gap sequence and vanishing positive location radii to retain
  every finite-block gap statistic while preserving finite jet surjectivity.
- 2026-07-11 -- Proved residual full complex translation independence, exact order one, all-power
  maximal HT, and a rational-quartet same-profield pair with identical real gap process and opposite
  real-zero predicates.

## 2026-08-15 — the probability half is formalized

The prescribed-process half of the theorem, sections *Prescribed stationary gap process* and *Exact
preservation of the gap-process law*, is now Lean-closed and unconditional.  Every capstone below
reports only `propext`, `Classical.choice`, `Quot.sound`.

**Birkhoff's pointwise ergodic theorem had to be built.**  Mathlib carries `birkhoffSum`,
`birkhoffAverage`, `Ergodic`, and the *mean* ergodic theorem, but not the pointwise one.

- `formal/GaloisForLFunctions/HTGeometry/MaximalErgodicTheorem.lean` proves Garsia's maximal
  ergodic theorem `setIntegral_nonneg_of_maxBirkhoff_pos`: with
  `maxBirkhoff T f N = max (S_0 f, …, S_N f)`, the integral of `f` over `{maxBirkhoff > 0}` is
  nonnegative.  Where the running maximum is positive it is attained at a positive index, so
  `M_N ≤ f + M_N ∘ T` there, while `M_N` vanishes off the set and `∫ M_N ∘ T = ∫ M_N`.
- `formal/GaloisForLFunctions/HTGeometry/BirkhoffPointwise.lean` proves
  `ae_tendsto_birkhoffAverage`.  The proof avoids `limsup` entirely.  The superlevel set of the
  upper limit is realized as

  ```text
  limsupGT T f a = ⋃ (r : ℚ) (_ : a < r), {x | r n < S_n f x for infinitely many n},
  ```

  which is measurable and **exactly** `T`-invariant — the rational cushion absorbs the additive
  defect `S_n f (T x) = S_{n+1} f x − f x`.  Ergodicity makes each such set null or conull, the
  maximal theorem bounds the threshold `sSup {a | μ (limsupGT T f a) = 1}` above by `∫ f`, and the
  same bound applied to `−f` bounds the lower threshold, so both thresholds equal the mean and the
  averages converge.

**Reducing the uncountable family of block observables to a countable one.**
`formal/GaloisForLFunctions/HTGeometry/CountableTestFamily.lean` builds

```text
testFamily E = {clampFun m ψ : m : ℕ, ψ ∈ testDense E} ∪ {bumpFun R : R : ℕ}
```

from a countable dense subset of `C(E, ℝ)` for uniform convergence on compact sets, plus the radial
cut-offs `bumpFun R`.  Its `tendsto_average_of_testFamily` upgrades convergence of the empirical
averages along `testFamily` to convergence for **every** bounded continuous function: the cut-offs
supply the uniform tail control that turns approximation on a ball into approximation everywhere.

**The generic sequence.**
`formal/GaloisForLFunctions/HTGeometry/GenericGapSequence.lean` proves `exists_generic_sequence`:
for a shift-ergodic probability law `P` on `ℕ → ℝ` with integrable, mean-one first coordinate and
almost surely positive coordinates there is a deterministic `g` with `g_j > 0`,
`N⁻¹ ∑_{j<N} g_j → 1`, and, for every block length `k` and every bounded continuous
`Φ : (Fin k → ℝ) → ℝ`,

```text
N⁻¹ ∑_{j<N} Φ (g_j, …, g_{j+k-1}) → ∫ Φ (ω_0, …, ω_{k-1}) dP.
```

This is `(1)`–`(2)`, with bounded continuous in place of bounded Lipschitz.

**The shrinking locations and the preservation law.**
`formal/GaloisForLFunctions/HTGeometry/GapBlockLawStability.lean` defines
`gapPartialSum`, `gapRadius g j = (1/2)^j · min (1, g_{j-1}, g_j) / 16`, and
`gapLocation g θ j = gapPartialSum g j + gapRadius g j · tanh (θ_j)`, and proves `(4)`–`(8)`:

```text
tendsto_gapLocation_diff_sub          d_j(θ) − g_j → 0
gapLocation_strictMono                the locations are strictly increasing
gapLocation_pos                       the locations are positive
tendsto_gapLocation_div               λ_j(θ) / j → 1
tendsto_block_average_of_tendsto_sub  a null perturbation preserves every Lipschitz block average
exists_prescribedGapProcess_locations the assembled statement, for every θ
```

The last is the exact content of `(8)`: for every parameter `θ`, every block length `k` and every
bounded Lipschitz `Φ`, the perturbed gaps have the prescribed limit `∫ Φ dP_k`.

**What remains.**  Only the canonical-product half.  The corpus already owns the complete residual
maximal-translation-freeness engine, but for the *clock* divisor
`movingCanonicalZero θ n = n + 1 + (1/4)·tanh (θ_n)`, with capstone
`movingEvenCanonical_fullTranslationFreeness_denseResidual` over `θ ∈ ℓ^∞(ℝ)`.  Transporting it to
the locations built here requires parameterizing that chain by an arbitrary base sequence and
arbitrary shrinking radii.  The interface actually consumed downstream is small — positivity, strict
monotonicity, injectivity, divergence, the coordinate derivative, positive coordinate speed, square
summability of the reciprocals, and exponent of convergence one — but `SpacedRayNodePacket.lean`
currently derives its row separation from `n + 3/4 < ζ_n < n + 5/4` and must instead *select* a
spaced subsequence, which the divergence of the base supplies.  After that: the rational-quartet
surgery and the all-power profield equality `T_n(F) = T_n(E)`.
