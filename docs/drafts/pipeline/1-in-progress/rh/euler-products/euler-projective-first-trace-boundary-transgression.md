# Euler projective first trace and exponential boundary transgression

- **ID:** `euler-projective-first-trace-boundary-transgression`
- **Stage:** 1-in-progress
- **Type:** `[BRIDGE THEOREM] [OPEN GENERAL-HT TRANSGRESSION] [RH PRESSURE TEST]`
- **Scientific status:** `[EXACT SOURCE WELD] [NOVELTY BEGINS AT TRANSGRESSION] [NOT RH]`
- **Parents:**
  - `../2-fully-proven/new_scientific_knowledge/prime-occupation-polarized-gamma-phase-survival.md`;
  - `../../../3-formalized/new_scientific_knowledge/prime-first-trace-exponential-flat-graph-fracture.md`;
  - `euler-gamma-conormal-markov-dilation-rh.md`;
  - `../../../3-formalized/clock-compass-noncommutative-tomography.md`;
  - `../2-fully-proven/not_new_scientific_knowledge/burnol-copoisson-quotient-bilateral-order-rh-law.md`.

## Exact source weld `[PROVED HERE; PARENT ALGEBRA]`

For a finite prime set `S`, define

```text
Z_S(s)=product_(q in S)(1-q^(-s))^(-1).
```

If `p` is not in `S`, then

```text
Z_(S union {p})(s)/Z_S(s)=(1-p^(-s))^(-1),
1-Z_S(s)/Z_(S union {p})(s)=p^(-s).                       (1)
```

Thus the projective defect of adjoining `p` is independent of the aperture `S`.  The connection
ratios commute around every finite prime square, so the finite connection is flat.

At the first-trace boundary `s=1`, equation `(1)` is exactly

```text
delta_p=1/p.                                              (2)
```

With the reciprocal-log source scale `a_p=1/log p`,

```text
a_p(-log delta_p)=1                                      (3)
```

identically.  The actual-prime Hardy first-trace witness has a perturbed source norm
`a'_p~1/log p` and response norm `b'_p~1/p`; its Lean-formalized grade
`a'_p(-log b'_p)->1` is therefore the stable graph realization of the same projective Euler
character, not an unrelated asymptotic coincidence.

Critical half-density centering gives

```text
chi_p(s)=p^(1/2-s),
chi_p(1-s)=chi_p(s)^(-1).                                 (4)
```

At a critical-Mellin pole `s=rho`, the modulus is

```text
|chi_p(rho)|=p^(1/2-Re(rho)).                             (5)
```

Hence the source character produced by the polarized first-trace completion is exactly the
forward/inverse dilation character already occurring in the Burnol and Deninger purity
selectors.

## Hostile correction: `(1)` is not curvature

Equation `(1)` is elementary Euler-factor algebra.  At every finite aperture its connection is
flat and explicitly gauged by `Z_S`.  Treating `chi_p` itself as a graviton polarization would be
false: the ordinary Riemann principal symbol kills pure gauge, and this finite connection is pure
gauge.

Novelty can begin only after cofinal completion.  At `s=1`, the first occupation moment
`Z_S(1)` is unbounded, so the finite gauges do not converge in the pointed completion used by the
polarized Gamma phase.  The surviving object must be a boundary class measuring failure of that
gauge to remain attainable.  It cannot be ordinary finite curvature, an algebraic `lim^1` label,
or the scalar character `(4)` written down after selecting a zero.

## Quantitative clock-compass bridge `[PROVED HERE; PARENT NORM ALGEBRA]`

Let `C_n : E_n -> F_n` and `D_n : F_n -> E_n` be bounded linear maps with `D_n C_n=1`.  For
nonzero `h_n`, put

```text
b_n=||h_n||,                  c_n=||C_n h_n||.
```

Then `c_n` is nonzero and

```text
-log b_n-log||C_n|| <= -log c_n
                              <= -log b_n+log||D_n||.      (6)
```

The left inequality is `c_n<=||C_n||b_n`; the right is
`b_n=||D_n C_n h_n||<=||D_n||c_n`.  Consequently, if `a_n->0` and

```text
a_n log||C_n||->0,           a_n log||D_n||->0,
```

then

```text
a_n(-log c_n)-a_n(-log b_n)->0.                           (7)
```

Thus a fixed finite left-invertible clock compass preserves every finite non-gauge polarization
and its exponential rate grade.  Pointwise left-invertibility alone does not control a varying
compass: exponential condition-number growth can change the grade without ever making a reporter
exactly zero.

## Completed-clock fracture `[CORPUS; UNQUALIFIED CLAIM FALSIFIED]`

The principal-symbol and joint-kernel theorems justify the exact finite statement

```text
all complete clock reporters vanish
  -> R_xi(h)=0
  -> h is pure metric gauge.                              (7a)
```

They do not justify the topological statement that a normalized cofinal polarization cannot become
arbitrarily invisible.  The actual Gamma source already separates these claims.  On its canonical
square-summable clock completion, the source-forced factorial reporter `A_Gamma` is injective and
every finite truncation is bijective, but the normalized clock basis satisfies

```text
||A_Gamma e_n||=1/(n+1)! ->0.                            (7b)
```

Its completed range is dense, proper, and nonclosed, and it has no continuous left inverse.  These
facts are unconditional Lean theorems:

- `gammaFactorialObservabilityOperator_injective`;
- `gammaFactorialObservabilityOperator_hasApproximateUnitKernel`;
- `gammaFactorialObservabilityOperator_not_isClosed_range`;
- `gammaFactorialObservabilityOperator_no_continuousLeftInverse`;
- `gammaFactorial_finite_effective_completed_nonsplit`.

Thus exact non-annihilation and stable observation are different.  A cofinal graviton polarization
can remain nonzero in every clock family while its observed norm tends to zero.  In particular,
clock-compass injectivity cannot by itself transfer the four-unit Hardy--Green estimate or any
uniform source norm bound.

The correct analytic hypothesis on an RH-bearing residual sector is stable conservativity:

```text
there is c>0 such that ||C h||>=c||h||                 (7c)
```

on that sector, equivalently bounded inversion on the reporter range in the Hilbert setting.  The
global Gamma factorial reporter fails `(7c)`, so imposing it on the whole completed clock space
would contradict the source corpus.  The surviving construction must instead produce a
source-defined residual graph norm in which the boundary map is a partial isometry or a
contractive Hodge projection onto the Hardy--Green conormal.  This is the exact compatibility
target of the calibrated residual-core Green--Hodge route; finite left-invertibility is only its
algebraic shadow.

## Open theorem

> **[CONJECTURE -- EULER FIRST-TRACE BOUNDARY TRANSGRESSION.]** The pointed cofinal finite-prime
> occupation system carries a functorial bornological defect complex.  The flat Euler gauges
> `Z_S` define a nonzero degree-zero boundary class at the first-trace completion wall.  There is
> a source-natural transgression of this class to the strict Euler--Gamma corona conormal such
> that:
>
> 1. its exponential associated-graded symbol is the grade-one class `(2)`--`(3)`;
> 2. critical-Mellin continuation acts on its `rho`-residue fibre by `chi_p(rho)`;
> 3. functional-equation reflection sends that fibre character to its inverse;
> 4. the Gamma contact normalization fixes its Hermitian scale rather than only its projective
>    line;
> 5. its Hardy--Green realization is nonexpansive;
> 6. a left-invertible clock compass preserves the resulting non-gauge class, and preserves its
>    exponential grade whenever the reporter and inverse are subexponentially conditioned on the
>    source scale.

Items 1--4 construct the missing source-derived exponential curvature reporter.  Item 5 is the
RH-bearing source theorem.  If a nonzero residue fibre is acted on isometrically by every prime
character, then `(5)` forces `Re(rho)=1/2`; critical-Mellin divisor tomography then gives RH.
For a cofinal source scale `a_n -> 0`, the quantitative condition in item 6 is

```text
a_n log ||C_n|| -> 0,        a_n log ||D_n|| -> 0,        D_n C_n=1.   (8)
```

The two norm comparisons then show that reporter and curvature families have the same exponential
grade.  A fixed finite clock compass satisfies `(8)` automatically.  Pointwise left-invertibility
without `(8)` prevents exact annihilation but can still hide the grade through exponentially bad
conditioning.  Thus item 6 prevents complete, uniformly calibrated clock data from hiding an
off-line polarization, but supplies neither the transgression nor nonexpansivity.

## Why this is narrower than previous open cores

The prime-occupation theorem already supplies the uniquely tangent-normalized polarized
completion and its divergent first-trace class.  The actual-prime graph theorem already fixes the
only surviving asymptotic scale and grade.  Critical-Mellin tomography already supplies the
complete on-shell divisor.  Clock-compass tomography already supplies injectivity modulo gauge.

The remaining construction is therefore one specific map:

```text
unattainable cofinal Euler gauge
  -> strict first-trace corona class
  -> calibrated Hardy--Green conormal.                    (9)
```

Another positivity equivalence, zero-indexed vector, finite jet, ordinary principal symbol, or
abstract unitary representation does not address `(9)`.

## Exponential-cofiber unit-root alternative `[CORPUS-REDUCED CRITERION; NOT RH]`

The metric clause in item 5 is not the only possible way to prevent a reflected off-line pair.
The new actual-prime graph rate gives a strictly weaker, integral alternative which does not ask
for a one-sided scalar sign.

For a prime-indexed normed source family define the polynomial-rate filtration

```text
F^lambda={v=(v_p): sup_(p>>1) p^lambda ||v_p||<infinity},
gr^lambda=F^lambda / union_(epsilon>0) F^(lambda+epsilon).       (10)
```

The actual first-trace response satisfies

```text
1/p<=b_p<=8/p,
```

so it gives a nonzero class in `gr^1`.  In the centered Xi coordinate

```text
XiC(z)=xi(1/2+i z),
```

translation by `log p` acts on the semisimple analytic defect at `z` through

```text
exp(-i log(p) z),       |exp(-i log(p) z)|=p^(Im z).      (11)
```

Consequently `(11)` sends a nonzero grade-`lambda` family to grade
`lambda-Im(z)`.  It and its inverse preserve one and the same nonzero graded
lattice only when

```text
Im(z)=0,
```

equivalently `Re(s)=1/2`.  This is the rank-one unit-root principle for the
prime-rate filtration.  Unlike determinant balance, it does not permit a
pair of opposite nonzero slopes: a bijective lattice automorphism and its
inverse must both have degree zero.

This observation is only a selector unless the following source theorem is
constructed.

> **[CONJECTURE -- EXPONENTIAL-COFIBER UNIT-ROOT EXHAUSTION.]**  The actual
> finite-prime Euler system and completed theta/Gamma comparison define a
> controlled unseparated cofiber `C_Xi^exp`, before divisor localization,
> with:
>
> 1. the lift-conditioning filtration `(10)`, in which the projective
>    first-trace boundary class is nonzero in `gr^1`;
> 2. a source-natural map from `C_Xi^exp` to the semisimple analytic
>    theta-multiplier defect which is exhaustive on every local support
>    fibre;
> 3. invertible prime translations acting by degree-zero automorphisms of
>    one source integral lattice, not merely by reciprocal automorphisms of
>    its fraction object;
> 4. exponent-zero Euler-gauge sensitivity, so multiplication of the
>    completed function by a symmetric rational quartet gauge does not
>    create an effective source fibre;
> 5. compatibility with the polarized first-trace anomaly and with the
>    completed Poisson relation, rather than with an arbitrary entire
>    multiplier presentation.

Items 1--3 and `(11)` would force the analytic support of `C_Xi^exp` to be
real in the centered coordinate and hence prove RH.  The RH-bearing step is
the construction and source-exhaustion of this cofiber, not the unit-root
calculation.

### Hostile controls

1. **Global rank one is insufficient.**  The Xi principal-part module is
   globally rank one, but its pole fibres still occur in
   functional-equation/Schwarz pairs.  A global reversible action may swap
   slopes `h` and `-h`.  The conjecture therefore requires one local
   source lattice before fibre specialization; determinant balance alone
   is rejected.
2. **Ordinary unseparated cofiber is insufficient.**  Theta convolution has
   dense nonclosed `L2` range, so its ordinary quotient seminorm is zero on
   every class.  The presenting arrows and their exponential lift costs
   must be retained; merely declining to Hausdorffize does not construct
   `(10)`.
3. **Entire-multiplier universality is a falsifier.**  The analytic
   multiplier defect exists for every nonzero entire function.  A
   construction using only that complex, translation covariance, or
   functional-equation symmetry cannot satisfy item 4.
4. **Positive quartet surgery is a falsifier.**  Positive generalized-prime
   density, entire symmetric completion, hypertranscendence, and favorable
   unsquared orientation coexist with off-line fibres.  The proposed
   cofiber must use the discrete actual-prime occupation lattice and exact
   Euler--theta incidence absent from that countermodel.
5. **The causal horizon constrains carriers but does not select the
   divisor.**  The dimension-free theorem with threshold
   `(2R+3)/(2 exp(1)^2)` assumes a fixed positive probability gap, whereas
   the actual first-trace response is `b_p=Theta(1/p)` and tends to zero.
   A pointwise consequence is available only after two unproved
   identifications: a source-natural nearest-neighbour realization whose
   endpoint probability gap is at least `1/p`, and an incidence
   `p |-> R_p`.  Under those assumptions, the exact condition

   ```text
   4p < 2^(2R_p+3)
   ```

   and the factorial tail force

   ```text
   |T| Lambda_p > (2R_p+3)/(2 exp(1)^2).
   ```

   The corpus supplies neither the Hardy-response/return-probability
   intertwiner nor the prime/radius incidence.  Moreover the optimal local
   future theorem realizes every terminal probability in `[0,1]` with
   energy--time cost `O(R)`, matching the lower order of scale.  Linear
   causal cost is therefore generic and divisor-blind; it cannot provide
   the missing Euler-to-Xi map.
6. **This is a rate-filtered collision with retired Route A.**  Items 2--3
   ask for a source-faithful analytic defect comparison on which prime
   translations preserve one effective lattice.  This is the
   associated-graded version of the failed faithful positive/unitary theta
   semisimplification in
   `prime-translation-theta-unitary-defect-conjecture.md`.  Its
   source-exhaustion is RH-equivalent.  The actual-prime grade-one class is
   new source data, but no theorem transports it to local Xi fibres.
   Therefore the unit-root paragraph is retained as an exact criterion and
   falsifier for future constructions, not as a live proof route.

The unit-root logic is standard slope/lattice parent mathematics, and
unseparated cofibres and rate filtrations are standard parent technology.
Potential novelty is only their source-effective collision with the
actual-prime first-trace anomaly and the Xi analytic defect.  Preliminary
search found related tropical scaling-site geometry, semilocal zeta
spectral constructions, and slope filtrations in non-Archimedean Hodge
theory, but no source-exhaustive exponential cofiber with properties
1--5.  This is a noncollision report, not a priority claim.

## Falsifiers

The conjecture fails if any of the following occurs:

1. the cofinal gauge class is zero in every source-natural bornological defect complex;
2. every transgression remains pure gauge in the strict corona;
3. the exponential grade depends on aperture or chosen zero;
4. Gamma contact fixes only a projective line, not a Hermitian scale;
5. the Hardy realization is nonclosable or expands one finite response matrix;
6. the alleged source construction already assumes bounded zero evaluation, quotient
   nonexpansivity, or an RH-equivalent sign;
7. every available cofinal clock left inverse has exponential condition-number growth, so the
   source grade is not observable.

## Collision audit

The identities `(1)`--`(5)` are parent mathematics and carry no novelty claim.  Exact corpus
search found no existing card welding the finite-prime polarized first-trace counterterm to the
actual-prime exponential grade through the aperture-independent projective defect `(1)`.

External searches located work on Euler products beyond their convergence boundary, formal-group
linearization of finite Euler cutoffs, zeta regularization, and cohomological interpretations of
zeta values.  None of the located sources constructs the typed bornological transgression `(9)`,
its clock-compass realization, or its Hardy--Green calibration.  This is only a negative
exact-mechanism audit, not a priority proof.

## Gates

- [x] finite Euler connection and projective defect computed
- [x] first-trace exponential grade identified
- [x] critical centered reflection character identified
- [x] finite connection classified as flat/pure gauge
- [x] detector theorem separated from source theorem
- [ ] construct the pointed cofinal bornological defect complex
- [ ] prove nonzero boundary gauge-attainment class
- [ ] construct source-natural corona transgression
- [ ] prove Gamma-calibrated Hardy--Green nonexpansivity
- [ ] formalize only after dependency-closed paper proof
- [ ] RH
