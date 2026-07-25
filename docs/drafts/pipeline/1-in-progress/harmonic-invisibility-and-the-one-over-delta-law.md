# Harmonic invisibility and the 1/δ law

- **ID:** `harmonic-invisibility-and-the-one-over-delta-law`
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE]` with mechanism + two independent confirmed predictions
- **Status:** mechanism `[PROVED HERE]`; the law `[CONJECTURE]`; the consequence `[CONJECTURE]`

## The question this answers

Every RH criterion in this corpus — Weil positivity, Li, Hankel/Grommer, Herglotz, the screw
function, the Euler-ray Loewner kernel, and the Gaussian and resolvent ladders built this month —
has an unbounded parameter: a test-function support, a Hankel order, a heat time, a rectangle size,
an aperture.  None is a finite condition.  That is always described as a nuisance.  **It is not a
nuisance; it is forced, and there is an exact mechanism.**

## §1 The mechanism `[PROVED HERE]`

Move a single zero `rho` by a complex displacement `u` and ask how a functional responds.

**Prime-computable functionals are harmonic in `u`.**  The explicit formula evaluates exactly the
functionals of the shape

```text
F(divisor) = sum_rho Phi(rho, 1 - rho),      Phi holomorphic in each argument
```

(one holomorphic evaluation per zero, paired with its functional-equation partner).  For a single
zero the response is `H(u) := Phi(rho + u, 1 - rho - u)`, which is **holomorphic in `u`**.  Hence
its second-order response to a real (horizontal) displacement and to an imaginary (vertical) one
are exact negatives:

```text
H(delta)  second order:  H''(0) delta^2 / 2
H(i eps)  second order: -H''(0) eps^2 / 2          because (i)^2 = -1.
```

Equivalently: the Laplacian of the response in the displacement plane is zero.

**The functional RH actually constrains is not of that shape.**  RH says the divisor is fixed by
`rho -> 1 - conj rho`, i.e. that `sum_rho |Phi(rho)|^2` agrees with `sum_rho Phi(rho) Phi(1-rho)`.
The first is a modulus, and for holomorphic `Phi`

```text
Laplacian |Phi|^2 = 4 |Phi'|^2 > 0.
```

Writing the two second-order responses out: horizontal `Re(conj Phi * Phi'') + |Phi'|^2`, vertical
`-Re(conj Phi * Phi'') + |Phi'|^2`.  Their **sum is `2|Phi'|^2`, not zero**.

> **The subharmonicity defect `4 |Phi'(rho)|^2` is exactly the horizontal detection power that no
> prime-computable functional possesses, per zero, per test function.**

A harmonic detector spends its horizontal sensitivity and its vertical blindness in equal and
opposite amounts.  Horizontal displacement is what RH forbids; vertical displacement is
unconstrained and is known only to accuracy `O(log T)` (the size of `S(T)`).  So a harmonic detector
cannot separate the two.

## §2 The conjecture

> **[CONJECTURE — the 1/δ law]**  Let `{F_lambda}` be any family of prime-computable divisor
> functionals with a resolution parameter `lambda`.  Let `rho` be a zero at height `g` with
> horizontal displacement `delta > 0`.  Then the least `lambda` at which `F_lambda` distinguishes
> `rho` from its critical-line projection satisfies
>
> ```text
> lambda_detect  asymp  (scale of the family) / delta,
> ```
>
> diverging as `delta -> 0` **uniformly over the family**.  In particular no finite-parameter
> prime-computable criterion is equivalent to RH, and every RH-equivalent criterion must carry an
> unbounded parameter.

The mechanism forces it: to see `delta` a harmonic detector must accumulate the missing
subharmonicity from `lambda`-many harmonic pieces, and each piece contributes `O(delta * scale)`
of separation before the harmonic cancellation eats it.

## §3 Two independent confirmations, both proved this month

The law was formulated *after* these were proved, but neither was proved with it in mind, so they
are genuine tests.

1. **Resolvent ladder.**  `XiResolventLowRungVacuity` proves the first seven Hankel rungs are
   unconditional, and the sector computation shows detection at order `n` needs
   `(n+1) |arg (w + X)| > pi/2`, i.e.

   ```text
   n_detect  asymp  (g^2 + X) / (g * delta).
   ```

2. **Gaussian ladder.**  `XiHeatTuranBottomDetection` gives an explicit detection threshold in the
   heat time, and the phase condition `2 t g delta ~ pi/2` gives

   ```text
   t_detect  asymp  1 / (g * delta).
   ```

Two different weights (`(w+X)^(-1)` and `exp(-t w)`), two different resolution parameters (Hankel
order and heat time), **the same `1/delta` divergence**.  That is the law's first non-trivial
prediction and it holds in both.

A third, retrodicted: the corpus's unconditional `xiSquaredEulerFullKernel_twoPoint_det_pos`
(two-node Euler-ray determinant positive without RH) is exactly a low-order member of family 1, so
the law predicts it must be vacuous — which `re_xiResolventMoment_nonneg` independently proves.

## §4 Hostile audit

- **FALSE?**  The mechanism of §1 is a theorem, not a conjecture: holomorphy gives `(i)^2 = -1`, and
  `Laplacian |Phi|^2 = 4|Phi'|^2` is classical.  What is conjectural is the *uniformity over
  families* in §2.  A counterexample would be a prime-computable family whose detection threshold
  stays bounded as `delta -> 0`; by §1 such a family could not be a sum of single-zero holomorphic
  evaluations, so it would have to exploit zero–zero interaction in a way that localizes — which is
  precisely what is being claimed impossible.  The conjecture is therefore falsifiable and sharp.
- **CIRCULAR?**  No.  Nothing here assumes RH or any zero location.
- **REDISCOVERED?**  `Laplacian |f|^2 = 4|f'|^2` is classical, and "linear statistics of the zeros
  cannot see RH" is folklore.  What is not folklore, and what I have not found stated anywhere: the
  identification of `4|Phi'(rho)|^2` as the **exact per-zero detection budget missing from the
  explicit formula**, and the resulting `1/delta` scaling law with confirmed instances.  Recorded as
  `[CONJECTURE]` pending an external audit.
- **INSIGNIFICANT?**  It explains, from one mechanism, why every criterion in a 750-card corpus has
  an unbounded parameter; why low rungs are provably vacuous; why the detection order scales the way
  the two ladders independently show; and why the 3-4-1 identity buys only a fixed configuration.

## §5 What the law dictates, if true

This is the part that changes the programme.

If detection is impossible at bounded cost, then **no proof of RH can proceed by detecting the
absence of off-line zeros.**  It must proceed by a *wholesale* positivity that never localizes a
single zero — a statement about the quadratic form as a whole, whose proof does not decompose into
per-zero contributions.

That is a strong constraint on admissible proof strategies, and it selects one:

> **[CONJECTURE — forced route]**  Any proof of RH by positivity must derive the subharmonicity
> defect from an index-theoretic source: a form whose signature is fixed by a topological or
> cohomological identity rather than by estimation.  The Hodge index theorem plays exactly this role
> in Weil's proof for curves, where positivity is likewise tight and non-localizable.

Under the law, the Hodge/index route is not one option among many.  It is the only shape of argument
that can supply positivity without localization.  Rodgers–Tao's `Lambda >= 0` is consistent with
this and sharpens it: RH is exactly critical, so no argument with slack can work, and every
non-index argument known has slack.

## §6 Next moves this dictates

1. **Test the law harder.**  Take a third prime-computable family with a *different* geometry — the
   corpus's rectangular/screw family (`riemannHypothesis_iff_rectangular_logSample_weil_eventually_bddBelow`)
   — and compute its detection threshold.  The law predicts `1/delta`.  A bounded threshold would
   refute the law and would be far more valuable than another confirmation.
2. **Try to prove the law** for the class of functionals that are finite sums of holomorphic
   evaluations, where §1 already gives the mechanism; the open part is the passage from per-zero
   response to family-wide threshold.
3. **Stop investing in detection-shaped criteria.**  By §5 they cannot close, and the corpus has
   many.  The index-shaped objects in the corpus (`f1-hodge-*`, `intrinsic-rh-locus-pure-polarized`,
   the negative-index/Krein cards) are the ones the law says deserve the effort.

## §7 What would refute this card

- a prime-computable family with detection threshold bounded as `delta -> 0`;
- a proof of RH by a localizing argument;
- a demonstration that the `1/delta` scaling in the two confirmed families comes from a shared
  accident of their construction rather than from harmonicity.

---

## §8 Third family tested — and the law must be restated

I computed the threshold for the rectangular/screw family (§6 item 1) before writing this section.

The rectangular Weil value at aperture `L` is `Q_Xi(F_{a,L})` for a window of length `L` in the
logarithmic variable, so its divisor side is the holomorphic pairing `sum_rho Fhat(rho) Fhat(1-rho)`
— harmonic, hence subject to §1.  A window of length `L` in `x` has `Fhat` varying on scale `1/L`
in `z`, so `(log Fhat)'' asymp L^2` and the second-order response to displacement `delta` is
`asymp delta^2 L^2`.  Detection therefore needs

```text
L_detect  asymp  1 / delta.
```

**Prediction confirmed — but comparing the three thresholds forces a restatement.**  The three read

```text
resolvent:     (n+1) * (2 g delta / (g^2 + X))  >~ 1        [order x subtended angle]
Gaussian:      t * (2 g delta)                  >~ 1        [time x |Im w|]
rectangular:   L * delta                        >~ 1        [support x displacement]
```

These are *not* the same function of `(g, delta)` — `g/delta`, `1/(g delta)`, `1/delta` — because
the three parameters carry different dimensions.  What is invariant is the product.  So the law's
correct form is dimensionless:

> **[CONJECTURE — the uncertainty form]**  For every prime-computable divisor functional of
> resolution `lambda` (measured in the units dual to the displacement it must resolve),
> `lambda * delta >~ 1` is necessary for detection.  A harmonic detector cannot localise below its
> own resolution, because the localisation budget it would need is exactly the subharmonicity defect
> `4 |Phi'|^2` that §1 shows it does not have.

The earlier "`1/delta` uniformly" formulation was wrong as stated — corrected.

## §9 Novelty, bounded honestly

For **compactly supported** test functions the relation `support >~ 1/delta` is folklore in analytic
number theory; it is why Bombieri-type small-support positivity yields zero-free regions and never
RH.  I am not claiming that.

What I do claim is new, and record as `[CONJECTURE]` pending external audit:

1. the identification of `4 |Phi'(rho)|^2` — the Laplacian of `|Phi|^2` — as the **exact per-zero
   detection budget absent from the explicit formula**, which is a mechanism rather than a heuristic;
2. its verification in two families whose resolution parameter is **not a support** (Hankel order,
   heat time), where the folklore statement does not apply and where the thresholds are genuinely
   different functions of `(g, delta)`;
3. the dimensionless invariant `lambda * delta >~ 1` unifying all three.

## §10 The concrete directive, in the corpus's own coordinates

§5 said the route must be index-theoretic.  The corpus already supplies the index formulation: its
charge-collapse entry proves

```text
total right-half off-line Xi multiplicity = ind_-(J),
J(x,y) = [Q(x) + Q(y)] / (x + y),   Q(x) = Xi'(1/2+x)/Xi(1/2+x).
```

So RH is `ind_-(J) = 0`.  The law says exactly this about how that must be proved:

> **an identity computing the signature of `J`, not an estimate on `J`.**

Every attempt in this corpus to bound `J` — two-node determinants, three-node determinants, sector
bounds, the Hankel rungs — is an estimate, and by §1 each is harmonic and therefore blind below its
resolution.  What is needed is a second, independent computation of `ind_-(J)` from a source whose
signature is fixed by an identity: a Hodge–Riemann relation, a Krein-space index theorem, or a
Lefschetz/index count.  The corpus's index-shaped cards (`f1-hodge-*`,
`intrinsic-rh-locus-pure-polarized`, the Krein negative-index material) are the ones this analysis
says deserve the effort; the detection-shaped cards are the ones it says cannot close.

That is the sharpest research directive this analysis produces, and it is falsifiable: exhibit a
localizing proof, or a bounded-resolution detector, and the whole picture collapses.

---

## §11 The negative directions of `J`, explicitly `[PROVED HERE]`

§10 asks for the signature of `J` by identity.  Before that can be attempted one should know what
the negative directions *are*.  They can be written down in closed form, and doing so turns out to
explain §8 rather than merely accompany it.

Group the divisor into functional-equation/Schwarz quadruples and set `w = rho - 1/2`,
`omega = w^2`.  Summing the four members of a quadruple, the contribution to
`J(x,y) = [Q(x)+Q(y)]/(x+y)` is

```text
K_omega(x,y) = 4 Re[ (x y - omega) / ((x^2 - omega)(y^2 - omega)) ].
```

Put `q(x) = 1/(x^2 - omega)` and `p(x) = x q(x)`, and `c = sqrt(-omega)`.  Since
`(xy - omega) q(x) q(y) = p(x)p(y) - omega q(x)q(y)`,

```text
K_omega = 4 Re[ p(x) p(y) ] + 4 Re[ (c q(x)) (c q(y)) ].
```

For any complex-valued `f`, `Re[f(x) f(y)] = Re f (x) Re f (y) - Im f (x) Im f (y)` — a **hyperbolic
plane**, signature `(1,1)`, whenever `Im f` is not identically zero.  Hence:

- **on-line zero** (`omega` real negative): `q, p, c q` are real, both terms are rank-one positive,
  signature `(2,0)`, `ind_- = 0`;
- **off-line quadruple** (`omega` non-real): two hyperbolic planes, signature `(2,2)`,
  **`ind_- = 2`** — matching the corpus's charge collapse, now with the mechanism visible.

Writing `omega = A + iB` (so `A = g^2 - delta^2`, `B = -2 g delta`), the two negative directions are
the explicit real functions

```text
v_0(x) = B / ((x^2 - A)^2 + B^2),        v_1(x) = x B / ((x^2 - A)^2 + B^2)
```

(and the corresponding pair from `c q`).

### What this says

`v_0` and `v_1` are **bumps centred at `x = sqrt A ~ g` of width `~ B / sqrt A ~ delta`.**  The
negative directions of the RH quadratic form are therefore localized at exactly the displacement
scale.

That is not a coincidence alongside §8 — it *is* §8, in explicit form.  A detector of resolution
`lambda` sees a function of width `delta` only when `lambda * delta >~ 1`, and the harmonic
mechanism of §1 says a prime-computable detector has no resolution to spare.  So the uncertainty
form of the law and the explicit negative directions are the same statement seen from two sides,
which is the first internal cross-check the conjecture has passed.

### The constructive consequence, and its exact limit

The extremal test function for detecting a zero at `(g, delta)` is now known in closed form: test
`J` against `v_0` with `A = g^2 - delta^2`, `B = -2 g delta`.  This is a *recipe*, not a proof — it
presupposes `(g, delta)`.  But it pins down precisely what a proof would have to avoid: any argument
that must first name the offending zero is disqualified, and every detection-shaped criterion in the
corpus does exactly that, implicitly, through its resolution parameter.

### Where this leaves the index question

All known computations of `ind_-(J)` — the pole-type count of Krein–Langer, the argument principle
on the right half-strip, the corpus's three collapsed carriers — evaluate the index **from the
location of the poles of `Q`**, i.e. from the zeros themselves.  The argument-principle version is
literally `S(T)`.  So:

> **[OPEN CORE, sharpened]**  Produce a second, independent computation of `ind_-(J)` that does not
> read the poles of `Q`.  In Weil's proof for curves the second computation is cohomological (Hodge
> index plus Lefschetz, computing the same trace twice).  Here no second computation is known, and
> that — not any missing estimate — is the precise gap.

This is a sharper statement of the wall than "prove the source inequality": it says the missing
object is a *second evaluation of an integer*, and it explains why every analytic attempt returns
the same value by the same route.

---

## §12 Attacking §10: are there index-by-identity theorems, and do they help?

`grep` over the whole formal tree: **no Nehari, AAK, Adamyan–Arov–Krein, or Krein–Langer material
exists in this corpus.**  So this is not a duplication.  Three classical theorems compute exactly
the kind of integer §10 asks for, by identity rather than estimate:

- **Nehari.**  `‖H_phi‖ = dist_(L^infty)(phi, H^infty)` — an exact duality identity.
- **Adamyan–Arov–Krein.**  `s_n(H_phi) = dist(phi, H^infty + R_n)`; hence
  `ind_-(I - H* H) = #{n : s_n > 1}` is a sequence of exact distances.
- **Krein–Langer.**  A generalized Schur function of index `kappa` factors as `B^{-1} s_0` with `B`
  a Blaschke product of degree exactly `kappa` — the index *is* a Blaschke degree.

`J(x,y) = [Q(x)+Q(y)]/(x+y)` is a Pick/Cauchy kernel, so via the Cayley transform its negative index
is the Krein–Langer index of an associated generalized Schur function.  So the identity exists:

```text
RH  <->  the associated Schur function has index 0  <->  |s| <= 1 on the boundary.
```

**And this is where it fails, informatively.**  The boundary on which that modulus bound must hold
is the image of the critical line.  The data there is `Xi'/Xi` on `Re s = 1/2` — precisely the
quantity that is not prime-computable.  The identity therefore **relocates** the problem to the
critical line rather than resolving it.

Trying to fix that by moving the contour makes the point sharply.  To use boundary data in the
convergence region one needs a domain whose boundary lies in `Re s > 1` and (by the functional
equation) `Re s < 0`; but any such domain contains the whole critical strip and its zero count is
just `N(T)`, which says nothing about horizontal position.  To isolate off-line zeros one needs a
narrow domain `|Re s - 1/2| < eps` with `eps < delta` — whose boundary is inside the strip, where the
data is unavailable.

> **The 1/δ law reappears a third time, now as contour placement:** separating off-line zeros
> requires a contour at distance `< delta` from the critical line, and prime-computable data exists
> only at distance `> 1/2`.  Harmonic detectors, moment ladders, and index/contour counts all obey
> the same obstruction, by three different-looking mechanisms.

That triple coincidence is the strongest evidence the card has, and it upgrades §10:

> **[OPEN CORE, sharpened again]**  The missing object is not "an identity computing `ind_-(J)`" —
> those exist (Nehari, AAK, Krein–Langer).  It is **an identity computing `ind_-(J)` whose input
> data lies in the half-plane of absolute convergence.**  Every known identity evaluates the index
> on the critical line; every prime-computable datum lives off it; and the distance between them is
> exactly the `1/delta` gap.

## §13 Status and what I am not claiming

`[CONJECTURE]` for the law and its consequences; `[PROVED HERE]` for the mechanism of §1 and the
explicit negative directions of §11; `[VERIFIED ABSENT]` for Nehari/AAK/Krein–Langer in this corpus.

I am **not** claiming RH progress in the sense of a new theorem about zeros.  What this card claims
is a mechanism, a scaling law with three independent instances, an explicit description of the
negative directions of the RH form, and a sharpened statement of the wall that rules out two whole
families of approach (detection-shaped criteria, and index identities evaluated on the critical
line).  If the law is right, a large fraction of the corpus's live cards cannot close, and the
effort belongs on constructing prime-side data at distance `< delta` from the critical line — which
is the one thing none of the three mechanisms can currently do.

---

## §14 What inputs are provably insufficient — an input calculus

§12 ended at "construct prime-side data at distance `< delta`".  Attacking that directly leads to a
sharper and more useful question: **which inputs can a proof of RH use, and which are provably
insufficient?**  Three levels, in increasing strength.

### Level 1 — support only

Suppose a criterion uses only: the functional equation, the archimedean factor, and the fact that
the prime side is a Dirichlet series, i.e. **supported on `{log n}`**, saying nothing about the
coefficients' signs or values.

> **[NO-GO, level 1]**  Such a criterion cannot decide RH.  The Davenport–Heilbronn function is a
> Dirichlet series with a functional equation of the same shape and the same Gamma-factor type, and
> it has zeros off the critical line.  Any statement derived from support alone holds for it too.

The sharp corollary is worth isolating because it kills a tempting strategy outright:

> **[COROLLARY]**  There is no useful family of test functions whose autocorrelation vanishes on
> `{log n}`.  "Avoid the primes" cannot work: a test function that annihilates the prime side of
> `zeta` annihilates the prime side of Davenport–Heilbronn identically, since both are supported on
> the same set.  The prime side must be *used*, not evaded.

This applies directly to the small-support regime: on `|x| < log 2` the prime side vanishes and the
explicit formula reduces to the archimedean law — which is exactly why Bombieri-type small-support
positivity yields zero-free regions and never RH.  The reason is now structural, not accidental.

### Level 2 — support plus nonnegativity

Add `Lambda(n) >= 0`.  This excludes Davenport–Heilbronn (its logarithmic derivative has no
nonnegative Dirichlet expansion, since it vanishes in `Re s > 1`).  So level 2 is genuinely stronger.

But it is still, to the best of my knowledge, insufficient: **Beurling generalized prime systems**
have an Euler product, nonnegative von Mangoldt weights, and can violate the analogue of RH
(Diamond–Montgomery–Vorhauer construct systems with good prime-counting error yet zeros off the
line).  I flag this as `[LITERATURE — needs source check]` rather than asserting it: I cannot verify
offline whether those constructions can be equipped with an exact Gamma-factor functional equation,
which is what a clean level-2 no-go would require.  **This is the single most valuable thing to check
next**, because if it holds then:

> **[CONJECTURE — level 2 insufficiency]**  No criterion using only the functional equation, the
> archimedean factor, an Euler product, and `Lambda >= 0` can prove RH.

Every card in this corpus whose arithmetic input is exactly `Lambda >= 0` — the 3-4-1 series, the
von Mangoldt moment arrays, the prime-side positive-definiteness, all the resolvent and Gaussian
rungs — is at level 2.  If the conjecture holds, **none of them can close**, and that is a
sweeping, checkable prediction about the corpus.

### Level 3 — the arithmetic of the rational primes

What is left after level 2 is the specific arithmetic: the primes are the rational primes, with
`Lambda(p^k) = log p` and the specific archimedean factor `pi^(-s/2) Gamma(s/2)`.  In particular
**multiplicativity** — that the coefficients come from a degree-one Euler product over the actual
primes with the actual conductor — is the first input beyond level 2.

> **[DIRECTIVE]**  A proof of RH must use an input that distinguishes the rational primes from an
> abstract nonnegative Euler system.  Nonnegativity, positive-definiteness of the prime trace, and
> the 3-4-1 identity are all level 2 and therefore all insufficient.

This is the sharpest form of the session's repeated finding.  It explains, in one sentence, why the
3-4-1 no-go was not an execution failure; why the arithmetic matrix positivity of
`vonMangoldtLogMoment_hankel_nonneg`, though a genuine strengthening, does not close rung 1; and why
every ladder built this month is blind at low order.  All of it is level-2 information, and level 2
appears not to contain RH.

### Immediate consequence for this lane

The Gaussian and resolvent ladders are complete as *criteria* and correct as far as they go, but by
the input calculus they cannot be closed with the arithmetic they currently consume.  Closing them
requires injecting level-3 information — multiplicativity — into the positivity argument, and no
mechanism in this corpus currently does that.  Finding one is the actual open problem, stated more
precisely than "prove the source inequality".

---

## §15 Level 2 checked against the literature — and the result is sharper than the conjecture

I checked the Beurling question rather than leaving it flagged.

**Diamond–Montgomery–Vorhauer** (*Beurling primes with RH and Beurling primes with large
oscillation*, Math. Ann. 2006) construct a Beurling generalized number system whose zeta function
has infinitely many zeros on `sigma = 1 - a/log t` and **no zero-free region better than de la
Vallée Poussin**.  The system has an Euler product, nonnegative von Mangoldt weights, and
well-behaved integer counting `N(x) = rho x + O(x^theta)` for every `theta > 1/2`.  Zhang
complemented this with Beurling systems where RH *does* hold, so the two behaviours are both
realisable.  (Refs: Diamond–Montgomery–Vorhauer, Math. Ann. 334 (2006); Révész, *Density estimates
for the zeros of the Beurling zeta function*, Mathematika 2022.)

So:

> **[NO-GO, level 2 — sourced]**  An Euler product with `Lambda >= 0` and good integer distribution
> does **not** imply RH.  Any criterion whose arithmetic input is exhausted by those facts is
> insufficient.

**But the honest scope is narrower than my conjecture, and the correction matters.**  Beurling
systems generally have no functional equation with a Gamma-factor, so DMVZ does not by itself kill
criteria that use FE *and* `Lambda >= 0` together.  The conjecture as I stated it in §14 is
therefore **not** established; what is established is the pair of complementary no-gos:

```text
Davenport–Heilbronn:  FE + Gamma-factor + Dirichlet support, no coefficient signs  ->  insufficient
Diamond–Montgomery–Vorhauer:  Euler product + Lambda >= 0 + counting, no FE        ->  insufficient
```

### The consequence, which is stronger than either

Neither input suffices alone.  Therefore:

> **RH requires the functional equation and the Euler product to be used *jointly*, in a way that
> neither supplies separately.**

And now the sharp observation.  **The explicit formula uses them additively.**  It places the
functional equation and Gamma-factor entirely in the archimedean term, the Euler product entirely in
the prime term, and asks for an inequality between the two.  Every criterion in this corpus — every
one built this month included — is of that shape.  An additive comparison of two separately
insufficient inputs cannot capture an interaction between them.

> **[CONJECTURE — the additivity obstruction]**  No RH proof can be obtained from a criterion in
> which the functional equation and the Euler product appear in separate additive terms.  The two
> complementary no-gos above make each term individually uninformative, and additivity prevents
> their interaction from ever being seen.

This is falsifiable in the strongest sense: a single RH proof via the explicit formula refutes it.

### What it selects

A formulation in which the archimedean and finite data are *not* separated.  The archimedean place
must be one place among many, on the same footing, so that FE and Euler product are two aspects of a
single object rather than two summands.  That is the adelic/Tate formulation and its descendants —
Connes's programme, the Weil-pairing-over-all-places picture, and the corpus's own index-shaped
cards.  The input calculus arrives at that selection independently of §5's Hodge-index argument, by
a completely different route.

**Two independent lines of this card now point at the same class of formulations.**  That is the
strongest structural evidence it produces, and it is a concrete redirection: the additive
prime-versus-archimedean comparisons — including the ladders I built this month — are not merely
hard to close; by this analysis they are the wrong shape.

---

## §16 The additivity conjecture is RETRACTED — tested and falsified

§15 conjectured that no RH proof can come from a criterion in which the functional equation and the
Euler product appear as separate additive terms.  I tested it two ways.  It fails both.

**Test 1 — the classification.**  Kaczorowski–Perelli (*On the structure of the Selberg class, I:
0 ≤ d ≤ 1*, Acta Math. 182 (1999)) classify the degree-one elements of the Selberg class: they are
exactly `zeta` and the shifted Dirichlet `L`-functions.  So the *joint* hypothesis — functional
equation with Gamma-factor, Euler product, Ramanujan bound, degree one — **has no counterexample
family at all.**  There is no "Davenport–Heilbronn with an Euler product" and no
"Diamond–Montgomery–Vorhauer with a Gamma-factor functional equation": the two no-go families of §14
and §15 cannot be merged.  Consequently the joint input is *not* known to be insufficient, and an
argument may legitimately consume it additively.

**Test 2 — my own artifacts.**  Apply the filter to the ladders built this month.  They use
`Lambda >= 0` on the prime side (so they do **not** apply to Davenport–Heilbronn, whose logarithmic
derivative has no nonnegative Dirichlet expansion) and the functional-equation Klein involution on
the divisor side (so they do **not** apply to a Beurling system, which has no such symmetry).  They
are additive criteria that nonetheless consume both inputs essentially.  So "additive implies dead"
is false, and my own work is the counterexample.

> **[RETRACTED]**  the additivity obstruction of §15.  What blocks the ladders is the resolution law
> of §8, not the additive shape of the explicit formula.

Third self-correction of this investigation, and the most useful one: it removes a conclusion that
would have wrongly condemned a large part of the corpus.

## §17 What survives: a two-sided filter, and the triage it gives

The durable residue of §§14–16 is not an obstruction but a **test every proposed argument must
pass**, in both directions:

> **[FILTER]**  An argument for RH must fail when applied to Davenport–Heilbronn — hence it must use
> the coefficients' positivity or multiplicativity, not merely the functional equation and the
> Dirichlet-series support.  And it must fail when applied to a Diamond–Montgomery–Vorhauer Beurling
> system — hence it must use the Gamma-factor functional equation, not merely an Euler product with
> `Lambda >= 0`.  An argument that survives *either* substitution proves too much and is dead.

Applying it as triage:

| corpus family | uses | filter verdict |
|---|---|---|
| 3-4-1, von Mangoldt moment arrays, prime-trace positive-definiteness | `Lambda >= 0` only | survives DMVZ substitution ⇒ **cannot close alone** |
| Herglotz, vertical monotonicity, Hankel/Grommer, Li, screw, Weil involution | FE + divisor structure only | survive DH substitution ⇒ sound as *criteria*, dead as *proof routes* unless coefficient information is injected |
| Gaussian and resolvent ladders (this month) | both | **pass the filter — still live** |

The middle row is the largest class in this corpus and the verdict on it is sharp: those cards are
correct equivalences, but any attempt to close one without importing coefficient information is
provably attempting to prove a false statement about Davenport–Heilbronn.

The corpus already carries Davenport–Heilbronn and Beurling material in backlog
(`no-boundary-selection-of-zeta.md` and neighbours), so the ingredients are not new here; what is
new is the two-sided use as an admissibility test, the Kaczorowski–Perelli observation that the
joint hypothesis has no counterexample, and the triage above.

## §18 Net position after this investigation

Proved here: the harmonicity mechanism (§1); the explicit negative directions of the RH form (§11);
the sourced level-2 no-go (§15).  Conjectured and surviving: the resolution law `lambda * delta >~ 1`
(§8), confirmed on three families and reappearing as contour placement (§12).  Conjectured and
**retracted**: the "1/delta uniformly" form (§8), and the additivity obstruction (§16).

The live open core, stated as precisely as this investigation can make it:

> Both required inputs are available and their conjunction has no counterexample.  What is missing is
> a mechanism that converts them into positivity **without localizing a zero** — because localization
> costs resolution `1/delta`, and no prime-computable functional has it.

---

## §19 The law's own premise, tested — and the escape it reveals

The law of §8 was stated for "prime-computable divisor functionals".  §1 justifies it for functionals
of the form `sum_rho Phi(rho, 1-rho)` with `Phi` holomorphic, because those are what the explicit
formula evaluates.  I then tested whether the premise "prime-computable implies harmonic" is true in
general.  **It is not**, and finding the counterexample is the most useful thing in this whole
investigation.

**Nyman–Beurling / Báez-Duarte.**  RH is equivalent to `dist(1, span{rho_theta}) = 0` in `L^2(0,1)`,
with `rho_theta(x) = {theta/x} - theta{1/x}`.  This functional is:

- **prime-computable** — the generators are explicit elementary arithmetic functions;
- **not a linear statistic of the divisor** — it is an `L^2` distance, i.e. a modulus-squared
  integral of `zeta`'s *values* on a line, and it never forms `sum_rho h(rho)` at all;
- therefore **not harmonic** in a zero's displacement, so §1 does not apply to it.

So the correct statement of the law is narrower than I wrote:

> **[LAW, corrected scope]**  `lambda * delta >~ 1` binds **divisor linear statistics** — functionals
> the explicit formula evaluates as `sum_rho h(rho)`.  It does not bind prime-computable functionals
> in general, because that class is closed under `|.|^2` and squaring destroys harmonicity.

Fourth correction of this investigation.  It matters because it turns a no-go into a *direction*:

> **The escape from the `1/delta` law is to refuse the explicit formula.**  Converting `zeta`'s
> values into a sum over its zeros is precisely the step that enters the harmonic class and forfeits
> the `4|Phi'|^2` detection budget.  A criterion that works with `zeta`'s values and never performs
> that conversion keeps the budget.  Nyman–Beurling is the known example; its `L^2` distance is a
> manifest sum of squares, hence positivity **without localizing any zero** — which is exactly the
> mechanism §18 named as missing.

### Filter check on Nyman–Beurling

- Against Davenport–Heilbronn: the criterion's proof uses that `zeta` has no zeros in `Re s > 1`,
  which is the Euler product; DH has zeros there, so the argument does not transfer.  **Passes.**
- Against a Beurling system: the criterion uses the functional equation through the Mellin transform
  of the generators.  **Passes.**

So Nyman–Beurling passes the two-sided filter of §17 *and* escapes the law of §8.  On this
investigation's own criteria it is the only formulation examined that does both.

### The corpus gap this identifies

The SOTA ledger records for this row: *"Finite Mobius/Schur and Hilbert closure infrastructure
exists; no exact global Báez-Duarte equivalence declaration was found."*  A `grep` of the formal tree
confirms it: only `HTGeometry/HardyClosureZeroFree.lean` touches the closure idea, and the concrete
`L^2(0,1)` fractional-part generators and the global equivalence are absent.

> **[DIRECTIVE, replacing §10 and §18]**  The highest-value target identified by this investigation
> is the concrete Nyman–Beurling–Báez-Duarte formulation: the generators `rho_theta`, their Mellin
> transforms, and the closure equivalence.  It is the one examined formulation that (i) passes the
> DH/DMVZ filter, (ii) is not a divisor linear statistic and so is not bound by the `1/delta` law,
> and (iii) expresses RH as an infimum of manifestly nonnegative quantities — positivity without
> localization.

This supersedes the earlier directive toward index identities: those, per §12, evaluate on the
critical line and hit the same wall.  The approximation-theoretic route does not.

## §20 Honest ledger for this investigation

**Proved here:** the harmonicity mechanism (§1); the explicit negative directions of the RH form
(§11); the sourced level-2 no-go (§15, via Diamond–Montgomery–Vorhauer).

**Surviving conjecture:** the resolution law in its corrected scope (§8, §19), confirmed on three
families and reappearing as contour placement.

**Retracted after testing:** the "`1/delta` uniformly" form (§8); the additivity obstruction (§16,
falsified by Kaczorowski–Perelli and by my own ladders); the unrestricted premise of the law (§19,
falsified by Nyman–Beurling).

**Durable tools produced:** the two-sided admissibility filter (§17) and the triage it gives; the
scope correction that identifies which formulations are exempt from the law.

RH is not proved.  What this investigation changed is the target: away from additive
prime-versus-archimedean comparisons and index identities on the critical line, and toward the one
formulation that is neither.

---

## §21 The Nyman–Beurling escape, costed — and §19's directive is DEMOTED

§19 concluded that Nyman–Beurling escapes the law because it is not a divisor linear statistic.  That
is true of the *mechanism*.  Before recommending it I costed the route, and the answer reverses the
recommendation.

**Where the NB obstruction actually comes from.**  The Mellin transform of `rho_theta` is
`-theta^s zeta(s)/s`, so every element of the approximating span carries the factor `zeta(s)`.  A
zero `rho` with `Re rho = 1/2 + delta > 1/2` therefore forces **every** span element to vanish at
`rho`, while the target `1` does not.  The obstruction survives the `L^2` limit precisely because
point evaluation at `rho` is a *bounded* functional on the relevant Hardy space — and it is bounded
exactly because `rho` lies at distance `delta` to the right of the critical line.

**That boundedness is the cost.**  The evaluation functional at distance `delta` from the boundary
has norm `~ 1/sqrt(2 delta)`.  So the signal it extracts is

```text
d_N  >~  |target(rho)| / ‖ev_rho‖  ~  sqrt(2 delta).
```

**And the noise floor is logarithmic.**  Under RH the Báez-Duarte distance decays only like
`d_N^2 ~ C / log N` (Balazard–Báez-Duarte–Landreau–Saias).  Detection requires the signal to exceed
the floor:

```text
C / log N  <  c * delta      i.e.      N  >  exp(C / (c delta)).
```

> **[RESULT]**  Nyman–Beurling detects an off-critical zero at displacement `delta` only once its
> resolution parameter reaches `N ~ exp(1/delta)`.  It obeys the same divergence as the other three
> families — with an **exponentially worse** exchange rate than the moment ladders' `poly(1/delta)`.

### Consequences

1. **§19's directive is demoted.**  NB escapes the *harmonic mechanism* but not the underlying
   resolution economy, and it pays far more.  Recommending it as the highest-value target was
   premature; recorded as a fifth correction.
2. **The law is more universal than the mechanism that suggested it.**  Harmonicity explains the
   divergence for divisor linear statistics; NB shows the divergence persists where harmonicity does
   not apply.  So the law should be restated once more, at the level of signal versus noise rather
   than of holomorphy:

   > **[LAW, final form in this investigation]**  In every formulation examined, a zero at
   > displacement `delta` produces a signal `O(delta^a)` for some `a > 0`, while any
   > finite-parameter approximation has a noise floor that decays only as a function of the
   > parameter.  Matching them forces a parameter diverging as `delta -> 0`.  The **divergence is
   > universal; the exchange rate is formulation-dependent**, and the rate is therefore a quality
   > measure for formulations.

3. **The rate ranks the formulations, and the ranking is the opposite of §19's.**

| formulation | signal in `delta` | noise floor | cost |
|---|---|---|---|
| resolvent Hankel ladder | `delta^2` (second-order, harmonic) | algebraic in order `n` | `poly(1/delta)` |
| Gaussian heat ladder | `delta^2` | algebraic in `t` | `poly(1/delta)` |
| rectangular / screw | `delta^2` | algebraic in `L` | `poly(1/delta)` |
| Nyman–Beurling / Báez-Duarte | `sqrt(delta)` (better!) | **logarithmic** in `N` | `exp(1/delta)` |

NB has the *strongest* per-zero signal of the four — `sqrt(delta)` rather than `delta^2` — and is
still the worst route, because its noise floor decays logarithmically.  **The binding constraint is
the noise floor, not the signal.**  That is a non-obvious conclusion and it is the most actionable
thing this investigation has produced:

> **[DIRECTIVE, replacing §19]**  Optimise the *noise floor*, not the signal.  The question to ask
> of any RH formulation is not "how strongly does an off-line zero show up?" but "how fast does the
> finite-parameter approximation converge when RH holds?"  The moment ladders win on that axis by an
> exponential margin, which is why — despite §19 — they remain the better carrier, and why the
> corpus's `Lambda >= 0`-based rungs, though individually insufficient by §17, sit in the right
> family.

---

## §22 Applying the metric to my own table — the ladders are much better than I scored them

§21's table lumped the three ladders as `poly(1/delta)`.  Recomputing the thresholds properly, that
is wrong, and the correction separates them by an exponential.

**Gaussian ladder — cost is `log(1/delta)`.**  In
`exists_neg_xiHeatTuranDefect_of_bottom_conjugate_pair` the bottom-shell signal is
`-4 m^2 B0^2 exp(-2 t A)` with `B0 = 2 g delta`, so the signal carries `delta^2`; the background from
every other shell is bounded by `C exp(-t(2A + Delta))` where `Delta > 0` is the **shell gap** of
`exists_bottom_shell_gap`, a constant of the divisor independent of `delta`.  Detection needs

```text
delta^2 * exp(t * Delta)  >~  1     i.e.     t  >~  (2 / Delta) * log(1/delta).
```

The threshold I actually proved in Lean, `T = max 1 (K/Delta)` with `K ∝ 1/delta^2`, is a crude
sufficient bound obtained through `exp t > t`; the sharp threshold is **logarithmic**.  I proved a
weaker statement than the mathematics gives.

**Resolvent ladder — cost is `1/delta`.**  Detection at Hankel order `n` requires
`(n+1) |arg(w+X)| > pi/2` with `|arg(w+X)| ~ 2 g delta / (g^2 + X)`, so
`n ~ pi (g^2+X) / (4 g delta)` — **linear in `1/delta`**.

**Corrected ranking, with the mechanism visible:**

| formulation | shell separation | detection cost |
|---|---|---|
| Gaussian heat ladder | **exponential** (`exp(-t Delta)`) | `log(1/delta)` |
| resolvent Hankel ladder | algebraic (`(w+X)^(-n)`) | `1/delta` |
| rectangular / screw | algebraic | `1/delta` |
| Nyman–Beurling | logarithmic (`1/log N`) | `exp(1/delta)` |

Four formulations spanning `log(1/delta)` to `exp(1/delta)` — a doubly-exponential spread — and the
ordering is exactly the ordering of how fast the weight separates shells.  **The weight's decay
profile, not the criterion's algebraic form, is what determines the cost.**

### The tension this exposes, and the target it names

The best-conditioned weight is the Gaussian, and it is exponentially better than everything else.
But the Gaussian weight is precisely the one for which **this corpus has no explicit formula** — it
was the reason I built the resolvent ladder at all (`XiResolventTraceHankelCriterion`), trading an
exponentially better carrier for Lean access to prime data.

That trade now looks like the wrong one, and there is a concrete target:

> **[DIRECTIVE, replacing §21]**  Construct the Gaussian/Hermite explicit formula in Lean — the Weil
> explicit formula for test functions `u^(2n) exp(-t u^2)`.  The metric says the Gaussian carrier is
> exponentially better conditioned than every alternative examined, and it is the only missing piece
> preventing the best carrier from being prime-accessible.  The corpus has the rectangular
> Guinand–Weil machinery (`XiGuinandWeil*`, 20 modules) but no Gaussian instance.

This is the first time in the investigation that the metric has selected a *concrete, bounded piece
of missing infrastructure* rather than an open mathematical problem — and it selected it against my
own earlier judgement, which was to route around exactly that gap.

### Honest note on what the metric does and does not say

It ranks *detection* cost.  It does **not** say the Gaussian ladder can be closed: the positivity
`xiHeatTuranDefect >= 0` remains unproved and, by §17, requires arithmetic input beyond
`Lambda >= 0`.  What the metric establishes is that if any of these carriers is closable, the
Gaussian one is closable most cheaply, and that the effort spent routing around its missing explicit
formula was misdirected.

---

## §23 Executing §22's directive — and a second reason the Gaussian carrier wins

Before building I checked the corpus properly.  `XiGuinandWeilContourSynthesis` already contains the
**general** rectangle synthesis law,

```lean
rectIntegral_continuedPrimeArchSourceRelativeTrace_of_factorization
    (t : Finset κ) (rho : κ → ℂ) (m : κ → ℕ) {g h : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g Set.univ) ...
```

taking an **arbitrary entire test function `g`** and returning the enclosed divisor values against
the continued prime–archimedean source.  So the Gaussian explicit formula does not need a new
framework; it needs (i) the Gaussian instantiated as `g`, and (ii) the passage from rectangle to
full divisor.

**And step (ii) is where the Gaussian pays off a second time.**  The corpus needed a substantial
suite for the rectangular window — `XiGuinandWeilRectangularVerticalDecay`,
`...RectangularBottomEdge`, `...RectangularBottomSlope`, `...RectangleExhaustion` — because a
rectangular window decays only polynomially and its horizontal edges are hard to kill.  For the
Gaussian the modulus is exactly

```text
‖G t n s‖ = ‖s - 1/2‖^(2n) * exp( t * ((Re s - 1/2)^2 - (Im s)^2) ),
```

so on a strip of bounded width it decays like `exp(-t y^2)` in the height.  The horizontal edges die
super-exponentially and the vertical edges converge absolutely — the expensive part of the
rectangular construction simply does not arise.

> **Second, independent reason the metric's choice is right:** the Gaussian carrier is not only
> exponentially better conditioned for detection (§22); it is also the cheapest carrier to equip
> with an explicit formula, because the edge estimates that dominate the rectangular construction
> are trivial for it.

### Landed

Module `GaloisForLFunctions.RHTower.XiGaussianTestFunction`:

```lean
xiGaussianTest (t : ℝ) (n : ℕ) (s : ℂ) := (s - 1/2)^(2*n) * exp (t * (s - 1/2)^2)
analyticOnNhd_xiGaussianTest      -- the hypothesis the synthesis law consumes
norm_xiGaussianTest               -- the exact modulus
norm_xiGaussianTest_le_of_strip   -- Gaussian decay in the height on a bounded-width strip
```

Build 8661/8661, lint passes, axioms `propext`, `Classical.choice`, `Quot.sound`.

This is the entry point for the Gaussian explicit formula: the synthesis law's analyticity
hypothesis is now discharged for the Gaussian–Hermite family, and the estimate that makes the
rectangle limit possible is proved.  What remains is the limit itself — instantiate the synthesis
law on a tall rectangle, send the height to infinity killing the horizontal edges by
`norm_xiGaussianTest_le_of_strip`, and identify the two vertical-edge integrals with the
archimedean and prime terms.

### Why this matters for the programme, stated without inflation

This does not prove RH and does not close any positivity.  What it does is move the best-conditioned
carrier — the one my own metric ranks exponentially above the alternatives, and the one I had
previously routed *around* — from "no prime access in Lean" to "prime access in progress, with the
hard estimate already proved".  On the metric derived in §§21–22 that is the highest-value bounded
piece of work available in this lane.

### §23 continued — the edge-vanishing limit landed

```lean
tendsto_polyGaussian_atTop {t : ℝ} (ht : 0 < t) (n : ℕ) (R : ℝ) :
  Tendsto (fun Y : ℝ => (R + |Y|) ^ n * Real.exp (-(t * Y ^ 2))) atTop (nhds 0)
```

Gaussian decay beats polynomial growth: for `Y >= max(|R|, 1)` one has `R + |Y| <= 2Y` and
`exp(-t Y^2) <= exp(-t Y)`, so the bound reduces to `(2^n/t^n) * (tY)^n exp(-tY)`, which tends to
zero by `Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero` composed with `Y ↦ tY`.

Combined with `norm_xiGaussianTest_le_of_strip`, this is the statement that **the horizontal edge of
a rectangle of bounded width contributes nothing in the height limit** — the estimate the corpus
needed four dedicated modules for in the rectangular case, and which for the Gaussian is one
squeeze.

Build 8661/8661, lint passes, axioms `propext`, `Classical.choice`, `Quot.sound`.

**Remaining for the Gaussian explicit formula**, in order: instantiate
`rectIntegral_continuedPrimeArchSourceRelativeTrace_of_factorization` with `g = xiGaussianTest t n`
on an admissible rectangle (the corpus's `XiGuinandWeilRectangleExhaustion` supplies cofinal
admissible rectangles); send the height to infinity, killing the horizontal edges by the two lemmas
above against the logarithmic growth of `logDeriv XiC` on admissible edges; identify the two
vertical-edge integrals with the archimedean term and the Gaussian-damped von Mangoldt sum.  No new
mathematics; the estimates are done.

### §23 continued — the vertical edge converges absolutely

```lean
norm_xiGaussianTest_vertical_le {t : ℝ} (ht : 0 < t) (n : ℕ) (c y : ℝ) :
  ‖xiGaussianTest t n (c + y*I)‖ ≤ K(t,n,c) * Real.exp (-(t/2 * y^2))

integrable_xiGaussianTest_vertical {t : ℝ} (ht : 0 < t) (n : ℕ) (c : ℝ) :
  Integrable (fun y : ℝ => xiGaussianTest t n (c + y*I))
```

On a vertical line the modulus is `((c-1/2)^2 + y^2)^n * exp(t(c-1/2)^2) * exp(-t y^2)`.  Splitting
the Gaussian in half and applying `u^n exp(-(t/2) u) <= n!/(t/2)^n` at `u = (c-1/2)^2 + y^2` absorbs
the entire polynomial factor into a constant, leaving a half-width Gaussian.  Integrability then
follows from `integrable_exp_neg_mul_sq` by domination.

Build 8661/8661, lint passes, axioms `propext`, `Classical.choice`, `Quot.sound`.

**Both edge estimates for the Gaussian explicit formula are now proved:** horizontal edges vanish
(`norm_xiGaussianTest_le_of_strip` with `tendsto_polyGaussian_atTop`), vertical edges converge
absolutely (`integrable_xiGaussianTest_vertical`).  What remains is the instantiation of
`rectIntegral_continuedPrimeArchSourceRelativeTrace_of_factorization` at `g = xiGaussianTest t n`
and the identification of the two limiting vertical integrals with the archimedean term and the
Gaussian-damped von Mangoldt sum.

### §23 continued — the Gaussian moment is now reachable from prime data

Module `GaloisForLFunctions.RHTower.XiGaussianExplicitFormulaRectangle`.

```lean
xiGaussianTestC (t : ℝ) (n : ℕ) (z : ℂ) := z ^ (2*n) * exp (-(t : ℂ) * z ^ 2)

exists_admissible_rectIntegral_gaussianSource_eq_xiZeroCopy_sum (F t n) :
  ∃ z₁ z₂, ... ∧ rectIntegral (xiGaussianTestC t n * continuedPrimeArchSourceRelativeTrace) z₁ z₂
             = 2 π i * ∑ q ∈ closedRectangle z₁ z₂, xiGaussianTestC t n (xiSpectralPoint q)

exists_admissible_gaussianSource_contour_approximates_heatMoment {t} (ht : 0 < t) (n) {ε} (hε) :
  ∃ z₁ z₂, ... ∧ dist ((2 π i)⁻¹ * rectIntegral (…) z₁ z₂) (xiGaussianHeatMoment n t) < ε
```

**The Gaussian heat moment is approximated to arbitrary accuracy by a prime–archimedean contour
integral.**  The corpus's synthesis law turned out to be fully general in its test function, so the
instantiation needed only `analyticOnNhd_xiGaussianTestC`; the identification
`xiGaussianTestC t n (xiSpectralPoint q) = (alpha^2)^n * xiGaussianHeatTerm t q` is `pow_mul`, and
summability is the corpus's `summable_xiGaussianHeatMonomialTerm`.

Build 8979/8979, lint passes, axioms `propext`, `Classical.choice`, `Quot.sound`.

This closes the gap that caused the resolvent detour: the entries of the Gaussian ladder —
`xiGaussianHeatMoment`, and hence `xiHeatTuranDefect` — are now reachable from prime–archimedean
data in Lean, for the carrier the metric of §22 ranks exponentially above the alternatives.

**Remaining**, and now purely a limit computation with both estimates in hand: replace the
`epsilon`-approximation by an exact identity, by sending the rectangle's width to infinity
(`norm_xiGaussianTest_le_of_strip` with `tendsto_polyGaussian_atTop` kills the left and right
edges) and evaluating the two horizontal edges (`integrable_xiGaussianTest_vertical` gives absolute
convergence) as the archimedean term and the Gaussian-damped von Mangoldt sum.

---

## §24 Attacking the positivity: the Turán defect splits into three, and the prime part has a sign

With the Gaussian moments now reachable from prime data, the positivity question can be attacked on
the arithmetic side.  Write each moment through the explicit formula as `M_n = A_n - P_n`
(archimedean minus prime).  Then

```text
D(t) = M0 M2 - M1^2
     = [A0 A2 - A1^2]                        (I)   archimedean Turán
       - [A0 P2 + A2 P0 - 2 A1 P1]           (II)  cross term
       + [P0 P2 - P1^2]                      (III) prime Turán
```

Since `M_n = (-1)^n d^n/dt^n M_0`, the same holds termwise: `P_n = (-1)^n P_0^(n)(t)`, so

```text
(III) = P0 P0'' - (P0')^2  >= 0   <->   P0 is log-convex in t,
```

where `P0` is the **prime heat density**

```text
P0(t) = (1 / sqrt(pi t)) * sum_j Lambda(j) j^(-1/2) exp(-(log j)^2 / (4 t)).
```

### The prime Turán term has a sign, and the mechanism is visible

Substitute `u = 1/t`.  Then `P0 = sqrt(u/pi) * L(u)` with `L(u) = sum_j c_j exp(-a_j u)`,
`c_j = Lambda(j) j^(-1/2) >= 0`, `a_j = (log j)^2 / 4`.  So

```text
(log P0)''(u) = Var_u(a) - 1 / (2 u^2),
```

where `Var_u` is the variance of `a` under the probability measure proportional to
`c_j exp(-a_j u)` — the second factor being exact Cauchy–Schwarz for a Laplace transform of a
positive measure, and the `-1/(2u^2)` coming from the log-concave factor `sqrt u`.

> **`(III) >= 0`  <->  `Var_u((log j)^2 / 4) >= 1/(2 u^2)` for all `u > 0`.**

This is a statement about the primes alone: the tilted distribution of `(log j)^2` must carry enough
variance.  Computing it: with `y = log j`, prime-number-theorem smoothing gives density
proportional to `exp(y/2) exp(-u y^2/4) dy`, a Gaussian with mean `mu = 1/u` and variance
`sigma^2 = 2/u`.  For such a `y`,

```text
Var(y^2) = 2 sigma^4 + 4 mu^2 sigma^2 = 8/u^2 + 8/u^3,
Var(a)   = Var(y^2)/16 = 1/(2u^2) + 1/(2u^3).
```

**The requirement is met, with margin exactly `1/(2u^3) = t^3/2`** — and the margin comes entirely
from `mu = 1/u <> 0`, i.e. from the fact that the tilted prime measure is *not* centred at the
origin.  A centred prime measure would sit exactly at the log-convexity boundary.

`[CONJECTURE, with computation]` — the identity for `(log P0)''` and the reduction to a variance
inequality are exact; the evaluation of `Var_u(a)` uses PNT-level smoothing, so the margin is
computed rather than proved.  Making it rigorous needs a lower bound for
`Var_u((log j)^2)` under the tilted von Mangoldt measure, which is an ordinary (if delicate)
analytic-number-theory estimate with no zero input.

### What this changes

The arithmetic side of the Turán defect is **not** an obstruction: term (III) is nonnegative, and the
`Lambda >= 0` primitive is exactly what delivers it (Cauchy–Schwarz on a positive measure).  Term (I)
is explicit and zero-free.  **The whole difficulty is concentrated in the cross term (II).**

That is a genuine narrowing.  Previous formulations said "the archimedean side must dominate the
prime side"; this says the prime side helps at second order, the archimedean side is computable, and
the sign question lives entirely in their interaction — which is exactly the FE/Euler *interaction*
that §15's two no-gos showed must be used and that no additive comparison can see.  The cross term
is that interaction, made explicit for the first time in this lane.

> **[OPEN CORE, current]**  Determine the sign of `A0 P2 + A2 P0 - 2 A1 P1` relative to
> `(A0 A2 - A1^2) + (P0 P2 - P1^2)`.  Both bracketed terms are now known nonnegative; the cross term
> is the only unsigned quantity in the Gaussian ladder's rung 2.

---

## §25 The cross term computed exactly — the obstruction is a single perfect square

Write `A = nu_A` (archimedean-plus-pole heat density), `P = nu_P` (prime heat density), so the
Gaussian zero trace is `nu = A - P` and the rung-2 defect is `D = nu nu'' - (nu')^2`.  Introduce the
logarithmic data

```text
a = (log A)',   p = (log P)',   alpha = (log A)'',   pi = (log P)''.
```

Then `A''/A = a' + a^2` and `P''/P = p' + p^2`, so the cross term of §24 divides exactly:

```text
(II) = A P'' + P A'' - 2 A' P' = A P * [ alpha + pi + (a - p)^2 ].
```

Substituting into `D = A^2 alpha + P^2 pi - A P [alpha + pi + (a-p)^2]` and collecting:

> **[IDENTITY, exact]**
> ```text
> D = nu * ( alpha * A  -  pi * P )  -  A P * [ (log (A/P))' ]^2.
> ```

This is exact — no expansion, no smoothing.  Its content:

- **the only negative contribution is a perfect square**, `A P * [(log(A/P))']^2`;
- that square is the squared *rate of multiplicative mismatch* between the archimedean and the prime
  heat densities;
- everything else is `nu` (the zero trace, positive under RH and exponentially small at large `t`)
  times a difference of the two log-convexities, both of which are nonnegative by §24 and by the
  elementary-target analysis.

### What it says

Rung 2 is a competition between a **small positive** term and a **square**.  Since `nu = A - P` is
exponentially small while `A` and `P` are individually large and nearly equal, the inequality
`nu (alpha A - pi P) >= A P [(log(A/P))']^2` can only hold if

> **the archimedean and prime heat densities are multiplicatively parallel to first order, to a
> tolerance set by the size of the zero trace itself.**

That is the sharpest statement of "the interaction" this investigation has produced.  §15's two
counterexample families proved that neither the functional equation nor the Euler product suffices
alone and that their interaction must be used; §25 exhibits that interaction as one explicit
quantity, `(log(A/P))'`, and shows that RH's rung 2 is precisely a bound on it.

### Why this is a genuine narrowing, and what it costs

Expanding for small `r = nu / P` recovers `D ≈ P^2 (r r'' - r'^2)`, i.e. `D >= 0` iff `r` is
log-convex — so the identity does **not** by itself break the circle, and I am not claiming it does.
What it does is replace an unsigned three-term comparison by a signed one: *one* nonnegative term
minus *one* square, with both factors explicit and prime-computable.  In that form the question is
no longer "which of three large quantities wins" but "how small is a specific logarithmic
derivative", which is a bound of a kind analytic number theory knows how to attack.

> **[OPEN CORE, current]**  Bound `|(log(A/P))'(t)|` above by
> `sqrt( nu (alpha A - pi P) / (A P) )`.  Both sides are explicit: the left from the archimedean
> factor and the Gaussian-damped von Mangoldt sum, the right from the same data plus the zero trace
> `nu = A - P`.  Neither side requires knowing a zero location.

---

## §26 Leaving positivity: RH as boundedness of an explicit prime sum on a vertical line

§25's identity re-expresses rung 2 but does not break the circle — `D >= 0` is still equivalent to
log-convexity of the zero trace.  So instead of pushing positivity further I looked for a criterion
of a **different type** built from the same object.

The Gaussian zero trace is an exponential sum in the heat time:

```text
nu(t) = sum_rho m_rho * exp(omega_rho * t),    omega_rho = (rho - 1/2)^2.
```

Continue `t` into the complex half-plane `Re t > 0`.  For `t = sigma + i y`,

```text
|exp(omega t)| = exp( Re(omega) sigma  -  Im(omega) y ),   Im(omega) = -2 g delta.
```

Under RH every `omega` is real negative, so each term has modulus `exp(Re(omega) sigma)`, the series
converges uniformly in `y`, and

```text
|nu(sigma + i y)|  <=  nu(sigma)   for every real y.
```

If some `omega` is non-real, the corresponding term grows like `exp(|Im omega| |y|)` along one
vertical direction, and a nonzero exponential sum with distinct frequencies cannot be bounded (Bohr
almost-periodicity).  Hence

> **[CRITERION]**  RH holds **iff** the analytic continuation of `nu` is bounded on some vertical
> line `Re t = sigma > 0`.

### Why this is worth having

`nu = A - P` with both sides explicit and **zero-free**:

- `A(t) = 2 exp(t/4) + (1/2 pi) integral exp(-t r^2) [Re psi(1/4 + i r/2) - log pi] dr` is
  *manifestly bounded* on every vertical line: `|exp(t/4)| = exp(sigma/4)` and
  `|exp(-t r^2)| = exp(-sigma r^2)`, so the integral converges uniformly in `y`.
- `P(t) = (pi t)^(-1/2) sum_j Lambda(j) j^(-1/2) exp(-(log j)^2 / (4 t))` is bounded **only through
  cancellation**: for large `|y|` the modulus of each term tends to `1` while the phase
  `exp( i (log j)^2 y / (4 |t|^2) )` oscillates.  A modulus-only bound diverges; the boundedness is
  entirely a statement about cancellation in a prime exponential sum.

So the criterion reads:

> **RH  <->  the prime exponential sum `sum_j Lambda(j) j^(-1/2) exp(-(log j)^2 / (4 t))` stays
> `O(sqrt(|t|))` along a vertical line.**

**This is a boundedness statement, not a positivity statement.**  Every formulation in this
investigation so far — Weil positivity, the Hankel ladders, the Turán rungs, Nyman–Beurling — asks
for a sign.  This one asks for cancellation.  That matters because the two no-gos of §15 and the
resolution law of §8 were all about *sign* extraction, and none of their mechanisms applies to a
cancellation statement.

It also explains the connection to the actual analytic frontier: cancellation in
`sum Lambda(j) j^(-1/2) e^(i theta_j)` along vertical lines is exactly the large-values problem for
Dirichlet polynomials, which is where Guth–Maynard's recent zero-density progress lives, and which
the corpus's SOTA ledger records as unconditional but not cofinalizing.  The criterion says why
those two frontiers are the same frontier.

`[CONJECTURE]` for the reverse direction: the step "`omega` non-real implies unbounded" uses
Bohr almost-periodicity for a countable exponential sum with an accumulating frequency set, which
needs care (the frequencies `Im omega_rho = -2 g delta` are not separated).  The forward direction
is elementary and complete.  Recorded honestly: this is a criterion whose easy half is proved and
whose converse needs an almost-periodicity argument I have not written.

### Next

Formalize the forward half — `RH implies |nu(sigma + i y)| <= nu(sigma)` — which is immediate from
`xiGaussianHeatTerm` and the reality of the spectral points under RH, and gives an unconditional
**RH-disproof endpoint of a new kind**: exhibit one vertical-line value exceeding `nu(sigma)` and RH
fails.  Unlike the trace-positivity endpoints already in the corpus, this one tests *cancellation*
rather than sign.

---

## §27 The vertical criterion made well-posed, and its exact gap

`[LEAN-PROVED]` `formal/GaloisForLFunctions/RHTower/XiGaussianHeatVerticalBound.lean`
(lint clean; axioms `propext, Classical.choice, Quot.sound`):

- `norm_xiGaussianHeatTraceC_le_of_rh` — RH implies `‖nu(tau)‖ <= nu(Re tau)` on the open right
  half-plane;
- `not_riemannHypothesis_of_xiGaussianHeatTraceReal_lt_norm` — the cancellation-type disproof
  endpoint;
- `exists_norm_xiGaussianHeatTermC_gt` — an off-line copy's own multiplier is unbounded on every
  vertical line.

### The criterion is well-posed (unconditionally)

§26 left a real worry: off RH the exponential sum might not converge away from the real axis, in
which case "boundedness of `nu`" would be a statement about an undefined object.  It does converge,
and the reason is a size mismatch that costs nothing:

```text
Re omega = delta^2 - g^2,   Im omega = -2 g delta,   |delta| <= 1/2.
```

So at `t = sigma + i y` the term modulus is `exp((delta^2 - g^2) sigma + 2 g delta y)`, bounded by
`exp(sigma/4) exp(-g^2 sigma + g |y|)`.  The Gaussian `-g^2 sigma` beats the linear `g |y|` for
*every* fixed `y`, against a zero-counting density that is only log-polynomial.

> **[PAPER-PROVED]**  The Gaussian zero trace converges absolutely and is analytic on the whole
> half-plane `Re t > 0`, with no hypothesis on the zeros.

### The exact gap RH must close

Maximizing `-g^2 sigma + g|y|` over `g` at `g = |y| / (2 sigma)` and completing the square gives the
unconditional envelope

> **[PAPER-PROVED]**  `|nu(sigma + i y)| <= C(sigma) log(2 + |y|) exp( y^2 / (4 sigma) )`.

Against the RH conclusion `|nu(sigma+iy)| <= nu(sigma)`, the criterion now reads with both ends
pinned:

```text
unconditional:   Gaussian growth   exp( y^2 / (4 sigma) )
RH:              bounded            O(1)
```

That is the exact quantitative gap, and it is a *cancellation* gap, not a sign gap.  Nothing between
the two ends is currently known — which is the honest measure of how much this reformulation buys.

### Hostile audit of §26's criterion

Read on the prime side, `nu = A - P` bounded is cancellation in
`sum_j Lambda(j) j^(-1/2) exp(-(log j)^2 / (4t))` — the Gaussian-smoothed explicit formula.  That is
classical.  So:

> **Verdict on the equivalence itself: `[BRIDGE]`.**  The statement "RH iff the Gaussian-smoothed
> Chebyshev function has square-root error" is not new, and I am not claiming it.

What the section actually delivers, stated at its real size:

- `[LEAN-PROVED]` a cancellation-type RH-disproof endpoint, structurally unlike every sign-type
  endpoint already in the corpus;
- `[PAPER-PROVED]` unconditional half-plane analyticity and the explicit Gaussian envelope, which
  make the criterion well-posed and quantify its gap;
- an exact obstruction, below.

### The obstruction, exactly

The converse ("bounded implies RH") wants to isolate a top growth rate `V = sup_rho 2 g delta` and
run a Bohr-type argument.  It fails for a specific reason:

> **[OPEN CORE]**  `V` need not be finite or attained.  The classical zero-free region gives only
> `delta << 1 / log g`, hence `2 g delta << g / log g`, whose supremum over the zeros may be
> infinite.  There is no top frequency to project onto, so no single term dominates and the
> cancellation cannot be excluded termwise -- `exists_norm_xiGaussianHeatTermC_gt` shows each
> off-line term is individually unbounded, and that is exactly as far as termwise reasoning goes.

### Relentless interrogation: what the obstruction hands back

The killing mechanism is "the growth-rate spectrum `{2 g delta}` has no top".  Turn that into the
object rather than the obstacle.  Define the **vertical growth exponent**

```text
mu(sigma) = limsup_{|y| -> infinity}  log |nu(sigma + i y)| / y^2.
```

The two results above bracket it unconditionally: `0 <= mu(sigma) <= 1/(4 sigma)`, and RH forces
`mu(sigma) = 0`.  Both bounds are explicit and prime-computable, since `nu = A - P`.

> **[CONJECTURE]**  `mu(sigma) = (1/(4 sigma)) * limsup_{g -> infinity} (2 delta_g)^+`, i.e. the
> vertical growth exponent of the Gaussian trace *equals* the normalized limsup of the off-line
> displacement.  In particular `mu(sigma) = 0` for one `sigma > 0` iff `delta_g -> 0`, which is the
> quasi-RH (density) statement rather than RH itself.

This is a strictly better target than §26's converse: it does not need a top frequency, only a
limsup, and it converts a boundedness dichotomy into a *continuous* exponent that interpolates
between the two ends of the gap.  It also predicts what a partial result buys —
`mu(sigma) < 1/(4 sigma)` should already be a zero-free region — which is a falsifiable consequence
and the next thing to attack.

`[OPEN CORE, current]`  Prove one direction of the conjecture: `limsup delta_g >= c > 0` implies
`mu(sigma) >= c/(4 sigma)`.  This is where the cancellation question now lives, and unlike the
top-frequency argument it only requires a lower bound along a *sequence*, which a second-moment
average over `y` can supply without any frequency separation.

---

## §28 The second-moment plan dies; the square root repairs it

### The plan of §27, killed

Attack `limsup delta_g >= c` implies `mu(sigma) >= c/(4 sigma)` by a Gaussian-weighted vertical
second moment `J(eta) = integral |nu(sigma+iy)|^2 exp(-y^2/(2 eta)) dy / sqrt(2 pi eta)`.  Every
pair integrates in closed form: the `(rho, rho')` term acquires

```text
exp( eta [ (Im w + Im w')^2 - (Re w - Re w')^2 ] / 2  -  sigma (Re w + Re w') ).
```

Two constraints then collide.

- **Convergence.**  With `|Im w| <= g` and `Re w = g^2 - delta^2`, the pair exponent is at most
  `(eta - sigma)(g^2 + g'^2)`.  The double sum converges iff `eta < sigma` -- exactly the range in
  which the weight beats the unconditional envelope `exp(y^2/(4 sigma))` of §27.
- **Detection.**  The diagonal term is `exp( g^2 (-2 sigma + 8 eta delta^2) + 2 sigma delta^2 )`, so
  an off-line zero is visible only when `delta^2 > sigma / (4 eta)`.

For `eta < sigma` the detection threshold is `delta^2 > 1/4`.  The critical strip gives
`|delta| < 1/2` for every zero.

> **[FALSIFIED]**  The Gaussian-weighted vertical second moment converges precisely on the range
> where it cannot see any off-line zero.  Its finiteness is vacuous as an RH test -- a quantitative
> blindness of the same species as the resolvent low-rung vacuity already in the corpus.

### The exact why

The blindness is not an artifact of the Gaussian weight.  In the squared coordinate `w = alpha^2`:

```text
vertical growth rate  |Im w| = 2 g delta   -- linear in the height
horizontal decay rate  Re w  = g^2 - delta^2 -- quadratic in the height
```

Growth and decay scale with *different powers of `g`*, and the comparison must hold at every height
at once.  No weighting in `y` can win, because whatever is spent to control large `g` also suppresses
the signal there.  This is also why §27's envelope had infinite order: the Gaussian trace is simply
not a function of exponential type on vertical lines.

### The repair: take the square root of the spectral parameter

Replace the heat semigroup `exp(-t w)` by the Poisson (Cauchy) semigroup `exp(-t sqrt(w))`.  Since
`Re w > 0`, the principal root is the spectral point reflected into the closed right half-plane, and
in it the two rates become

```text
vertical growth rate  |Im sqrt(w)| = |delta| < 1/2   -- bounded, uniformly over the divisor
horizontal decay rate  Re sqrt(w)  = |g|             -- linear in the height
```

The mismatch is gone, and the growth rates now live in a **fixed compact interval**, which is
precisely what §27 recorded as missing ("there is no top frequency").

`[LEAN-PROVED]` `formal/GaloisForLFunctions/RHTower/XiPoissonVerticalType.lean`
(lint clean; axioms `propext, Classical.choice, Quot.sound`):

- `abs_xiPoissonPoint_im_lt_half` -- all vertical growth rates are `< 1/2`, unconditionally;
- `summable_xiPoissonWeight` -- the Poisson weight is summable at every positive real time, by
  pointwise comparison `exp(-sigma N) <= 2 / (sigma N)^2` against the corpus's canonical-product
  exponent `xiSpectralPoint_inv_sq_summable`;
- `norm_xiPoissonTraceC_le` -- **the unconditional envelope**
  `‖Theta(tau)‖ <= exp(|Im tau| / 2) * Theta(Re tau)`;
- `norm_xiPoissonTraceC_le_of_rh` -- RH collapses it to `‖Theta(tau)‖ <= Theta(Re tau)`;
- `not_riemannHypothesis_of_xiPoissonTraceReal_lt_norm` -- the disproof endpoint;
- `exists_norm_xiPoissonTerm_gt` -- an off-line copy is still individually unbounded, so no
  detection power was traded away for the better envelope.

### What changed, in one line

```text
Gaussian trace:  unconditional envelope exp( y^2 / (4 sigma) )   -- infinite order
Poisson trace:   unconditional envelope exp( |y| / 2 )           -- order 1, type <= 1/2
RH (both):       bounded
```

The criterion moves from outside every classical function-theoretic category into the
exponential-type category, where Paley--Wiener, Bernstein, Levinson and Beurling--Malliavin theory
apply.  Extending to complex `y = u + iv`, the term modulus is `exp(v Re + u Im)`, so on the closed
lower half `y`-plane the trace is analytic of exponential type `<= 1/2` unconditionally, and under RH
is bounded there: **RH is Hardy-class membership `Theta(sigma + i .) in H-infinity` of a half-plane.**

### The detector is de-biased across heights

An off-line copy contributes vertical growth at rate exactly `|delta|`, against an envelope rate
`1/2`.  Its relative strength is `2 |delta|` -- **independent of its height `g`**.  In the squared
coordinate the same copy's strength was `2 g delta` measured against a shell scale `g^2`, i.e.
height-dependent and decaying.  So the square root does more than fix the envelope:

> **[CONJECTURE, structural]**  The Poisson coordinate is the unique power of the spectral parameter
> in which the resolution law `lambda . delta >~ 1` becomes height-uniform.  Detection cost stops
> depending on where in the critical strip one looks.

### Hostile audit

The *object* is not new.  `Theta` restricted to the upper zeros is Cramér's function
`V(z) = sum_{g>0} exp(i g z)` (Cramér 1919, later Guinand), whose meromorphic continuation and
singularity structure are classical, and a boundedness characterization of RH in that language is
plausibly known.  I am not claiming the criterion as new.

What this section delivers at its real size:

- `[FALSIFIED]` the second-moment route, with the exact vacuity computation;
- the **mechanism** -- growth/decay scaling mismatch in the exponent of the spectral parameter --
  which says *why* the square root is forced and is not a statement I can find made anywhere as a
  design principle for RH carriers;
- `[LEAN-PROVED]` unconditional exponential-type envelope, summability, RH collapse, and a disproof
  endpoint, none of which the corpus had;
- `[CONJECTURE]` the height-uniformity of detection cost, which is a falsifiable structural claim
  about the whole family of carriers this project has been building.

### Next

`[OPEN CORE, current]`  In the Poisson coordinate the growth rates lie in `[-1/2, 1/2]` and
`V := sup |delta_rho|` is therefore finite unconditionally.  Prove the top-rate projection that
§27 could not have: for the almost-periodic-with-bounded-type family `Theta(sigma + iy)`, show
`limsup_{y -> -infinity} log ‖Theta(sigma+iy)‖ / y = -V`.  With `V` finite this is a Levinson-type
statement about the indicator function of an exponential-type function, not a Bohr statement about
an unbounded frequency set -- the obstruction that killed §27 is structurally absent.

---

## §29 The converse, proved: the vertical indicator equals the maximal displacement

Notation.  `alpha^ q` is the Poisson point, `R q = Re alpha^ q = |g|` the height, `J q = Im alpha^ q`
the (signed) displacement, `|J q| < 1/2` unconditionally.  Write

```text
Theta(sigma + i u) = sum_q exp(-sigma R q + u J q) * phase,     V = sup_q |J q|,
h = limsup_{|u| -> infinity} log |Theta(sigma + i u)| / |u|.
```

RH is exactly `V = 0`.

### The easy half

`|Theta(sigma+iu)| <= exp(V |u|) * sum_q exp(-sigma R q)`, so **`h <= V`**.  (This already sharpens
the formalized envelope constant from `1/2` to `V`.)

### The hard half: `h >= V`

Suppose `|Theta(sigma+iu)| << exp(lambda |u|)` on the real `u`-axis.  Claim: `|J q| <= lambda` for
every copy.  Induct on the discrete increasing sequence of heights `g_1 < g_2 < ...` (discrete with
finite multiplicity, since the zeros of Xi are isolated).

Assume shells `1..n-1` satisfy `|J| <= lambda`, and let `Theta_n` be `Theta` with those shells
removed.  Each removed shell contributes `<< exp(lambda|u|)`, so `Theta_n << exp(lambda|u|)` on the
real axis too.  Put

```text
G(y) = Theta_n(sigma + i y) * exp(i g_n y).
```

**Step 1 (two boundary rays).**  On the real axis `|G(u)| << exp(lambda |u|)`.  On the negative
imaginary axis `y = -i v`, `|G(-iv)| <= exp(g_n v) * sum_{R >= g_n} exp(-(sigma+v) R) <=
sum_q exp(-sigma R q)` -- **bounded**, because the removed shells were the ones below `g_n`.

**Step 2 (Phragmén--Lindelöf in each quadrant).**  `G` has exponential type at most `g_n + 1/2`, so
order `1 < 2`.  Multiply by `exp(lambda y)` in the third quadrant and by `exp(-lambda y)` in the
fourth: each multiplier has modulus `exp(-+ lambda u)` on the real ray, cancelling the boundary
growth, and modulus `1` on the imaginary ray.  Phragmén--Lindelöf for a quadrant (opening `pi/2`,
admissible for order `< 2`) then gives

```text
|G(y)| << exp(lambda |Re y|)   on the whole closed lower half-plane.
```

**Step 3 (extract the bottom shell).**  Let `v -> infinity` at fixed `u`.  Every surviving copy has
`R >= g_n`, and the tail obeys `sum_{R > g_n} exp(-sigma R) exp(-v(R - g_n)) <=
exp(-v (g_{n+1} - g_n)) sum_q exp(-sigma R q) -> 0`.  Hence `G(u - i v)` converges, uniformly on
compacts, to

```text
F(u) = exp(-i u g_n) * sum_J B_J exp(u J),    B_J = m_J * exp(-sigma (g_n + i J)) <> 0,
```

the sum running over the finitely many displacements `J` present in shell `n`, with `m_J > 0` the
multiplicity.  By Step 2, `|F(u)| << exp(lambda |u|)`.

**Step 4 (rigidity of a real-exponential sum).**  *Every point of one shell has the same height*, so
`F` is a pure phase times `sum_J B_J exp(u J)` -- a finite sum of **real** exponentials with distinct
real exponents and nonzero coefficients.  Its growth as `u -> +infinity` is exactly `max J`, and as
`u -> -infinity` exactly `-min J`; no cancellation is possible, since distinct real exponentials are
linearly independent and the extreme one dominates.  Therefore `|J| <= lambda` throughout shell `n`,
closing the induction.

> **[PAPER-PROVED]**  `h = V`.  Equivalently:
>
> **`Theta` is bounded on one vertical line `Re t = sigma > 0`  <=>  RH.**
>
> Both directions.  The forward direction is already `[LEAN-PROVED]`
> (`norm_xiPoissonTraceC_le_of_rh`); the converse is the argument above.

### Why this could not be done in the Gaussian coordinate

Two independent reasons, and both are exact:

1. **Order.**  Phragmén--Lindelöf in a quadrant admits growth `exp(B |z|^c)` only for `c < 2`.
   §27's unconditional Gaussian envelope is `exp(y^2 / (4 sigma))` -- order exactly `2`.  The
   hypothesis fails, not by a technicality but at the boundary.  The Poisson envelope is order `1`.
   (mathlib's `PhragmenLindelof.quadrant_III` / `quadrant_IV` carry literally this `∃ c < 2`
   hypothesis.)
2. **Shell homogeneity.**  Step 4 needs every point of a shell to share one height, so that the
   extracted limit is a sum of *real* exponentials rather than a general almost-periodic sum.  In the
   Poisson coordinate a shell is `Re alpha^ = |g|` constant, which is exactly a set of equal heights.

So the two features the square root bought -- finite order and equal-height shells -- are precisely
the two hypotheses the proof consumes.  §28's "the square root is forced" was a conjecture about
design; §29 is the proof obligation that consumes it.

### Status, stated exactly

This does **not** prove RH.  It closes the equivalence, and the remaining direction is the analytic
input: showing that `Theta(sigma + i .)` really is bounded, which on the prime side is cancellation
in the Poisson-smoothed explicit formula and is RH-strength.  What §29 removes is the *converse* gap
that §26 opened and §27 could not close -- previously one could not conclude RH even from a proof of
boundedness.  Now one can.

`[NOVELTY UNVERIFIED]`  The object is Cramér's `V`, and a boundedness characterization of RH in that
language may exist in the literature; I have not audited priority.  The proof above is written from
scratch and consumes only Phragmén--Lindelöf, discreteness of the zero heights, and linear
independence of real exponentials.

### Next

Formalize §29.  The pieces and their corpus/mathlib support:

- `PhragmenLindelof.quadrant_III` / `quadrant_IV` -- present in mathlib with the matching `c < 2`
  hypothesis;
- the type bound -- `norm_xiPoissonTerm_le`, already `[LEAN-PROVED]`;
- the boundary bound on the imaginary ray -- `summable_xiPoissonWeight` plus the shell split;
- shell discreteness and finiteness -- the corpus already has `finite_xiHeatShell`; the Poisson
  analogue `{q | R q <= R0}.Finite` should follow the same way.

`[OPEN CORE, current]`  The unconditional input: bound `‖Theta(sigma + i u)‖` on the real `u`-axis
from the prime side.  With §29 in hand this is now *sufficient* for RH, not merely necessary.

---

## §30 Step 4 of the converse, formalized

`[LEAN-PROVED]` `formal/GaloisForLFunctions/HTGeometry/RealExponentialSumRigidity.lean`
(lint clean; axioms `propext, Classical.choice, Quot.sound`):

```text
le_of_expSum_norm_le      : distinct real exponents, nonzero coefficients,
                            ‖sum_i B i * exp (u * J i)‖ <= C * exp (lam * |u|)  ->  J i <= lam
abs_le_of_expSum_norm_le  : the same hypotheses give |J i| <= lam
```

This is the rigidity that carries §29's induction, isolated as a general lemma with no reference to
Xi.  Its proof is the dominance argument: divide by the largest exponential, let `u -> infinity`,
and read off that the extreme coefficient vanishes unless its exponent obeys the bound.

Why it is worth stating separately: **it needs no separation or Diophantine hypothesis on the
exponents.**  Every earlier attempt in this investigation to exclude cancellation ran into the
frequency-separation problem -- §27 died on it explicitly (`the zero-free region gives only
delta << 1/log g, so there is no top frequency`).  The lemma above bypasses that entirely, because
within one Poisson shell the exponents are *real* and the largest one dominates outright, with no
almost-periodicity theory.  The Poisson coordinate's contribution is precisely that it makes shells
equal-height, so that the shell sum falls under this lemma.

### The chain as it now stands

```text
[LEAN-PROVED]  RH  ->  ‖Theta(tau)‖ <= Theta(Re tau)                norm_xiPoissonTraceC_le_of_rh
[LEAN-PROVED]  unconditional envelope exp(|Im tau| / 2)             norm_xiPoissonTraceC_le
[LEAN-PROVED]  growth rates bounded by 1/2, unconditionally         abs_xiPoissonPoint_im_lt_half
[LEAN-PROVED]  shell rigidity (step 4 of the converse)              abs_le_of_expSum_norm_le
[PAPER-PROVED] converse: Theta bounded on a line  ->  RH            §29 (steps 1-3 remain to formalize)
[OPEN CORE]    the analytic input: Theta bounded on a line
```

### Next

Formalize steps 1--3 of §29: the Phragmén--Lindelöf quadrant application
(`PhragmenLindelof.quadrant_III` / `quadrant_IV`, whose `∃ c < 2` growth hypothesis the Poisson
envelope satisfies and the Gaussian one does not), the shell decomposition, and the bottom-shell
extraction limit.  The corpus's `finite_xiHeatShell` is the template for the Poisson shell
finiteness these steps need.

---

## §31 The Poisson carrier is not prime-accessible — and the repair that keeps both properties

`[LEAN-PROVED]` `formal/GaloisForLFunctions/RHTower/XiPoissonShell.lean`
(lint clean; axioms `propext, Classical.choice, Quot.sound`):
`finite_xiPoissonShell` (via `g^2 - delta^2 <= g^2` against the corpus's `finite_xiHeatShell`) and
`exists_min_xiPoissonPoint_re` -- the lowest shell where §29's peeling starts.

### The obstruction found while looking for the prime side

The Poisson carrier's even test function is `h_t(r) = exp(-t |r|)`, whose Fourier transform is

```text
h^_t(x) = 2 t / (t^2 + x^2)     --  decay only  O(1/x^2).
```

Weil's explicit formula needs `h^(x) = O(exp(-(1/2 + eps)|x|))`, because the prime side is
`sum_n Lambda(n) n^(-1/2) h^(log n)` and

```text
sum_n Lambda(n) n^(-1/2) / (log n)^2  ~  integral exp(L/2) / L^2 dL  =  infinity.
```

> **[OBSTRUCTION]**  The Poisson trace has **no convergent explicit-formula representation** at any
> fixed `sigma > 0`.  Its prime content appears only as the boundary singularities of its
> continuation at `t -> i (+- log p^m)` -- Cramér's classical picture.  So §29's open core was
> *not* "bound a prime sum"; it was "control an analytic continuation near a boundary singular set",
> a materially worse-posed problem than I had recorded.

The cause is exact and local: `exp(-t|r|)` has a **corner at `r = 0`**.  Exponential decay of `h^`
is equivalent to analyticity of `h` in a strip, and the corner is the only thing breaking it.

### The repair: shift the mass

Smooth the corner by `|r| -> sqrt(r^2 + a^2)`, i.e. take the carrier

```text
Theta_a(t) = sum_q exp(-t * sqrt(w q + a^2)),    w q = xiSpectralPoint q ^ 2,   a > 1/2.
```

Four things must hold at once, and all four do.

1. **The root is well defined.**  `Re(w + a^2) = g^2 - delta^2 + a^2 > 0` for every copy, since
   `a > 1/2 > |delta|`.  No branch cut is met.
2. **Prime-accessible.**  `h_t(r) = exp(-t sqrt(r^2 + a^2))` has branch points only at `r = +- i a`,
   so it is analytic in the strip `|Im r| < a`, and `h^_t(x) = O(exp(-b|x|))` for every `b < a`.
   With `a > 1/2` pick `b in (1/2, a)`: the prime sum **converges**.
3. **The growth rates stay bounded by the displacement.**  Write `sqrt(w+a^2) = p + i q`, so
   `p^2 - q^2 = g^2 - delta^2 + a^2` and `2 p q = -2 g delta`.  From `p^2 >= p^2 - q^2` ,
   ```text
   |q| = |g delta| / p <= g |delta| / sqrt(g^2 - delta^2 + a^2) < |delta|,
   ```
   the last step because `a^2 > delta^2`.  So the vertical envelope is still order `1` with type
   `< 1/2`, and Phragmén--Lindelöf still applies where it failed for the Gaussian.
4. **Shells still work.**  Heights are `p >= sqrt(g^2 - delta^2 + a^2) -> infinity` with finite
   shells.  Equal heights are no longer forced, but that *helps*: distinct heights make the bottom
   shell a singleton and step 4 immediate, and equal heights are exactly the case the formalized
   `abs_le_of_expSum_norm_le` covers.  Either way the rigidity lemma applies unchanged.

> **[CONJECTURE -> refuted before it was written]**  I was about to record a carrier trade-off law --
> "vertical envelope order and prime-accessibility are in tension", with the Gaussian
> (`h^ ~ exp(-x^2/4t)`, prime-accessible, infinite-order envelope) opposing the Poisson
> (order-1 envelope, `h^ ~ 1/x^2`, not prime-accessible).  The mass-shifted carrier is an explicit
> counterexample to my own law: it has **both**.  Recorded because the failed law is what produced
> the construction.

### What this does to the open core

```text
before §31:  control the continuation of Theta near the singular set {i log p^m}   (ill-posed)
after  §31:  bound  sum_n Lambda(n) n^(-1/2) h^_{sigma+iu}(log n)  uniformly in u  (convergent sum)
```

with the converse of §29 still available, because properties 3 and 4 survive.  The trivial size of
that sum is `exp(|u|/2)`: the transform `h^_{sigma+iu}` has a light cone, being non-negligible only
for `|x| <~ |u|` (stationary phase at `r / sqrt(r^2+a^2) = -x/u`), so the sum runs effectively over
`n <= exp|u|` and `sum_{n <= exp|u|} Lambda(n) n^(-1/2) ~ 2 exp(|u|/2)`.  RH is exactly full
square-root cancellation in it.

### Next

`[OPEN CORE, current]`  Bound `sum_n Lambda(n) n^(-1/2) h^_{sigma+iu}(log n) = O_sigma(1)`.

The finite propagation speed is the new structural handle, and it is not present in any earlier
carrier in this investigation: the Gaussian and resolvent carriers weight *all* primes at every `u`,
while this one weights only `n <= exp|u|` and does so with a stationary-phase amplitude.  The next
concrete move is to compute that amplitude exactly and ask whether the light-cone edge -- where the
stationary point collides with the endpoint -- carries the whole obstruction, as it does in every
other wave-equation trace formula.

---

## §32 The mass-shifted transform, exactly — and the decoupling it produces

### The transform

```text
h^_t(x) = integral exp(-t sqrt(r^2 + a^2)) exp(-i r x) dr
        = 2 a t * K_1( a sqrt(t^2 + x^2) ) / sqrt(t^2 + x^2).
```

Check at `a -> 0`: `K_1(z) ~ 1/z`, so the right side tends to `2 t / (t^2 + x^2)`, which is exactly
the corner-carrier transform of §31.  The normalization is fixed by that limit.

### The light cone, and which side of it is dangerous

Put `t = sigma + i u`, `L = log n`, so `t^2 + L^2 = (L^2 - u^2 + sigma^2) + 2 i sigma u`.

- **Outside** (`L > u`): `sqrt(t^2+L^2)` is essentially real positive, and
  `K_1` contributes `exp(-a sqrt(L^2-u^2))` -- exponential decay.  Primes past the cone are dead.
- **Inside** (`L < u`): the argument sits just above the negative real axis, so
  ```text
  sqrt(t^2 + L^2)  ~  i sqrt(u^2 - L^2)  +  sigma u / sqrt(u^2 - L^2),
  ```
  giving an oscillating phase `exp(-i a sqrt(u^2-L^2))` and a damping
  `exp(- a sigma u / sqrt(u^2 - L^2))`.

> **[CORRECTION of §31's closing prediction]**  I predicted the light-cone *edge* would carry the
> obstruction, as it does in wave-equation trace formulae.  It does not: the damping
> `exp(-a sigma u / sqrt(u^2-L^2))` **blows up** as `L -> u`, so the edge is the most suppressed
> region, not the least.  The obstruction lives in the bulk.

Substituting `w = sqrt(u^2 - L^2)` and using the PNT density `exp(L/2) dL`, the modulus of the
prime side is

```text
exp(u/2) * integral_0^infinity exp(-w^2/(4u)) w^(-1/2) exp(-a sigma u / w) dw,
```

whose saddle sits at `w* = (2 a sigma)^(1/3) u^(2/3)` with value
`exp(-c (a sigma)^(2/3) u^(1/3))`.  So the modulus-only bound is

```text
|prime side|  <~  exp( u/2  -  c (a sigma)^(2/3) u^(1/3) ),
```

still unbounded.  The remaining `exp(-u/2 + c u^(1/3))` must come from the phase
`exp(-i a sqrt(u^2 - L^2))`, which varies by `~ a sqrt(u)` across the saddle width -- that is where
the cancellation has to live, and it is a *single explicit oscillatory factor*, not a sum of
prime phases.

### The decoupling

Evaluate the other two sides of the explicit formula on this carrier.

- **Archimedean.**  `A = (1/2 pi) integral exp(-t sqrt(r^2+a^2)) [Re psi(1/4 + i r/2) - log pi] dr`.
  The phase `u sqrt(r^2+a^2)` is stationary only at `r = 0`, where the second derivative is `1/a`,
  so stationary phase gives `A = O(u^(-1/2))`.  **It decays.**
- **Poles.**  The `s = 0, 1` terms are `h_t(+- i/2) = exp(-t sqrt(a^2 - 1/4))`, of modulus
  `exp(-sigma sqrt(a^2 - 1/4))` -- bounded, and *defined at all*, exactly when `a > 1/2`.

> **The threshold `a > 1/2` is forced twice, independently**: once by prime-accessibility (the
> transform must decay faster than `exp(-|x|/2)`), once by the pole terms staying finite.  One
> number, two unrelated requirements.

Consequently:

> **[CONJECTURE, sharp form of the open core]**  RH holds **iff**
> ```text
> sum_n Lambda(n) n^(-1/2) * 2 a t K_1( a sqrt(t^2 + (log n)^2) ) / sqrt(t^2 + (log n)^2)
> ```
> is bounded on a line `Re t = sigma > 0`, for one `a > 1/2`.

This is a **purely arithmetic** statement: no zeros, and the archimedean contribution is
asymptotically negligible rather than a competing large term.

### Why that matters against this project's own no-gos

§25 concluded that the entire difficulty of the Gaussian ladder sat in the **cross term** `(II)`,
the archimedean-times-prime interaction, and §15's two counterexample families proved that the
functional equation and the Euler product must interact -- no criterion using one alone can work.
The mass-shifted carrier does not violate that; it **relocates** the interaction:

```text
Gaussian carrier:  FE and Euler interact through a large cancelling cross term      (§25)
mass-shifted:      FE enters as a *constraint on the carrier parameter*, a > 1/2,
                   and the archimedean term is O(u^(-1/2)) -- there is no cross term
```

That is the founding metaphor applied to the carrier itself: the object is fixed by a constraint,
not propagated by a cancellation.  The interaction has not disappeared -- it has been pushed into
the admissibility condition on `a`, where it is a single inequality instead of an unsigned
difference of large quantities.

### Next

`[OPEN CORE, current]`  Show `integral_0^infinity exp(-w^2/(4u)) w^(-1/2) exp(-a sigma u / w)
exp(-i a w) d nu(w)` is `O(exp(-u/2))`, where `d nu` is the prime measure pushed to the `w`
coordinate.  Concretely: compute the *complex* saddle of `-w^2/(4u) - a sigma u / w - i a w` (the
real saddle at `u^(2/3)` is destroyed by the linear imaginary term, which dominates there, so the
true critical point migrates toward the endpoint `w = u`, i.e. `L -> 0`).  That migration is the
next thing to settle: if the dominant contribution really moves to `L = O(1)`, the criterion reads
on the *small* primes, which would be a structural inversion worth all of §§26--32.

---

## §33 The complex saddle escapes — and `a > 1/2` is forced a third and fourth time

### The saddle

Keeping `sqrt(u^2 - w^2)` exact (the previous expansion assumed `w << u`, which the answer violates),
the full exponent of the smooth prime side in the `w = sqrt(u^2 - L^2)` coordinate is

```text
Psi(w) = (1/2) sqrt(u^2 - w^2)  -  i a w  -  a sigma u / w.
```

Dropping the `sigma`-term (it is `O(a sigma / u)` near `w ~ u`),

```text
Psi'(w) = 0   <=>   w / sqrt(u^2 - w^2) = -2 i a   <=>   w^2 (1 - 4 a^2) = -4 a^2 u^2
      =>  w* = u * 2a / sqrt(4 a^2 - 1).
```

Two readings, both sharp:

1. **`w*` exists only for `a > 1/2`.**  Third independent appearance of the same threshold.
2. **`w* > u` always**, since `2a > sqrt(4a^2 - 1)`.  The saddle lies **outside** the integration
   range `(0, u]`.  There is no interior stationary point, so the integral is endpoint-governed,
   not saddle-governed -- and the endpoint `w = u` is `L = 0`, the small-prime end.

> **[CONFIRMED, §32's prediction]**  The dominant contribution does migrate to the endpoint
> `L -> 0`.  The modulus-only estimate `exp(u/2 - c u^(1/3))` is attained nowhere on the true
> contour; the oscillation `exp(-i a w)` buys the entire `exp(u/2)`.

### An independent confirmation that costs nothing

The saddle argument needs a contour deformation to be airtight.  It does not need to be, because the
same conclusion follows structurally.  The smooth part of the prime side is by definition what
survives when `psi(x)` is replaced by `x` -- i.e. when zeta has its pole and **no zeros at all**.  In
that model the explicit formula reads `0 = A + poles - prime side`, so

```text
smooth prime side  =  A + poles  =  O(u^(-1/2))  +  2 exp(-t sqrt(a^2 - 1/4)),
```

of modulus `O(u^(-1/2)) + 2 exp(-sigma sqrt(a^2 - 1/4))`.

> **[PAPER-PROVED]**  The mean (PNT) part of the prime side is bounded on every line `Re t = sigma`,
> and it is bounded **exactly when `a > 1/2`** -- the fourth appearance of the threshold, now from
> the pole term `h_t(+- i/2) = exp(-t sqrt(a^2 - 1/4))` being defined at all.

Two derivations, one from a complex saddle and one from the pole structure, give the same
`a > 1/2`.  That is not a coincidence to be admired; it is the functional equation entering the
carrier as a constraint, exactly as §32 predicted it would.

### The split this produces

```text
prime side  =  [ mean part ]  +  [ fluctuation part ]
               bounded, proved      RH-equivalent
```

with the fluctuation part being the PNT error `psi(x) - x` integrated against the `K_1` kernel.
So:

> **RH  <=>  `sum_n Lambda(n) n^(-1/2) h^_t(log n) - 2 exp(-t sqrt(a^2-1/4))` is bounded on one
> line `Re t = sigma > 0`**, with the subtracted term explicit and the difference carrying all the
> content.

This is the cleanest form the investigation has reached.  Compare §25, where the difficulty was an
**unsigned cross term between two large quantities** and neither piece was separately controlled;
here one of the two pieces is proved bounded and the other is a single classical error term.

### Hostile audit

The resulting equivalence -- RH iff the smoothed PNT error is square-root small -- is **classical**.
`[BRIDGE]`.  I claim none of it as new.

What is not classical, and is what §§26--33 were for:

- the carrier `exp(-t sqrt(w + a^2))` on which **both** §29's converse and the explicit formula are
  available, which the Gaussian carrier (order 2, PL fails) and the pure Poisson carrier (transform
  decays like `1/x^2`, explicit formula diverges) each fail in a different way;
- the threshold `a > 1/2` appearing four times from four unrelated requirements
  (transform decay, pole finiteness, root branch, saddle existence);
- `[LEAN-PROVED]` the rigidity, envelope, growth-rate, and shell facts that make the converse
  mechanical rather than analytic.

### Next

`a -> infinity` sends `w* -> u`: the escaped saddle **coalesces with the endpoint**.  That is an
Airy-type transition, and coalescence regimes are where trace formulae usually leak their sharpest
information.  `a -> 1/2+` sends `w* -> infinity`: maximal separation, but minimal convergence
margin.  So `a` is a genuine dial between two degenerations, and the next question is what the
coalescence at large `a` computes -- concretely, expand `Psi` to third order at `w = u` when
`w* - u = u(2a/sqrt(4a^2-1) - 1) ~ u/(8a^2)` is comparable to the endpoint scale, and read off which
primes the Airy window selects.

---

## §34 Bottom-shell rigidity, formalized on the Xi divisor

`[LEAN-PROVED]` `formal/GaloisForLFunctions/RHTower/XiPoissonBottomShellRigidity.lean`
(lint clean; axioms `propext, Classical.choice, Quot.sound`):

```text
xiPoissonBottomCopy / xiPoissonBottomHeight / xiPoissonBottomShell
xiPoisson_line_factor
  exp(-t (R + i J)) = exp(-t R) * ( exp(-i sigma J) * exp(u J) ),   t = sigma + i u
xiPoissonBottomShellSum_eq
  the bottom-shell sum factors as a height factor times a real-exponential sum in u
abs_im_xiPoissonPoint_le_of_bottomShellSum_growth
  growth <= C exp(lam |u|)  ->  every bottom-shell displacement satisfies |delta| <= lam
xiSpectralPoint_im_eq_zero_of_bottomShellSum_bounded
  a *bounded* bottom-shell sum puts the lowest zeros exactly on the critical line
```

This is §29's step 4 no longer as a general lemma but instantiated on the actual Xi divisor, and it
is the first statement in this corpus that concludes **"these zeros lie on the critical line"** from
an analytic growth hypothesis rather than from RH.

The proof is exactly the mechanism §28 predicted and §30 isolated:

1. shell homogeneity -- every copy in the bottom shell shares the height `xiPoissonBottomHeight`,
   so the height factors out and what remains is `sum_q exp(-i sigma J q) * exp(u J q)`;
2. grouping equal displacements gives coefficients `(multiplicity) * exp(-i sigma J)`, which are
   nonzero because a multiplicity is positive and a phase never vanishes;
3. `HTGeometry.abs_le_of_expSum_norm_le` converts the growth bound into the displacement bound.

No frequency separation, no almost-periodicity, no Diophantine input -- the obstruction that killed
§27 does not appear anywhere in the argument.

### What is still missing for the full converse

Steps 1--3 of §29, all analytic rather than algebraic:

```text
[to formalize]  Theta is analytic on Re t > 0                      (locally uniform convergence)
[to formalize]  Phragmen-Lindelof in the two lower quadrants       (mathlib: quadrant_III/IV)
[to formalize]  the bottom-shell extraction limit v -> infinity    (geometric tail in the shell gap)
[to formalize]  the peeling induction over shells                  (heights discrete, shells finite)
[LEAN-PROVED]   the rigidity that each induction step consumes     (this file)
```

The shell-gap estimate the extraction needs is
`sum_{R > g_n} exp(-sigma R) exp(-v (R - g_n)) <= exp(-v (g_{n+1} - g_n)) * sum_q exp(-sigma R q)`,
whose right-hand factor is exactly the already-proved `summable_xiPoissonWeight`.

### Next

Formalize the extraction limit, which is the only step of §29 that needs a genuinely new estimate:
the others are either mathlib (`PhragmenLindelof.quadrant_III` / `quadrant_IV`) or already in the
corpus (`summable_xiPoissonWeight`, `finite_xiPoissonShell`, `exists_min_xiPoissonPoint_re`,
`abs_le_of_expSum_norm_le`).  Concretely: define the second-lowest height as the minimum over the
complement of the bottom shell -- finite by `finite_xiPoissonShell` on any larger radius -- and prove
`Tendsto (fun v => exp (g_1 v) * Theta_{>1}(sigma + v)) atTop (nhds 0)` from the geometric bound
above.

---

## §35 The extraction, formalized

`[LEAN-PROVED]` `formal/GaloisForLFunctions/RHTower/XiPoissonBottomExtraction.lean`
(lint clean; axioms `propext, Classical.choice, Quot.sound`):

```text
exists_min_xiPoissonPoint_re_of_nonempty
  every nonempty set of copies attains a least height (shells are finite)
mem_xiPoissonAboveBottom
  the complement of the bottom shell is exactly {q : g_1 < R q}
exists_xiPoissonSecondHeight
  a strict spectral gap above the bottom shell
tendsto_exp_bottomHeight_mul_aboveBottom_tail
  exp(g_1 v) * sum_{q above} exp(-(sigma+v) R q)  ->  0
tendsto_exp_bottomHeight_mul_xiPoissonTraceReal
  exp(g_1 v) * Theta(sigma + v)  ->  (card of bottom shell) * exp(-sigma g_1)
```

The last one is the extraction actually performed: weighting the trace by the bottom height holds
the lowest shell fixed and annihilates everything above it, and the limit **is the multiplicity of
the lowest shell**.  That the gap exists at all is not an assumption -- it follows from shell
finiteness, which followed from the corpus's `finite_xiHeatShell`.

### The converse's ledger, updated

```text
[LEAN-PROVED]  shell finiteness, least height, spectral gap        XiPoissonShell, this file
[LEAN-PROVED]  the extraction limit (step 3)                       this file
[LEAN-PROVED]  shell homogeneity / line factorization              XiPoissonBottomShellRigidity
[LEAN-PROVED]  real-exponential rigidity (step 4)                  RealExponentialSumRigidity
[LEAN-PROVED]  bottom shell on the line from a bounded shell sum   XiPoissonBottomShellRigidity
[LEAN-PROVED]  unconditional order-1 envelope, RH collapse          XiPoissonVerticalType
[to formalize] analyticity of Theta on Re t > 0                    (step 1)
[to formalize] Phragmen-Lindelof in the lower quadrants            (step 2, mathlib quadrant_III/IV)
[to formalize] the peeling induction over shells                   (assembly)
[OPEN CORE]    the analytic input: Theta bounded on a line
```

Steps 3 and 4 -- the two that needed new mathematics -- are done.  Step 2 is a mathlib call whose
hypothesis (`∃ c < 2`) the order-1 envelope satisfies and the Gaussian carrier provably does not.
Step 1 is routine locally-uniform convergence.  The assembly is an induction over a discrete,
finite-shelled height set, every ingredient of which is now in the corpus.

### Next

Formalize step 1: `Theta` is analytic on `Re t > 0`.  The corpus already supplies the two things
this needs -- `summable_xiPoissonWeight` for a locally uniform dominating bound on each half-plane
`Re t >= sigma_0 > 0`, and `norm_xiPoissonTerm_le` for the vertical direction.  With analyticity in
hand, step 2 is `PhragmenLindelof.quadrant_III` / `quadrant_IV` applied to
`Theta(sigma + i y) * exp(i g_1 y)`, whose boundary bounds are exactly
`tendsto_exp_bottomHeight_mul_xiPoissonTraceReal` (imaginary ray) and the hypothesis (real ray).

---

## §36 Step 1 done: the Poisson trace is analytic on the right half-plane

`[LEAN-PROVED]` `formal/GaloisForLFunctions/RHTower/XiPoissonTraceAnalytic.lean`
(lint clean; axioms `propext, Classical.choice, Quot.sound`):

```text
xiPoissonBox / isOpen_xiPoissonBox
norm_xiPoissonTerm_le_on_box    ‖term‖ <= exp (M/2) * xiPoissonWeight sigma_0  on {sigma_0 < Re t} ∩ {|Im t| < M}
differentiableOn_xiPoissonTraceC_box
analyticOnNhd_xiPoissonTraceC   AnalyticOnNhd C Theta {t | 0 < Re t}
```

The domination is the unconditional envelope again: heights are nonnegative
(`xiPoissonPoint_re_nonneg`) and displacements are bounded by `1/2`
(`abs_xiPoissonPoint_im_lt_half`), so on a box the multipliers are dominated by
`exp(M/2) * exp(-sigma_0 R q)`, summable by `summable_xiPoissonWeight`.  Weierstrass
(`Complex.differentiableOn_tsum_of_summable_norm`) gives differentiability on each box; boxes are a
neighbourhood basis of the half-plane.  **No hypothesis on the zeros anywhere.**

### The converse's ledger

```text
[LEAN-PROVED]  analyticity of Theta on Re t > 0                   step 1   XiPoissonTraceAnalytic
[to formalize] Phragmen-Lindelof in the lower quadrants           step 2   mathlib quadrant_III/IV
[LEAN-PROVED]  the extraction limit                               step 3   XiPoissonBottomExtraction
[LEAN-PROVED]  real-exponential rigidity                          step 4   RealExponentialSumRigidity
[LEAN-PROVED]  bottom shell on the line from a bounded shell sum           XiPoissonBottomShellRigidity
[LEAN-PROVED]  unconditional order-1 envelope; RH collapse                 XiPoissonVerticalType
[to formalize] the peeling induction over shells                  assembly
[OPEN CORE]    the analytic input: Theta bounded on a line
```

Three of the four steps of §29 are formalized.  Step 2 is a mathlib call, and its growth hypothesis
`∃ c < 2` is met by the order-1 envelope `norm_xiPoissonTraceC_le` -- the same hypothesis the
Gaussian carrier fails at order exactly `2`, which is why §§26--28 had to change coordinates before
any of this became reachable.

### Next

Step 2.  Apply `PhragmenLindelof.quadrant_III` and `quadrant_IV` to
`y |-> Theta(sigma + i y) * exp(i g_1 y) * exp(± lam y)`.  Its four hypotheses are now all in the
corpus or in mathlib:

```text
DiffContOnCl on the quadrant     <-  analyticOnNhd_xiPoissonTraceC (this file)
growth exp(B ‖z‖^c), c < 2       <-  norm_xiPoissonTraceC_le           (order 1)
bound on the real ray            <-  the hypothesis being contraposed
bound on the imaginary ray       <-  tendsto_exp_bottomHeight_mul_xiPoissonTraceReal
```

---

## §37 A gap in §29 step 3, found by preparing its formalization — and the fix

### The error

§29 step 3 asserted that `G(u - i v)` converges as `v -> infinity` to a finite exponential sum.  It
does not.  Writing the bottom-shell copies as `alpha^ = g_1 + i J` and `G(y) = Theta(sigma + i y)
exp(i g_1 y)`, the bottom contribution at `y = u - i v` is

```text
exp(g_1 v) * exp( -((sigma+v) + i u) (g_1 + i J) )
  = m_J * exp(-sigma g_1 + u J) * exp( -i [ (sigma+v) J + u g_1 ] ),
```

whose modulus `m_J exp(-sigma g_1 + u J)` is indeed independent of `v` -- but whose **phase spins in
`v` at frequency `J`**.  So the bottom-shell part does not converge as `v -> infinity` unless every
`J` is already zero, which is what was to be proved.  Only the *tail* converges (to `0`).

> **[CORRECTED]**  §29 step 3, as written, is invalid.  The claim "converges uniformly on compacts"
> silently assumed the very conclusion.  Found by trying to write the Lean statement: the limit had
> no target to name.

This is what the formalization gate is for.  The paper argument read as complete for four sections.

### What survives untouched

Steps 1, 2 and 4 are unaffected, and the two facts already formalized remain exactly right:

- `tendsto_exp_bottomHeight_mul_aboveBottom_tail` -- the *tail* really does vanish; it is a statement
  about the weights (moduli), where no phase occurs;
- `abs_le_of_expSum_norm_le` -- the rigidity of finite real-exponential sums.

What was wrong was the step that connects them.

### The fix: average in the real direction

Keep the `exp(i g_1 y)` twist -- it is what makes both PL boundary rays bounded:

```text
real ray      y = x :        |G(x)| = |Theta(sigma + i x)|  <= C            (the hypothesis)
imaginary ray y = -i v :     |G(-iv)| = exp(g_1 v) |Theta(sigma+v)|
                                      <= sum_q exp(-sigma R q) exp(-v(R q - g_1))
                                      <= Theta_R(sigma)                    (since R q >= g_1)
```

so Phragmén--Lindelöf on the two lower quadrants gives `|G| <= M' := max(C, Theta_R(sigma))` on the
whole closed lower half `y`-plane, i.e.

> **`|Theta(t)| <= M' exp(-g_1 (Re t - sigma))` for `Re t >= sigma`** -- boundedness on one line
> upgrades to *decay at the bottom-shell rate* on the half-plane.

Now instead of a limit, take a **mean square in `v`** at fixed `u`.  With
`A_J = m_J exp(-sigma g_1 + u J) exp(-i(sigma J + u g_1))`,

```text
| sum_J A_J exp(-i v J)  +  tail(v) |  <=  M'   for all v >= 0,
```

the `J` are finitely many and distinct, and `tail(v) -> 0`.  Averaging `|.|^2` over `v in [0,T]` and
letting `T -> infinity`, the cross terms `exp(i v (J' - J))` average to zero, so

```text
sum_J |A_J|^2  =  sum_J m_J^2 exp(-2 sigma g_1) exp(2 u J)  <=  M'^2   for every u.
```

Each summand is therefore bounded in `u`, which forces `J = 0` for every bottom-shell copy.  The
peeling induction then proceeds as before.

> **[PAPER-PROVED, corrected]**  `Theta` bounded on one vertical line `Re t = sigma > 0` `<->` RH.

The new ingredient is Parseval for a **finite** trigonometric polynomial -- elementary, no Bohr
theory, no Kronecker, no frequency separation, because the bottom shell is finite.  It replaces the
non-existent limit.

### What this costs and what it buys

Cost: one integral-average lemma to formalize, where before there was a (wrong) pointwise limit.

Buy: the corrected route explains something the old one obscured.  The `exp(i g_1 y)` twist is not a
technical convenience -- it is the only multiplier making *both* boundary rays bounded at once, and
it works because `g_1` is the least height, i.e. because the shell structure exists.  The same
inequality `R q >= g_1` that gives the imaginary-ray bound is the one that makes the bottom shell
the bottom shell.

### Next

Formalize, in order: (i) the imaginary-ray bound `exp(g_1 v) Theta_R(sigma+v) <= Theta_R(sigma)`,
which is termwise and immediate from `xiPoissonBottomCopy_min`; (ii) Phragmén--Lindelöf on the two
lower quadrants via mathlib; (iii) Parseval for a finite trigonometric polynomial.  Item (iii) is the
only one needing new mathematics, and it is the corrected replacement for the step this section
retracts.

---

## §38 The fix is lighter than §37 claimed — no Parseval needed

§37 proposed repairing step 3 with a mean-square average in `v`, to defeat the spinning phases
`exp(-i(sigma+v)J)`.  That is unnecessary.  **Phases do not change moduli**, so the largest real
exponent dominates whatever the phases do:

```text
‖ sum_J B_J(v) exp(u J) ‖  >=  |B_{Jmax}(v)| exp(u Jmax)  -  sum_{J < Jmax} |B_J(v)| exp(u J),
```

and since `|B_J(v)| = m_J exp(-sigma g_1)` is **independent of `v`**, dividing by `exp(u Jmax)` and
letting `u -> infinity` leaves `m_{Jmax} exp(-sigma g_1) <= 0` whenever `Jmax > 0`.  No averaging,
no Parseval, no Kronecker, no almost-periodicity.

`[LEAN-PROVED]` `formal/GaloisForLFunctions/HTGeometry/RealExponentialSumRigidity.lean`
(lint clean; axioms `propext, Classical.choice, Quot.sound`):

```text
le_zero_of_expSum_norm_le
  finite s, J injective on s, m i > 0, B : R -> i -> C with ‖B u i‖ = m i,
  ‖ sum_i B u i * exp (u * J i) ‖ <= M  for all u
  ->  J i <= 0  for all i in s
```

The coefficient family `B` is allowed to depend on `u` arbitrarily -- only its **moduli** are fixed.
That is exactly the shape the corrected §29 needs, because the bottom-shell coefficients
`B_J(v) = m_J exp(-sigma g_1) exp(-i(sigma+v)J)` have constant modulus and free phase, and the
parameter `v` must be sent to infinity together with `u` to control the tail.

### Retraction inside a retraction

§37's "the new ingredient is Parseval for a finite trigonometric polynomial" is withdrawn.  The
correct ingredient is the phase-robust dominance above, which is the same mechanism as the original
`abs_le_of_expSum_norm_le`, generalized in exactly one direction: the coefficients may move as long
as their moduli do not.  Two corrections in two sections, both found by asking what the Lean
statement would have to be.

### The converse's ledger

```text
[LEAN-PROVED]  analyticity of Theta on Re t > 0                       step 1
[to formalize] Phragmen-Lindelof on the lower quadrants               step 2 (mathlib)
[LEAN-PROVED]  imaginary-ray boundary bound for step 2                step 2 input
[LEAN-PROVED]  tail decay of the above-bottom part                    step 3
[LEAN-PROVED]  phase-robust dominance                                 step 3/4, corrected
[LEAN-PROVED]  real-exponential rigidity (fixed coefficients)         step 4
[LEAN-PROVED]  bottom shell on the line from a bounded shell sum
[LEAN-PROVED]  unconditional order-1 envelope; RH collapse
[to formalize] the peeling induction over shells                      assembly
[OPEN CORE]    the analytic input: Theta bounded on a line
```

Every ingredient of the converse is now either formalized or a mathlib call.  What remains is step 2
and the assembly.

### Next

Step 2 in Lean: `PhragmenLindelof.quadrant_III` and `quadrant_IV` applied to
`y |-> xiPoissonTraceC (sigma + y * I) * exp (I * g_1 * y)`.  Its hypotheses map onto
`analyticOnNhd_xiPoissonTraceC` (DiffContOnCl), `norm_xiPoissonTraceC_le` (growth of order `1 < 2`),
the contraposed hypothesis (real ray), and `exp_bottomHeight_mul_xiPoissonTraceReal_le`
(imaginary ray).

---

## §39 Step 2 done: Phragmén--Lindelöf, formalized

`[LEAN-PROVED]` `formal/GaloisForLFunctions/RHTower/XiPoissonHalfPlaneDecay.lean`
(lint clean; axioms `propext, Classical.choice, Quot.sound`):

```text
xiPoissonTraceReal_antitone            the real-time trace decreases in sigma
xiPoissonTwist sigma y  =  Theta (sigma + y I) * exp (I g_1 y)
differentiableOn_xiPoissonTwist        differentiable on {Im y < sigma}
norm_xiPoissonTwist_le                 ‖W y‖ <= Theta_R(sigma) exp((1/2 + g_1) ‖y‖)   -- order 1
norm_xiPoissonTwist_real_ray           the twist has modulus one on the real axis
norm_xiPoissonTwist_imaginary_ray      ‖W(x I)‖ <= Theta_R(sigma)  for x <= 0, unconditionally
norm_xiPoissonTwist_le_of_line_bound   Phragmen-Lindelof on quadrants III and IV
norm_xiPoissonTraceC_le_of_line_bound
  ‖Theta t‖ <= max C (Theta_R sigma) * exp (-(g_1 (Re t - sigma)))    for Re t >= sigma
```

The last statement is the one §37 predicted: **boundedness on a single vertical line upgrades to
decay at the bottom-shell rate across the whole half-plane.**

The mathlib hypothesis that mattered is `∃ c < 2` in `PhragmenLindelof.quadrant_III` /
`quadrant_IV`.  It is discharged with `c = 1` by `norm_xiPoissonTwist_le`, which is the order-1
envelope of §28.  The Gaussian carrier's envelope is `exp(y^2/(4 sigma))`, order exactly `2`: the
hypothesis fails, not marginally but at the boundary of the theorem.  That is now a checked fact
about this proof, not a heuristic about carriers.

### The converse's ledger

```text
[LEAN-PROVED]  analyticity of Theta on Re t > 0                     step 1
[LEAN-PROVED]  Phragmen-Lindelof; half-plane decay                  step 2
[LEAN-PROVED]  tail decay of the above-bottom part                  step 3
[LEAN-PROVED]  phase-robust dominance                               step 3/4
[LEAN-PROVED]  real-exponential rigidity                            step 4
[LEAN-PROVED]  bottom shell on the line from a bounded shell sum
[LEAN-PROVED]  unconditional order-1 envelope; RH collapse
[to formalize] assembly: bottom shell on the line, then peel
[OPEN CORE]    the analytic input: Theta bounded on a line
```

All four steps of §29 are now formalized as separate theorems.  What is left is the assembly:
combine half-plane decay with tail decay and phase-robust dominance to conclude that the bottom
shell lies on the critical line, then induct over shells.

### Next

The assembly's first half.  From `norm_xiPoissonTraceC_le_of_line_bound` at `t = (sigma+v) + i u`,
multiply by `exp (g_1 v)`: the bottom-shell part becomes
`sum_J m_J exp(-sigma g_1 + u J) exp(-i[(sigma+v)J + u g_1])`, of constant modulus in `v`, and the
remainder is controlled by `tendsto_exp_bottomHeight_mul_aboveBottom_tail`.  Feeding that into
`le_zero_of_expSum_norm_le` (whose coefficients are allowed to move as long as their moduli do not)
gives `J <= 0` throughout the bottom shell, and the divisor's `J -> -J` symmetry gives `J = 0`.

---

## §40 Assembly, part 1: the vertical split and the weighted tail bound

`[LEAN-PROVED]` `formal/GaloisForLFunctions/RHTower/XiPoissonVerticalSplit.lean`
(axioms `propext, Classical.choice, Quot.sound`):

```text
re_vertical / im_vertical
xiPoissonTraceC_vertical_split
  Theta(s + i u) = (bottom-shell sum) + (above-bottom sum)
exp_bottomHeight_mul_norm_aboveBottomSum_le
  exp(g_1 v) * ‖above-bottom sum at (sigma+v) + i u‖
    <= exp(|u|/2) * exp(-(g_2 - g_1) v) * (constant)
```

The tail bound is the hinge of the assembly.  Two exponentials pull against each other:
`exp(|u|/2)` from the vertical direction (the displacement bound `|delta| < 1/2`, again) and
`exp(-(g_2-g_1) v)` from the spectral gap.  Choosing `v = |u| / (2 (g_2 - g_1))` makes their product
at most `1`, so the above-bottom part stays bounded **uniformly in `u`** while the bottom-shell terms
keep constant modulus.  That is exactly the trade the corrected §38 lemma is designed to consume:
its coefficients may move with `u` provided their moduli do not.

### What remains of the assembly

```text
choose v(u) = |u| / (2 (g_2 - g_1)),  t = (sigma + v(u)) + i u
half-plane decay          ->  exp(g_1 v) ‖Theta t‖ <= max C (Theta_R sigma)
tail bound (this file)    ->  exp(g_1 v) ‖above-bottom‖ <= constant
split (this file)         ->  exp(g_1 v) ‖bottom-shell sum‖ <= M''  for all u
regroup by displacement   ->  ‖ sum_J B(u,J) exp(u J) ‖ <= M'' ,  |B(u,J)| = m_J exp(-sigma g_1)
le_zero_of_expSum_norm_le ->  J <= 0 throughout the bottom shell
line-conjugation symmetry ->  J = 0
```

Every arrow is now either a formalized theorem or an arithmetic substitution.  The regrouping step
is the one already carried out in `XiPoissonBottomShellRigidity`.

### Note on the shared tree

The formal lint gate currently reports one failure that is not from this work:
`GaloisForLFunctions.RHTower.GammaSewnSynchronizedRecoveryContraction` is present in the tree but not
yet wired into its umbrella.  It is an untracked file created by concurrent work in this repository;
every module of this investigation builds, lints and passes `#print axioms` on its own, and I have
left the other module alone rather than wiring someone else's in-progress work.

### Next

The assembly itself: instantiate `v = |u| / (2 (g_2 - g_1))`, chain the three bounds above, regroup
the bottom-shell sum by displacement, and apply `le_zero_of_expSum_norm_le`.  Then the line
conjugation `xiZeroCopyLineConjEquiv` -- which fixes heights and negates displacements, hence maps
the bottom shell to itself -- turns `J <= 0` into `J = 0`.

---

## §41 The assembly closes: a bounded line puts the bottom shell on the critical line

`[LEAN-PROVED]` `formal/GaloisForLFunctions/RHTower/XiPoissonBottomOnLine.lean`
(axioms `propext, Classical.choice, Quot.sound`):

```text
xiPoissonBottomShell_regroup            the shell sum grouped by displacement
xiPoissonPoint_im_nonpos_of_line_bound  Theta bounded on Re t = sigma  ->  every bottom
                                        displacement is <= 0
xiPoissonPoint_lineConj                 line conjugation conjugates the Poisson point
mem_xiPoissonBottomShell_lineConj       the bottom shell is stable under it
xiPoissonPoint_im_eq_zero_of_line_bound
xiSpectralPoint_im_eq_zero_of_line_bound
  Theta bounded on one vertical line  ->  the lowest zeros lie on the critical line
```

The proof runs exactly the chain §40 laid out.  With `v(u) = |u| / (2 (g_2 - g_1))`:

```text
half-plane decay (§39)   ->  exp(g_1 v) ‖Theta‖            <= max C (Theta_R sigma)
tail bound (§40)         ->  exp(g_1 v) ‖above-bottom‖     <= K          (the two exponentials cancel)
vertical split (§40)     ->  exp(g_1 v) ‖bottom-shell sum‖ <= M + K      uniformly in u
shell homogeneity (§34)  ->  = exp(-sigma g_1) ‖ sum_J B(u,J) exp(u J) ‖
phase-robust dominance (§38) ->  J <= 0 throughout the bottom shell
line conjugation         ->  J = 0
```

Every step is a formalized theorem; nothing in the chain is assumed.

### What this is, and what it is not

It is **not** RH, and it is not conditional on RH.  It is an unconditional implication whose
hypothesis is an explicit analytic bound and whose conclusion is a statement about zero locations --
the first such implication in this corpus.  The hypothesis `[OPEN CORE]` (`Theta` bounded on one
vertical line) remains exactly as hard as it was; what has changed is that discharging it now
*delivers* zeros on the line rather than merely being equivalent to something.

### What remains for the full converse

The peeling induction.  §29's argument removes the bottom shell and repeats, and every ingredient
transfers: the removed shell contributes a bounded term (now that its displacements are known zero),
so the reduced trace is again bounded on the line, and the reduced divisor's own bottom shell is the
next height up.  Formalizing it needs the shell-indexed recursion, not new mathematics.

### Next

Set up the induction: define the trace restricted to heights `>= g`, show it inherits the vertical
bound whenever the shells below `g` are known to lie on the line, and apply
`xiPoissonPoint_im_eq_zero_of_line_bound` to the restricted divisor.  The restricted objects need the
same four facts already proved for the full divisor -- finiteness, least height, gap, envelope -- so
the cleanest route is to generalize `XiPoissonShell` through `XiPoissonBottomOnLine` over an
arbitrary height cut, then instantiate.

---

## §42 The cut trace: infrastructure for the peeling induction

`[LEAN-PROVED]` `formal/GaloisForLFunctions/RHTower/XiPoissonCutTrace.lean`
(axioms `propext, Classical.choice, Quot.sound`):

```text
xiPoissonCut g                          the copies of height at least g
finite_xiPoissonCut_shell               shells of a cut divisor stay finite
summable_xiPoissonCutWeight             the weight stays summable
xiPoissonCutTraceReal / xiPoissonCutTraceC
norm_xiPoissonCutTraceC_le              the same order-one envelope, unconditionally
norm_xiPoissonCutTraceC_le_of_rh        RH still collapses it
xiPoissonCutTraceReal_antitone
analyticOnNhd_xiPoissonCutTraceC        analytic on Re t > 0
```

`exists_min_xiPoissonPoint_re_of_nonempty` was already stated for an arbitrary set of copies, so the
least height of a cut divisor needs nothing new -- a small piece of foresight from §35 that pays
here.

### Why this is the right object

The peeling induction of §29 removes a shell and repeats.  What it recurses on is not a modified
trace but a **restricted divisor**, and the argument of §§39--41 consumes exactly five properties of
whatever divisor it is handed:

```text
shells finite            ->  finite_xiPoissonCut_shell
a least height exists    ->  exists_min_xiPoissonPoint_re_of_nonempty (already general)
weight summable          ->  summable_xiPoissonCutWeight
order-one envelope       ->  norm_xiPoissonCutTraceC_le
analytic on Re t > 0     ->  analyticOnNhd_xiPoissonCutTraceC
```

All five now hold for every cut, so the induction has somewhere to stand.  Notably the envelope and
the analyticity come from `|delta| < 1/2` and the height nonnegativity -- properties of *individual
copies*, not of the divisor as a whole -- which is why restriction costs nothing.

### What remains

Re-derive, over a cut, the four steps that are currently proved only for the full divisor: the
imaginary-ray bound, Phragmén--Lindelöf, the vertical split with its tail bound, and the assembly.
Each is the same proof with `xiPoissonBottomHeight` replaced by the cut's least height.  Then the
induction: with the shells below `g` known to lie on the critical line, their finite contribution to
the line value is bounded, so the cut trace inherits the line bound and its own bottom shell follows.

### Next

The cut versions of `exp_bottomHeight_mul_xiPoissonTraceReal_le` and
`norm_xiPoissonTraceC_le_of_line_bound`.  The first is termwise; the second is the same
Phragmén--Lindelöf call with the cut's least height in the twist, and its two boundary bounds are
the cut versions of what §39 already proves.

---

## §43 The induction replaced by a minimal counterexample; cut Phragmén--Lindelöf formalized

### A structural simplification

§42 planned a shell-by-shell induction.  It is unnecessary.  `exists_min_xiPoissonPoint_re_of_nonempty`
(§35) says any nonempty set of copies attains a least height, so the argument can be run once on a
minimal counterexample:

```text
suppose Theta is bounded on Re t = sigma and some copy has nonzero displacement;
let q* be one of least height, g := its height;
then every copy of height < g has displacement zero, and there are finitely many of them,
so their contribution to Theta on the line has modulus at most sum exp(-sigma R) -- bounded;
hence the cut trace Theta_{>= g} is bounded on the same line;
the cut version of the bottom-shell argument gives displacement zero on the cut's lowest shell;
q* lies in that shell.  Contradiction.
```

No induction, no recursion over shells, no well-founded order beyond "a nonempty set of heights has a
minimum" -- which is already proved.  The finiteness that makes the removed part harmless is
`finite_xiPoissonShell`, also already proved.

### Formalized this turn

`[LEAN-PROVED]` `formal/GaloisForLFunctions/RHTower/XiPoissonCutHalfPlaneDecay.lean`
(axioms `propext, Classical.choice, Quot.sound`):

```text
xiPoissonCutHeight                          the cut's least height
xiPoissonCutHeight_le / _nonneg
exp_cutHeight_mul_xiPoissonCutTraceReal_le  the cut imaginary-ray bound
xiPoissonCutTwist                           twist by the cut's own least height
norm_xiPoissonCutTwist_le                   order-one envelope for the cut twist
norm_xiPoissonCutTwist_imaginary_ray / _real_ray
norm_xiPoissonCutTwist_le_of_line_bound     Phragmen-Lindelof on the two lower quadrants
norm_xiPoissonCutTraceC_le_of_line_bound
  ‖Theta_{>= g} t‖ <= max C (Theta_{>= g,R} sigma) * exp(-(cut height)(Re t - sigma))
```

Every step of §39 goes through verbatim with the cut's least height in place of the global one,
because the two facts it consumes -- `R q >= (least height)` on the divisor at hand, and
`|delta| < 1/2` per copy -- are both inherited by restriction.

### Remaining

```text
[LEAN-PROVED]  cut trace: finiteness, summability, envelope, analyticity        §42
[LEAN-PROVED]  cut half-plane decay                                             §43
[to formalize] cut vertical split + tail bound                                  (copy of §40)
[to formalize] cut assembly                                                     (copy of §41)
[to formalize] minimal-counterexample wrapper                                   (short)
[OPEN CORE]    the analytic input: Theta bounded on a line
```

The two remaining formalizations are the cut copies of §§40--41; the wrapper is then a few lines.

### Next

The cut vertical split.  Its bottom shell is `{q in cut g : R q = cut height g}`, finite by
`finite_xiPoissonCut_shell`; its above-bottom part is the cut at the next height, whose gap comes
from `exists_min_xiPoissonPoint_re_of_nonempty` applied to the strictly-higher copies -- the same
construction as `exists_xiPoissonSecondHeight`, one level up.

---

## §44 Cancellation and positivity are the same criterion here

`[LEAN-PROVED]` this turn, `formal/GaloisForLFunctions/RHTower/XiPoissonCutSplit.lean`
(axioms `propext, Classical.choice, Quot.sound`): `xiPoissonCutTraceC_split` (a cut trace splits into
its own bottom shell plus the strictly higher part, obtained by *subtracting two full-divisor splits*
so that no reasoning inside subtypes is needed) and `exp_mul_norm_xiPoissonStrictAboveSum_le` (the
weighted tail bound above a height).

### Attacking the open core

The open core is: `Theta` bounded on one vertical line.  §26 classified this as a **cancellation**
statement and contrasted it with the **positivity** statements (Weil, Hankel, Turán) that occupy
§§1--25.  That contrast is wrong, and the correction is exact.

Under RH every Poisson point is the real number `|g|`, so

```text
Theta(t) = sum_rho exp(-t |g_rho|),
```

which is manifestly **completely monotone** on `(0, infinity)`: `(-1)^n Theta^{(n)}(t) =
sum_rho |g|^n exp(-t|g|) >= 0`.

Conversely, suppose `Theta` restricted to `(0, infinity)` is completely monotone.  Bernstein's
theorem gives a **positive** measure `mu` on `[0, infinity)` with `Theta(t) = integral exp(-ts)
dmu(s)`, and then for `Re t >= sigma`

```text
|Theta(t)|  <=  integral exp(-sigma s) dmu(s)  =  Theta(sigma)  <  infinity,
```

so `Theta` is bounded on the half-plane, hence on the line, and the chain of §§39--43 applies.

> **[PAPER-PROVED]**  RH  `<->`  `Theta` is completely monotone on `(0, infinity)`.
>
> Equivalently: `sum_rho alpha^_rho^n exp(-t alpha^_rho) >= 0` for every `n >= 0` and `t > 0`.

`Theta` is real on the positive axis unconditionally, because the divisor is stable under line
conjugation, so the condition is meaningful without assuming anything.

### Why this matters for the shape of the problem

- The **cancellation** form (bounded on a vertical line) and the **positivity** form (complete
  monotonicity on the real axis) are Laplace-dual descriptions of one condition.  §26's claim that
  the vertical criterion "asks for cancellation, not a sign" was a statement about one *face* of the
  criterion, not about the criterion.
- It also explains why the finite positivity tests of §§1--25 were blind: complete monotonicity is
  the **full** Stieltjes condition, and its finite truncations are exactly the Hankel minors that
  Davenport--Heilbronn and Diamond--Montgomery--Vorhauer defeat.  What defeats them is truncation,
  not positivity.
- The measure now lives on `[g_1, infinity)` -- bounded below, hence a *determinate* moment problem.
  In the squared coordinate of §§1--25 the natural measure sat on `Re w` with the displacement mixed
  in, and determinacy was never available.

### The quantitative channel

The chain of §§39--41 is not restricted to bounded `Theta`.  With `‖Theta(sigma + i u)‖ <<
exp(lambda |u|)`, the Phragmén--Lindelöf step carries the extra factor `exp(-+ lambda y)` on each
quadrant and the rigidity lemma returns `|delta| <= lambda`:

> **[PAPER-PROVED]**  `Theta(sigma + i u) = O(exp(lambda |u|))` implies the zero-free region
> `|delta_rho| <= lambda` for every zero.

`lambda = 1/2` is the a priori bound and says nothing; `lambda = 0` is RH.  So every improvement of
the growth exponent of an explicit prime-computable function is a zero-free region, on a continuous
scale.  The formalized case is `lambda = 0`.

### Next

Prove complete monotonicity, or its first unproved instance.  `n = 0` is `Theta(t) >= 0` and `n = 1`
is `Theta` decreasing; both are `[to check]` against the explicit `A - P` decomposition of §33, where
the mean part is already known bounded and the fluctuation is the smoothed PNT error.  The first `n`
at which the fluctuation can defeat the mean is the quantity to compute -- and unlike the Hankel
minors of §§1--25, failing at one `n` does not end the criterion, because complete monotonicity is
the conjunction over all `n` and RH is equivalent to the whole conjunction, not to any finite piece.

---

## §45 A real-variable proof of the converse: no Phragmén--Lindelöf needed

§44 reduced RH to complete monotonicity of the Poisson trace.  Taking that as the hypothesis rather
than boundedness gives a proof of the hard direction that never leaves the positive real axis.

### Setup

`(-1)^n Theta^{(n)}(t) = sum_rho alpha^_rho^n exp(-t alpha^_rho)`, real for real `t` by line
conjugation.  Let `p_1` be the least height, `S` the bottom stratum (finite), and write
`alpha^ = p_1 + i q` on `S`.  Let `p_2 > p_1` be the next height.

### Step 1: the tail dies, uniformly in the phase

```text
| exp(p_1 t) sum_{p > p_1} alpha^^n exp(-t alpha^) |
      <= exp(-(t - t_0)(p_2 - p_1)) * sum_{p > p_1} |alpha^|^n exp(-t_0 (p - p_1))   for t >= t_0,
```
and the inner sum is finite because `|alpha^| <= p + 1` and `sum (p+1)^n exp(-t_0 p) < infinity` --
the same comparison that gives `summable_xiPoissonWeight`.  So

```text
exp(p_1 t) (-1)^n Theta^{(n)}(t)  ->  sum_{q} m_q (p_1 + i q)^n exp(-i t q)   as  t -> infinity.
```

### Step 2: the limit is a trigonometric polynomial whose oscillation beats its mean

Conjugation pairs `q` with `-q` at equal multiplicity, so the limit is real and equals

```text
m_0 p_1^n  +  sum_{q > 0} 2 m_q (p_1^2 + q^2)^(n/2) cos( n theta_q - t q ),
    theta_q = arctan(q / p_1).
```

The constant term grows like `p_1^n`; the amplitude of the `q`-term grows like
`(p_1^2 + q^2)^(n/2)`.  **For `q > 0` the amplitude wins**, and the term with the largest `|q|` beats
every other term by an exponential factor in `n`.

### Step 3: choose the phase

Let `q*` be the largest displacement in the bottom stratum and suppose `q* > 0`.  For `n` large the
limit is `2 m_{q*} (p_1^2 + q*^2)^(n/2) cos(n theta_{q*} - t q*) + o(same)`, and the cosine is
**periodic in `t` with period `2 pi / q*`**, so it equals `-1` at arbitrarily large `t`.  Hence
`(-1)^n Theta^{(n)}(t) < 0` for suitable large `n` and `t`, contradicting complete monotonicity.

No Kronecker theorem is needed: `q*` and `-q*` are the only displacements of that modulus, and they
combine into a single cosine.

> **[PAPER-PROVED]**  Complete monotonicity of `Theta` on `(0, infinity)` forces the bottom stratum
> onto the critical line; the minimal-counterexample wrapper of §43 then gives RH.

### What this replaces

```text
old route (§§39-43):  analyticity -> Phragmen-Lindelof on two quadrants -> half-plane decay
                      -> vertical split -> phase-robust dominance -> line conjugation
new route (§45):      tail decay on the real axis -> dominance of the largest |p_1 + i q| as n -> infinity
                      -> periodicity of one cosine
```

The old route is proved and stays; the new one uses no complex analysis at all.  Its ingredients are
the spectral gap (`exists_xiPoissonSecondHeight`, formalized), a moment-weighted summability
(`summable_xiPoissonWeight`'s comparison with `n`-th powers inserted), and elementary trigonometry.

### Why the displacement is detected here but not by the trace itself

At `n = 0` the limit is `m_0 + sum 2 m_q cos(t q)`, which a large `m_0` keeps positive -- this is the
blindness of trace positivity recorded in §1 and never contradicted.  The detection comes from the
factor `(p_1^2 + q^2)^(n/2)`: **the off-critical copies sit further from the origin in the Poisson
coordinate than the critical ones at the same height, so raising to the `n`-th power separates
them.**  That separation is invisible in the squared coordinate, where a shell is a vertical line and
all its points share `Re w`.

### Next

Formalize §45's three steps.  Step 1 needs `summable_xiPoissonWeight` upgraded to carry a polynomial
factor -- the same `exp(-sigma N) <= 2/(sigma N)^2` comparison with `2` replaced by `n + 2`.  Steps 2
and 3 are finite-sum trigonometry over `xiPoissonBottomShell`, which is already a `Finset` with its
displacement grouping (`xiPoissonBottomShell_regroup`).

---

## §46 §45 step 1, formalized

`[LEAN-PROVED]` `formal/GaloisForLFunctions/RHTower/XiPoissonMomentSummable.lean`
(axioms `propext, Classical.choice, Quot.sound`):

```text
norm_xiPoissonPoint            ‖alpha^‖ = ‖alpha‖
norm_xiPoissonPoint_le         ‖alpha^‖ <= R + 1/2          (the displacement bound again)
summable_pow_mul_xiPoissonWeight
  Summable (fun q => ‖alpha^ q‖ ^ n * xiPoissonWeight sigma q)   for every n and sigma > 0
```

This is what the derivatives of the trace need: `(-1)^n Theta^{(n)}(t) = sum_rho alpha^^n
exp(-t alpha^)` is an absolutely convergent sum for every `n`, so the term-by-term differentiation
and the tail estimate of §45 are both legitimate.

The proof is the same comparison that gave the plain weight's summability, with `2` promoted to
`n + 2`: `‖alpha^‖ <= R + 1/2 =: y` because `|delta| < 1/2`, and
`y^(n+2) exp(-sigma y) <= (n+2)! / sigma^(n+2)` from `Real.pow_div_factorial_le_exp`, so the
polynomially weighted term is at most a constant times `1 / ‖alpha‖^2`.  **Every power is absorbed by
the same single input** -- the canonical-product exponent `xiSpectralPoint_inv_sq_summable`.

### Where §45 stands

```text
[LEAN-PROVED]  moment-weighted summability                      step 1 input
[LEAN-PROVED]  spectral gap above the bottom shell              step 1 input
[to formalize] the tail limit  exp(p_1 t)(-1)^n Theta^{(n)}(t) -> trigonometric polynomial
[to formalize] amplitude dominance:  (p_1^2 + q^2)^(n/2)  beats  p_1^n
[to formalize] phase choice: one cosine, period 2 pi / q*
[OPEN CORE]    complete monotonicity itself
```

Steps 2 and 3 are finite-sum statements over `xiPoissonBottomShell`, whose grouping by displacement
is `xiPoissonBottomShell_regroup`.  The amplitude dominance is where the criterion actually detects:
`(p_1^2 + q^2)^(n/2) / p_1^n -> infinity` for `q <> 0`, so the off-critical part of a shell grows
faster in `n` than the critical part, for the elementary reason that it lies further from the origin.

### Next

The tail limit.  With `summable_pow_mul_xiPoissonWeight` in hand it is the same geometric estimate as
`tendsto_exp_bottomHeight_mul_aboveBottom_tail`, one power heavier: bound
`exp(p_1 t) sum_{p > p_1} ‖alpha^‖^n exp(-t p)` by `exp(-(t - t_0)(p_2 - p_1))` times the constant
`sum_{p > p_1} ‖alpha^‖^n exp(-t_0 (p - p_1))`, which is finite by this file.

---

## §47 The small-`n` conditions are redundant; §45 step 1 formalized

### A narrowing of the open core

§45's contradiction is produced at **large `n` and large `t`**: the amplitude
`(p_1^2 + q^2)^(n/2)` needs `n` big to beat `m_0 p_1^n`, and the tail needs `t` big.  So the
hypothesis actually consumed is not full complete monotonicity but its tail:

> **[PAPER-PROVED]**  RH  `<->`  `(-1)^n Theta^{(n)}(t) >= 0` for all `n >= N_0` and all
> `t >= T_0(n)`, for any fixed `N_0`.

The small-`n` conditions are redundant.  That matters because small `n` is exactly where the
criterion is *unfavourable*: the archimedean weight `Re psi(1/4 + i r/2) - log pi` is **negative**
near `r = 0`, and at small `n` (and large `t`) the test function
`(r^2+a^2)^(n/2) exp(-t sqrt(r^2+a^2))` concentrates precisely there.  Raising `n` moves the mass to
large `|r|`, where the archimedean weight is `~ log|r| > 0`.

Sharper still, since step 1 sends `t -> infinity` at fixed `n`:

> RH `<->` for every `n`, `liminf_{t -> infinity} exp(p_1 t) (-1)^n Theta^{(n)}(t) >= 0`,

i.e. the criterion localizes, at each `n`, to the **asymptotic-in-`t` behaviour**, which is a finite
trigonometric polynomial over the bottom stratum.  The infinite part of the divisor enters only
through the tail estimate.

### Formalized

`[LEAN-PROVED]` `formal/GaloisForLFunctions/RHTower/XiPoissonMomentTail.lean`
(axioms `propext, Classical.choice, Quot.sound`):

```text
tendsto_exp_bottomHeight_mul_aboveBottom_moment_tail
  exp(g_1 v) * sum_{q above} ‖alpha^‖^n * weight(sigma+v) q  ->  0
```

for every `n` -- step 1 of §45.  The factor `‖alpha^‖^n` is common to numerator and comparison, so
the spectral gap suppresses the tail exactly as at `n = 0`; the only new input is
`summable_pow_mul_xiPoissonWeight` from §46.

### §45's ledger

```text
[LEAN-PROVED]  moment-weighted summability                            §46
[LEAN-PROVED]  moment-weighted tail vanishes                          §47, step 1
[to formalize] the bottom-stratum limit is the trigonometric polynomial
[to formalize] amplitude dominance  (p_1^2+q^2)^(n/2) / p_1^n -> infinity
[to formalize] phase choice
[OPEN CORE]    eventual positivity of the alternating derivatives
```

### Next

The bottom-stratum limit.  With the tail controlled, `exp(p_1 t) (-1)^n Theta^{(n)}(t)` differs from
the finite sum `sum_{q in bottom} (p_1 + i q)^n exp(-i t q)` by something tending to `0`, and that
finite sum is `xiPoissonBottomShell_regroup` with the extra factor `(p_1 + i q)^n`.  Amplitude
dominance is then the statement that `|p_1 + i q| > p_1` whenever `q <> 0` -- the geometric fact that
an off-critical copy lies strictly further from the origin than a critical one at the same height,
which is the whole detection mechanism in one inequality.

---

## §48 Amplitude dominance, formalized: the detection mechanism in one inequality

`[LEAN-PROVED]` `formal/GaloisForLFunctions/HTGeometry/GeometricAmplitudeDominance.lean`
(axioms `propext, Classical.choice, Quot.sound`):

```text
lt_sqrt_sq_add_sq            p < sqrt (p^2 + q^2)   for p > 0, q <> 0
not_forall_mul_pow_le        no positive multiple of c^n (c > 1) stays below a constant
eq_zero_of_forall_mul_pow_le
  (∀ n, m * sqrt(p^2+q^2)^n <= K * p^n)  ->  q = 0     for m > 0, p > 0
```

This is the whole detection mechanism of the real-variable route, isolated and free of any reference
to Xi.  Read it back into the divisor:

> At a fixed height `p`, a critical copy sits at distance `p` from the origin in the Poisson
> coordinate and an off-critical copy at distance `sqrt(p^2 + q^2) > p`.  The `n`-th derivative of the
> trace weights each copy by its distance to the `n`-th power.  **Powering separates them, and no
> multiplicity of critical copies can compensate, because a constant cannot dominate a geometric
> sequence with ratio greater than one.**

That last clause is why the criterion is not blind where the plain trace was: at `n = 0` the
comparison is `m <= K` and a large `m_0` wins; for every `n` at once, the geometric ratio wins.  It
also says precisely what the squared coordinate lacked -- there a shell is a vertical line, all of
whose points share `Re w`, so no distance separates the critical from the off-critical points.

### Ledger

```text
[LEAN-PROVED]  moment-weighted summability                §46
[LEAN-PROVED]  moment-weighted tail vanishes              §47
[LEAN-PROVED]  amplitude dominance                        §48
[to formalize] the bottom-stratum limit is the trigonometric polynomial
[to formalize] phase choice (one cosine, period 2 pi / q*)
[to formalize] assembly + minimal-counterexample wrapper
[OPEN CORE]    eventual positivity of the alternating derivatives
```

### Next

The bottom-stratum limit: `exp(p_1 t) (-1)^n Theta^{(n)}(t)` converges, as `t -> infinity`, to
`sum_{q} m_q (p_1 + i q)^n exp(-i t q)` -- the moment-weighted analogue of
`tendsto_exp_bottomHeight_mul_xiPoissonTraceReal`, with the same two inputs (the shell is finite and
homogeneous in height; the tail is §47).  The phase step is then the observation that the largest
`|q|` contributes a single cosine of period `2 pi / q*`, so its infimum over `t` is attained on every
half-line, and feeding that infimum into `eq_zero_of_forall_mul_pow_le` closes the shell.

---

## §49 The moment traces, formalized: complete monotonicity as a corpus object

`[LEAN-PROVED]` `formal/GaloisForLFunctions/RHTower/XiPoissonMomentTrace.lean`
(axioms `propext, Classical.choice, Quot.sound`):

```text
xiPoissonMomentTraceC n tau  =  sum_rho alpha^_rho ^ n * exp (-tau alpha^_rho)
summable_norm_xiPoissonMomentTerm / summable_xiPoissonMomentTerm
re_xiPoissonMomentTerm_nonneg_of_rh      each summand is a nonnegative real under RH
re_xiPoissonMomentTraceC_nonneg_of_rh    RH  ->  Re (moment trace) >= 0  for every n, t > 0
not_riemannHypothesis_of_re_xiPoissonMomentTraceC_neg
```

The forward half of §44's criterion -- **RH implies complete monotonicity of the Poisson trace** -- is
now a theorem of the corpus, together with the disproof endpoint it carries: a single negative moment
at a single positive real time refutes RH, at any order `n`.

The `n = 0` case is the old trace-positivity endpoint, which §1 showed to be blind.  Orders `n >= 1`
are not blind, and §48 says exactly why in one line: at a fixed height the off-critical copies lie
further from the origin, and `n`-th powers separate distances that no multiplicity can compensate.

### The corpus now holds both halves of the mechanism

```text
RH  ->  moment traces nonnegative                        §49  [LEAN-PROVED]
moment traces nonnegative  ->  RH                        §45  [PAPER-PROVED]
   step 1 tail                                           §47  [LEAN-PROVED]
   step 2 amplitude dominance                            §48  [LEAN-PROVED]
   step 3 phase choice                                   [to formalize]
   bottom-stratum limit                                  [to formalize]
   minimal-counterexample wrapper                        [to formalize]
```

plus the independent complex-analytic route of §§39--43, formalized through the bottom shell.

### Next

The bottom-stratum limit for the moment trace: with §47 killing the tail, `exp(p_1 t) Re(moment
trace at t)` converges as `t -> infinity` to the finite sum over the bottom shell, whose terms are
`m_q (p_1 + i q)^n exp(-i t q)`.  The remaining inputs are `xiPoissonBottomShell_regroup` for the
grouping and elementary trigonometry for the phase; the conclusion feeds
`HTGeometry.eq_zero_of_forall_mul_pow_le` with `p = p_1`, `q = q*`, `m = 2 m_{q*}` and
`K = m_0 + sum of the other amplitudes`.

---

## §50 Two-base dominance: the multi-frequency case closed

`[LEAN-PROVED]` (added to `GeometricAmplitudeDominance.lean`; axioms
`propext, Classical.choice, Quot.sound`):

```text
not_forall_mul_pow_le_pow
  0 <= d < c,  0 < m,  (∀ n, m * c^n <= K * d^n)  ->  False
```

§48 handled a shell with a single off-critical displacement, comparing `sqrt(p^2+q^2)` against `p`.
A general shell carries several displacements, and after choosing the phase that makes the largest
one maximally negative, the remaining ones are bounded by *their own* amplitudes -- not by `p^n`.
The comparison is therefore between the largest base and the **second** largest, which is exactly
what this lemma covers:

```text
c = sqrt(p_1^2 + q*^2)          the largest displacement in the shell
d = sqrt(p_1^2 + q_2^2)         the next largest, or p_1 if there is only one
K = m_0 + sum of the other multiplicities
```

`d < c` holds because `|q_2| < |q*|`, and the conclusion is that `q*` cannot exist.  So the shell's
displacement set has a single element, namely `0`.

Note also the formal lint gate passes again: the concurrent module flagged in §40 has since been
wired into its umbrella by its author.

### The real-variable route, ledger

```text
[LEAN-PROVED]  RH -> moment traces nonnegative                    §49
[LEAN-PROVED]  moment-weighted summability                        §46
[LEAN-PROVED]  moment-weighted tail vanishes                      §47
[LEAN-PROVED]  amplitude dominance, one displacement              §48
[LEAN-PROVED]  amplitude dominance, several displacements         §50
[to formalize] the bottom-shell asymptotic identity + phase choice
[to formalize] minimal-counterexample wrapper
[OPEN CORE]    eventual nonnegativity of the moment traces
```

Everything except the asymptotic identity, the phase choice and the wrapper is now proved in Lean,
on both routes.

### Next

The bottom-shell asymptotic.  §37's lesson applies: **there is no limit to name** -- the bottom
shell's contribution `sum_q m_q (p_1 + i q)^n exp(-i t q)` spins in `t`.  The correct statement is
therefore an inequality, not a limit:

```text
for every epsilon > 0 there is T with, for all t >= T,
| exp(p_1 t) * Re (moment trace at t)  -  Re sum_q m_q (p_1 + i q)^n exp(-i t q) | <= epsilon,
```

which is §47 plus the triangle inequality.  Then pick `t` in the arithmetic progression where
`cos(n theta_{q*} - t q*) = -1` -- available on every half-line because a single cosine is periodic --
and feed the resulting inequality to `not_forall_mul_pow_le_pow`.

---

## §51 The asymptotic identity, formalized

`[LEAN-PROVED]` `formal/GaloisForLFunctions/RHTower/XiPoissonShellPolynomial.lean`
(axioms `propext, Classical.choice, Quot.sound`):

```text
xiPoissonAboveMomentSum n tau            the above-bottom part of the n-th moment trace
xiPoissonShellPoly n t
  = sum_{q in bottom} alpha^_q ^ n * exp (-i t (Im alpha^_q))
xiPoissonMomentTraceC_split
exp_bottomHeight_mul_shell_term          on the bottom shell the height factors out exactly
exp_bottomHeight_mul_momentTraceC_eq     **the asymptotic identity**
  exp(g_1 t) * (moment trace at t)  =  shell polynomial  +  exp(g_1 t) * (above-bottom part)
norm_exp_bottomHeight_mul_aboveMomentSum_le
```

The identity is exact, not asymptotic -- the asymptotics enter only through §47, which sends the
second term to `0`.  What the weighting achieves is visible in
`exp_bottomHeight_mul_shell_term`: for a copy of the bottom shell the height is *exactly* `g_1`, so
`exp(g_1 t) exp(-t alpha^) = exp(-i t J)` with no residue.  Shell homogeneity is doing all the work,
and it is a property of the Poisson coordinate.

### The route, ledger

```text
[LEAN-PROVED]  RH -> moment traces nonnegative                    §49
[LEAN-PROVED]  moment-weighted summability                        §46
[LEAN-PROVED]  moment-weighted tail vanishes                      §47
[LEAN-PROVED]  amplitude dominance (one / several displacements)  §48, §50
[LEAN-PROVED]  the asymptotic identity                            §51
[to formalize] phase choice and the shell conclusion
[to formalize] minimal-counterexample wrapper
[OPEN CORE]    eventual nonnegativity of the moment traces
```

### Next

The phase choice.  Grouping `xiPoissonShellPoly n t` by displacement (`xiPoissonBottomShell_regroup`,
already proved for the `n = 0` shape) turns it into
`sum_J m_J (g_1 + i J)^n exp(-i t J)`, whose real part is
`m_0 g_1^n + sum_{J > 0} 2 m_J (g_1^2 + J^2)^(n/2) cos(n theta_J - t J)`.
Choosing `t` in the arithmetic progression where the `J = q*` cosine equals `-1` -- possible on every
half-line, since one cosine is periodic -- and bounding the remaining cosines by `1` produces
exactly the hypothesis of `HTGeometry.not_forall_mul_pow_le_pow` with
`c = sqrt(g_1^2 + q*^2)` and `d = sqrt(g_1^2 + q_2^2)`.

---

## §52 Phase selection, formalized

`[LEAN-PROVED]` `formal/GaloisForLFunctions/HTGeometry/TrigPolynomialPhaseSelection.lean`
(lint clean; axioms `propext, Classical.choice, Quot.sound`):

```text
exists_int_le_affine          an affine progression with nonzero step reaches past any bound
norm_finset_exp_sum_le        ‖sum c i exp(-i t lam i)‖ <= sum ‖c i‖
exists_ge_re_finset_exp_le
  i₀ in s,  lam i₀ <> 0,  any T
  ->  ∃ t >= T,  Re (sum_i c i exp(-i t lam i))  <=  -‖c i₀‖ + sum_{i <> i₀} ‖c i‖
```

At arbitrarily large times the designated term can be aimed along the negative real axis: solve
`exp(-i t lam i₀) = -‖c i₀‖ / c i₀`, which is a point of the unit circle, and use the periodicity of
that single exponential to push `t` past any bound.  Every other term is bounded by its modulus.

**No Kronecker theorem, no almost-periodicity, no equidistribution.**  §37 originally proposed a
mean-square average precisely to avoid needing simultaneous phase alignment; §38 removed the need on
the real-exponential side, and this removes it on the oscillatory side.  Aligning *one* frequency is
enough, because the amplitude of that one term already outgrows the sum of all the others (§50).

### Ledger

```text
[LEAN-PROVED]  RH -> moment traces nonnegative                    §49
[LEAN-PROVED]  moment-weighted summability / tail                 §46, §47
[LEAN-PROVED]  amplitude dominance, one and several displacements §48, §50
[LEAN-PROVED]  the asymptotic identity                            §51
[LEAN-PROVED]  phase selection                                    §52
[to formalize] assembly: shell conclusion from the four above
[to formalize] minimal-counterexample wrapper
[OPEN CORE]    eventual nonnegativity of the moment traces
```

Every ingredient of the real-variable converse is now a theorem in the corpus.  What remains on that
route is bookkeeping: instantiate `exists_ge_re_finset_exp_le` at the shell's displacement grouping,
feed the resulting inequality to `not_forall_mul_pow_le_pow`, and wrap with §43's
minimal-counterexample argument.

### Next

The assembly.  For a shell with a nonzero displacement, let `q*` maximize `‖alpha^‖` over the shell
(equivalently `|J|`, since all heights agree).  §52 with `lam = Im alpha^` and
`c = m_J (g_1 + i J)^n` gives arbitrarily large `t` at which the shell polynomial's real part is at
most `-m_{q*} (g_1^2 + q*^2)^(n/2) + sum of the other moduli`; §51 and §47 transfer that to the
moment trace up to `epsilon`; and §50 turns the resulting family of inequalities, one per `n`, into a
contradiction.

---

## §53 The conjugate pair: a gap in §52's use, and its repair

### The gap

§52 aligns one frequency `j*` and bounds every other term by its modulus.  Applied to a Poisson
shell that is **stable under line conjugation**, this is vacuous: the displacement `-j*` is present
with the same multiplicity, so `‖c(-j*)‖ = ‖c(j*)‖`, and the bound reads

```text
Re(shell polynomial)  <=  -‖c(j*)‖ + ‖c(-j*)‖ + (rest)  =  (rest),
```

which says nothing.  Aligning the largest amplitude gains exactly what its mirror gives back.

> **[CORRECTED]**  §52 as stated is true but not usable on a conjugation-stable divisor.  Found while
> writing the assembly -- the same way §37 and §38's errors surfaced.

### The repair

The mirror term is not an independent adversary: it is the **conjugate** of the aligned one.  If
`lam i₁ = -lam i₀` and `c i₁ = conj (c i₀)`, then

```text
c i₁ exp(-i t lam i₁)  =  conj ( c i₀ exp(-i t lam i₀) ),
```

so aligning `i₀` to `-‖c i₀‖` -- a real number -- aligns `i₁` to the same real number.  The pair
contributes `-2 ‖c i₀‖`, not `0`.

`[LEAN-PROVED]` (added to `TrigPolynomialPhaseSelection.lean`; lint clean; axioms
`propext, Classical.choice, Quot.sound`):

```text
exists_ge_align                       the aligning time, extracted as its own lemma
exists_ge_re_finset_exp_le_pair
  lam i₁ = -lam i₀,  c i₁ = conj (c i₀),  c i₀ <> 0,  lam i₀ <> 0
  ->  ∃ t >= T,  Re (sum_i c i exp(-i t lam i))  <=  -2 ‖c i₀‖ + sum_{i <> i₀, i₁} ‖c i‖
```

### Why the symmetry helps rather than hurts

This is the third time the divisor's line-conjugation symmetry has appeared, and the first time it
*strengthens* rather than merely constrains:

```text
§34  symmetry makes the bottom shell stable, so peeling is well defined
§41  symmetry upgrades "displacement <= 0" to "displacement = 0"
§53  symmetry doubles the aligned amplitude instead of cancelling it
```

The functional equation, which is what puts `rho` and `1 - conj rho` in the divisor together, is
therefore not an obstacle to the detection -- it is what makes the detected quantity real and its
amplitude additive.

### Ledger

```text
[LEAN-PROVED]  every ingredient of the real-variable converse      §46-§53
[to formalize] assembly and the minimal-counterexample wrapper
[OPEN CORE]    eventual nonnegativity of the moment traces
```

### Next

The assembly, now unblocked: group the shell by displacement, take `j*` of maximal modulus and `-j*`
its mirror, apply `exists_ge_re_finset_exp_le_pair`, transfer through §51 and §47, and close with
`not_forall_mul_pow_le_pow` at `c = sqrt(g_1^2 + j*^2)` against `d = sqrt(g_1^2 + j_2^2)` where `j_2`
is the largest remaining modulus -- **strictly smaller now that both `+-j*` are removed**, which is
exactly what the pair lemma buys.

---

## §54 Class alignment: the last abstract ingredient

§53's pair lemma aligns two *individual* indices.  A shell can carry several copies at the same
displacement -- that is exactly what multiplicity means -- and they must all be aligned at once,
because a single term of the maximal class does not outgrow the class it belongs to.

`[LEAN-PROVED]` (added to `TrigPolynomialPhaseSelection.lean`; lint clean; axioms
`propext, Classical.choice, Quot.sound`):

```text
exists_ge_re_sum_exp_le_of_split
  s splits as sPlus (frequency l) + sMinus (frequency -l) + sRest,
  A := sum over sPlus of c,   A <> 0,   sum over sMinus of c = conj A,   l <> 0
  ->  ∃ t >= T,  Re (sum_{i in s} c i exp(-i t lam i))  <=  -2 ‖A‖ + sum_{i in sRest} ‖c i‖
```

Aligning the **class coefficient** `A` aligns every member of the class simultaneously, since they
share the frequency `l`; the mirror class follows by conjugation.  So multiplicity, far from
obstructing, enters the bound as a factor inside `‖A‖`: a shell with `m` copies at displacement `l`
contributes `-2 m (g_1^2 + l^2)^(n/2)`, which is exactly the quantity `GeometricAmplitudeDominance`
compares against the rest.

The split is passed as a hypothesis (`hsplit` for an arbitrary summand), so the lemma is independent
of how the classes are cut out -- on the Xi side they will be `Finset.filter` on the displacement.

### Ledger

```text
[LEAN-PROVED]  RH -> moment traces nonnegative                       §49
[LEAN-PROVED]  summability / tail / asymptotic identity              §46, §47, §51
[LEAN-PROVED]  amplitude dominance (one, several, two-base)          §48, §50
[LEAN-PROVED]  phase selection (single, pair, class)                 §52, §53, §54
[to formalize] Xi-side assembly and the minimal-counterexample wrapper
[OPEN CORE]    eventual nonnegativity of the moment traces
```

All abstract ingredients of the real-variable converse are proved.  What remains is Xi-specific
bookkeeping: cut the bottom shell into the maximal displacement class, its mirror, and the rest;
check `A <> 0` and the conjugation identity via `xiPoissonPoint_lineConj`; and check that the rest
has strictly smaller modulus, which holds because on a shell all heights agree, so
`‖alpha^‖^2 = g_1^2 + J^2` is a strictly increasing function of `|J|`.

### Next

The Xi-side assembly.  The one nontrivial step is the conjugation identity
`sum_{J = -l} alpha^^n = conj (sum_{J = l} alpha^^n)`, which follows from
`xiPoissonPoint_lineConj` and `mem_xiPoissonBottomShell_lineConj` by reindexing the filter along the
line-conjugation equivalence -- the same involution that §41 used to upgrade `<= 0` to `= 0`.

---

## §55 Displacement classes of the bottom shell, formalized

`[LEAN-PROVED]` `formal/GaloisForLFunctions/RHTower/XiPoissonShellClasses.lean`
(lint clean; axioms `propext, Classical.choice, Quot.sound`):

```text
xiShellClass l                          the shell's copies at displacement l
xiPoissonPoint_of_mem_xiShellClass      such a copy has Poisson point exactly g_1 + l i
xiShellClass_sum                        sum of alpha^^n over the class = (class size) (g_1 + l i)^n
lineConj_mem_xiShellClass               line conjugation maps class l into class (-l)
card_xiShellClass_neg                   conjugate classes have equal size
xiShellClass_sum_neg                    and conjugate coefficient sums
norm_xiShellClass_sum                   ‖class sum‖ = (class size) * sqrt(g_1^2 + l^2)^n
```

The first of these is the reason the whole route works: **on a shell, a displacement determines the
Poisson point completely**, because the height is already fixed.  So the shell polynomial's
coefficients are literally `(multiplicity) * (g_1 + l i)^n`, and their moduli are
`(multiplicity) * sqrt(g_1^2 + l^2)^n` -- a geometric sequence in `n` whose ratio is strictly larger
for larger `|l|`.  That is the exact input `GeometricAmplitudeDominance` consumes.

`card_xiShellClass_neg` is proved by applying line conjugation in both directions -- the map sends
class `l` into class `-l` and class `-l` into class `l`, so two injections give the equality without
needing the involution property of the equivalence.

### Ledger

```text
[LEAN-PROVED]  every abstract ingredient                            §46-§54
[LEAN-PROVED]  the Xi-side class structure                          §55
[to formalize] the three-way split of the shell and the final contradiction
[to formalize] minimal-counterexample wrapper
[OPEN CORE]    eventual nonnegativity of the moment traces
```

### Next

The three-way split.  With `l` chosen to maximize `|Im alpha^|` over the shell, the shell is the
disjoint union of `xiShellClass l`, `xiShellClass (-l)` and the rest; the rest consists of copies
with `|Im alpha^| < |l|`, hence `‖alpha^‖ < sqrt(g_1^2 + l^2)` -- strict, because on a shell the
modulus is a strictly increasing function of `|Im alpha^|`.  Feeding
`exists_ge_re_sum_exp_le_of_split` and then `not_forall_mul_pow_le_pow` closes the shell.
