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

---

## §56 The three-way split, formalized

`[LEAN-PROVED]` `formal/GaloisForLFunctions/RHTower/XiPoissonShellSplit.lean`
(lint clean; axioms `propext, Classical.choice, Quot.sound`):

```text
xiPoissonBottomHeight_pos                 0 < g_1
norm_xiPoissonPoint_of_mem_bottomShell    ‖alpha^‖ = sqrt (g_1^2 + (Im alpha^)^2) on the shell
xiShellRest l                             the shell minus the classes at +- l
xiPoissonBottomShell_split
  sum over the shell  =  class l  +  class (-l)  +  rest        (for any summand)
norm_lt_of_mem_xiShellRest
  if |l| is maximal on the shell, every remaining copy has ‖alpha^‖ < sqrt (g_1^2 + l^2)
```

`xiPoissonBottomHeight_pos` comes from the same two facts that run the whole route:
`‖alpha^‖ = ‖alpha‖ > 4` and `‖alpha^‖ <= Re alpha^ + 1/2`.  The bottom height is not merely
nonnegative but bounded away from zero, which is what makes the geometric ratio
`sqrt(g_1^2+l^2) / g_1` finite and the dominance argument non-degenerate.

`norm_lt_of_mem_xiShellRest` is the strictness the dominance needs, and it is where the shell
structure pays for the last time: because all heights on a shell agree, the modulus is a strictly
increasing function of `|Im alpha^|`, so "not one of the two extreme displacements" upgrades directly
to "strictly smaller modulus".

### Ledger

```text
[LEAN-PROVED]  all abstract ingredients                              §46-§54
[LEAN-PROVED]  Xi-side class structure                               §55
[LEAN-PROVED]  Xi-side three-way split and strict modulus gap        §56
[to formalize] the final contradiction and the minimal-counterexample wrapper
[OPEN CORE]    eventual nonnegativity of the moment traces
```

Every structural fact the real-variable converse needs is now proved.  The remaining Lean work is a
single chain: pick the maximal displacement, apply `xiPoissonBottomShell_split` and
`exists_ge_re_sum_exp_le_of_split`, transfer through the asymptotic identity (§51) and the tail (§47),
let the error tend to zero, and apply `not_forall_mul_pow_le_pow` with

```text
c = sqrt(g_1^2 + l^2),   d = max modulus on the rest (< c by §56),
m = 2 * (class size)  >  0,   K = card of the rest.
```

### Next

That chain.  Its only remaining subtlety is the order of quantifiers: the tail bound is uniform in
`n` only after `t` is chosen, so the argument fixes `n`, then `epsilon`, then `t`, and the family of
inequalities indexed by `n` is assembled at the end -- which is exactly the shape
`not_forall_mul_pow_le_pow` consumes.

---

## §57 The real-variable converse closes on the bottom shell

`[LEAN-PROVED]` `formal/GaloisForLFunctions/RHTower/XiPoissonShellClosure.lean`
(lint clean; axioms `propext, Classical.choice, Quot.sound`):

```text
xiPoissonShellPoly_eq          the shell polynomial in the phase-selection normal form
exists_tail_bound              the weighted above-bottom tail is uniformly small beyond some time
xiPoissonPoint_im_eq_zero_of_forall_moment_nonneg
  (∀ n, ∀ t > 0, 0 <= Re (moment trace n t))  ->  every bottom-shell copy has zero displacement
```

The proof is the chain §45 predicted, now checked:

```text
pick l maximizing |Im alpha^| on the shell                    Finset.exists_max_image
split shell = class l + class (-l) + rest                     §56
align the class at arbitrarily large t                        §54
   -> Re (shell polynomial)  <=  -2 ‖A‖ + (rest moduli)
transfer via the asymptotic identity                          §51
   exp(g_1 t) Re(moment trace) = Re(shell poly) + Re(tail)
kill the tail                                                 §47, this file
let epsilon -> 0                                              le_of_forall_pos_le_add
   -> 2 (class size) M^n  <=  (rest card) d^n   for every n
d < M by strict modulus monotonicity on a shell               §56
   -> contradiction                                           §50
```

Nothing in the chain is assumed.  The hypothesis is exactly the positivity of the moment traces --
the `[OPEN CORE]` -- and the conclusion is a statement about zero locations.

### What is now proved, end to end

```text
[LEAN-PROVED]  RH  ->  every moment trace is nonnegative                          §49
[LEAN-PROVED]  every moment trace nonnegative  ->  bottom shell on the line       §57
[LEAN-PROVED]  Theta bounded on a vertical line  ->  bottom shell on the line     §41
   (independent complex-analytic route, §§39-43)
[to formalize] the minimal-counterexample wrapper from the bottom shell to all zeros
[OPEN CORE]    nonnegativity of the moment traces
```

Two independent routes now reach the bottom shell from an explicit analytic hypothesis, one through
Phragmén--Lindelöf and one through nothing but the real axis.

### Next

The wrapper.  §43 replaced the peeling induction by a minimal counterexample: a copy of least height
among those with nonzero displacement makes every lower shell real, hence bounded, hence the cut
divisor inherits the hypothesis, and the cut's own bottom shell is exactly where that copy lives.
For the moment-trace route the same wrapper applies with the cut moment traces, whose infrastructure
is §42's -- the cut versions of summability, envelope and analyticity are already proved, and the
moment versions need only the same one-line promotions used in §46.

---

## §58 Moment positivity does not peel — and what that settles

### The check

§57's closing note proposed running the peeling wrapper on the moment route.  It does not work, and
the reason is structural, not technical.

Peeling needs the hypothesis to descend to the cut divisor.  For **boundedness** it does: the removed
shells are finite and, once known real, contribute a bounded term, so

```text
Theta_{>= g}  =  Theta  -  (finite bounded sum)   is bounded.
```

For **positivity** it does not.  Subtracting a nonnegative quantity from a nonnegative quantity gives
nothing:

```text
Re (cut moment trace)  =  Re (moment trace)  -  Re (removed shells),
```

and the removed shells contribute a *positive* amount once they are known to lie on the line.  Worse,
weighting by the cut's own height makes the removed part grow like `exp((g_2 - g_1) t)`, which
swamps everything above it.

> **[NEGATIVE RESULT]**  The moment-positivity hypothesis is visible only at the bottom shell.  It
> cannot be propagated upward by removal, because removal destroys the sign.

### What this settles

It is not a defect of the argument; it is a statement about what the criterion sees.  Complete
monotonicity is a statement about the **whole** measure, and its bottom-shell consequence is the only
part extractable by a single asymptotic.  To reach every zero one must go through Bernstein:

```text
complete monotonicity  ->  Theta is a positive-measure Laplace transform  ->  Theta bounded
                       ->  peel (boundedness descends)  ->  RH
```

So §44's Bernstein step is not a convenience -- it is the only bridge from the positivity form to a
form that peels.  §57 remains a genuinely simpler proof of the bottom-shell case, free of complex
analysis, but the full converse runs through boundedness.

### Formalized this turn

`[LEAN-PROVED]` `formal/GaloisForLFunctions/RHTower/XiPoissonCutBottomShell.lean`
(lint clean; axioms `propext, Classical.choice, Quot.sound`):

```text
xiPoissonCutBottomShell g            the cut's own bottom shell
mem_xiPoissonCutBottomShell
xiPoissonCutBottomShellSum_eq        the height factors out exactly on it
mem_xiPoissonCut_lineConj            the cut is stable under line conjugation
mem_xiPoissonCutBottomShell_lineConj and so is its bottom shell
```

These are the cut analogues of §34, and the last structural inputs the boundedness wrapper needs.

### Ledger

```text
[LEAN-PROVED]  RH -> moment traces nonnegative                                  §49
[LEAN-PROVED]  moment traces nonnegative -> bottom shell on the line            §57
[LEAN-PROVED]  Theta bounded on a line -> bottom shell on the line              §41
[LEAN-PROVED]  cut trace: shells, envelope, analyticity, Phragmen-Lindelof      §42, §43
[LEAN-PROVED]  cut bottom shell and its symmetry                                §58
[to formalize] cut assembly, then the minimal-counterexample wrapper
[OPEN CORE]    boundedness of Theta on a vertical line
```

### Next

The cut assembly: repeat §41 with `xiPoissonCutHeight g` in place of the global bottom height, using
`xiPoissonCutBottomShellSum_eq` for the factorization and `norm_xiPoissonCutTraceC_le_of_line_bound`
for the half-plane decay.  Then the wrapper of §43 closes the converse.

---

## §59 The converse closes: `RH <-> Theta bounded on a vertical line`, in Lean

`[LEAN-PROVED]` `formal/GaloisForLFunctions/RHTower/XiPoissonCutOnLine.lean` and
`XiPoissonLineBoundRH.lean` (lint clean; axioms `propext, Classical.choice, Quot.sound`):

```text
xiShellSum_regroup                              a shell sum regrouped by displacement
xiPoissonCutBottomShell_eq_sdiff                at an actual height, the cut's bottom shell is
                                                the difference of the two lower sets
xiPoissonPoint_im_nonpos_of_cut_line_bound      the cut assembly
xiPoissonPoint_im_eq_zero_of_cut_line_bound     with the conjugation symmetry
le_xiPoissonCutHeight
riemannHypothesis_of_xiPoissonTrace_line_bound  **the wrapper: bounded line  ->  RH**
riemannHypothesis_iff_exists_xiPoissonTrace_line_bound
  RH  <->  the Poisson zero trace is bounded on some vertical line of Re t > 0
```

The wrapper is the minimal-counterexample argument of §43, now checked: among the off-line copies
take one of least height `g`; every copy below `g` is then on the line, so the finite sum it
contributes to the line value has constant modulus; hence the cut trace above `g` inherits the
bound; the cut assembly puts the cut's bottom shell -- which contains the chosen copy -- on the
critical line.  **No induction over shells appears anywhere**; the minimum over a nonempty set of
copies and the finiteness of shells do all the work.

### What this completes

The programme opened in §26 and corrected twice (§37, §53) is now a theorem of the corpus in both
directions.  The chain that carries it:

```text
§28  order-one vertical envelope, unconditional        (why Phragmen-Lindelof applies at all)
§36  analyticity of the trace on Re t > 0
§39  Phragmen-Lindelof -> half-plane decay
§40  vertical split and the weighted tail bound
§38  phase-robust dominance
§41  the bottom shell, for the full divisor
§42-43, §58  the same over a height cut
§59  the cut assembly and the minimal-counterexample wrapper
```

Every step is unconditional; the hypothesis enters only as the boundedness assumption, and the
conclusion is `RiemannHypothesis` itself.

### The open core, unchanged and now isolated

```text
[OPEN CORE]  ∃ sigma > 0, ∃ C, ∀ x, ‖Theta(sigma + i x)‖ <= C.
```

This is now the *only* thing between the corpus and RH along this route.  It is RH-strength: §44
shows it is equivalent to complete monotonicity of `Theta` on `(0, infinity)`, and §33 shows that on
the prime side it is full square-root cancellation in the Poisson-smoothed explicit formula.  What
the last twenty sections bought is that the statement is now a single, explicit, zero-free analytic
inequality with a formally verified path from it to the theorem.

### Next

Attack the open core directly.  Two concrete handles, both from §§32--33:
the mass-shifted carrier makes the criterion a convergent prime sum with an archimedean side that
*decays*, so the whole content sits in one oscillatory factor; and the escaped complex saddle
(`w* = 2 a u / sqrt(4a^2 - 1) > u`) says the sum is endpoint-governed rather than saddle-governed,
which is where the small primes enter.

---

## §60 What the proof actually consumes — the admissible-family interface

Reading §§28--59 back, the chain never uses the Xi divisor as such.  It uses a family of points
`beta : XiZeroCopy -> C` with six properties:

```text
(P1)  Re beta q  >=  c > 0                      heights bounded away from zero
(P2)  |Im beta q|  <=  B  for a fixed B         displacements uniformly bounded
(P3)  sum_q exp(-sigma Re beta q) < infinity    for every sigma > 0
(P4)  {q : Re beta q <= R} is finite            shells are finite
(P5)  beta (lineConj q) = conj (beta q)         conjugation stability
(P6)  Im beta q = 0  <->  q lies on the critical line
```

`(P1)`+`(P2)` give the order-one envelope and hence Phragmén--Lindelöf; `(P3)`+`(P4)` give
summability, least heights and the spectral gap; `(P5)` upgrades `Im <= 0` to `Im = 0` and doubles
the aligned amplitude; `(P6)` converts the conclusion into RH.  Nothing else is used.

### Why this matters: the prime bridge

The Poisson family `beta = alpha^` satisfies all six but is **not prime-accessible** (§31: its test
function has a corner at `r = 0`, so its Fourier transform decays only like `1/x^2` and the explicit
formula's prime sum diverges).

The **mass-shifted** family `beta_a q = sqrt(alpha^ q ^ 2 + a^2)` with `a > 1/2` satisfies all six as
well -- §31 checked (P1) with `c = sqrt(a^2 - 1/4)`, (P2) with `B = 1/2` (indeed `|Im beta_a| <
|delta|`), (P4) and the branch condition; (P5) holds because the principal root commutes with
conjugation on the right half-plane; and (P6) because `Im beta_a = 0` iff `g delta = 0` -- **and it
is prime-accessible**, its transform decaying like `exp(-a|x|)`.

> **[CONJECTURE, structural]**  The chain of §§28--59, restated over an admissible family, applies
> verbatim to `beta_a`.  Consequently
> ```text
> RH  <->  sum_n Lambda(n) n^(-1/2) * 2 a t K_1(a sqrt(t^2 + (log n)^2)) / sqrt(t^2 + (log n)^2)
>          is bounded on a vertical line,
> ```
> with a formally verified path from the right-hand side to `RiemannHypothesis`.

That is the shape the open core should be attacked in: the archimedean side decays like `u^(-1/2)`
(§33), the pole side is bounded exactly when `a > 1/2`, so the entire content is one oscillatory
prime sum.

### Honest status

The interface above is a reading of the finished proof, not a new theorem; restating the Lean
development over an abstract admissible family is a refactor, not a discovery, and I have not done
it.  What is proved is the instance at `beta = alpha^`:

```text
[LEAN-PROVED]  riemannHypothesis_iff_exists_xiPoissonTrace_line_bound
[OPEN CORE]    the boundedness itself
```

The open core is RH.  Nothing in §§26--60 reduces its difficulty; what they change is its *form* --
from a statement about zeros to a single explicit analytic inequality, with every step from that
inequality to the theorem machine-checked.

### Next

Two independent lines, both concrete:

1. **Refactor to the admissible interface**, then instantiate at `beta_a`.  This is bounded work with
   a known endpoint, and it is what makes the open core a statement about primes rather than about
   an inaccessible trace.
2. **Attack the oscillatory prime sum** in the form §33 left it: the complex saddle escapes the
   contour for every `a > 1/2`, so the sum is endpoint-governed; compute the endpoint contribution
   exactly and compare it with the pole term `2 exp(-t sqrt(a^2 - 1/4))`, which is the only other
   bounded quantity in the identity.

---

## §61 The admissible-family interface, formalized

`[LEAN-PROVED]` `formal/GaloisForLFunctions/RHTower/XiSpectralFamily.lean`
(lint clean; axioms `propext, Classical.choice, Quot.sound`):

```text
structure SpectralFamily
  pt, base, base_pos, base_le, abs_im_lt, summable_weight, shell_finite, conj_stable
SpectralFamily.weight / term / traceReal / traceC
SpectralFamily.norm_term_le              order-one envelope, from abs_im_lt alone
SpectralFamily.summable_norm_term
SpectralFamily.norm_traceC_le            ‖trace tau‖ <= exp(|Im tau|/2) * traceReal (Re tau)
SpectralFamily.norm_traceC_le_of_im_eq_zero
SpectralFamily.traceReal_antitone
xiPoissonFamily                          the Poisson coordinate is an instance
```

§60 read the six properties off the finished proof; this turns that reading into a Lean structure and
checks that the envelope, summability, antitonicity and the RH-collapse follow from the interface
alone -- no reference to the Xi divisor beyond the index type.

The point is the **second** instance.  The Poisson family is not prime-accessible (§31); the
mass-shifted family `sqrt(alpha^^2 + a^2)` with `a > 1/2` is, and §31 verified each of the six
properties for it.  Once the remaining steps of the chain are stated over `SpectralFamily`, the
criterion transfers to a carrier whose explicit formula converges, and the open core becomes a
statement about an explicit prime sum rather than about an inaccessible trace.

### What is instantiated and what is not

`xiPoissonFamily` takes `0 < xiPoissonBottomHeight` as an argument rather than proving it inside,
because that fact lives downstream (`XiPoissonShellSplit`).  That is a wiring detail, not a gap: the
hypothesis is `[LEAN-PROVED]` as `xiPoissonBottomHeight_pos`.

### Ledger

```text
[LEAN-PROVED]  RH <-> Theta bounded on a vertical line              §59
[LEAN-PROVED]  the admissible-family interface and its envelope     §61
[to formalize] the rest of the chain over SpectralFamily
[to formalize] the mass-shifted instance
[OPEN CORE]    the boundedness itself
```

### Next

Continue the transfer: state analyticity, Phragmén--Lindelöf, the shell structure and the assembly
over `SpectralFamily`.  Each is the existing proof with `xiPoissonPoint` replaced by `F.pt` and the
four structure fields supplying what was previously a named lemma; the abstract ingredients
(`GeometricAmplitudeDominance`, `TrigPolynomialPhaseSelection`, `RealExponentialSumRigidity`) are
already family-independent and need no change.

---

## §62 Analyticity and shell structure over the interface

`[LEAN-PROVED]` `formal/GaloisForLFunctions/RHTower/XiSpectralFamilyAnalytic.lean`
(lint clean; axioms `propext, Classical.choice, Quot.sound`):

```text
SpectralFamily.norm_term_le_on_box       box domination, from abs_im_lt and re_nonneg
SpectralFamily.differentiableOn_traceC_box
SpectralFamily.analyticOnNhd_traceC      the trace is analytic on Re t > 0
SpectralFamily.exists_min_re_of_nonempty every nonempty set of copies attains a least height
SpectralFamily.cut / mem_cut / cut_lineConj / finite_cut_shell
```

Two of the four blocks of the chain are now interface-level.  Notably `exists_min_re_of_nonempty` --
the lemma that replaced the shell induction by a minimal counterexample (§43) -- needs only
`shell_finite`, and `cut_lineConj` needs only `conj_stable`: the peeling structure is a consequence
of the interface, not of the Poisson coordinate.

### Transfer ledger

```text
[LEAN-PROVED, interface]  envelope, summability, antitonicity, RH-collapse        §61
[LEAN-PROVED, interface]  analyticity, least heights, cuts, shells                §62
[to transfer]             Phragmen-Lindelof and the half-plane decay
[to transfer]             the bottom-shell assembly and the wrapper
[to instantiate]          the mass-shifted family
[OPEN CORE]               the boundedness itself
```

The two remaining transfers are the Phragmén--Lindelöf step (§39) and the assembly (§41, §59); both
are the existing proofs with `F.pt` in place of `xiPoissonPoint`, and both consume only interface
fields plus the three family-independent abstract lemmas.

### Next

Transfer the Phragmén--Lindelöf step.  Its four hypotheses map onto interface facts exactly as they
did for the Poisson coordinate: `DiffContOnCl` from `analyticOnNhd_traceC`, the `∃ c < 2` growth from
`norm_traceC_le` (order one, because `abs_im_lt` bounds the displacements), the real-ray bound from
the hypothesis being contraposed, and the imaginary-ray bound from `base_le` -- every height is at
least the family's base, which is what makes the twist by the least height bounded there.

---

## §63 Phragmén--Lindelöf over the interface

`[LEAN-PROVED]` `formal/GaloisForLFunctions/RHTower/XiSpectralFamilyDecay.lean`
(lint clean; axioms `propext, Classical.choice, Quot.sound`):

```text
SpectralFamily.bottomCopy / bottomHeight / bottomHeight_le / bottomHeight_pos
SpectralFamily.exp_bottomHeight_mul_traceReal_le       the imaginary-ray bound
SpectralFamily.twist                                   the least-height twist
SpectralFamily.norm_twist_le                           order-one envelope for the twist
SpectralFamily.norm_twist_imaginary_ray / _real_ray
SpectralFamily.norm_twist_le_of_line_bound             Phragmen-Lindelof, quadrants III and IV
SpectralFamily.norm_traceC_le_of_line_bound
  ‖trace t‖ <= max C (traceReal sigma) * exp(-(bottomHeight (Re t - sigma)))   for Re t >= sigma
```

Three of the four blocks of the chain are now interface-level.  The `∃ c < 2` hypothesis is
discharged by `norm_twist_le`, which comes from `abs_im_lt` alone -- so **the reason the argument
works is a single structure field**: displacements bounded by one half.  A family whose
displacements were unbounded would have an envelope of order greater than one and the quadrant
theorem would not apply, which is exactly the Gaussian coordinate's failure recorded in §39.

Note `bottomHeight` is the family's own least height, obtained from `shell_finite` via
`exists_min_re_of_nonempty`; `base` only has to be *some* positive lower bound, which is what makes
the interface easy to instantiate.

### Transfer ledger

```text
[LEAN-PROVED, interface]  envelope, summability, antitonicity, RH-collapse   §61
[LEAN-PROVED, interface]  analyticity, least heights, cuts, shells           §62
[LEAN-PROVED, interface]  Phragmen-Lindelof and half-plane decay             §63
[to transfer]             the bottom-shell assembly and the wrapper
[to instantiate]          the mass-shifted family
[OPEN CORE]               the boundedness itself
```

### Next

The assembly.  Over the interface it needs: the bottom shell as a `Finset` (from `shell_finite`), the
line factorization on it (heights agree there, so the twist leaves only a phase), the vertical split
and tail bound (from `summable_weight` and the gap given by `exists_min_re_of_nonempty` on the copies
strictly above), and then `RealExponentialSumRigidity` -- which is already family-independent.  The
wrapper then repeats §59 with `F.cut` in place of `xiPoissonCut`.

---

## §64 The shell structure over the interface

`[LEAN-PROVED]` `formal/GaloisForLFunctions/RHTower/XiSpectralFamilyShell.lean`
(lint clean; axioms `propext, Classical.choice, Quot.sound`):

```text
SpectralFamily.bottomShell / mem_bottomShell / mem_bottomShell_lineConj
SpectralFamily.aboveBottom / mem_aboveBottom / exists_secondHeight
SpectralFamily.bottomShellSum / aboveBottomSum
SpectralFamily.bottomShellSum_eq                      the height factors out, leaving a phase
SpectralFamily.traceC_vertical_split
SpectralFamily.exp_bottomHeight_mul_norm_aboveBottomSum_le    the weighted tail bound
```

All four structural blocks of the chain are now stated over the interface.  `bottomShellSum_eq`
reuses `xiPoisson_line_factor` unchanged -- that lemma was always a statement about four real
numbers, not about the Xi divisor, which is why it transfers for free.

### Transfer ledger

```text
[LEAN-PROVED, interface]  envelope, summability, antitonicity, RH-collapse   §61
[LEAN-PROVED, interface]  analyticity, least heights, cuts, shells           §62
[LEAN-PROVED, interface]  Phragmen-Lindelof and half-plane decay             §63
[LEAN-PROVED, interface]  bottom shell, split, tail bound                    §64
[to transfer]             the assembly and the wrapper
[to instantiate]          the mass-shifted family
[OPEN CORE]               the boundedness itself
```

What remains of the transfer is the assembly (§41 verbatim, with `F.pt`) and the wrapper (§59
verbatim, with `F.cut`).  Both consume only what is now proved plus the three family-independent
abstract lemmas.

### Next

The interface assembly: regroup the bottom-shell sum by displacement, bound it uniformly in `u` by
combining half-plane decay (§63) with the tail bound (§64) at `v = |u| / (2 (g_2 - g_1))`, and apply
`HTGeometry.le_zero_of_expSum_norm_le`.  Then `conj_stable` upgrades the conclusion from
`Im <= 0` to `Im = 0`, and the minimal-counterexample wrapper closes it -- both already proved for
the Poisson instance, and both using only interface fields.

---

## §65 The assembly over the interface

`[LEAN-PROVED]` `formal/GaloisForLFunctions/RHTower/XiSpectralFamilyOnLine.lean`
(lint clean; axioms `propext, Classical.choice, Quot.sound`):

```text
SpectralFamily.bottomShell_regroup       the shell sum grouped by displacement
SpectralFamily.im_nonpos_of_line_bound   bounded line  ->  every bottom displacement <= 0
SpectralFamily.im_eq_zero_of_line_bound  and, by conjugation stability, = 0
```

The transfer of the whole chain is complete except for the wrapper: for **any** admissible family,
boundedness of its trace on one vertical line forces its least-height shell onto the real axis.

That statement no longer mentions the Riemann zeta function.  It says: a countable family of points
in the closed right half-plane, with heights bounded below and away from zero, displacements bounded
by one half, summable weight, finite shells and conjugation symmetry, has a real least-height shell
as soon as its exponential sum is bounded on one vertical line.

### Transfer ledger

```text
[LEAN-PROVED, interface]  envelope, summability, antitonicity, RH-collapse   §61
[LEAN-PROVED, interface]  analyticity, least heights, cuts, shells           §62
[LEAN-PROVED, interface]  Phragmen-Lindelof and half-plane decay             §63
[LEAN-PROVED, interface]  bottom shell, split, tail bound                    §64
[LEAN-PROVED, interface]  the assembly                                       §65
[to transfer]             the minimal-counterexample wrapper
[to instantiate]          the mass-shifted family
[OPEN CORE]               the boundedness itself
```

### Next

The wrapper.  Over the interface it needs the cut family: given `g`, the sub-family supported on
`F.cut g` is admissible whenever the cut is nonempty (all six fields restrict), so the wrapper is
`im_eq_zero_of_line_bound` applied to the cut family, exactly as §59 applied the Poisson version to
`xiPoissonCut`.  Then instantiating at the mass-shifted family turns the open core into boundedness
of a convergent prime sum.

---

## §66 The lift: applying the assembly at every height without reindexing

`[LEAN-PROVED]` `formal/GaloisForLFunctions/RHTower/XiSpectralFamilyLift.lean`
(lint clean; axioms `propext, Classical.choice, Quot.sound`):

```text
SpectralFamily.below g          the copies below a height cut
SpectralFamily.finite_below     finite, from shell_finite
SpectralFamily.below_lineConj   conjugation-stable, from conj_stable
SpectralFamily.lift g H hH      the family with each copy below g replaced by the real point H
```

`lift` is a `SpectralFamily`: all six fields survive the replacement.  Heights stay above the base
because `H` does; displacements stay bounded because the replacements have displacement zero;
summability survives because the replaced set is finite (`summable_subtype_and_compl` splits the sum
into a finite part and an unchanged part); shells stay finite because the replaced set is finite;
and conjugation stability survives because line conjugation preserves heights, so it preserves the
branch, and a real point is its own conjugate.

### Why this is the right move

The wrapper of §59 needed the trace *above* a height, which for the Poisson coordinate meant a whole
parallel development (`XiPoissonCutTrace` through `XiPoissonCutOnLine`, §§42--43, 58--59).  At the
interface that is unnecessary: raising the low copies to a common real height turns "the trace above
`g`" into "the trace of another admissible family", and the assembly already proved for **every**
admissible family applies directly.  The replaced copies contribute a bounded real amount to the line
value, so the line bound transfers.

### Transfer ledger

```text
[LEAN-PROVED, interface]  the whole chain through the assembly       §61-§65
[LEAN-PROVED, interface]  the lift                                   §66
[to transfer]             the wrapper, now a short argument
[to instantiate]          the mass-shifted family
[OPEN CORE]               the boundedness itself
```

### Next

The interface wrapper: given a line bound for `F` and a copy of least height among those off the
line, apply the assembly to `F.lift g H` for `g` that copy's height and `H` above the cut's least
height.  The lifted family's bottom shell is the cut's, its trace differs from `F`'s by two finite
sums of bounded modulus, and the chosen copy lies in that shell -- a contradiction.

---

## §67 The transfer completes: the criterion holds for every admissible family

`[LEAN-PROVED]` `formal/GaloisForLFunctions/RHTower/XiSpectralFamilyRH.lean`
(lint clean; axioms `propext, Classical.choice, Quot.sound`):

```text
SpectralFamily.lift_pt_of_le / lift_pt_of_lt
SpectralFamily.im_eq_zero_of_line_bound_all
  boundedness on one vertical line  ->  every displacement of the family vanishes
```

The wrapper takes the lift at `H = g`, so the copies below the cut land exactly on the bottom shell
of the lifted family.  They are real by minimality, the two finite correction sums have bounded
modulus on the line, the lifted least height is `g`, and the chosen counterexample lies in the lifted
bottom shell -- which §65 has already made real.  Contradiction.

### The statement, free of zeta

> Let `beta` assign to each copy of the Xi divisor a complex number with: heights bounded below by a
> positive constant, displacements bounded by `1/2`, summable weight `exp(-sigma Re beta)` for every
> `sigma > 0`, finite shells, and `beta` conjugation-equivariant for the critical-line involution.
> If `sum_q exp(-t beta q)` is bounded on one vertical line of the open right half-plane, then every
> `beta q` is real.

Instantiated at the Poisson coordinate this is RH (§59, and now again through the interface).  The
point of the interface is the *second* instantiation.

### Ledger

```text
[LEAN-PROVED]  the criterion for every admissible family        §61-§67
[LEAN-PROVED]  RH <-> Theta bounded on a vertical line           §59
[to instantiate]  the mass-shifted family sqrt(alpha^^2 + a^2)
[OPEN CORE]       the boundedness itself
```

### Next

Instantiate at `beta_a q = sqrt(alpha^ q ^2 + a^2)` for `a > 1/2`.  What has to be built is the
principal square root on the right half-plane together with two estimates already computed on paper
in §31: `Re sqrt(w + a^2) >= sqrt(a^2 - 1/4)` and `|Im sqrt(w + a^2)| < |delta| < 1/2`.  Conjugation
equivariance is automatic because the principal root commutes with conjugation off the cut, and
shell finiteness and summability follow by comparison with the Poisson heights.  With that instance,
`im_eq_zero_of_line_bound_all` turns boundedness of a **convergent prime sum** into RH.

---

## §68 The principal square root, formalized

`[LEAN-PROVED]` `formal/GaloisForLFunctions/HTGeometry/PrincipalSquareRoot.lean`
(lint clean; axioms `propext, Classical.choice, Quot.sound`):

```text
csqrtRe z = sqrt ((‖z‖ + Re z)/2),   csqrtIm z = Im z / (2 csqrtRe z),   csqrt z
csqrtRe_pos            0 < Re z  ->  0 < csqrtRe z
sq_csqrtRe             csqrtRe z ^ 2 = (‖z‖ + Re z)/2
re_le_sq_csqrtRe       Re z <= csqrtRe z ^ 2
abs_csqrtIm            |csqrtIm z| = |Im z| / (2 csqrtRe z)
csqrtIm_eq_zero_iff    csqrtIm z = 0  <->  Im z = 0
csqrt_conj             the root commutes with conjugation
```

These are exactly the four facts the mass-shifted instantiation consumes, and no branch-cut theory
is needed: on the right half-plane `‖z‖ + Re z > 0`, so the formulas are unambiguous and positivity
is immediate.

### How they give the mass-shifted family's five conditions

Write `alpha^ = R + i J` with `R` the height and `|J| < 1/2`, and `z = alpha^^2 + a^2`, so

```text
Re z = R^2 - J^2 + a^2 >= a^2       (since R > 4 and |J| < 1/2),
Im z = 2 R J.
```

Then, using only the lemmas above:

```text
Re beta_a = csqrtRe z,     csqrtRe z ^ 2 >= Re z >= a^2   =>   Re beta_a >= a          (P1)
|Im beta_a| = |Im z| / (2 csqrtRe z) = R |J| / csqrtRe z
            <= R |J| / sqrt(Re z) = R |J| / sqrt(R^2 - J^2 + a^2) < |J| < 1/2          (P2)
csqrtRe z ^ 2 >= R^2 - J^2 + a^2 >= R^2 - 1/4  =>  Re beta_a >= R - 1                  (P3), (P4)
csqrt_conj and the conjugation-equivariance of alpha^                                  (P5)
csqrtIm_eq_zero_iff:  Im beta_a = 0  <->  R J = 0  <->  J = 0                          (P6)
```

The strict inequality in (P2) is the only one that needs `a > 1/2`: it is `J^2 < a^2`.

### Ledger

```text
[LEAN-PROVED]  the criterion for every admissible family        §61-§67
[LEAN-PROVED]  the principal square root and its four facts     §68
[to instantiate]  assemble the five conditions into a SpectralFamily
[OPEN CORE]       the boundedness itself
```

### Next

Assemble the instance.  Each of the five lines above is a short calculation from
`PrincipalSquareRoot` plus the Poisson facts already in the corpus (`four_lt_norm_xiSpectralPoint`,
`abs_xiPoissonPoint_im_lt_half`, `finite_xiPoissonShell`, `summable_xiPoissonWeight`,
`xiPoissonPoint_lineConj`).  With the instance in hand, `im_eq_zero_of_line_bound_all` reads: if the
mass-shifted trace is bounded on one vertical line then every zero is on the critical line -- and
that trace is the one whose explicit formula converges.

---

## §69 The mass-shifted instance: the criterion in prime-accessible form

`[LEAN-PROVED]` `formal/GaloisForLFunctions/RHTower/XiMassShiftedFamily.lean`
(lint clean; axioms `propext, Classical.choice, Quot.sound`):

```text
xiMassArg a q = alpha^ q ^ 2 + a^2
xiMassArg_re / xiMassArg_im     Re = R^2 - J^2 + a^2,  Im = 2 R J
three_lt_xiPoissonPoint_re      3 < R, from ‖alpha‖ > 4 and |J| < 1/2
xiMassArg_re_pos
xiPoissonPoint_re_lt_csqrtRe    R < Re beta_a, because a^2 > J^2
xiMassFamily ha                 **the admissible instance**, for any a > 1/2
riemannHypothesis_of_xiMassTrace_line_bound
  boundedness of the mass-shifted trace on one vertical line  ->  RH
```

Every one of the six admissibility conditions is discharged from the two inequalities computed on
paper in §31 -- `Re beta_a >= a` and `|Im beta_a| < |J|` -- and the single comparison
`R < Re beta_a`, which supplies summability and finite shells simultaneously.  The threshold
`a > 1/2` is used exactly once, as `J^2 < a^2`.

### What the corpus now states

```text
[LEAN-PROVED]  RH  <->  the Poisson trace is bounded on a vertical line        §59
[LEAN-PROVED]  the same criterion for every admissible family                  §67
[LEAN-PROVED]  the mass-shifted family is admissible, so its boundedness       §69
               on one vertical line implies RH
```

The last is the criterion on the carrier whose explicit formula **converges** (§31): the test
function `exp(-t sqrt(r^2+a^2))` is analytic in the strip `|Im r| < a`, so its transform decays like
`exp(-a|x|)` and the prime side `sum_n Lambda(n) n^(-1/2) h^_t(log n)` is a convergent sum.  On paper
(§§32--33) that sum's archimedean partner decays like `u^(-1/2)` and its pole term is bounded exactly
when `a > 1/2`, so the entire content of the open core is one oscillatory prime sum.

### Ledger

```text
[LEAN-PROVED]  everything from the boundedness hypothesis to RiemannHypothesis
[OPEN CORE]    the boundedness hypothesis itself, now on a prime-accessible carrier
[PAPER]        the identification of that trace with the explicit-formula prime sum
```

### Next

Two things, in order of how much they buy:

1. **Attack the open core** in its prime form: show
   `sum_n Lambda(n) n^(-1/2) 2 a t K_1(a sqrt(t^2 + log^2 n)) / sqrt(t^2 + log^2 n)` is bounded on a
   vertical line.  §33 reduced this to the fluctuation of the PNT error against the `K_1` kernel,
   with the mean part provably bounded and the complex saddle escaping the contour.
2. **Formalize the explicit formula for this carrier**, which would connect
   `riemannHypothesis_of_xiMassTrace_line_bound` to the prime sum inside Lean rather than on paper.

---

## §70 The interface cannot be gamed

`[LEAN-PROVED]` (added to `XiSpectralFamilyRH.lean`; lint clean; axioms
`propext, Classical.choice, Quot.sound`):

```text
SpectralFamily.im_eq_zero_iff_exists_line_bound
  (∀ q, Im (F.pt q) = 0)  <->  ∃ sigma > 0, ∃ C, ∀ x, ‖F.traceC (sigma + i x)‖ <= C
```

### Why this is worth stating

The interface was built to let the open core be moved to a prime-accessible carrier (§69).  A natural
follow-up question is whether it can be moved further -- to some cleverer admissible family whose
boundedness is *easier* than RH.  It cannot:

> For **every** admissible family, boundedness on a vertical line is equivalent to the reality of its
> points, and reality of the points of any family satisfying (P6) is RH.

So the whole family of criteria produced in §§26--69 is a single criterion in many coordinates, all
exactly as hard as each other.  Changing carrier changes the *form* of the open core -- from an
inaccessible trace to a convergent prime sum -- and nothing else.  That is not a defect: it is the
precise sense in which the reformulation is faithful, and it is why §31's prime-accessibility was
worth the work while a search for a "softer" carrier would not be.

### The corpus, in one line each

```text
riemannHypothesis_iff_exists_xiPoissonTrace_line_bound     RH <-> a bounded vertical line   §59
SpectralFamily.im_eq_zero_iff_exists_line_bound            the same, for any admissible family §70
riemannHypothesis_of_xiMassTrace_line_bound                the prime-accessible instance      §69
re_xiPoissonMomentTraceC_nonneg_of_rh                      RH -> complete monotonicity        §49
xiPoissonPoint_im_eq_zero_of_forall_moment_nonneg          its converse at the bottom shell   §57
```

Everything from an explicit analytic hypothesis to `RiemannHypothesis` is machine-checked.  What is
not proved, and is the only thing not proved, is the hypothesis.

### Next

The open core, in the only form that now matters:

```text
∃ sigma > 0, ∃ C, ∀ x,  ‖ sum_rho exp(-(sigma + i x) sqrt(alpha^_rho^2 + a^2)) ‖ <= C
```

for one `a > 1/2`.  §§32--33 put its prime side in closed form -- a `K_1` kernel against the von
Mangoldt weight, with a decaying archimedean partner and a pole term bounded exactly at the same
threshold -- and showed the complex saddle escapes the contour, so the sum is endpoint-governed.  The
next concrete computation is that endpoint contribution.

---

## §71 Promotion: the criterion carded into `3-formalized`

`docs/drafts/pipeline/3-formalized/poisson-vertical-line-rh-criterion.md` now carries the finished
result with its Lean surface, module list, approach, open core, and -- explicitly -- the four
corrections made during the work (§37, §38, §53, §58).  Seventy sections of in-progress notes were
overdue for a card; the Kanban discipline exists so that a reader arrives at the theorem and its
exact status rather than at a transcript.

Stage gates recorded honestly:

```text
[x] 1 -> 2  paper proof complete (as corrected)
[x] 2 -> 3  Lean theorems, lake build green, axioms exactly the three standard ones, lint passes
[ ] 3 -> 4  publication-ready
```

The card states the open core as the open core, not as a step.

### What the card claims, precisely

- **Proved:** RH is equivalent to boundedness of the Poisson zero trace on one vertical line; the
  same criterion holds for every admissible spectral family; the mass-shifted family is admissible,
  so boundedness of the prime-accessible trace implies RH; RH implies complete monotonicity of the
  trace, and the converse holds at the bottom shell by a real-variable argument.
- **Not proved:** the boundedness.  That is RH.

### Next

Two directions remain open, and they are different in kind:

1. **The open core.**  §§32--33 leave it as one oscillatory prime sum with a decaying archimedean
   partner; the next computation is the endpoint contribution left by the escaped saddle.
2. **The quantitative channel.**  §44 showed `Theta(sigma + i u) = O(exp(lambda|u|))` implies the
   zero-free region `|delta| <= lambda`; formalizing that would turn every improvement of an
   explicit growth exponent into a zero-free region, on a continuous scale, rather than an
   all-or-nothing criterion.  It is the same Phragmén--Lindelöf chain with `exp(-+ lambda y)` carried
   through each quadrant, and it is the one part of the development whose value does not depend on
   settling the open core.

---

## §72 The graded dominance lemma

`[LEAN-PROVED]` (added to `HTGeometry/RealExponentialSumRigidity.lean`; lint clean; axioms
`propext, Classical.choice, Quot.sound`):

```text
le_of_expSum_norm_le_exp
  distinct real exponents, coefficients of fixed positive moduli (phases free),
  ‖ sum_i B u i exp(u J i) ‖ <= K exp(lam |u|)  for all u
  ->  J i <= lam  for every i
```

`lam = 0` is `le_zero_of_expSum_norm_le`; the general case is the abstract core of the quantitative
channel.  The proof is the same dominance -- divide by the largest exponential and let `u ->
infinity` -- with the majorant `K exp(u (lam - J i₀))`, which still tends to zero precisely when the
largest exponent exceeds `lam`.

### Why the graded version matters

The criterion proved in §§59--70 is all-or-nothing: `Theta` bounded, or nothing.  The graded version
turns the growth exponent into a continuous parameter:

> **[PAPER-PROVED, §44]**  `‖Theta(sigma + i u)‖ << exp(lam |u|)`  implies the zero-free region
> `|delta_rho| <= lam` for every zero.

`lam = 1/2` is the a priori bound and says nothing; `lam = 0` is RH; every value in between is a
zero-free region obtained from an explicit, zero-free, prime-computable growth exponent.  This is the
one part of the development whose value does not wait on the open core: a partial bound on the
exponent is a partial result about zeros, immediately.

### What remains for the graded chain

```text
[LEAN-PROVED]  graded dominance                                    §72
[to formalize] the lam-twisted Phragmen-Lindelof
               (multiply by exp(-+ lam y) on each quadrant; the boundary bounds become
                constants again, so the quadrant theorem applies unchanged)
[to formalize] the graded assembly and wrapper
```

### Next

The `lam`-twisted Phragmén--Lindelöf.  On the third quadrant, `G(y) exp(lam y)` has modulus
`|G(y)| exp(lam Re y)`, which on the real ray `x <= 0` is at most `C exp(lam|x|) exp(lam x) = C`, and
on the imaginary ray is unchanged because `|exp(lam i v)| = 1`.  The fourth quadrant uses
`exp(-lam y)`.  So the *same* quadrant theorem, with the same `∃ c < 2` supplied by the order-one
envelope, yields `|G(y)| <= M exp(lam |Re y|)` -- and the rest of the chain carries the extra factor
through to `le_of_expSum_norm_le_exp`.

---

## §73 Graded Phragmén--Lindelöf

`[LEAN-PROVED]` `formal/GaloisForLFunctions/RHTower/XiSpectralFamilyGraded.lean`
(lint clean; axioms `propext, Classical.choice, Quot.sound`):

```text
SpectralFamily.gtwist / norm_gtwist / differentiableOn_gtwist / norm_gtwist_le
SpectralFamily.norm_twist_le_of_line_growth
  ‖trace(sigma + i x)‖ <= C exp(lam |x|)  for all x
  ->  ‖twist sigma y‖ <= max C (traceReal sigma) * exp(lam |Re y|)  on the lower half plane
```

The extra factor `exp(+- lam y)` is applied per quadrant, and it does exactly what it should: on the
real ray it cancels the hypothesis' `exp(lam|x|)` and turns the boundary bound back into a constant;
on the imaginary ray its modulus is one, so that bound is untouched; and it raises the exponential
type from `1/2 + g_1` to `1/2 + g_1 + lam`, which is still order one and so still admissible for the
quadrant theorem.

That last point is the reason the grading is free: the `∃ c < 2` hypothesis has slack.  It would not
have slack for the Gaussian carrier, whose envelope already sits at the boundary `c = 2` -- so the
graded channel exists only in the Poisson coordinate, for the same reason the ungraded one does.

### Ledger

```text
[LEAN-PROVED]  graded dominance                    §72
[LEAN-PROVED]  graded Phragmen-Lindelof            §73
[to formalize] the graded assembly and wrapper
[OPEN CORE]    the boundedness (lam = 0 case)
```

### Next

The graded assembly: the same chain as §65 with the extra `exp(lam|u|)` carried through the master
bound, ending in `le_of_expSum_norm_le_exp` instead of `le_zero_of_expSum_norm_le`.  The conclusion
is `|Im (F.pt q)| <= lam` for every copy of the bottom shell, and the graded wrapper then gives it
for every copy -- i.e. an explicit growth exponent on one vertical line becomes an explicit zero-free
region, with no reference to the zeros anywhere in the hypothesis.

---

## §74 The graded assembly: a growth exponent is a zero-free region

`[LEAN-PROVED]` `formal/GaloisForLFunctions/RHTower/XiSpectralFamilyGradedOnLine.lean`
(lint clean; axioms `propext, Classical.choice, Quot.sound`):

```text
SpectralFamily.im_le_of_line_growth
  ‖trace(sigma + i x)‖ <= C exp(lam |x|)  ->  Im (F.pt q) <= lam  on the bottom shell
SpectralFamily.abs_im_le_of_line_growth
  and, by conjugation stability, |Im (F.pt q)| <= lam
```

The factor `exp(lam |u|)` rides through the whole chain without interacting with anything: the
half-plane decay carries it (§73), the tail bound never sees it -- it is controlled by the spectral
gap alone -- and the shell sum inherits it, so the chain ends at
`HTGeometry.le_of_expSum_norm_le_exp` instead of its `lam = 0` case.  The only new ingredient is that
`exp(lam|u|) >= 1`, which lets `M exp(lam|u|) + K` be absorbed into `(M + K) exp(lam|u|)`.

### What this gives that the ungraded statement does not

```text
lam = 1/2   the a priori envelope; says nothing
lam = 0     RH
0 < lam < 1/2   an explicit zero-free region |delta| <= lam
```

The hypothesis mentions no zeros: it is a growth exponent for an explicit trace on one vertical line.
So any unconditional bound of the form `‖Theta(sigma + i x)‖ << exp(lam|x|)` with `lam < 1/2` is an
unconditional zero-free region -- and, by §69, the same holds with the prime-accessible
mass-shifted trace in place of `Theta`.

This is the part of the development that pays before the open core is settled: progress on the
exponent is progress on the zeros, continuously, rather than all at once.

### Ledger

```text
[LEAN-PROVED]  graded dominance, graded Phragmen-Lindelof, graded assembly   §72-§74
[to formalize] the graded wrapper (from the bottom shell to all copies)
[OPEN CORE]    the lam = 0 case, i.e. RH
```

### Next

The graded wrapper.  It is §67's argument verbatim -- minimal counterexample, lift the low copies to
a common real height, transfer the growth hypothesis through two finite sums -- with `exp(lam|x|)`
carried along; the finite corrections are bounded, hence absorbed into the constant, so the lifted
family satisfies the same graded hypothesis.

---

## §75 The graded chain closes

`[LEAN-PROVED]` (added to `XiSpectralFamilyGradedOnLine.lean`; lint clean; axioms
`propext, Classical.choice, Quot.sound`):

```text
SpectralFamily.abs_im_le_of_line_growth_all
  ‖trace(sigma + i x)‖ <= C exp(lam |x|)  for all x
  ->  |Im (F.pt q)| <= lam  for **every** copy
```

The wrapper is §67's with the growth factor carried through.  One point deserves note: in the
ungraded case the copies below the cut were *real*, so their finite contribution had constant
modulus; here they are only known to satisfy `|Im| <= lam`, and their contribution has modulus at
most `weight sigma q * exp(lam |x|)` -- which is exactly the shape of the hypothesis, so the lifted
family inherits it unchanged.  The grading is self-propagating.

### The graded criterion, complete

> For any admissible family: an explicit growth exponent `lam >= 0` for its trace on one vertical
> line of the open right half-plane bounds every displacement by `lam`.

```text
lam = 1/2        the unconditional envelope; vacuous
0 < lam < 1/2    an explicit zero-free region
lam = 0          RH  (and then §70 makes it an equivalence)
```

Instantiated at the Poisson family this reads: any unconditional bound
`‖Theta(sigma + i x)‖ << exp(lam |x|)` with `lam < 1/2` is an unconditional zero-free region
`|delta_rho| <= lam`.  Instantiated at the mass-shifted family (§69) the same holds for the carrier
whose explicit formula converges.

### What the corpus contains at the end of this line of work

```text
riemannHypothesis_iff_exists_xiPoissonTrace_line_bound      RH <-> bounded line            §59
SpectralFamily.im_eq_zero_iff_exists_line_bound             the same, any family           §70
SpectralFamily.abs_im_le_of_line_growth_all                 the graded version             §75
riemannHypothesis_of_xiMassTrace_line_bound                 prime-accessible instance      §69
re_xiPoissonMomentTraceC_nonneg_of_rh                       RH -> complete monotonicity    §49
xiPoissonPoint_im_eq_zero_of_forall_moment_nonneg           converse at the bottom shell   §57
```

All unconditional; all machine-checked; all reducing RH, or a zero-free region, to an explicit
analytic bound on a zero-free object.

### The open core, restated once more

```text
∃ sigma > 0, ∃ C, lam,  ∀ x,  ‖Theta(sigma + i x)‖ <= C exp(lam |x|)   with lam < 1/2.
```

Any such `lam` is a zero-free region; `lam = 0` is RH.  On the prime side (§§32--33) this is
cancellation in a `K_1`-weighted von Mangoldt sum whose archimedean partner decays and whose pole
term is bounded exactly at the threshold `a > 1/2`.

### Next

Attack that cancellation.  The concrete first target is not `lam = 0` but any `lam < 1/2`: by §75
that is already a theorem about zeros, and unlike RH it is not known to be equivalent to anything
famous -- the trivial bound gives `lam = 1/2` and the classical zero-free region gives
`lam < 1/2` only through the zeros, not through the trace.  An unconditional trace bound with
`lam < 1/2` would be new.

---

## §76 Where the two targets actually sit

The card now carries the graded channel.  Before pushing further it is worth being exact about what
`lam < 1/2` would cost, because §75 left it as "the concrete first target" and that deserves a check.

### `lam < 1/2` is not a soft target

A uniform `lam < 1/2` says every zero satisfies `|delta| <= lam`, i.e. `zeta` has **no zeros with
`Re s > 1/2 + lam`** -- a zero-free half-plane strictly inside the critical strip.  That is open.

The classical zero-free region does *not* supply it: de la Vallée Poussin gives
`delta < 1/2 - c / log(|gamma| + 2)`, whose supremum over all heights is exactly `1/2`.  The bound
degrades with height, so it yields no uniform `lam` below `1/2`.

> **[CORRECTION to §75's framing]**  `lam < 1/2` is weaker than RH but is *not* a routine or partially
> known statement; it is open, and by §75 it is equivalent to an unconditional growth bound for the
> trace.  Calling it "the concrete first target" was right about its logical position and wrong to
> imply it is close.

### What that settles about the whole line of work

Both ends of the graded scale are open, and §70 showed the criterion is faithful in every admissible
coordinate, so no reformulation inside this family will make either end easier.  The value delivered
is therefore exactly:

- a **faithful** reduction of RH, and of every intermediate zero-free region, to an explicit analytic
  bound on a zero-free, prime-computable object;
- with **every step from that bound to the conclusion machine-checked**;
- on a carrier for which the explicit formula converges, so the bound is a statement about a
  convergent prime sum;
- together with the negative results that fix the route: the Gaussian carrier fails Phragmén--Lindelöf
  at order exactly two (§39), the pure Poisson carrier is not prime-accessible (§31), moment
  positivity does not peel (§58), and the interface cannot be gamed (§70).

### Honest status

```text
[LEAN-PROVED]  everything from the analytic hypothesis to RiemannHypothesis, in both the
               all-or-nothing and the graded forms, for the Poisson and mass-shifted carriers
[OPEN]         the analytic hypothesis, at every value of lam in [0, 1/2)
```

I have not proved the Riemann Hypothesis, and nothing in §§26--76 reduces the difficulty of the
remaining step; what they change is its form and its verifiability.

### Next

The remaining mathematical question is unchanged and is the one to keep attacking:

> Bound `sum_n Lambda(n) n^(-1/2) * 2 a t K_1(a sqrt(t^2 + log^2 n)) / sqrt(t^2 + log^2 n)` on a
> vertical line, by `C exp(lam|Im t|)` for some `lam < 1/2`.

§33 established that its mean part is bounded unconditionally and that the complex saddle escapes the
contour for every `a > 1/2`, so the sum is endpoint-governed; the endpoint contribution is the next
thing to compute exactly.

---

## §77 The endpoint computation, done — and what it closes

§§33, 75 and 76 all ended by pointing at the same computation: the endpoint contribution of the
oscillatory prime sum left by the escaped saddle.  Here it is, and it is a negative result with an
exact reason.

### The split, once more

```text
P(t)  =  [ mean part ]  +  [ fluctuation ],
```
the mean part being what survives when `psi(x)` is replaced by `x`.  §33 proved the mean part
bounded, structurally: in the no-zero model the explicit formula reads `0 = A + poles - P`, so the
mean part *is* `A + poles`, of modulus `O(u^(-1/2)) + 2 exp(-sigma sqrt(a^2-1/4))`.

The fluctuation is `integral h^_t(L) exp(-L/2) dE(e^L)` with `E(x) = psi(x) - x`.

### The endpoint contribution

Integrating by parts and inserting the classical error term `E(x) << x exp(-c sqrt(log x))`, the
integrand carries `exp(L/2) exp(-c sqrt L)` against `|h^_t|`, which inside the light cone is
`~ u w^(-3/2) exp(-a sigma u / w)` with `w = sqrt(u^2 - L^2)`.  The saddle of the modulus sits at
`w* ~ (2 a sigma)^(1/3) u^(2/3)` (§32), giving

```text
| fluctuation |  <<  exp(u/2) * exp(-c' u^(1/3)) * exp(-c'' sqrt u) * poly(u).
```

Both corrections are **subexponential**.  The exponential rate is still `1/2`.

> **[NEGATIVE RESULT]**  The classical PNT error term yields `lam = 1/2` and nothing better.  The
> endpoint contribution does not improve the exponent.

### Why, exactly

The fluctuation's growth rate on a vertical line is not an accident of the kernel.  `E(x)` is,
through the explicit formula, a sum over the zeros with amplitudes `x^beta`; its exponential rate
against the `K_1` kernel is therefore

```text
sup_rho beta - 1/2  =  sup_rho |delta|  =  V,
```

exactly the quantity the criterion is trying to bound.  Improving `lam` below `1/2` requires an error
term `E(x) << x^theta` with `theta < 1`, which is a zero-free half-plane -- the same open statement.

> **The reduction is faithful on the arithmetic side too.**  §70 proved this abstractly (no
> admissible coordinate is softer); §77 confirms it concretely: no classical input about primes
> breaks the circle, because the prime side's growth rate *is* the zero side's.

### What this closes and what it leaves

Closed: the line of attack that hoped the mass-shifted carrier's convergent explicit formula would
yield an unconditional exponent.  It does not, and the reason is structural rather than technical.

Left standing, unchanged and machine-checked:

```text
[LEAN-PROVED]  ‖trace‖ <= C exp(lam|x|) on one vertical line  ->  |delta_rho| <= lam for all rho
[LEAN-PROVED]  lam = 0 gives RH, and conversely
[OPEN]         any unconditional bound with lam < 1/2
```

### Next

Since neither the archimedean side nor the classical prime input moves the exponent, the remaining
lever is the **interaction** that §15's two counterexample families showed must be used and §32
relocated into the admissibility threshold `a > 1/2`.  Concretely: the pole term
`2 exp(-t sqrt(a^2 - 1/4))` and the transform's decay rate `exp(-a|x|)` are both governed by the same
`a`, and the criterion must hold for *every* `a > 1/2` simultaneously.  A bound that is uniform in
`a` -- or a contradiction extracted from letting `a -> 1/2+`, where the pole term degenerates while
the transform's decay is exactly critical -- is the one place in this construction where the two
inputs are still coupled and unexploited.

---

## §78 The `a`-lever audited: it is not a lever

§77 named the last unexploited coupling -- the parameter `a`, which controls both the pole term
`2 exp(-t sqrt(a^2 - 1/4))` and the transform's decay rate `exp(-a|x|)` -- and asked whether
uniformity in `a`, or the degeneration `a -> 1/2+`, yields anything.  Audited:

### The growth exponent does not depend on `a`

```text
|Im beta_a| = R |delta| / sqrt(R^2 - delta^2 + a^2),
```
so for zeros of height `R >> a` this is `|delta| (1 + O(a^2/R^2))`.  The supremum over the divisor is
therefore approached by the *high* zeros, where the `a`-dependence vanishes:

```text
V_a := sup_rho |Im beta_a|  =  limsup_{R -> infinity} |delta|  =  V   for every a.
```

Large `a` shrinks the displacements of the low zeros -- which are on the line anyway -- and does
nothing to the high ones.  No choice of `a` improves the exponent.

### The threshold is admissible but not accessible

`[LEAN-PROVED]`  `xiMassFamily` now takes `1/2 <= a` rather than `1/2 < a`: the only place the
threshold entered was `delta^2 < a^2`, and `|delta| < 1/2` makes that true already at `a = 1/2`.
So `beta_{1/2}` **is** an admissible family and the criterion holds for it.

But `a = 1/2` is exactly where prime-accessibility fails: the transform decays like `exp(-|x|/2)`,
and the prime sum becomes `sum_n Lambda(n)/n`, logarithmically divergent -- and its divergence is the
pole.  So at the threshold the pole term and the prime sum's divergence merge, which is precisely why
`a > 1/2` was needed for the explicit formula and precisely why `a = 1/2` gives no new information:
the two sides degenerate together.

> **[NEGATIVE RESULT]**  The `a`-family is a one-parameter family of *equivalent* criteria, not a
> deformation with a soft point.  Its two degenerations -- `a -> infinity` (pole term vanishes,
> transform decays fast) and `a -> 1/2+` (pole term flattens, transform decay becomes critical) --
> both leave the growth exponent at `V`.

### Where this leaves the construction

Every degree of freedom in the reduction has now been audited:

```text
carrier order       Gaussian fails Phragmen-Lindelof at order exactly 2       §39
carrier corner      pure Poisson is not prime-accessible                      §31
positivity form     moment positivity does not peel                           §58
coordinate choice   the interface cannot be gamed                             §70
prime input         the classical error term leaves the exponent at 1/2       §77
mass parameter      no value of `a` moves the exponent                        §78
```

Each is a genuine no-go with an exact mechanism, and together they say the reduction is tight: it is
faithful in every direction one might hope to deform it.  That is the correct outcome for a
*reduction* -- and it means the remaining step is not a matter of choosing better coordinates.

### Honest status

```text
[LEAN-PROVED]  ‖trace‖ <= C exp(lam|x|) on one vertical line  ->  |delta_rho| <= lam
[LEAN-PROVED]  lam = 0 is RH, and conversely; for the Poisson and mass-shifted carriers;
               and for every admissible family
[OPEN]         any unconditional bound with lam < 1/2
```

RH is not proved.  The remaining step is an unconditional analytic bound, and §§70, 77, 78 show it
cannot be obtained by re-choosing anything inside this construction.

### Next

The next genuinely new move has to come from outside the reduction: an input that bounds the trace
without going through the zeros.  The one structural asset not yet used is that the criterion holds
for the *whole* one-parameter family simultaneously, together with the explicit `a`-dependence of the
pole term -- i.e. a differential relation in `a` linking `Theta_a` to `Theta_{a'}`.  Whether that
relation is non-trivial is the next thing to compute: `d/da beta_a = a / beta_a`, so
`d/da Theta_a(t) = -t sum_rho (a / beta_a) exp(-t beta_a)`, which is a *weighted* trace of the same
family -- and weighted traces are exactly what the moment machinery of §§46--57 already handles.

---

## §79 The `a`-derivative identity, and the last lever audited

§78 ended by asking what the differential relation in `a` computes.  Here it is.

### The identity

`beta_a = sqrt(alpha^^2 + a^2)` gives `d beta_a / da = a / beta_a`, so

```text
d/da Theta_a(t)  =  - t a * sum_rho beta_rho^{-1} exp(-t beta_rho)
                 =  - t a * integral_t^infinity Theta_a(s) ds,
```

the second equality because `integral_t^infinity exp(-s beta) ds = exp(-t beta) / beta`.

> **[IDENTITY]**  `d/da Theta_a(t) = - t a * integral_t^infinity Theta_a(s) ds`.

A clean integro-differential relation in the two parameters, with no zeros in it.

### Why it is not a lever

Suppose `‖Theta_a(sigma + i x)‖ << exp(lam|x|)`.  The half-plane decay of §63 gives
`‖Theta_a(t + r)‖ <= M exp(lam|x|) exp(-g_1 r)` for `r >= 0`, so the integral converges and

```text
‖d/da Theta_a(sigma + i x)‖  <=  a |sigma + i x| M exp(lam |x|) / g_1  ~  C |x| exp(lam|x|).
```

Integrating in `a` moves `Theta_{a_0}` to `Theta_{a_1}` at the cost of a polynomial factor only: the
exponential rate is unchanged.  So the identity transports bounds across the family without
improving them -- exactly what §78 found by direct computation, now with the mechanism visible.

### The threshold, seen through the identity

Differentiating the explicit formula in `a`, the pole term contributes

```text
d/da [ 2 exp(-t sqrt(a^2 - 1/4)) ]  =  -2 t (a / sqrt(a^2 - 1/4)) exp(-t sqrt(a^2 - 1/4)),
```

whose coefficient **blows up as `a -> 1/2+`**, while `d/da Theta_a` stays bounded by the estimate
above.  So the archimedean and prime sides must have matching singular behaviour in `a` at the
threshold -- which is exactly the merging of the pole with the divergence of `sum Lambda(n)/n`
recorded in §78.  The identity confirms the weld; it does not pry it open.

> **[NEGATIVE RESULT]**  The `a`-derivative identity is a transport law, not a constraint.  It moves
> information along the family and cannot create it.

### Closing the audit

With §79 the construction's degrees of freedom are exhausted:

```text
§31  carrier corner        §39  carrier order         §58  positivity form
§70  coordinate choice     §77  prime input           §78  mass parameter
§79  the a-derivative
```

Seven no-gos, each with an exact mechanism, and each one a reason the reduction is faithful rather
than a defect in it.  The reduction stands; the analytic input does not follow from anything inside
it.

### Honest status, unchanged

```text
[LEAN-PROVED]  ‖trace‖ <= C exp(lam|x|) on one vertical line  ->  |delta_rho| <= lam for all rho,
               for the Poisson carrier, the mass-shifted carrier (1/2 <= a), and every
               admissible family; lam = 0 gives RH, and conversely
[OPEN]         any unconditional bound with lam < 1/2
```

RH is not proved.

### Next

The identity of this section is the first object in the whole development that couples two
parameters, and its transport property is exactly the reason it cannot help by itself.  What would
help is a *second*, independent relation in `a` -- one not derivable from the definition of
`beta_a` -- since two transport laws with different characteristics can pin a solution that one
cannot.  The natural candidate is the explicit formula's own `a`-dependence, which enters through the
transform `h^_t` rather than through the spectral points; computing `d/da h^_t(x)` and comparing it
with the identity above is the next concrete step, and it is the first place where the two sides of
the explicit formula are differentiated against each other rather than merely equated.

---

## §80 The transform's `a`-derivative: clean, and not independent

§79 asked for a second relation in `a`, coming from the transform rather than the spectral points.
Computed.

### The derivative

With `R = sqrt(t^2 + x^2)` and `h^_t(x) = 2 a t K_1(a R) / R`, using `K_1'(z) = -K_0(z) - K_1(z)/z`:

```text
d/da h^_t(x)  =  2t K_1(aR)/R  +  2at K_1'(aR)
              =  2t K_1(aR)/R  -  2at K_0(aR)  -  2t K_1(aR)/R
              =  -2 a t K_0(a sqrt(t^2 + x^2)).
```

> **[IDENTITY]**  `d/da h^_t(x) = -2 a t K_0(a sqrt(t^2 + x^2))`.

The `K_1` terms cancel exactly and the order drops by one.  Differentiating the explicit formula in
`a` therefore gives

```text
integral_t^infinity Theta_a(s) ds
  =  -(d/da A_a + d/da pole_a)/(t a)  -  (2/pi) sum_n Lambda(n) n^(-1/2) K_0(a sqrt(t^2 + log^2 n)).
```

### Why it is still not independent

`d/da h^_t(x)` is the Fourier transform of `d/da h_t(r)`, and

```text
d/da exp(-t sqrt(r^2 + a^2))  =  -(t a / sqrt(r^2 + a^2)) exp(-t sqrt(r^2 + a^2)),
```

which is again a function of `sqrt(r^2 + a^2)` alone -- analytic in the same strip `|Im r| < a`, with
transform decaying at the same rate `exp(-a|x|)`.  So the "second relation" is the **explicit formula
for another admissible carrier**, not a new constraint.

> **[NEGATIVE RESULT]**  The transform's `a`-derivative reproduces the explicit formula for the
> carrier `(t a / beta) exp(-t beta)`.  By §70 that carrier's criterion is equivalent to the
> original's, so the pair of relations is one relation.

### What the computation does reveal

Iterating, `d^k/da^k h_t` runs through the whole Bessel tower `K_1, K_0, K_1, ...` with polynomial
coefficients, and every member is an admissible carrier.  So the reduction sits inside an infinite
tower of criteria, all equivalent:

```text
h_t = exp(-t beta),  d/da h_t,  d^2/da^2 h_t, ...      ->  K_1, K_0, K_1, ...
```

That is the sharpest form of §70's faithfulness on the analytic side: not only is no *coordinate*
softer, no *derivative* of the carrier in its own parameter is either.  A tower of equivalent
criteria is what a faithful reduction looks like from the inside.

### Honest status, unchanged

```text
[LEAN-PROVED]  ‖trace‖ <= C exp(lam|x|) on one vertical line  ->  |delta_rho| <= lam,
               for every admissible family; lam = 0 is RH, and conversely
[OPEN]         any unconditional bound with lam < 1/2
```

RH is not proved.  Eight levers have now been audited (§§31, 39, 58, 70, 77, 78, 79, 80), each with
an exact mechanism, and none of them supplies the analytic input.

### Next

Every deformation *internal* to the construction is exhausted.  The remaining moves are external, and
the honest list is short:

1. an unconditional bound on the `K_1`-weighted von Mangoldt sum along a vertical line, obtained by
   methods outside this development (large sieve, zero-density, Guth--Maynard-type large-values
   input) -- this is where the reduction hands off to analytic number theory proper;
2. a positivity or self-adjointness input for the trace that is not a rearrangement of the explicit
   formula -- the Hilbert--Pólya direction, for which this development now supplies the exact target:
   an operator whose spectrum is the Poisson points `alpha^`, since reality of that spectrum is
   `[LEAN-PROVED]`-equivalent to RH.

---

## §81 What the reduction hands to Hilbert--Pólya

§80's second exit was "a positivity or self-adjointness input".  The development sharpens what such
an input would have to be, and the sharpening is worth stating on its own.

### The operator-theoretic reading

Suppose a candidate operator `T` has spectrum (with multiplicity) the Poisson points
`alpha^_rho = |gamma| - i sign(gamma) delta`.  Then `Theta(t) = Tr exp(-t T)` and the corpus theorem
reads:

> **`Tr exp(-t T)` is bounded on one vertical line `Re t = sigma > 0`  <->  `T` has real spectrum.**

The forward direction is the trivial one for a self-adjoint `T` with positive spectrum:
`|Tr exp(-t T)| <= Tr exp(-sigma T)`.  The converse is §§59--70.

### The point for the programme

Hilbert--Pólya asks for an operator that is **self-adjoint**.  The reduction says that is more than
needed:

> To conclude RH it suffices to bound `‖Tr exp(-t T)‖` on **one** vertical line.  Self-adjointness is
> not required, only that one bound.

And by §75 the requirement is graded: a bound `C exp(lam |Im t|)` with `lam < 1/2` gives the
zero-free region `|delta| <= lam` -- so a candidate operator that is *nearly* self-adjoint, in the
sense of a quantitative heat-trace bound, already yields a quantitative result.

### The admissibility conditions, read as facts about zeta

The six structure fields are, in this reading, exactly the classical facts a candidate's spectrum
must reproduce:

```text
heights bounded below and away from zero   the lowest zero is at height ~14.13
|displacement| <= 1/2                      the critical strip
summable weight                            the canonical product (sum 1/|rho|^2 < infinity)
finite shells                              the Riemann--von Mangoldt counting function
conjugation equivariance                   the functional equation
displacement zero <-> critical line        the definition
```

None of these is a hypothesis about RH; all six are theorems, and all six are `[LEAN-PROVED]` for the
Poisson and mass-shifted coordinates.  A candidate operator has to reproduce them, and then a single
heat-trace bound finishes the job.

### Honest status

```text
[LEAN-PROVED]  the criterion, all-or-nothing and graded, for every admissible family
[OPEN]         the analytic input, at every lam in [0, 1/2)
```

RH is not proved.  What §81 adds is not a proof but a specification: the exact, minimal property a
Hilbert--Pólya candidate must have, weaker than self-adjointness and quantitative rather than
all-or-nothing.

### Next

Two concrete continuations, both outside the reduction:

1. **Test the specification against an existing candidate.**  The Berry--Keating operator `xp` and
   its regularisations have spectra conjecturally matching the zeros; the reduction says the thing to
   check is not self-adjointness of a candidate but the vertical-line heat-trace bound, which is a
   statement about its resolvent growth.
2. **Hand off the prime-side bound.**  The `K_1`-weighted von Mangoldt sum on a vertical line is a
   Dirichlet-polynomial large-values question in disguise (§26); the exchange rate is now explicit,
   and any unconditional exponent below `1/2` transfers immediately through `[LEAN-PROVED]`
   machinery to a zero-free region.

---

## §82 Corpus cross-check: what is new here and what parallels existing work

Running `scripts/formal_tools.py research` against the finished statements — the discipline this
project mandates before claiming anything — turns up two pre-existing criteria of the same *kind*.
Recording the comparison honestly.

### What was already there

```text
RHTower.all_xiZeros_re_le_iff_negativeChannelSpectrum
  (∀ rho, xi rho = 0 → Re rho <= 1/2 + alpha)  ↔  two explicit channel-energy conditions
  on sequences (a, b) supplied by a `XiRectangularNegativeChannelSplit`

RHTower.xi_central_spectrum_real_of_traceHankel_nonnegative_on_principalIdeal
  Hankel positivity on a principal polynomial ideal, in the reciprocal-square coordinate,
  excludes every non-real Xi atom
```

The first is a **graded zero-free-half-plane criterion** — the same target as §75.  The second is a
**moment-positivity spectrum-reality criterion** — the same shape as §57.  Both predate this
session.

> **[NOT NEW]**  "A graded zero-free-half-plane criterion" and "a moment-positivity reality
> criterion" are not new to this corpus.  Claiming either as novel would have been wrong.

### What this session's chain adds

Three things, stated at their real size:

1. **A single scalar hypothesis.**  The negative-channel criterion is an equivalence conditional on
   auxiliary data (a split into sequences `a, b` with their own admissibility).  The Poisson
   criterion's hypothesis is one inequality about one explicit function:
   `‖Theta(sigma + i x)‖ <= C exp(lam|x|)`.  No auxiliary object is chosen.
2. **A prime-accessible carrier with a proved transfer.**  §69 gives an instance whose explicit
   formula converges, with the passage from its trace bound to `RiemannHypothesis` machine-checked.
3. **The coordinate analysis.**  The seven no-gos (§§31, 39, 58, 70, 77–80) say *why* this
   coordinate and not another: order one rather than two for Phragmén--Lindelöf, equal-height shells
   for the rigidity step, and faithfulness under every deformation tried.

### What the coexistence means

Three independent criteria — channel energies, Hankel positivity, vertical-line growth — all
equivalent to the same open statements.  That is the same faithfulness pattern §70 proved inside the
Poisson family, now visible across unrelated developments in this corpus: the reductions multiply,
the difficulty does not move.

The useful reading is not discouraging: each reduction exposes a *different* analytic surface, and
the surfaces are not equally attacked by existing technique.  The vertical-line surface is the one
that touches Dirichlet-polynomial large values directly (§26), which is where unconditional progress
in the literature actually happens.

### Honest status

```text
[LEAN-PROVED]  the vertical-line criterion, all-or-nothing and graded, for every admissible
               family, with a prime-accessible instance
[NOT NEW]      the existence of graded zero-free-region criteria in this corpus
[OPEN]         every one of them, at every lam in [0, 1/2)
```

RH is not proved.

### Next

Compare the three surfaces quantitatively rather than structurally: for the same target
`|delta| <= lam`, what does each criterion require of the primes?  The channel criterion asks for
energy bounds on a chosen split; the Hankel criterion asks for positivity of an infinite family of
minors; the vertical-line criterion asks for one exponential bound on a `K_1`-weighted von Mangoldt
sum.  Writing the three side by side in the same variables is a concrete next step and would say
which surface is closest to what unconditional technique currently delivers.

---

## §83 The three surfaces, in the same variables

§82 asked what each criterion requires of the primes for the same target `|delta| <= lam`.  Written
out, the answer is short and it is a closure.

### Surface 1 — vertical-line growth (this development)

`‖Theta(sigma + i x)‖ <= C exp(lam |x|)`.  Through the explicit formula (§§32--33) the content is
cancellation in a `K_1`-weighted von Mangoldt sum with a light cone at `log n ~ |x|`; setting
`X = exp|x|`, the trivial size is `2 sqrt X` and the requirement is `O(X^lam)`.  In the standard
normalisation that is

```text
psi(x) - x  <<  x^(1/2 + lam + epsilon).
```

### Surface 2 — Hankel positivity (`xi_central_spectrum_real_of_traceHankel_...`)

An infinite family of polynomial inequalities in the trace moments, each moment a prime sum.  Its
`lam`-graded form is the same statement about the error term, expressed as positivity rather than as
a bound.

### Surface 3 — channel energies (`all_xiZeros_re_le_iff_negativeChannelSpectrum`)

Energy bounds on a chosen split `(a, b)`; the criterion is an equivalence with
`∀ rho, Re rho <= 1/2 + alpha`, hence again the same error-term exponent with `alpha = lam`.

### The comparison

```text
Surface 1   one exponential bound on one explicit sum      <->  psi(x) - x << x^(1/2+lam+eps)
Surface 2   an infinite family of positivity conditions    <->  the same
Surface 3   energy bounds on auxiliary sequences           <->  the same
```

> **[CLOSURE]**  All three surfaces are the classical error-term exponent in different coordinates.
> Surface 1 is the one whose hypothesis is a single scalar inequality, but its analytic content is
> exactly `psi(x) - x << x^(1/2+lam+eps)` — the standard formulation.

So the honest summary of this line of work is: it produces a **new, faithful, machine-checked route**
from the classical error-term exponent to the zeros, graded at every `lam`, on a carrier whose
explicit formula converges — and it does not produce a new way to bound the error term.

### Why that is still worth having

The classical equivalence `psi(x) - x << x^(theta+eps)  <->  no zeros with Re rho > theta` is
textbook, but its proof of the hard direction runs through contour shifts and zero-density
bookkeeping that is not formalised anywhere in this corpus.  What §§59--75 provide is that direction,
unconditionally and in Lean, through an argument that uses no contour shifting at all: an order-one
envelope, one Phragmén--Lindelöf call, shell homogeneity, and a dominance lemma about real
exponentials.

That is a genuine formalisation contribution even though it is not a new analytic input, and it is
the first time in this corpus that "an explicit growth bound implies a zero-free region" exists as a
theorem rather than as a citation.

### Honest status

```text
[LEAN-PROVED]  an explicit growth exponent for the trace on one vertical line
               implies the zero-free region |delta| <= lam, for every admissible family;
               lam = 0 is RH, and conversely
[EQUIVALENT]   to the classical error-term exponent, hence not a new analytic input
[OPEN]         the exponent itself, at every lam in [0, 1/2)
```

RH is not proved, and this development does not bring it closer; it makes the last step exactly
identifiable and everything after it checkable.

### Next

The remaining work that this development can carry is formalisation, not discovery: the corpus now
has the hard direction of the error-term/zero-free-region equivalence, and the natural completion is
the easy direction in the same coordinates (zero-free region implies the growth bound), which is
`norm_traceC_le_of_im_eq_zero` at `lam = 0` and its graded analogue.  With both, the corpus would
contain the full classical equivalence, proved rather than cited, in a form that applies to any
admissible spectral family.

---

## §84 The graded equivalence, both directions

`[LEAN-PROVED]` (added to `XiSpectralFamilyGradedOnLine.lean`; axioms
`propext, Classical.choice, Quot.sound`):

```text
SpectralFamily.norm_traceC_le_of_abs_im_le
  |Im (F.pt q)| <= lam for all q  ->  ‖trace tau‖ <= traceReal (Re tau) * exp (lam |Im tau|)
SpectralFamily.abs_im_le_iff_exists_line_growth
  (∀ q, |Im (F.pt q)| <= lam)  <->  ∃ sigma > 0, ∃ C, ∀ x,
      ‖trace (sigma + i x)‖ <= C exp (lam |x|)
```

The easy direction is one line of termwise arithmetic: `|term| = exp(-sigma Re + x Im)` and
`x Im <= |x| lam`.  With it the corpus now contains, for every admissible spectral family and every
`lam >= 0`, the **full** equivalence

> displacements bounded by `lam`  `<->`  trace growth exponent at most `lam` on one vertical line,

whose `lam = 0` case is `RH <-> boundedness` and whose analytic content (§83) is the classical
error-term exponent `psi(x) - x << x^(1/2 + lam + eps)`.

### What the corpus now holds on this line

```text
abs_im_le_iff_exists_line_growth        the graded equivalence, any admissible family     §84
im_eq_zero_iff_exists_line_bound        its lam = 0 case                                  §70
riemannHypothesis_iff_exists_xiPoissonTrace_line_bound   the same, named for RH           §59
riemannHypothesis_of_xiMassTrace_line_bound              on the prime-accessible carrier  §69
```

All unconditional, all machine-checked, all with axioms exactly `propext, Classical.choice,
Quot.sound`.

### Honest status, unchanged

```text
[LEAN-PROVED]  the equivalence, at every lam, for every admissible family
[EQUIVALENT]   to the classical error-term exponent (§83) -- not a new analytic input
[OPEN]         the exponent itself, at every lam in [0, 1/2)
```

RH is not proved.

### Note on the shared tree

The formal lint gate currently reports one unreachable module,
`GaloisForLFunctions.HTGeometry.StanleyReisnerEmptyTriangleRank`, from concurrent work by another
agent; it is not part of this development.  Every module of this line builds, and each theorem cited
above passes `#print axioms` with the three standard axioms only.

### Next

With both directions in place the development is closed as a reduction.  The remaining research
question is unchanged and lies outside it:

> an unconditional bound `psi(x) - x << x^(1/2 + lam + eps)` with `lam < 1/2`,

equivalently an unconditional exponent for the `K_1`-weighted von Mangoldt sum on a vertical line.
Everything downstream of such a bound — the zero-free region, and at `lam = 0` the Riemann
Hypothesis — is now a theorem of this corpus rather than a citation.

---

## §85 A correction about large values, and a weaker sufficient hypothesis

### The correction

§§82--83 said the vertical-line surface "touches Dirichlet-polynomial large values directly, which
is where unconditional progress happens".  That is misleading and should be withdrawn.

Large-values technique -- the large sieve, zero-density estimates, Guth--Maynard -- bounds the
**number** `N(sigma, T)` of zeros with `Re rho >= sigma`.  It never produces zero.  But Surface 1 at
any `lam < 1/2` is a **zero-free half-plane** `Re rho <= 1/2 + lam`, which no density bound can
supply, however strong.

> **[CORRECTION]**  The vertical-line criterion does not hand off to zero-density technique.  Density
> bounds and zero-free half-planes are different species; the criterion needs the latter.

Nor is a mean-square version any softer: an off-line zero contributes `exp(2 J x)` to `|Theta|^2`, so
the mean square over `[-T, T]` grows at rate `2V` as well -- the same threshold.

### A weaker sufficient hypothesis

The hypothesis can, however, be weakened in a different direction, and this costs nothing:

`[LEAN-PROVED]` (added to `XiSpectralFamilyGradedOnLine.lean`; axioms
`propext, Classical.choice, Quot.sound`):

```text
SpectralFamily.im_eq_zero_of_subexponential
  (∀ eps > 0, ∃ sigma > 0, ∃ C, ∀ x, ‖trace(sigma + i x)‖ <= C exp(eps |x|))
  ->  every displacement vanishes
```

The line is allowed to depend on `eps`.  In particular a **polynomial** bound
`‖Theta(sigma + i x)‖ << (1 + |x|)^A` suffices, since a polynomial is `O(exp(eps|x|))` for every
`eps > 0`.

So the criterion's hypothesis is not "bounded" but "subexponential" -- visibly weaker, and obtained
from the graded chain by taking `lam = eps` and letting `eps -> 0`, with no new analysis.  It is
still equivalent to RH (RH gives boundedness, which is subexponential), but a *candidate* proof only
has to reach subexponential growth, not a constant.

### Honest status

```text
[LEAN-PROVED]  subexponential growth on vertical lines  ->  RH; and the graded equivalence
               at every lam, for every admissible family
[CORRECTED]    the criterion does not reduce to a zero-density statement
[OPEN]         subexponential growth, equivalently psi(x) - x << x^(1/2 + eps) for every eps
```

RH is not proved.

### Next

The weakened hypothesis changes what a partial result would have to look like.  Under the graded
equivalence, a bound with `lam` *decreasing to zero along a sequence of lines* -- `sigma_n` varying
with `eps_n` -- already gives RH; the lines need not be the same.  That is a genuinely different
target from a single uniform bound, and the natural place to look for it is the `sigma -> infinity`
regime, where the trace is dominated by the lowest shell and the prime side by the smallest primes
(§33's endpoint).  Whether the growth exponent on the line `Re t = sigma` can be shown to tend to
zero as `sigma -> infinity` is a well-posed question that the ungraded criterion could not even
state.

---

## §86 The `sigma`-freedom is illusory

§85 ended by asking whether the growth exponent could be made to tend to zero along a sequence of
*different* vertical lines, since the subexponential criterion allows the line to move with `eps`.
It cannot, and the reason was already in §29.

### The exponent does not depend on the line

Let `lambda(sigma) := limsup_{|x| -> infinity} log ‖Theta(sigma + i x)‖ / |x|`.  Each term
contributes `exp(-sigma R + x J)`, so

```text
log ‖Theta(sigma + i x)‖ / x   ~   sup_rho ( J_rho - sigma R_rho / x ).
```

For any fixed `rho` the correction `sigma R_rho / x` vanishes as `x -> infinity`, so for every
`eps > 0` a zero with `J_rho > V - eps` forces `lambda(sigma) >= V - eps`; and the unconditional
envelope gives `lambda(sigma) <= V`.  Hence

> **`lambda(sigma) = V` for every `sigma > 0`.**

The weight `exp(-sigma R)` is a *constant per term*: it cannot compete with the growth in `x`, no
matter how large `sigma` is.  Moving the line changes the constant, never the exponent.

> **[NEGATIVE RESULT]**  The subexponential criterion is formally weaker than the bounded one but has
> the same content: since `lambda(sigma)` is independent of `sigma`, the freedom to choose a
> different line for each `eps` buys nothing.

### What this closes

Every direction named in §§77--85 has now been audited:

```text
§77  the endpoint contribution              classical PNT error leaves the exponent at 1/2
§78  the mass parameter                     no value of a moves the exponent
§79  the a-derivative identity              a transport law, not a constraint
§80  the transform's a-derivative           another admissible carrier, not a new relation
§82  corpus cross-check                     graded criteria already existed in other coordinates
§83  the three surfaces                     all equal the classical error-term exponent
§85  large values                           density bounds cannot give a zero-free half-plane
§86  the sigma-freedom                      the exponent is line-independent
```

Together with §§31, 39, 58, 70 that is eleven audited levers, each closed with an exact mechanism.

### What stands

```text
[LEAN-PROVED]  for every admissible spectral family and every lam >= 0,
                 |Im (pt q)| <= lam for all q  <->  ‖trace(sigma + i x)‖ << exp(lam|x|)
                 on some vertical line of the open right half-plane;
               subexponential growth therefore implies reality, and lam = 0 is RH;
               with instances at the Poisson coordinate and at the prime-accessible
               mass-shifted coordinate, and with the whole chain also available over the
               abstract interface
[EQUIVALENT]   to psi(x) - x << x^(1/2 + lam + eps) -- the classical error-term exponent
[OPEN]         that exponent, at every lam in [0, 1/2)
```

RH is not proved.  The development is complete as a reduction and closed against every internal
deformation; the remaining step is an analytic input that none of its own machinery can supply.

### Next

The honest next step is not another reformulation.  It is either

1. an analytic input from outside — a bound on `psi(x) - x` below `x^{1/2 + 1/2}`, i.e. a zero-free
   half-plane, which is open and not approached by current technique; or
2. a Hilbert--Pólya construction meeting the specification of §81 — an operator reproducing the six
   admissibility facts, for which only a subexponential heat-trace bound on one vertical line is then
   needed, not self-adjointness.

Of these, (2) is the one where this development contributes something a candidate-builder did not
have before: a weaker, quantitative, and machine-checked sufficient condition.

---

## §87 A second corpus cross-check, and two overlaps I should have found earlier

Searching for operator-theoretic material (§86's direction 2) surfaced two pre-existing results that
overlap this session's work more directly than §82's did.  Recording them.

### Overlap 1 — Hilbert--Pólya is already in the corpus

```text
RHTower.riemannHypothesis_of_kapustin_symmetric_pointSpectrum
  a Hilbert-symmetric operator whose point spectrum contains all Kapustin Xi-divisor
  eigenvalues implies RH
RHTower.kapustin_symmetricPointSpectrum_horizontalMultiplicity_eq_order
  and then the horizontal divisor mass at each zero is its analytic order
```

So "a symmetric operator with the right eigenvalues gives RH" was already a theorem here.  §81 is
therefore not the introduction of a Hilbert--Pólya statement to this corpus; what it adds is a
**weakening of the hypothesis**: not symmetry of the operator, but a subexponential bound on
`Tr exp(-tT)` along one vertical line -- plus the graded form, which symmetry cannot provide because
symmetry is all-or-nothing.

### Overlap 2 — a complete-positivity equivalence already exists

```text
RHTower.primeArchHausdorffMomentDifferencesNonnegative_iff_riemannHypothesis
  **Complete Hausdorff value law for RH**: all complementary Hausdorff finite differences of the
  normalized prime--Gamma source are nonnegative  <->  RH
```

That is the Hausdorff ([0,1] moment problem) counterpart of §44's Bernstein ((0, infinity) Laplace
transform) criterion, and it is an equivalence, already formalized, on the **prime** source rather
than the zero trace.

> **[NOT NEW]**  "RH is equivalent to complete positivity of a moment family" was already in this
> corpus, in the Hausdorff coordinate on the prime side.  §44's complete-monotonicity criterion is
> its Bernstein counterpart on the zero side, related by the standard Hausdorff/Bernstein
> correspondence.  I should have found this before writing §44, and the search that would have found
> it -- on "complete monotonicity" or "Bernstein" rather than on "moment" -- is the one I did not run.

### What survives as this session's own contribution

Stated at its real size, after both cross-checks:

1. **The vertical-line criterion in the Poisson coordinate**, with its graded form at every `lam`,
   both directions, for an abstract admissible family — and the coordinate analysis (eleven audited
   levers) explaining why that coordinate and not the Gaussian or the squared one.
2. **A prime-accessible instance** whose explicit formula converges, with the transfer to
   `RiemannHypothesis` machine-checked.
3. **A weakening of the Hilbert--Pólya hypothesis**: subexponential heat-trace growth on one line in
   place of symmetry, graded so that partial bounds give partial results.
4. **The negative results**: order-two failure of the Gaussian carrier, non-accessibility of the pure
   Poisson carrier, non-peelability of moment positivity, faithfulness of the interface, and the
   line-independence of the growth exponent.

Items 1--3 are additions to what was already here; item 4 is what makes them non-arbitrary.

### Honest status

```text
[LEAN-PROVED]  the graded vertical-line equivalence, for every admissible family
[NOT NEW]      RH-from-a-symmetric-operator; RH-from-complete-moment-positivity
[OPEN]         the analytic exponent, at every lam in [0, 1/2)
```

RH is not proved.

### Next

Given Overlap 1, the sharpest remaining question this development can pose is a comparison rather
than a construction:

> the Kapustin criterion needs a **symmetric** operator with a prescribed point spectrum; the
> vertical-line criterion needs **no symmetry**, only `Tr exp(-tT)` subexponential on one line.  For
> a concrete candidate operator, which hypothesis is easier to verify?

That is a question about candidates, not about the reduction, and it is where the two corpus results
should be read together.

---

## §88 Off the zeta index: the abstract spectral family

§87 concluded that the live exit is a candidate operator, and that what such a candidate needs is a
statement about *its* spectrum, not about the Xi divisor.  The interface was still indexed by
`XiZeroCopy`.  It no longer has to be.

`[LEAN-PROVED]` `formal/GaloisForLFunctions/HTGeometry/AbstractSpectralFamily.lean`
(axioms `propext, Classical.choice, Quot.sound`):

```text
structure AbstractSpectralFamily (ι : Type*)
  pt : ι → C,  inv : ι ≃ ι,  base, base_pos, base_le, abs_im_lt,
  summable_weight, shell_finite, conj_stable
AbstractSpectralFamily.norm_term_le / norm_traceC_le          the order-one envelope
AbstractSpectralFamily.norm_traceC_le_of_abs_im_le            the easy direction, graded
AbstractSpectralFamily.traceReal_antitone
AbstractSpectralFamily.exists_min_re_of_nonempty              least heights, from shell_finite
AbstractSpectralFamily.analyticOnNhd_traceC                   analytic on Re t > 0
```

The index is now an arbitrary type carrying an involution.  Nothing about zeta appears; the
conjugation symmetry that was the functional equation is now a structure field, and everything proved
here is a statement about a countable set of points in a horizontal strip of the right half-plane.

### Why this is the right final shape

A Hilbert--Pólya candidate comes with an operator `T` and a spectrum, not with the Xi divisor.  For
such a candidate the question posed by §81 --

> is `Tr exp(-tT)` subexponential on one vertical line?

-- is now askable in the corpus's own language, because the criterion's hypotheses are conditions on
an arbitrary spectrum:

```text
heights bounded below by a positive constant        the operator is bounded below
displacements bounded by 1/2                        the spectrum lies in a strip
summable weight                                     exp(-sigma T) is trace class
finite shells                                       discrete spectrum with finite multiplicity
an involution conjugating the points                the spectrum is conjugation-symmetric
```

Every one is a standard operator-theoretic condition.  A candidate satisfying them plus the
subexponential trace bound has real spectrum -- and if its spectrum is the Xi divisor's Poisson
image, that is RH.

### Ledger

```text
[LEAN-PROVED]  the abstract interface and its analytic block                       §88
[LEAN-PROVED]  the full chain (envelope, Phragmen-Lindelof, shells, assembly,
               wrapper, graded form) over the XiZeroCopy-indexed interface          §61-§85
[TO TRANSFER]  the remaining blocks of the chain to the abstract index
[OPEN]         the analytic exponent
```

RH is not proved.

### Next

Carry the remaining blocks -- Phragmén--Lindelöf, the shell structure, the assembly, the lift and the
wrapper -- from the `XiZeroCopy`-indexed interface to `AbstractSpectralFamily`.  Each is a
substitution of `ι` for `XiZeroCopy` and `F.inv` for `xiZeroCopyLineConjEquiv`; the proofs use no
other property of the index, which is exactly what §§61--85 established by writing them against the
interface in the first place.

---

## §89 The decay block, off the zeta index

`[LEAN-PROVED]` `formal/GaloisForLFunctions/HTGeometry/AbstractSpectralDecay.lean`
(lint clean; axioms `propext, Classical.choice, Quot.sound`):

```text
AbstractSpectralFamily.bottomIndex / bottomHeight / bottomHeight_le / bottomHeight_pos
AbstractSpectralFamily.exp_bottomHeight_mul_traceReal_le    the imaginary-ray bound
AbstractSpectralFamily.twist / norm_exp_twist / differentiableOn_twist
AbstractSpectralFamily.norm_twist_le                        the order-one envelope for the twist
AbstractSpectralFamily.norm_twist_imaginary_ray
```

All of it over an arbitrary index type with an involution.  The only hypothesis added is
`[Nonempty ι]`, needed to name a least-height index; when `ι` is empty the trace is `0` and the
conclusion is vacuous.

At this point the entire analytic apparatus of the criterion -- envelope, summability, analyticity,
least heights, the twist and both boundary bounds -- exists in a form that mentions no `L`-function
at all.  What it now says is:

> Let `S` be a countable multiset of complex numbers with real parts bounded below by a positive
> constant, imaginary parts bounded by `1/2`, `sum exp(-sigma Re s)` finite for every `sigma > 0`,
> finitely many points below any height, and closed under conjugation.  Then
> `Theta(t) = sum_{s in S} exp(-t s)` is analytic on `Re t > 0`, has exponential type at most `1/2`
> on vertical lines, and its least-height twist has bounded boundary values on the two lower
> quadrants.

### Ledger

```text
[LEAN-PROVED]  abstract interface: envelope, summability, analyticity, least heights   §88
[LEAN-PROVED]  abstract decay block: twist, boundary bounds                            §89
[TO TRANSFER]  Phragmen-Lindelof assembly, shells, wrapper, graded form
[LEAN-PROVED]  all of the above already, over the XiZeroCopy-indexed interface          §61-§85
[OPEN]         the analytic exponent
```

RH is not proved.

### Next

The quadrant application itself: `PhragmenLindelof.quadrant_III` and `quadrant_IV` against
`differentiableOn_twist`, `norm_twist_le`, `norm_twist_imaginary_ray` and the contraposed hypothesis
-- the same four inputs as §63, now all available over the abstract index.  After that the shell
block and the assembly transfer the same way, and the criterion becomes a theorem about spectra
rather than about the Riemann zeta function, which is the form a Hilbert--Pólya candidate can
actually be tested against.

## §90 — The criterion leaves zeta: index-free spectral rigidity, and what the coordinate really is

### 90.1 The transfer is complete

Everything from §63 onwards now lives over an arbitrary index type. Four new modules, all built,
all with axioms exactly `propext, Classical.choice, Quot.sound`:

- `HTGeometry/AbstractSpectralShell.lean` — vertical-line algebra (`re_vertLine`, `im_vertLine`,
  `vertLine_factor`, `norm_exp_neg_ofReal_mul_I_mul'`), `bottomShell`, `aboveBottom`,
  `exists_secondHeight`, `bottomShellSum_eq` (shell homogeneity), `traceC_vertical_split`,
  `exp_bottomHeight_mul_norm_aboveBottomSum_le` (the weighted tail bound).
- `HTGeometry/AbstractSpectralDecay.lean` — extended with `norm_twist_real_ray`,
  `norm_twist_le_of_line_bound` (the quadrant Phragmén–Lindelöf application) and
  `norm_traceC_le_of_line_bound` (half-plane decay).
- `HTGeometry/AbstractSpectralRigidity.lean` — `bottomShell_regroup`, `im_nonpos_of_line_bound`,
  `im_eq_zero_of_line_bound`, `below`/`finite_below`/`lift`, and the two capstones

  ```lean
  theorem im_eq_zero_of_line_bound_all {σ C : ℝ} (hσ : 0 < σ)
      (hline : ∀ x : ℝ, ‖F.traceC ((σ : ℂ) + (x : ℂ) * I)‖ ≤ C) : ∀ i : ι, (F.pt i).im = 0
  theorem im_eq_zero_iff_exists_line_bound :
      (∀ i : ι, (F.pt i).im = 0) ↔
        ∃ σ C : ℝ, 0 < σ ∧ ∀ x : ℝ, ‖F.traceC ((σ : ℂ) + (x : ℂ) * I)‖ ≤ C
  ```
- `HTGeometry/AbstractSpectralGraded.lean` — `gtwist`, graded Phragmén–Lindelöf, graded half-plane
  decay, graded assembly, and

  ```lean
  theorem abs_im_le_iff_exists_line_growth {lam : ℝ} (hlam : 0 ≤ lam) :
      (∀ i : ι, |(F.pt i).im| ≤ lam) ↔
        ∃ σ C : ℝ, 0 < σ ∧ ∀ x : ℝ,
          ‖F.traceC ((σ : ℂ) + (x : ℂ) * I)‖ ≤ C * Real.exp (lam * |x|)
  ```

[LEAN-PROVED] **Exponential type = displacement supremum.** For any admissible family — points in
the right half-plane, heights bounded below by a positive constant, `|Im| < 1/2`, summable
`exp (-σ Re)`, finite shells, a conjugating involution — the exponential type of `Tr exp (-tA)`
along *any* vertical line of the open right half-plane equals `sup_i |Im α_i|`. Reality of the
spectrum is the case `lam = 0`.

The hypothesis is one scalar bound on one line; there is no self-adjointness, no almost
periodicity, no frequency separation, no Kronecker. This is the form a Hilbert–Pólya candidate can
be tested against: exhibit an operator with this spectrum whose semigroup trace is bounded on one
line, and RH follows.

### 90.2 Faithfulness: the abstraction returns zeta

`RHTower/XiAbstractInstance.lean` (built, same three axioms) closes the loop rather than leaving a
parallel copy: `SpectralFamily.toAbstract`, `xiPoissonAbstract`, `xiPoissonAbstract_traceC` (`rfl`),
and

```lean
theorem riemannHypothesis_of_abstract_line_bound {σ C : ℝ} (hσ : 0 < σ)
    (hline : ∀ x : ℝ, ‖xiPoissonAbstract.traceC ((σ : ℂ) + (x : ℂ) * I)‖ ≤ C) : RiemannHypothesis
theorem abs_re_sub_half_le_of_abstract_line_growth {σ C lam : ℝ} (hσ : 0 < σ) (hlam : 0 ≤ lam)
    (hline : ∀ x : ℝ,
      ‖xiPoissonAbstract.traceC ((σ : ℂ) + (x : ℂ) * I)‖ ≤ C * Real.exp (lam * |x|))
    (q : XiZeroCopy) : |(xiSpectralPoint q).im| ≤ lam
```

So the ζ criterion is a corollary of the index-free theorem, and the graded corollary reads: a
growth exponent `lam` on one vertical line is a zero-free strip `|Re ρ - 1/2| ≤ lam`.

### 90.3 What the Poisson coordinate is, in arithmetic terms

Interrogating the open core rather than the machinery. Write `ρ = 1/2 + δ + iγ`. By construction
`α̂_ρ = -i(ρ - 1/2)·sign γ`, so for `γ > 0`, `exp(-τ α̂) = exp(iτ(ρ - 1/2))`. Put

  `Z = exp(iτ)`,  so for `τ = σ + it`:  `|Z| = e^{-t}`, `arg Z = σ`.

Then `exp(iτ(ρ-1/2)) = Z^{ρ-1/2}`, and using the conjugation symmetry of the zero set for the
`γ < 0` half,

  **`Θ(σ + it) = X^{-1/2} W(X) + conj( Y^{-1/2} W(Y) )`,  `W(Z) := Σ_{γ>0} Z^ρ`,**

with `X = e^{-t+iσ}`, `Y = e^{t+iσ}`: both on the ray `arg = σ`, with `|X||Y| = 1`. The series
`W` converges absolutely on that ray — `|Z^ρ| = |Z|^{Re ρ} e^{-σγ}` and `Σ_{γ>0} e^{-σγ} < ∞` —
because the *rotation angle* `σ` supplies the damping.

[OBSERVATION, exact] `W(Z) = Σ_{γ>0} Z^ρ` is exactly half of the oscillating term of the explicit
formula, evaluated off the positive real axis and with **no** `1/ρ` weight and **no** smoothing: the
rotation regularises it. The vertical-line criterion is therefore a *complexified Chebyshev bound*:
`|W(Z)| ≪ |Z|^{1/2}` on one ray `arg Z = σ ∈ (0,π)` implies RH, and the graded version says the
exponential type of `W` along the ray measures the zero-free strip width exactly.

[BRIDGE, not new] The object is a twisted Cramér function: under RH, `W(Z) = Z^{1/2} V(σ-coordinate)`
with `V(z) = Σ_{γ>0} e^{iγz}` (Cramér 1919, Guinand). What §90.1 adds is not the object but the
*dictionary*: type along the ray ↔ strip width, proved for an arbitrary admissible spectrum.

This also explains, structurally, both earlier no-gos. §31 (carrier corner): the Poisson kernel is
the Fourier transform of `e^{-τ|γ|}`, decaying only like `u^{-2}`, so the prime side diverges —
i.e. the rotation regularises the *zero* side but not the *prime* side. §§78–80 (mass shift) bought
prime-side convergence by moving the branch point to `±ia`, at the cost of a parameter that cannot
be sent to `0`.

### 90.4 Next generative move

The rotation angle `σ` is a parameter the mass `a` never was: it *can* be sent to `0`. §86 proved
the growth exponent is line-independent; in the `Z` coordinate that says the type of `W` along the
ray does not depend on `arg Z = σ`. So the type may be read at the boundary `σ → 0+`, where the
boundary distribution of `W` is arithmetic — Cramér's function continues past the real axis with
singularities exactly at `±k log p`.

Concrete next question: **is the `σ → 0+` boundary value of `W(Z)/Z^{1/2}` a tempered distribution
whose singular support is `{±k log p}`, and does its order at those points control the type?**
A positive answer converts the open core from "prove a sup bound on a ray" into a statement about
the *order of the prime-power singularities* of a single boundary distribution — the prime side,
reached without a mass parameter and without smoothing. That is the object to construct next.

Second move, to be drawn against it: collide the ray picture with two wild-analogy domains
(`scripts/rng pick`) before choosing the attack, so the boundary-value route is not adopted merely
because it is the one already in view.

### §90.5 — Entropy draw before choosing the attack

`scripts/rng pick` over the analogy deck returned **bell-ringing-changes** and **auction-theory**.
Forced collisions with `W(Z) = Σ_{γ>0} Z^ρ` on the ray:

**Auction theory.** The real-time trace `Θ_R(σ) = Σ e^{-σR}` is a cumulant generating function, so
`log Θ_R` is convex automatically: in mechanism-design terms the "allocation rule" (the Gibbs
measure on shells) is already monotone and *ironing is vacuous*. The envelope theorem then says the
whole real-direction data is the integral of the Gibbs mean height. Conclusion of the collision:
nothing is hidden in the real direction — the entire difficulty is that the complex trace need not
be the Laplace transform of a positive measure. That is the Bernstein/complete-monotonicity face
already in the corpus, so this collision **reduces to known** and is recorded as such rather than
pursued.

**Change ringing.** A method is a closed walk on the Cayley graph of `S_n` with adjacent
transpositions; a bell may move at most one place per change (a physical constraint, not a chosen
flow), and an extent is forced to close back to rounds. Two structural matches, both exact rather
than decorative: the "at most one place" constraint is `|Im α| < 1/2`, and closure to rounds is the
functional equation's involution `δ ↦ -δ` at a common height. The productive part is the third
match: **calls.** A plain course does not cover the extent; ringers insert bobs and singles at
chosen points to restructure the orbit. That is exactly the lift of §90.1 — a local discrete
intervention at a chosen height that makes a global covering argument (minimal counterexample over
all heights) go through.

The question this produces, which the boundary-value route does not: change ringing has *parity
obstructions* — not every method admits an extent, because a conserved parity blocks it. So:

[OPEN QUESTION, §90.5] Is there a **lift-invariant** of an admissible family? The lift alters only
finitely many points, so any quantity that is (i) insensitive to finitely many points and (ii)
computable from the trace is preserved along the whole minimal-counterexample tower. If some such
invariant is forced to differ between a real family and one with `δ ≠ 0`, the contradiction is
reached without any sup bound on the line — i.e. without the open core. Candidates to test first:
the mean argument variation of `Θ` along the line, and the shell-summed displacement
`Σ_{shell} Im α` (zero for a conjugation-stable shell, hence uninformative — so the invariant must
be of even degree in the displacements, e.g. `Σ_{shell} (Im α)²`).

The even-degree remark is what makes this non-vacuous: conjugation stability kills every odd
invariant, so any obstruction must be quadratic or higher in `δ`, which is exactly the regime the
moment route of §§54–58 failed to peel. The difference now is that the lift supplies a *tower* of
families along which such an invariant would have to be constant — a rigidity the moment route
never had.

## §91 — The defect: RH as one scalar equation at one point

### 91.1 The lift-invariant question of §90.5, answered

[RETRACTED, §90.5 first candidate] "The mean argument variation of `Θ` along the line" is not a
usable lift-invariant. The graded theorem already identifies the only line-computable invariant of
the family — the exponential type — and it equals `sup_i |Im α_i|`, which is *not* insensitive to
finitely many points: a single point with `J ≠ 0` contributes `e^{xJ}` by itself. So the type is
both the invariant and the open core; the parity analogy does not bypass it.

[KEPT, and it is the right shape] The other prediction of §90.5 does survive: conjugation stability
kills every odd functional of the displacements, so an obstruction must be *even*. There is one, it
is elementary, and it was sitting at real time all along.

### 91.2 The defect

At real `σ > 0` the trace is real by conjugation stability, and termwise

  `Re (traceC σ) = Σ_i e^{-σ R_i} cos(σ J_i)`,  `traceReal σ = Σ_i e^{-σ R_i}`.

Define the **defect**

  `D(σ) := traceReal σ - Re (traceC σ) = Σ_i e^{-σ R_i} (1 - cos(σ J_i)) = Σ_i e^{-σ R_i} 2 sin²(σ J_i/2) ≥ 0`.

[LEAN-PROVED] `HTGeometry/AbstractSpectralDefect.lean`, axioms `propext, Classical.choice,
Quot.sound`:

```lean
def defect (σ : ℝ) : ℝ := F.traceReal σ - (F.traceC (σ : ℂ)).re
theorem defect_eq_tsum {σ : ℝ} (hσ : 0 < σ) :
    F.defect σ = ∑' i, F.weight σ i * (1 - Real.cos (σ * (F.pt i).im))
theorem defect_nonneg {σ : ℝ} (hσ : 0 < σ) : 0 ≤ F.defect σ
theorem im_eq_zero_iff_defect_eq_zero {σ : ℝ} (hσ : 0 < σ) (hle : σ ≤ 4 * Real.pi) :
    (∀ i : ι, (F.pt i).im = 0) ↔ F.defect σ = 0
```

The mechanism: `|J| < 1/2` and `σ ≤ 4π` confine `σJ` to `(-2π, 2π)`, the interval on which
`cos = 1` forces the argument to vanish. Positivity of the weights then makes a vanishing sum a
vanishing of every term. The `4π` is exactly the reach of the displacement bound — the admissibility
axiom `|Im α| < 1/2` is what converts a periodic condition into an equality.

And on the Xi divisor (`RHTower/XiAbstractInstance.lean`, same three axioms):

```lean
theorem riemannHypothesis_iff_xiPoissonDefect_eq_zero {σ : ℝ} (hσ : 0 < σ) (hle : σ ≤ 4 * Real.pi) :
    RiemannHypothesis ↔ xiPoissonTraceReal σ = (xiPoissonTraceC (σ : ℂ)).re
```

**RH is equivalent to one equation between two real numbers, at one point of the positive real
axis:** the Poisson trace of the Xi divisor attains its own majorant at `σ`. No line, no uniformity,
no limit. Choose `σ = 1`, or `σ = π`, or any point of `(0, 4π]`.

### 91.3 What this changes and what it does not

It does not prove RH. `Re (traceC σ)` and `traceReal σ` are both sums over the zeros, and the
inequality `D ≥ 0` is one-sided by construction; the content is the reverse inequality
`traceReal σ ≤ Re (traceC σ)`, which is RH.

What it changes is the *type* of the remaining obstruction, and this is a real shift:

- The vertical-line criterion needed an estimate uniform in a non-compact parameter. The defect needs
  a single number. An estimate can only be attacked by analytic technique; a number can be attacked
  by an identity.
- `D(σ) = Σ e^{-σR}(1 - cos σJ)` is even and quadratic to leading order in the displacements
  (`D(σ) ≈ (σ²/2) Σ e^{-σR} J²` as `σ → 0+`), which is exactly the degree the moment route of
  §§54–58 could not peel. Here it is not peeled but *summed*: the whole quadratic form is one
  convergent series with an explicit generating function in `σ`.
- Both terms are traces of the same family at the same time. `traceReal σ = Σ e^{-σ|γ|}` is not of
  Weil type (not analytic in `ρ`), but `Re traceC σ = Re Σ e^{-σ α̂}` is the real part of the
  quantity §90.3 identified as the twisted Cramér function on the unit circle `|Z| = 1`,
  `arg Z = σ`. So the equation reads: **`2 Re(e^{-iσ/2} Σ_{γ>0} e^{iσρ}) = Σ_ρ e^{-σ|γ|}`.**

### 91.4 Next

The equation of §91.3 pairs an arithmetically accessible left side against an inaccessible right
side. Two moves follow, in this order:

1. **Make the right side accessible too.** `traceReal σ = Σ_ρ e^{-σ|Im ρ|}` is the Poisson-kernel
   pairing whose prime side diverged in §31. But it is *not* needed in full: only the difference
   `D(σ)` is, and `D` is quadratic in the displacements. Question to settle next: does `D(σ)` admit
   a representation as a **single** Weil-type pairing — i.e. is there a test function `h_σ`, analytic
   in the strip, with `Σ_ρ h_σ(γ_ρ) = D(σ)`? If yes, `D ≥ 0` becomes an explicit-formula identity
   with an arithmetic right-hand side and RH becomes the vanishing of a specific prime-archimedean
   expression. The obstruction to expect is the same corner as §31; the new leverage is that `D`
   already contains the difference of the two carriers, so the corners may cancel.
2. **Differentiate.** `D(0+) = 0` and `D ≥ 0` for all `σ ∈ (0, 4π]`, so `D` has a minimum at the
   left endpoint. `D''(0+)` is `Σ e^{-σR} J²`-shaped. A lower bound on `D''(0+)` from below by a
   nonzero arithmetic quantity would contradict `D ≡ 0`; an upper bound going to zero would prove
   RH. This is where the `1/δ` law of the card's title should be tested against `D`.

The corpus asset to check before either move: `xiGuinandWeilExplicitFormula` and
`xiGuinandWeilExplicitFormula_single` (resolvent test algebra, `RHTower/XiGuinandWeilExplicitFormula.lean`)
— the explicit formula there is stated for regularized Cauchy kernels, and `e^{-τα}` is a contour
integral of those, so move 1 has a corpus route that does not require re-deriving Guinand–Weil.

## §92 — The defect is not a Weil pairing, and why that is the point

### 92.1 Move (1) of §91.4 fails, with an exact mechanism

[NO-GO, exact] `D(σ)` admits **no** representation as a Weil pairing `Σ_ρ h_σ(γ_ρ)` with `h_σ`
analytic in the strip. In terms of the actual zero data,

  `D(σ) = Σ_ρ e^{-σ|γ_ρ|} (1 - cos(σ δ_ρ))`,  `δ_ρ = Re ρ - 1/2`,  `γ_ρ = Im ρ`.

Both factors are real-analytic in `(ρ, ρ̄)` jointly and neither is holomorphic in `ρ`: `|γ_ρ|` is the
§31 corner, and `δ_ρ = (ρ + ρ̄)/2 - 1/2` is not a function of `ρ` alone. A Weil pairing evaluates one
holomorphic `h` at the single complex point `γ_ρ = γ - iδ`; it cannot factor into a modulus in `γ`
times a function of `δ`. So the corpus route through `xiGuinandWeilExplicitFormula` does not apply to
`D`, and the hoped-for cancellation of the two carriers' corners does not occur — they are corners in
different variables.

### 92.2 Why this is the correct obstruction rather than a dead end

The signed first moment of the displacement **vanishes identically**: the functional equation maps
`ρ ↦ 1 - ρ̄`, which fixes `γ` and sends `δ ↦ -δ`, so `Σ_{0<γ≤T} δ_ρ = 0` for every `T`. (This is why
Littlewood's lemma applied to `ζ` on the critical strip yields the unconditional
`∫_0^T log|ζ(1/2+it)| dt = O(log T)` rather than information about the zeros: the zero side is zero.)

Every *odd* functional of the displacements is therefore identically zero and carries no information
— exactly the prediction of §90.5, now with its mechanism named. The first functional that is not
forced to vanish is the **even** one, and `D` is the smallest such: quadratic, positive, and
convergent. So the failure of §92.1 is not an accident of the chosen representation; it says that
the object which detects RH is precisely the one no classical explicit formula evaluates, because
every classical formula is linear in a holomorphic test function and therefore odd-blind.

### 92.3 Positive salvage: the defect ladder

[LEAN-PROVED] `HTGeometry/AbstractSpectralDefect.lean`, axioms `propext, Classical.choice,
Quot.sound`:

```lean
theorem two_div_pi_sq_mul_sq_le_one_sub_cos {x : ℝ} (hx : |x| ≤ Real.pi) :
    2 / Real.pi ^ 2 * x ^ 2 ≤ 1 - Real.cos x
theorem sq_im_mul_weight_le_defect {σ : ℝ} (hσ : 0 < σ) (hσ' : σ ≤ 2 * Real.pi) (i : ι) :
    2 * σ ^ 2 / Real.pi ^ 2 * ((F.pt i).im ^ 2 * F.weight σ i) ≤ F.defect σ
theorem sq_im_le_of_defect_le {σ M : ℝ} (hσ : 0 < σ) (hσ' : σ ≤ 2 * Real.pi)
    (h : F.defect σ ≤ M) (i : ι) :
    (F.pt i).im ^ 2 ≤ Real.pi ^ 2 / (2 * σ ^ 2) * M * Real.exp (σ * (F.pt i).re)
```

and on the Xi divisor (`RHTower/XiAbstractInstance.lean`, same axioms), using
`(xiSpectralPoint q).im = 1/2 - Re ρ`:

```lean
theorem sq_im_xiSpectralPoint_le_of_defect_le {σ M : ℝ} (hσ : 0 < σ) (hσ' : σ ≤ 2 * Real.pi)
    (h : xiPoissonTraceReal σ - (xiPoissonTraceC (σ : ℂ)).re ≤ M) (q : XiZeroCopy) :
    (xiSpectralPoint q).im ^ 2 ≤
      Real.pi ^ 2 / (2 * σ ^ 2) * M * Real.exp (σ * (xiPoissonPoint q).re)
```

i.e. `|Re ρ - 1/2| ≤ (π/σ) sqrt(M/2) · exp(σ |Im ρ| / 2)`.

This changes the criterion from all-or-nothing to a ladder. RH no longer requires `D = 0` to be
proved in one step: **any** unconditional upper bound on the defect at **any** admissible time is a
theorem about zeros. The weight `e^{-σ|γ|}` makes `D(σ)` a probe localized at height scale `1/σ`, and
the loss `e^{σ|γ|/2}` in the conclusion says a bound `M` at time `σ` controls exactly the zeros with
`|γ| ≲ (2/σ) log(1/M)`. Bottom-shell first — the same locality the rigidity argument runs on.

### 92.4 Next

The target is now sharp and, for the first time in this line, *quantitative and partial-credit*:

> Produce an unconditional upper bound for `D(σ) = xiPoissonTraceReal σ - Re (xiPoissonTraceC σ)`
> at one `σ ∈ (0, 2π]`.

Both terms are explicit sums over the Xi divisor, so the bound must come from a formula for their
difference, not from estimating each. Two candidate sources, in order:

1. `Re (xiPoissonTraceC σ)` is `2 Re(e^{-iσ/2} Σ_{γ>0} e^{iσρ})` (§90.3), a twisted Cramér value on
   the unit circle, and Cramér's function is the one classical object in this circle of ideas whose
   *singularity structure* is known exactly. `xiPoissonTraceReal σ = Σ_ρ e^{-σ|γ_ρ|}` is its
   `δ`-blind companion. The difference is what must be estimated; the question is whether the two
   have a common continuation whose difference is boundary data.
2. §90.4's rotation-angle route, now with a target that no longer needs uniformity: only the value at
   one `σ`.

Before either, the even-blindness of §92.2 must be respected: any proposed source that is linear in
a holomorphic test function is odd-blind and will return `0 = 0`. The source has to be quadratic —
a Gram/Toeplitz object, not a trace. The corpus already carries such objects
(`XiWeilArithmeticGram`, `ConstrainedProlateWeilToeplitzSchur`); the next check is whether `D(σ)` is
a diagonal of one of them.

## §93 — Correction to §92.2, the energy, and where the wall sits numerically

### 93.1 Correction

[RETRACTED, §92.2 as stated] "Every functional linear in a holomorphic test function is odd-blind"
overstates the case and is wrong as a claim about detection. For `h` even, the functional-equation
quadruple `{ρ, ρ̄, 1-ρ, 1-ρ̄}` contributes `2[h(γ - iδ) + h(γ + iδ)]`, which is *even* in `δ` with
second-order term `-2 h''(γ) δ²`. So a Weil pairing does detect `δ`, at second order — that is
precisely Weil's positivity criterion, and nothing here supersedes it.

What survives, and is what §92.1 actually proves:

[CORRECTED STATEMENT] `D(σ)` is not `Σ_ρ h(γ_ρ)` for any analytic `h`, for a sharper reason than
non-holomorphy: **the summand of `D` vanishes identically when `δ = 0`.** If `Σ_ρ h(γ_ρ)` had that
property termwise then `h ≡ 0` on `ℝ`, hence `h ≡ 0` by analyticity, hence the pairing is trivial.
So `D` is a *pure* defect — a Weil pairing minus the same pairing evaluated at the critical-line
projection of the divisor — and the subtracted term is the one that is not arithmetically accessible.
Also unchanged and correct: `Σ_{0<γ≤T} δ_ρ = 0` exactly, by `ρ ↦ 1 - ρ̄`, so the signed first moment
is identically zero.

### 93.2 The energy

[LEAN-PROVED] `HTGeometry/AbstractSpectralDefect.lean` (axioms `propext, Classical.choice,
Quot.sound`), with `energy σ := ∑' i, weight σ i * (Im α_i)²`:

```lean
theorem defect_le_energy {σ : ℝ} (hσ : 0 < σ) : F.defect σ ≤ σ ^ 2 / 2 * F.energy σ
theorem energy_le_defect {σ : ℝ} (hσ : 0 < σ) (hσ' : σ ≤ 2 * Real.pi) :
    2 * σ ^ 2 / Real.pi ^ 2 * F.energy σ ≤ F.defect σ
theorem im_eq_zero_iff_energy_eq_zero {σ : ℝ} (hσ : 0 < σ) (hσ' : σ ≤ 2 * Real.pi) :
    (∀ i : ι, (F.pt i).im = 0) ↔ F.energy σ = 0
```

so `defect σ ≍ σ² · energy σ` on `(0, 2π]`, with explicit constants `2/π²` and `1/2`.  On the Xi
divisor (`RHTower/XiAbstractInstance.lean`, same axioms):

```lean
theorem xiPoissonAbstract_energy (σ : ℝ) :
    xiPoissonAbstract.energy σ =
      ∑' q, Real.exp (-(σ * (xiPoissonPoint q).re)) * (xiSpectralPoint q).im ^ 2
theorem riemannHypothesis_iff_xiPoissonEnergy_eq_zero {σ : ℝ} (hσ : 0 < σ) (hσ' : σ ≤ 2 * Real.pi) :
    RiemannHypothesis ↔ xiPoissonAbstract.energy σ = 0
```

Since `(xiSpectralPoint q).im = 1/2 - Re ρ`, this reads: **RH is the vanishing of the weighted second
moment `Σ_ρ e^{-σ|Im ρ|} (Re ρ - 1/2)²`.** That is the object any arithmetic input must bound, and it
is the weighted form of the classical `Σ_{0<γ≤T} (β - 1/2)²`.

### 93.3 Where the wall sits, numerically

Both sides of `D(σ) = traceReal σ - Re traceC σ` are unconditionally accessible, and the barrier can
now be located exactly rather than described.

*Left side.* `traceReal σ = Σ_ρ e^{-σ|γ_ρ|} = 2∫_0^∞ e^{-σT} dN(T)` depends only on the ordinates, so
Riemann--von Mangoldt applies unconditionally. Writing `N = θ/π + 1 + S`, two integrations by parts
give the `S`-contribution as `2σ² ∫_0^∞ e^{-σT} S₁(T) dT` with `S₁(T) = ∫_0^T S`. Littlewood's
unconditional `S₁(T) = O(log T)` yields

  `traceReal σ = (1/πσ) log(1/(2πσ)) + O(1/σ) + O(σ log(1/σ))`.

*Right side.* `Re traceC σ = 2 Re(e^{-iσ/2} Σ_{γ>0} e^{iσρ})`, and the rectangle contour of §90.3 with
`w = iσ` expresses `Σ_{γ>0} e^{iσρ}` as: an archimedean left-edge integral of size `(1/σ)log(1/σ)`, a
bounded bottom-edge integral, and a prime sum `Σ_n Λ(n) n^{-2-iε} e^{(2+iε)iσ} / (iσ - log n)` which is
absolutely convergent and `O(1)` — the primes enter with an `n^{-2}` weight, not `n^{-1/2}`.

*The coincidence.* The trivial bound from `|δ| < 1/2` is
`D(σ) ≤ (σ²/4)·traceReal σ ≍ σ log(1/σ)`, which is **exactly the order of the unconditional
uncertainty `O(σ log(1/σ))` in `traceReal σ`** coming from `S₁ = O(log T)`. So comparing the two
explicit formulas term by term cannot currently prove `D` small: the argument-function uncertainty on
the left is the same size as the entire quantity being bounded. This is a sharp, checkable statement
of the barrier in this coordinate, and it names the exact classical quantity that controls it.

### 93.4 Next

The two orders coincide, so the gain must come from *cancellation*, not from estimating the sides
separately: the same `S`-data must appear on the contour side and cancel in the difference. Concrete
next target:

> Compute `D(σ)` as a single contour expression in which the `S(T)` contributions from the two sides
> are subtracted before being estimated, and identify what remains.

The classical shadow of the answer is known and is the right check on any such computation: by
Littlewood's lemma applied at every abscissa and integrated,
`Σ_{0<γ≤T} (β - 1/2)² = (1/π) ∫_{1/2}^{∞} ∫_0^T log|ζ(a+it)| dt da + (boundary)`,
so the energy of §93.2 is the double integral of `log|ζ|` over the right half of the critical strip.
An unconditional upper bound for that double integral is, via `energy_le_defect` and
`sq_im_le_of_defect_le`, an explicit zero-free region. That is the arithmetic object to attack, and
unlike the sup-bound of the earlier open core it admits partial credit.

## §94 — The argument function does not cancel: the defect *is* the excess of smoothed `S`

### 94.1 The contour computation of §93.4, carried out

Both sides of `D` were traced to their contour origins. Write `f(s) = e^{iσ(s-1/2)}`; on the critical
line `f(1/2+iT) = e^{-σT}`, so with `ρ = 1/2 + δ + iγ`,

  `D(σ)/2 = Σ_{γ>0} [ f(1/2 + iγ_ρ) - Re f(ρ) ]`,

the *same* analytic weight evaluated at the zero and at its projection onto the critical line. This
makes the "pure defect" structure of §93.1 explicit and gives the two computations:

- **Projection side** `Σ_{γ>0} f(1/2+iγ_ρ) = ∫_0^∞ e^{-σT} dN(T)` depends only on ordinates.
  With `N = θ/π + 1 + S` it splits into a smooth `θ`-part with main term `(1/2πσ)(log(1/2πσ) - γ_E)`
  and the Laplace--Stieltjes transform `L(σ) := ∫_0^∞ e^{-σT} dS(T) = σ ∫_0^∞ e^{-σT} S(T) dT`.
- **Zero side** `Σ_{γ>0} f(ρ)` is the rectangle contour of §90.3 with `w = iσ`: right edge
  `Re s = 2` gives an absolutely convergent prime sum `Σ_n Λ(n) n^{-2-iε} e^{(2+iε)iσ}/(iσ - log n)`,
  left edge `Re s = -1` gives the archimedean term via the functional equation, bottom edge
  `Im s = ε` gives a bounded integral. **No `S` appears anywhere on this side.**

[FINDING, exact] The argument function does **not** cancel in `D`. It occurs on the projection side
only. Consequently, with `P(σ)` the explicit prime--archimedean--boundary expression and
`Θ_sm(σ)` the smooth `θ`-part,

  **`D(σ)/2 = Θ_sm(σ) + L(σ) - P(σ)`,**

so `D ≥ 0` says exactly: *the Laplace-smoothed argument function is never below its prime-archimedean
prediction*, and RH is the assertion of equality. This is a family of unconditional one-sided
inequalities for `S`, one for each `σ > 0`, obtained from nothing but `cos ≤ 1`.

It also confirms the §93.3 accounting from the other direction: `L(σ) ≪ σ log(1/σ)` from Littlewood's
`S₁ = O(log T)` is the same order as the trivial bound on `D`, so no term-by-term comparison closes
the gap. The route reformulates RH as an identity for the smoothed argument function; it does not
break it. Recorded as a reformulation, not a reduction.

### 94.2 What was added to the corpus instead

[LEAN-PROVED] `HTGeometry/AbstractSpectralDefect.lean` and `RHTower/XiAbstractInstance.lean`, axioms
`propext, Classical.choice, Quot.sound`:

```lean
theorem im_eq_zero_iff_traceReal_le {σ : ℝ} (hσ : 0 < σ) (hle : σ ≤ 4 * Real.pi) :
    (∀ i : ι, (F.pt i).im = 0) ↔ F.traceReal σ ≤ (F.traceC (σ : ℂ)).re
theorem riemannHypothesis_iff_xiPoissonTraceReal_le {σ : ℝ} (hσ : 0 < σ) (hle : σ ≤ 4 * Real.pi) :
    RiemannHypothesis ↔ xiPoissonTraceReal σ ≤ (xiPoissonTraceC (σ : ℂ)).re
theorem energy_le_exp_mul_energy {σ σ' : ℝ} (hσ : 0 < σ) (h : σ ≤ σ') :
    F.energy σ' ≤ Real.exp (-((σ' - σ) * F.base)) * F.energy σ
theorem card_le_of_energy_le {σ M T η : ℝ} (hσ : 0 < σ) (hη : 0 < η) (h : F.energy σ ≤ M)
    (s : Finset ι) (hs : ∀ i ∈ s, (F.pt i).re ≤ T ∧ η ≤ |(F.pt i).im|) :
    (s.card : ℝ) * (η ^ 2 * Real.exp (-(σ * T))) ≤ M
theorem card_le_of_xiPoissonEnergy_le {σ M T η : ℝ} (hσ : 0 < σ) (hη : 0 < η)
    (h : xiPoissonAbstract.energy σ ≤ M) (s : Finset XiZeroCopy)
    (hs : ∀ q ∈ s, (xiPoissonPoint q).re ≤ T ∧ η ≤ |(xiSpectralPoint q).im|) :
    (s.card : ℝ) * (η ^ 2 * Real.exp (-(σ * T))) ≤ M
```

Three usable shapes. **RH as one inequality** whose converse is unconditional — the sharpest form yet:
no line, no limit, no equation, just `xiPoissonTraceReal σ ≤ Re (xiPoissonTraceC σ)` at one `σ`.
**Energy decay** at the base-height rate, so a bound at one time propagates to all later times.
**Zero density from an energy bound**: `M` at time `σ` caps the number of zeros with `|Im ρ| ≤ T` and
`|Re ρ - 1/2| ≥ η` by `M e^{σT}/η²` — partial credit in the classical currency, from a single scalar
bound.

### 94.3 Next

`§94.1` shows the obstruction is now a *single* classical quantity: the smoothed argument function
`L(σ) = σ∫_0^∞ e^{-σT}S(T)dT`, which must equal `P(σ) - Θ_sm(σ)` exactly. Two moves:

1. `S` has its own explicit formula (Landau/Selberg):
   `S(T) = -(1/π) Σ_n Λ(n) n^{-1/2} sin(T log n)/log n + O(...)`. Substituting it into `L(σ)` turns
   the identity `D = 0` into a statement purely about prime sums on both sides. The question is
   whether the two prime expressions are *the same* series in disguise — if they are, `D = 0` is an
   identity and the argument closes; if they differ, the difference is the exact arithmetic content
   of RH in this coordinate. This is a finite symbolic computation, not an estimate, and it is the
   first move that can be *settled* rather than bounded.
2. Independently: `card_le_of_xiPoissonEnergy_le` converts any energy bound into a density theorem.
   Running it in reverse — feeding known unconditional density theorems (`N(σ,T) ≪ T^{a(1-σ)}`) into
   a *lower* bound for the energy — tests whether the known density results are already strong enough
   to contradict any hypothetical energy bound, i.e. whether this route can possibly work.

## §95 — Both moves of §94.3 resolve negatively; the precision barrier named

### 95.1 Move (1): the identity is not a formal prime identity

Carrying out the contour computation of `Z(σ) := Σ_{γ>0} e^{iσ(ρ-1/2)}` on the rectangle
`-1 ≤ Re s ≤ 2`, `Im s ≥ ε`:

- **right edge** `s = 2+iy`: `ζ'/ζ = -Σ_n Λ(n) n^{-2-iy}` and `f(s) = e^{3iσ/2} e^{-σy}`, giving
  `(1/2πi) I_right = -(e^{3iσ/2}/2π) Σ_n Λ(n) n^{-2} e^{-ε(σ + i log n)}/(σ + i log n)`,
  absolutely convergent and `O(1)` uniformly in `σ`;
- **left edge** `s = -1+iy`: by the functional equation
  `ζ'/ζ(-1+iy) = -log y + O(1) + Σ_n Λ(n) n^{-2} n^{iy}`, so it contributes the archimedean main term
  `(e^{-3iσ/2}/2πσ)(log(1/σ) - γ_E)` plus primes again at weight `n^{-2}`;
- **bottom edge** `Im s = ε`: a fixed finite integral, `O_ε(1)`.

[FINDING] The two sides of `D(σ) = 0` do **not** carry the same prime series. The zero side carries
primes at weight `Λ(n) n^{-2}/(σ + i log n)` — absolutely convergent, total size `O(1)`. The
projection side carries primes only inside `L(σ)`, through `S(T)`, whose Selberg formula has weight
`Λ(n) n^{-1/2}/log n` — conditionally convergent and oscillating, and only approximate (its error
involves the zeros themselves). So `D = 0` is not an identity between two presentations of one
series; the substitution does not close, and it cannot be made to close by rearrangement, since the
weights differ by `n^{3/2}`.

### 95.2 Move (2): the error floor

The same computation gives the quantitative verdict. The archimedean main terms on both sides are of
size `σ^{-1} log(1/σ)`, the contour's irreducible error (bottom edge plus the `n^{-2}` prime sums) is
`O(1)`, and the target is

  `D(σ) ≍ σ² · energy σ ≍ σ log(1/σ)` at worst.

So the route requires **relative precision `σ²`** in an explicit formula whose error floor is
relative `σ log(1/σ)` — off by a factor `1/(σ log(1/σ))`. Attaining relative precision `σ²` means
moving the contour to `Re s = 1/2 ± η`, i.e. re-encountering the zeros. This is the exact numerology
of the obstruction, and it is uniform across every variant tried in §§90–94: the wall is not the
choice of test function but the required *relative* precision.

### 95.3 Positive salvage: the unconditional window

The barrier statement is itself a theorem, and it is worth having as one.

[LEAN-PROVED] `HTGeometry/AbstractSpectralDefect.lean`, `RHTower/XiAbstractInstance.lean`, axioms
`propext, Classical.choice, Quot.sound`:

```lean
theorem energy_le_quarter_traceReal {σ : ℝ} (hσ : 0 < σ) : F.energy σ ≤ 1 / 4 * F.traceReal σ
theorem defect_le_traceReal {σ : ℝ} (hσ : 0 < σ) : F.defect σ ≤ σ ^ 2 / 8 * F.traceReal σ
theorem traceReal_mul_le_re_traceC {σ : ℝ} (hσ : 0 < σ) :
    (1 - σ ^ 2 / 8) * F.traceReal σ ≤ (F.traceC (σ : ℂ)).re
theorem xiPoissonTraceReal_mul_le_re_xiPoissonTraceC {σ : ℝ} (hσ : 0 < σ) :
    (1 - σ ^ 2 / 8) * xiPoissonTraceReal σ ≤ (xiPoissonTraceC (σ : ℂ)).re
```

Unconditionally, with no hypothesis on the zeros beyond admissibility,

  `(1 - σ²/8) · xiPoissonTraceReal σ ≤ Re (xiPoissonTraceC σ) ≤ xiPoissonTraceReal σ`,

and RH is exactly the assertion that the left factor may be taken to be `1`. The window **closes as
`σ → 0`**: the two quantities are unconditionally equal to relative precision `σ²/8`. Combined with
§94.2's `riemannHypothesis_iff_xiPoissonTraceReal_le`, this is the sharpest quantitative form the
criterion has taken:

> RH is a relative-`σ²` statement, and relative `σ²/8` is already unconditional.

Consequence, and the target for any arithmetic method: **any evaluation of both
`xiPoissonTraceReal σ` and `Re (xiPoissonTraceC σ)` to relative precision `o(σ²)` at a single
`σ ∈ (0, 4π]` settles RH.** That is a precise, checkable specification — a number and an accuracy —
rather than an estimate to be improved indefinitely.

### 95.4 Next

The representation must change: every route in §§90–95 computes `D` by comparing two expansions and
dies at the relative-precision floor. What does not die that way is a route that forces `D ≤ 0`
*structurally*, without computing either side. In this framework there is exactly one such shape
available and it has not been tried:

> The window `(1 - σ²/8) traceReal ≤ Re traceC` is a *termwise* consequence of `|Im α| < 1/2`. The
> displacement bound is itself a theorem (the zeros lie in the critical strip). Iterate: feed the
> conclusion of `sq_im_le_of_defect_le` back into the displacement bound to get a smaller
> `|Im α| ≤ η₁ < 1/2`, which sharpens the window to `1 - σ²η₁²/2`, which sharpens the conclusion
> again. Does the iteration `η_{k+1} = Φ(η_k)` contract to `0`?

This is a fixed-point question about an explicit real map, not an estimate — and if `Φ` is a
contraction with fixed point `0`, the strip bound alone forces RH, with no arithmetic input at all.
That is almost certainly too strong to be true (it would prove RH for every admissible family, and
families with `Im α ≠ 0` exist), so the *interesting* outcome is the exact obstruction: what feature
of the zeta divisor, absent from a general admissible family, would make `Φ` contract? Computing
`Φ` explicitly and locating its non-contraction is the next concrete step, and it is finite work.

## §96 — The fixed-point map computed: self-reference forces gain ≥ 1

### 96.1 `Φ` explicitly

Assume `|J_i| ≤ η` for all `i`, with `η ≤ 1/2` and `ση ≤ π`. Then

- upper: `D(σ) = Σ_i e^{-σR_i}(1 - cos σJ_i) ≤ (1 - cos ση) · traceReal σ`;
- lower at the least-height index `i₀` (height `g`): `D(σ) ≥ e^{-σg}(1 - cos σJ_{i₀})`.

Hence, with `K(σ) := e^{σg} · traceReal σ` (the *normalised* trace),

  **`1 - cos(σ J_{i₀}) ≤ K(σ) · (1 - cos ση)`,   so   `|J_{i₀}| ≲ √K(σ) · η`.**

So `Φ(η) = √K(σ) · η`, and the iteration contracts iff `K(σ) < 1`.

[NO-GO, exact] `K(σ) ≥ card (bottom shell) ≥ 1` for every `σ > 0`, because the point being bounded is
itself a summand of the majorant that bounds it. The gain is at least `1` by *self-reference*, and
the conjugating bijection puts a second point of equal `|J|` in the same shell, so `K ≥ 2` for any
family with a non-real bottom point. The deleted variant (bound `i₀` by `Σ_{j ≠ i₀}`) does not help:
the mirror term is in that sum and equals the deleted one, so its gain is `≥ 1` as well.

**General lesson.** No bound of the form "each displacement ≤ `f`(all displacements)" with `f`
monotone can contract, because the displacement appears on both sides. Self-referential bounds cannot
prove RH; an external input — arithmetic — is required. This is the same wall as §95.2 seen from the
combinatorial side rather than the analytic one, and it explains why every equivalence in §§90–95 is
an equivalence.

### 96.2 The parity analogy of §90.5, resolved

Change ringing suggested a parity obstruction. It does not exist here, for a precise reason: the
interface supplies `inv : ι ≃ ι` with `pt (inv i) = conj (pt i)`, a **sign-reversing bijection**, not
an involution — `inv ∘ inv` need only preserve `pt`, not be the identity. Sign-reversing bijections
of a finite set do not force fixed points, so no parity count is available. What does survive is the
degenerate case:

[LEAN-PROVED] `HTGeometry/AbstractSpectralShell.lean`, axioms `propext, Classical.choice, Quot.sound`:

```lean
theorem im_eq_zero_of_card_bottomShell_eq_one (h : F.bottomShell.card = 1) :
    (F.pt F.bottomIndex).im = 0
```

A one-point bottom shell is fixed by the conjugating bijection, hence real. Conjugation therefore
forbids a *simple* non-real bottom point: an off-line lowest zero always comes with a partner at the
same height. That is exactly the `√2` in the loop gain of §96.1.

### 96.3 Positive salvage: multiplicity is recoverable from the trace

The constant that defeats the iteration is itself a computable spectral invariant.

[LEAN-PROVED] same module and axioms:

```lean
def normalizedTraceReal (σ : ℝ) : ℝ := Real.exp (σ * F.bottomHeight) * F.traceReal σ
theorem normalizedTraceReal_eq {σ : ℝ} (hσ : 0 < σ) :
    F.normalizedTraceReal σ =
      (F.bottomShell.card : ℝ) +
        ∑' i : F.aboveBottom, Real.exp (-(σ * ((F.pt (i : ι)).re - F.bottomHeight)))
theorem le_normalizedTraceReal {σ : ℝ} (hσ : 0 < σ) :
    (F.bottomShell.card : ℝ) ≤ F.normalizedTraceReal σ
theorem tendsto_normalizedTraceReal :
    Filter.Tendsto F.normalizedTraceReal Filter.atTop (nhds (F.bottomShell.card : ℝ))
```

**The least-height multiplicity is read off the real-time trace asymptotics**, unconditionally: the
spectral gap makes every higher point exponentially negligible, so `e^{σg} traceReal σ → card(shell)`
and is `≥ card(shell)` throughout. On the Xi divisor this says
`e^{σ γ₁} Σ_ρ e^{-σ|Im ρ|} → ` (number of Poisson copies at the lowest height), i.e. twice the
multiplicity of the lowest zero — a spectral recovery statement with no hypothesis on where the zeros
lie.

### 96.4 Next

§§95–96 close the "compute or iterate" family of routes with a single mechanism: relative precision
`σ²` is needed and self-reference gives gain `≥ 1`. What has not been tried, and is not of that
family, is to **change what the family is**. Every result so far applies to *any* admissible family,
which is why they are equivalences. The next move must use a property of the zeta divisor that a
general admissible family lacks. Two candidates, both testable against the interface:

1. **Multiplicativity.** The Xi divisor is the zero set of an Euler product; a general admissible
   family has no such structure. Concretely: `traceReal` and `traceC` of the Poisson family are
   *not* multiplicative, but the corresponding objects for the Euler factors are. Does the interface
   admit a "tensor product" of admissible families matching the Euler product, and is the defect
   subadditive under it? If the defect of a product is bounded by the defects of the factors, and
   each factor (a single Euler factor has no zeros off `Re s = 0`) has zero defect, the product has
   zero defect. The place this must fail is where the analytic continuation enters — locating that
   failure exactly is the next finite task.
2. **The functional equation as more than conjugation.** The interface uses only
   `pt (inv i) = conj (pt i)`. The Xi divisor satisfies the *stronger* `ρ ↦ 1 - ρ`, which in Poisson
   coordinates is `α̂ ↦ -conj(α̂)` composed with the reflection — a second involution the interface
   never records. Adding it as an axiom and re-running the §96.1 loop changes `K`: the two
   involutions together may force the bottom shell to have `card ≥ 4` unless real, which changes the
   gain but not its sign. Worth computing exactly, since it is the only structural axiom available
   that has not been used.

## §97 — Both §96.4 candidates resolved; the Poisson coordinate *is* the functional-equation quotient

### 97.1 Candidate (2): the second involution acts trivially

On centred spectral points `z = xiSpectralPoint ρ = γ - iδ` the Klein four-group of the divisor acts
as `z ↦ z`, `-z̄`, `-z`, `z̄`, corresponding to `ρ ↦ ρ, ρ̄, 1-ρ, 1-ρ̄`. The Poisson point is `z` folded
into `Re ≥ 0`, so `ρ ↦ 1-ρ` (which is `z ↦ -z`) leaves it **unchanged**, and `ρ ↦ 1-ρ̄` (which is
`z ↦ z̄`) is exactly the `conj_stable` already in the interface.

[LEAN-PROVED] `RHTower/XiAbstractInstance.lean`, axioms `propext, Classical.choice, Quot.sound`:

```lean
theorem xiPoissonPoint_reflect (q : XiZeroCopy) :
    xiPoissonPoint (xiZeroCopyReflectEquiv q) = xiPoissonPoint q
```

(The degenerate case `Re z = 0` is excluded by `xiPoissonBottomHeight_pos`: no zero has `Im ρ = 0`.)

So there is no unused second involution: **the Poisson coordinate is the quotient of the Xi divisor
by the functional equation**, and `conj_stable` already carries the whole symmetry group. Adding
`ρ ↦ 1-ρ` as an axiom would add nothing. The one quantitative consequence goes the *wrong* way: each
Poisson point is carried by at least two copies (a reflection pair), so a non-real bottom point has
shell cardinality `≥ 4` once conjugation is included, and the §96.1 loop gain `√K` becomes `≥ 2`
rather than `≥ √2`.

This also explains, structurally, why the whole branch has been constraint-shaped rather than
flow-shaped: the coordinate in which the criterion is clean is precisely the one that has already
divided out the functional equation, so nothing is left to propagate.

### 97.2 Candidate (1): the divisor is not a product

The Euler product converges only on `Re s > 1`, where `ζ` has no zeros; each factor `(1-p^{-s})^{-1}`
has poles and no zeros. The zero divisor is therefore not a union or product over primes, and there
is no "tensor of admissible families" to form: multiplicativity reaches the zeros only through the
explicit formula, i.e. only as `Λ(n) ≥ 0`. That is the same channel whose precision floor §95.2
computed. Candidate (1) is empty as stated.

### 97.3 The loop gain, machine-checked

[LEAN-PROVED] `HTGeometry/AbstractSpectralShell.lean`, same axioms:

```lean
theorem defect_le_of_abs_im_le {σ η : ℝ} (hσ : 0 < σ)
    (hall : ∀ i, |(F.pt i).im| ≤ η) (hpi : σ * η ≤ Real.pi) :
    F.defect σ ≤ (1 - Real.cos (σ * η)) * F.traceReal σ
theorem one_sub_cos_bottomShell_le {σ η : ℝ} (hσ : 0 < σ)
    (hall : ∀ i, |(F.pt i).im| ≤ η) (hpi : σ * η ≤ Real.pi)
    {i : ι} (hi : i ∈ F.bottomShell) :
    1 - Real.cos (σ * (F.pt i).im) ≤ F.normalizedTraceReal σ * (1 - Real.cos (σ * η))
```

This is §96.1 as a theorem: the self-referential bound returns itself amplified by the normalised
trace, and `le_normalizedTraceReal` says that factor is `≥ card(bottom shell) ≥ 1`. The iteration is
provably non-contracting, for every admissible family.

### 97.4 Next

With both §96.4 candidates closed, the unused ζ-specific inputs are down to a short list, and only
one of them is a *positivity* rather than a symmetry:

> **Pólya's kernel.** `Ξ(z) = 2∫_0^∞ Φ(u) cos(zu) du` with
> `Φ(u) = Σ_{n≥1} (2π²n⁴ e^{9u/2} - 3πn² e^{5u/2}) e^{-πn² e^{2u}}`, and `Φ > 0` on `ℝ`
> (unconditional, from the theta transformation). `Φ > 0` immediately gives `|Ξ(x+iy)| ≤ Ξ(iy)`, and
> it is the only unconditional *inequality* about `Ξ` that is not a consequence of the symmetries the
> interface already encodes.

A corpus search for it (`formal_tools.py research "Polya positivity Fourier transform Xi"`) returns
rectangular-Fourier and Mercer-capacity material but no `Φ`-positivity declaration, so it is absent.
The concrete next task, in order:

1. Formalize `Φ` and `Φ > 0` (theta transformation route), or locate an equivalent already present
   under another name.
2. Express `traceReal σ` and `Re traceC σ` as pairings against `Φ`. The Poisson weight `e^{-σ|γ|}`
   is the Fourier transform of the Poisson kernel, so both traces become `∫ Φ · (kernel)`, and the
   defect becomes `∫ Φ(u) · K_σ(u) du` for an explicit `K_σ`. If `K_σ ≥ 0` fails only on a set where
   `Φ` is controlled, the sign of the defect is decided by a *pointwise* comparison rather than by an
   estimate — the first mechanism in this branch that is not self-referential and not
   precision-limited.

## §98 — The Entire-Part Obstruction

A conjecture, its one-line falsification, and the principle the falsification exposes. The principle
is the actual result of §§90–97: it explains, structurally rather than case by case, why every route
tried there returned an equivalence or a precision floor, and it says what kind of functional can
possibly do better.

### 98.1 The conjecture

[CONJECTURE — Singular-Data Rigidity] Let `𝒵` be a multiset in `0 < Re s < 1`, stable under
`s ↦ s̄` and `s ↦ 1-s`, with `N(T) ≪ T log T`, and set `W_𝒵(w) := Σ_{s ∈ 𝒵, Im s > 0} e^{ws}`
(convergent for `Im w > 0`). Suppose `W_𝒵` continues meromorphically to `ℂ` with only simple poles at
`w ∈ ±{log p^k}`, residues `-Λ(p^k)/2π`, and a logarithmic branch point at `0`. Then
`𝒵 ⊂ {Re s = 1/2}`.

This is the natural "the arithmetic singular data forces the critical line" statement, and it is the
statement that every explicit-formula route implicitly hopes for. It is the right conjecture to
make: it is exact, falsifiable, implies RH, and is bold enough to be false.

### 98.2 [FALSIFIED]

Move one quadruple `{ρ₀, ρ̄₀, 1-ρ₀, 1-ρ̄₀}` off the critical line. `W_𝒵` changes by

  `e^{wρ₀} + e^{wρ̄₀} + e^{w(1-ρ₀)} + e^{w(1-ρ̄₀)} - (the four unmoved terms)`,

a finite sum of exponentials — an **entire** function of `w`. Every pole, every residue, the entire
principal part at every singularity, and the branch point at `0` are unchanged. A divisor with an
off-line quadruple has exactly the same singular data as one without. The conjecture fails, and it
fails for a reason that has nothing to do with zeta.

### 98.3 The principle

[PRINCIPLE — Entire-Part Obstruction] *Every functional of a spectral trace that depends only on the
singular data of its analytic continuation is invariant under finite perturbation of the spectrum.
The Riemann Hypothesis is not such a functional. Hence no finite combination of residue identities —
no explicit formula, no Landau-type sum rule, no contour evaluation — can separate a divisor with
off-line zeros from one without.*

[LEAN-PROVED] `HTGeometry/AbstractSpectralFamily.lean`, axioms `propext, Classical.choice,
Quot.sound`:

```lean
theorem traceC_sub_eq_finset_sum {ι : Type*} (F G : AbstractSpectralFamily ι) (s : Finset ι)
    (h : ∀ i ∉ s, F.pt i = G.pt i) {τ : ℂ} (hτ : 0 < τ.re) :
    F.traceC τ - G.traceC τ = ∑ i ∈ s, (F.term τ i - G.term τ i)
theorem differentiable_term_sub {ι : Type*} (F G : AbstractSpectralFamily ι) (s : Finset ι) :
    Differentiable ℂ fun τ : ℂ => ∑ i ∈ s, (F.term τ i - G.term τ i)
```

Two admissible families agreeing outside a finite set have traces differing by an entire function.

### 98.4 What it explains, retroactively and exactly

Each obstruction met in §§90–97 is now one corollary:

- **§92.1** `D` is not a Weil pairing because its summand vanishes at `δ = 0`. Corollary: a Weil
  pairing is a residue functional; `D` is an entire-part functional; the two classes are disjoint on
  the nose.
- **§93.3 / §95.2** the precision floor. The archimedean main terms of both sides of `D` are singular
  data (they come from poles and branch points); `D` itself lives in the entire part. Comparing the
  two sides is comparing a singular functional against an entire one, so the difference is *all* of
  the error term. That is why the required relative precision was `σ²` and the available floor was
  `σ log(1/σ)`: the floor is not an artefact of the contour, it is the size of the entire part.
- **§95.1** the two prime series differ by `n^{3/2}`. Corollary: the residues (weight `n^{-2}`) are
  singular data; `S(T)`'s prime expansion (weight `n^{-1/2}`) is not a residue expansion at all — it
  is an asymptotic one. The weights differ because the two sides live on opposite sides of the
  divide.
- **§96.1** self-reference. The defect is finite-perturbation-sensitive, so any bound on one point by
  the whole trace must retain that point's own contribution: gain `≥ 1` is the entire-part functional
  refusing to be estimated by a singular one.
- **§97.1** the functional equation acts trivially in the Poisson coordinate. Corollary: symmetries
  are automorphisms of the singular data; they cannot see the entire part either.

The branch has been consistent all along: `D`, the defect, is precisely an **entire-part functional**
— it is exactly the part of the trace that the explicit formula does not determine — and every tool
applied to it was a singular-data tool.

### 98.5 What the principle predicts, and the next object

The principle is not only a no-go; it is a specification. A functional that can prove RH must be
**sensitive to finite perturbation**, i.e. must depend on the entire part of the trace. Three
invariants of an entire function are available, and only three: its **order and type**, its **indicator
diagram**, and its **global growth along rays**. The defect is a value; the correct object is the
*growth* of the entire part.

[CONJECTURE — Entire-Part Type] Write `W = P + E` with `P` the (arithmetically determined) sum of
principal parts and `E` entire. Then the indicator function of `E` along the positive real axis is

  `h_E(0) := limsup_{u → +∞} (log |E(u)|)/u = 1/2 + λ`,   `λ := sup_ρ |Re ρ - 1/2|`,

so **RH ⟺ `h_E(0) = 1/2`**, and more generally the indicator diagram of `E` is the convex hull of the
set `{Re ρ}`. The content is that the *singular* part `P` is arithmetic and known while the *type* of
the complementary entire part is precisely the zero-free-strip width — the two halves of the trace
carry exactly complementary information, and RH is the statement that the entire half is as small as
the singular half permits.

Why this is the right next object rather than another equivalence: `P` is explicitly computable from
`Λ`, so `E = W - P` is computable wherever `W` is; and the indicator of an entire function is *not* a
residue functional — it is exactly the kind of quantity the principle says is required. The first
finite task is to compute `h_{E}(θ)` for `θ` in the upper half plane, where `W` is given by its
convergent series and `P` by its explicit sum, and check the predicted equality
`h_E(π/2) = 0` against the known `Σ e^{-σγ}` asymptotics — a consistency test that can falsify the
conjecture cheaply before any effort is spent proving it.

## §99 — Correction to §98.5, and what the Lean corpus says the target actually is

### 99.1 §98.5 was ill-posed. [RETRACTED]

The promised cheap test killed it. `W = P + E` is not a canonical decomposition: `P`, a sum of
principal parts, is defined only modulo entire functions (and the naive `Σ_n` over all poles does not
even converge — `Σ Λ(n)` diverges; the contour form `Σ_n Λ(n) n^{-c} e^{c w}/(w - log n)` converges
but is not a pure principal-part sum). Since `E` is defined only modulo entire functions, its
indicator `h_E` is not an invariant of `W`. The conjecture has no content as stated.

The well-posed replacement is the indicator of `W` itself in the upper half `w`-plane, and it is
computable: for `θ ∈ (0, π)`,

  `h_W(θ) = sup_ρ (β_ρ cos θ - γ_ρ sin θ)`,

the support function of the divisor. So the indicator diagram of `W` is the closed convex hull of the
divisor, and "RH ⟺ that hull is a vertical half-line" — a restatement, not a route. Worse, at
`θ → 0+` the limit is `1` unconditionally, driven by the classical zero-free region's shape at large
height, so the indicator is not even sensitive to `sup β` at bounded height. The Entire-Part
Obstruction of §98.3 stands; the specific object I proposed to exploit it does not.

[LEAN-PROVED] What survived from the attempt, and it is the right shape — a *finite-perturbation
sensitive* extraction, in `HTGeometry/AbstractSpectralShell.lean` (axioms `propext,
Classical.choice, Quot.sound`):

```lean
theorem tendsto_exp_mul_traceC_sub_bottomShell :
    Filter.Tendsto
      (fun σ : ℝ => Real.exp (σ * F.bottomHeight) * F.traceC (σ : ℂ)
          - ∑ i ∈ F.bottomShell, Complex.exp (-(σ : ℂ) * (F.pt i - (F.bottomHeight : ℂ))))
      Filter.atTop (nhds 0)
```

The trace determines its extreme shell exactly in the limit. Moving one least-height point moves the
limit — unlike every residue functional.

### 99.2 The corpus already holds a different characterisation of the critical line

Following the corpus rather than my own route: `RHTower/XiHurwitzFEAnchorCircuitCollision.lean`
contains, all with axioms `propext, Classical.choice, Quot.sound`:

```lean
theorem continuedHurwitzFESchwarzPairDifferentiallyDependent_iff_re_eq_half
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) :
    ContinuedHurwitzPairDifferentiallyDependent (1 - rho) ((starRingEnd ℂ) rho) ↔ rho.re = 1 / 2
theorem xiHurwitzFESchwarzPairCircuit_iff_riemannHypothesis :
    XiHurwitzFESchwarzPairCircuit ↔ RiemannHypothesis
theorem xiZero_continuedHurwitzHalfFEAnchorTriple_independent
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) (hzero : xi rho = 0) :
    ¬ ContinuedHurwitzFEAnchorTripleDependent rho (1 / 2 : ℂ)
```

The critical line is the locus where the functional-equation partner and the Schwarz partner of a
zero become **differentially dependent** as Hurwitz functions, and the third theorem shows the method
has teeth: it proves an *unconditional* independence at every Xi zero for the anchor `1/2`.

This branch is on the correct side of §98.3: it is pointwise and value-type, never a sum over zeros.
My §§90–98 analytic branch and this one are disjoint, and the obstruction proved in §98 applies to
mine, not to this one.

### 99.3 What the mechanism actually says, and the reframing it forces

Reading the proof rather than the statement: dependence is decided by the Hurwitz monodromy character
through `monoScalar_eq_monoScalar_iff_integerDifference` — two exponents carry the same character
exactly when they differ by an **integer**. For the FE/Schwarz pair,

  `(1 - rho) - conj rho = 1 - 2 Re rho`,

so the critical line is the locus where that number is an integer, and the open strip confines it to
`(-1, 1)` where the only integer is `0`. Equivalently `monoScalar rho = e^{2πi rho}`, and `Re rho = 1/2`
is exactly the condition that this character be a *negative real*.

[LEAN-PROVED] `RHTower/XiCriticalLineIntegrality.lean`, same axioms:

```lean
theorem riemannHypothesis_iff_forall_exists_int_one_sub_two_re :
    RiemannHypothesis ↔
      ∀ rho : XiDivisorSupport, ∃ m : ℤ, 1 - 2 * (rho : ℂ).re = (m : ℝ)
```

**The Riemann Hypothesis is an integrality statement.** Not an estimate, not a positivity, not a
bound: every Xi zero must place the single real number `1 - 2 Re rho` in `Z`. The strip supplies the
width; integrality supplies the location.

This is what the corpus was saying and what the analytic branch could not see. It also retro-explains
§98 once more: an integrality condition is manifestly finite-perturbation sensitive (move one zero and
it fails at that zero), so no residue functional can reach it — consistent with the Entire-Part
Obstruction, and now with a positive statement of what must be proved instead.

### 99.4 Next

Integrality statements are not proved by estimates. The methods that prove them, none of which this
project has used, are:

1. **Monodromy finiteness / quasi-unipotence.** `1 - 2 Re rho ∈ Z` is the resonance condition for the
   local exponents of a connection. If the Hurwitz family over the exponent line carries a connection
   whose monodromy at the Xi divisor is quasi-unipotent, integrality is automatic. The object to
   construct: the connection, and the statement that the Xi divisor is its resonant locus.
2. **Rationality/period arguments.** `monoScalar rho = e^{2πi rho}` is a period-type invariant; RH
   says it is real at every zero. Real periods come from Galois-descent or from a real structure on
   the underlying motive-like object. The object to construct: the real structure whose fixed locus
   is the critical line.
3. **`p`-adic integrality.** `1 - 2 Re rho ∈ Z` at every zero is exactly the kind of statement a
   `p`-adic valuation argument settles, if a `p`-adic avatar of the divisor exists.

Immediate finite task, in the corpus's own language: `xiZero_continuedHurwitzHalfFEAnchorTriple_independent`
proves independence for the anchor `1/2` unconditionally; `xiHurwitzFESchwarzPairCircuit` requires
*dependence* for the Schwarz anchor. Both are statements about the same three-function differential
matroid at the same point. Determine the exact matroid of `{H_rho, H_{1-rho}, H_{conj rho}, H_{1/2}}`
at a hypothetical off-line zero — a rank computation over a differential field, entirely finite — and
see which rank patterns are consistent with the unconditional theorem. A contradiction there is a
proof; an admissible pattern is an explicit description of what an off-line zero would have to look
like differential-algebraically, which is the first concrete portrait of the enemy this project has
had.

## §100 — The differential matroid computed: no contradiction, and what it leaves

### 100.1 The rank computation

The corpus decides differential dependence of a Hurwitz family through `monoScalar`, and
`monoScalar_eq_monoScalar_iff_integerDifference` makes character equality *integer difference*. So the
matroid on any finite set of exponents is: **partition by residue class mod `Z`; a set is dependent
exactly when two members share a class.**

At a hypothetical off-line zero `rho = beta + i gamma` (`gamma ≠ 0`, `delta := beta - 1/2 ≠ 0`) the
four exponents `rho`, `1-rho`, `conj rho`, `1/2` have pairwise differences

  `2 delta + 2 i gamma`, `2 i gamma`, `delta + i gamma`, `-2 delta`, `1/2 - delta - i gamma`,
  `delta - i gamma`.

Four of these have nonzero imaginary part `±gamma` or `±2 gamma`, hence are not integers; and
`-2 delta` is not an integer precisely because `0 < |2 delta| < 1`. **All four exponents lie in
distinct classes mod `Z`: the quadruple is differentially independent.**

[NO-GO] No contradiction. The rank pattern at an off-line zero is the generic one, fully consistent
with `xiZero_continuedHurwitzHalfFEAnchorTriple_independent`. The differential-algebraic encoding is
*faithful* — it detects the critical line exactly — but it carries **no information beyond the
integrality of `1 - 2 Re rho`**, because the character map `s ↦ e^{2 pi i s}` is injective modulo `Z`.
So `XiHurwitzFESchwarzPairCircuit` cannot be attacked through the matroid: proving the circuit *is*
proving the integrality, with no intermediate structure to exploit.

This is worth recording precisely because the route looked richer than it is. The Hurwitz functions
are a faithful coordinate for the critical line, not a source of leverage on it.

### 100.2 What the computation leaves: an involution with no free orbits

Strip the encoding away and the statement that remains is geometric.

[LEAN-PROVED] `RHTower/XiCriticalLineIntegrality.lean`, axioms `propext, Classical.choice,
Quot.sound`:

```lean
theorem riemannHypothesis_iff_forall_exists_int_one_sub_two_re :
    RiemannHypothesis ↔ ∀ rho : XiDivisorSupport, ∃ m : ℤ, 1 - 2 * (rho : ℂ).re = (m : ℝ)
theorem riemannHypothesis_iff_forall_add_conj_eq_one :
    RiemannHypothesis ↔ ∀ rho : XiDivisorSupport, (rho : ℂ) + (starRingEnd ℂ) (rho : ℂ) = 1
```

The map `sigma(rho) = 1 - conj rho` is the functional equation composed with Schwarz reflection. It is
an anti-holomorphic **involution**; the Xi divisor is `sigma`-invariant; its fixed locus is exactly
the critical line. So:

> **RH ⟺ `sigma` acts on the Xi divisor with no free orbits.**

A free orbit is a pair `{rho, 1 - conj rho}` with `beta ≠ 1/2`. Nothing in the analytic theory
forbids free orbits; the whole content of RH is that there are none.

This is also, exactly, the `inv` field of the abstract interface: `conj_stable` is `sigma`-equivariance
and `im = 0` is being fixed. §96.2 noticed that the interface supplies only a sign-reversing
*bijection*; for the Xi divisor it is a genuine involution, which is the axiom the interface is
missing and the reason parity arguments are available for zeta but not for a general admissible
family.

### 100.3 Why this is the right frame, and the next object

"An involution acts with no free orbits" is not an estimate, not a positivity, and not an integrality
in disguise — it is an **equivariant counting statement**, and equivariant counting statements are
settled by index theory: a Lefschetz number, an equivariant Euler characteristic, a signature.

The precedent is exact rather than analogical. Over function fields the Riemann Hypothesis is a
theorem, and Weil's proof is of this type: the Frobenius eigenvalues satisfy `|alpha| = q^{1/2}`
because the **Hodge index theorem** on `C x C` forces a signature, which is precisely a statement that
an involution-like pairing has no room for the analogue of a free orbit. The number-field obstruction
has always been the absence of the surface. What §§99–100 add is that one no longer needs the surface
to *state* the target: the target is the vanishing of a free-orbit count for one explicit
anti-holomorphic involution on one explicit discrete set.

Concrete next object, and it is constructible rather than hypothetical:

> Build the `sigma`-equivariant pairing on the divisor directly. For each free orbit
> `{rho, 1 - conj rho}` the two points have `Re` summing to `1`; for a fixed point the single value is
> `1/2`. Define on finitely supported divisor classes the quadratic form
> `Q(D) = Σ_{rho, rho' ∈ D} K(rho, sigma rho')` with `K` the Weil/Guinand kernel, and ask for its
> **signature**. Weil positivity says `Q ≥ 0` on a subspace iff RH; the index-theoretic question is
> whether `Q`'s signature is computable equivariantly — by localisation at the fixed locus, where the
> only contributions are archimedean and prime, both explicit.

That is the first formulation in this card in which RH is a *signature* rather than a bound, and
signatures localise. The immediate finite task is to write `Q` on the Xi divisor in the corpus's
existing Weil-Gram language (`XiWeilArithmeticGram`, `ConstrainedProlateWeilToeplitzSchur`) and
compute its restriction to a single free orbit — a `2 x 2` determinant, entirely finite, whose sign
decides whether free orbits are compatible with positivity at all.

## §101 — The orbit block: each free orbit is a hyperbolic plane

### 101.1 The 2×2 computation

Take a Weil test function in polarised form `h(z) = f(z) f#(z)` with `f#(z) = conj f(conj z)` -- the
involution the corpus already carries as `xiWeilSharp`. At a zero `rho = 1/2 + delta + i gamma` the
centred spectral points of the `sigma`-orbit are `gamma - i delta` and `gamma + i delta`. Put

  `u := f(gamma - i delta)`,  `v := f(gamma + i delta)`.

Then `f#(gamma - i delta) = conj v` and `f#(gamma + i delta) = conj u`, so the orbit contributes

  `h(gamma - i delta) + h(gamma + i delta) = u conj v + v conj u = 2 Re(u conj v)`.

**A fixed point** (`delta = 0`) has `u = v` and contributes `|u|²`: a positive definite rank-one
block. **A free orbit** contributes the form with matrix `[[0,1],[1,0]]` in the basis `(u,v)`:
determinant `-1`, **signature `(1,1)` -- a hyperbolic plane.**

[COMPUTED] The Weil quadratic form on the Xi divisor decomposes, orbit by orbit, as

  `(positive definite)^{#fixed points}  ⊕  (hyperbolic plane)^{#free orbits}`,

so its **negative index equals the number of free `sigma`-orbits**, and

> **RH ⟺ the Weil form has negative index zero.**

This is why Weil positivity is the correct criterion and also why it is hard in exactly the way it
is: positivity is not a delicate inequality about a single quantity, it is the vanishing of an
index, and each off-line orbit contributes exactly one hyperbolic plane -- no more, no less. The
failure of RH would be quantised: negative index `= ` number of free orbits, an integer.

### 101.2 The involution, formalised

[LEAN-PROVED] `RHTower/XiCriticalLineIntegrality.lean`, axioms `propext, Classical.choice,
Quot.sound`:

```lean
def xiZeroLineConjEquiv : XiDivisorSupport ≃ XiDivisorSupport :=
  xiZeroConjEquiv.trans xiZeroReflectEquiv
theorem xiZeroLineConjEquiv_apply (rho : XiDivisorSupport) :
    ((xiZeroLineConjEquiv rho : XiDivisorSupport) : ℂ) = 1 - (starRingEnd ℂ) (rho : ℂ) := rfl
theorem xiZeroLineConjEquiv_involutive : Function.Involutive xiZeroLineConjEquiv
theorem riemannHypothesis_iff_xiZeroLineConj_fixed :
    RiemannHypothesis ↔ ∀ rho : XiDivisorSupport, xiZeroLineConjEquiv rho = rho
```

`sigma` is now an explicit involution of the divisor in the corpus, so "free orbit" is a formal
notion and "no free orbits" is a formal statement equivalent to RH. Note this is the same map the
abstract interface carries as `inv`: `conj_stable` is `sigma`-equivariance and `im = 0` is being
fixed. §96.2's missing axiom is exactly `xiZeroLineConjEquiv_involutive`, and it is a theorem for
zeta while being false in general for an abstract admissible family.

### 101.3 Where this puts the problem

Three statements, all now proved equivalent to RH in the corpus, in increasing structure:

1. `riemannHypothesis_iff_forall_exists_int_one_sub_two_re` — an **integrality**: `1 - 2 Re rho ∈ Z`.
2. `riemannHypothesis_iff_xiZeroLineConj_fixed` — a **fixed-point property**: `sigma` has no free
   orbit.
3. §101.1 — an **index**: the Weil form's negative index is zero.

These are the same statement in three categories, and the third is the one with a proof technology.
Negative indices of quadratic forms attached to a variety with an involution are computed by
localisation to the fixed locus; that is the content of the Hodge index theorem, which is exactly how
the function-field Riemann Hypothesis is proved. The number-field difficulty has always been stated
as "there is no surface". §§99–101 sharpen that: one does not need the surface to state the target,
only to compute the index. What is missing is not a criterion but a **localisation formula** for the
negative index of the Weil form.

### 101.4 Next

The finite next step is to write the localisation candidate and test it on the one case where both
sides are computable:

> The Weil form's arithmetic expression is `archimedean - prime`. Its negative index, if it localises,
> should be expressible as a sum of local contributions at the fixed locus (the critical line) plus a
> defect from the primes. Compute both sides for the truncated form on a finite-dimensional test
> space -- the corpus already carries such truncations (`ConstrainedProlateWeilToeplitzSchur`,
> `XiWeilArithmeticGram`) -- and check whether the negative eigenvalue count of the truncated Gram
> matrix matches the free-orbit count of the zeros inside the corresponding window.

That comparison is a finite linear-algebra statement about matrices the corpus already defines, it is
falsifiable, and a match would be the first evidence that the index localises. A mismatch would say
the Weil form's negative index is *not* the free-orbit count at finite truncation, which would itself
locate the error term that any index formula must carry.

## §102 — The index is finite for a structural reason, and what still blocks the formula

### 102.1 Why the truncation is finite (no numerics needed)

The comparison proposed in §101.4 was a numerical eigenvalue count, which this project's rules
exclude as evidence. The mathematical content behind it is available directly.

For a test function of exponential type at most `Delta`, the autocorrelation `g` is supported in
`[-Delta, Delta]`, so `g(log n) = 0` for `n > e^Delta`: **only the prime powers below `e^Delta` enter
the Weil functional at all.** On that space

  `Q = (archimedean part, nonnegative)  -  (prime part, vanishing outside finitely many n)`.

A nonnegative form cannot be negative, so every direction on which `Q` is negative must be seen by
the prime part. That is the whole argument, and it is structural rather than estimative.

[LEAN-PROVED] `HTGeometry/NegativeIndexRankBound.lean`, axioms `propext, Classical.choice,
Quot.sound`:

```lean
theorem negativeSubspace_inf_radical_eq_bot
    (P R : V → ℝ) (hP : ∀ v, 0 ≤ P v)
    (K : Submodule ℝ V) (hK : ∀ v ∈ K, R v = 0)
    (W : Submodule ℝ V) (hW : ∀ v ∈ W, v ≠ 0 → P v - R v < 0) :
    W ⊓ K = ⊥
theorem finrank_negativeSubspace_add_finrank_le [FiniteDimensional ℝ V] ... :
    Module.finrank ℝ W + Module.finrank ℝ K ≤ Module.finrank ℝ V
```

A negative-definite subspace of `P - R` meets the radical of `R` trivially, hence has dimension at
most the corank of that radical. Applied to the Weil functional on band-limited test functions: the
**negative index is bounded by the number of prime powers below `e^Delta`** -- the primes are not
merely the source of the negativity, they bound how much of it there can be.

### 102.2 What this gives and what it does not

Combined with §101.1 -- each free `sigma`-orbit contributes exactly one hyperbolic plane -- the shape
of an index formula is now visible:

  `#{free orbits resolved at scale Delta}  =  neg-index Q_Delta  ≤  #{prime powers ≤ e^Delta}`.

The left equality is §101.1 *provided* the evaluation map from test functions to orbit values is
surjective onto the resolved orbits; the right inequality is §102.1 and is unconditional. So the
missing ingredient is precisely:

[OPEN CORE, named exactly] **Resolution.** For test functions of exponential type `Delta`, which
`sigma`-orbits can be independently prescribed? Equivalently: what is the rank of the evaluation map
`f ↦ (f(gamma_rho))_rho` restricted to zeros with `|gamma| ≤ T`? Beurling--Selberg theory answers the
analogous one-sided extremal question; the two-sided interpolation question at *complex* nodes
`gamma - i delta` is what an index formula needs and is not classical.

Note what the two bounds would say if the resolution count grows like the zero count `T log T` while
the prime bound grows like `e^Delta / Delta`: for the inequality to be consistent, the number of
*free* orbits below the resolution height must stay below the prime count. That is not a proof of RH
-- the resolution dictionary between `Delta` and `T` is exactly the unproved ingredient, and getting
it wrong is how one manufactures a false theorem here -- but it identifies the single quantitative
comparison on which an index proof would turn.

### 102.3 Status of the three equivalent forms

All three remain equivalent to RH and all three are in the corpus:

1. integrality: `1 - 2 Re rho ∈ Z` (`riemannHypothesis_iff_forall_exists_int_one_sub_two_re`);
2. no free orbits for `sigma rho = 1 - conj rho` (`riemannHypothesis_iff_xiZeroLineConj_fixed`);
3. vanishing negative index of the Weil form (§101.1, computed; the per-orbit block is hyperbolic).

The gain of §102 is that form 3 now has an unconditional *upper* bound on the index from the prime
side, which forms 1 and 2 do not admit at all. RH remains unproved: the index is bounded, not shown
to vanish.

### 102.4 Next

The resolution question of §102.2 is the whole of it, and it is a concrete problem in entire-function
theory rather than in number theory:

> Given `Delta > 0` and a finite set of nodes `z_1, ..., z_N` in the strip `|Im z| < 1/2`, when can an
> entire function of exponential type `≤ Delta`, real on `R`, take prescribed values at the `z_j` and
> at their conjugates independently?

For real nodes this is classical cardinal interpolation with the Nyquist threshold `N ≈ Delta T / pi`.
For complex nodes the conjugate-pair constraint couples the values, and the coupling is exactly the
hyperbolic block of §101.1. Determining the interpolation rank in the presence of that coupling is a
finite, self-contained question whose answer converts §102.2's inequality into an index formula. That
question -- not another criterion for RH -- is the next object to construct.

## §103 — Two corrections: the rank bound does not apply, and resolution was a red herring

### 103.1 [RETRACTED] §102.2's inequality

`neg-index Q_Delta ≤ #{prime powers ≤ e^Delta}` is **false**, and the error is instructive.

The abstract lemma of §102.1 is correct and proved: a negative-definite subspace of `P - R` meets the
radical of `R` trivially. Its application to the Weil functional is not. The prime part is

  `R(phi) = Σ_{n ≤ e^Delta} c_n ∫ phi(u) conj(phi(u - log n)) du + c.c.`,

a **quadratic** form in `phi`, whose associated Hermitian operator is `Σ_n c_n (S_{log n} + S_{log n}^*)`
with `S_t` the truncated shift on `L²[-Delta, Delta]`. A truncated shift has infinite rank. So `R` is
a finite sum of *shifts*, not a finite-rank operator: only finitely many prime **frequencies** appear,
which is not the same as finitely many **dimensions**. The set `{phi : R(phi) = 0}` is a quadric, not
a subspace, and has infinite codimension in no useful sense.

The retraction is necessary rather than pedantic. The false inequality, combined with §103.2 below,
would have forced the number of zeros with `|Re rho - 1/2| ≥ eta` to be finite for every `eta > 0` --
a quasi-RH statement far beyond any known zero-density theorem. Deriving that from two easy lemmas is
itself the signal that one of them was misapplied.

What is true, and is the correct replacement: `R` is a Toeplitz-type operator whose symbol is the
generalized trigonometric polynomial `Σ_{n ≤ e^Delta} c_n · 2 cos(xi log n)`. By Szegő asymptotics its
negative eigenvalue count grows **linearly in `Delta`**, with density the measure of the set where the
total symbol is negative. So the index does not stay bounded; it has a density, and

  `neg-index Q_Delta ≈ (Delta / 2 pi) · |{xi : Omega(xi) < 0}|`,

with `Omega` the Riemann--Weil symbol. RH is the vanishing of that density -- i.e. `Omega ≥ 0` almost
everywhere, which is the statement that the Riemann--Weil distribution is a positive measure. The
index formula of §101--102 is therefore a **Szegő limit theorem**, not a finite-rank count.

### 103.2 The Resolution question, answered -- and it was the wrong question

§102.4 asked when an entire function of exponential type `≤ Delta`, real on `R`, can take prescribed
values at finitely many nodes `z_j` in the strip and at their conjugates independently. The answer is:
**always, for every `Delta > 0`.**

Evaluation at `z` on `PW_Delta` is `f(z) = ∫_{-Delta}^{Delta} phi(u) e^{i z u} du = ⟨phi, e_z⟩` with
`e_z(u) = e^{-i conj(z) u}`. The family attached to the nodes and their conjugates is
`{e^{-i conj(z_j) u}, e^{-i z_j u}}`, a set of exponentials with **pairwise distinct frequencies**
(distinct because the `z_j` are distinct and non-real). Exponentials with distinct frequencies are
linearly independent on any interval of positive length -- vanishing of a finite combination on
`[-Delta, Delta]` propagates to all of `R` by analyticity, where Dedekind independence of characters
applies. Hence the evaluation map onto the `2N` values is surjective.

So there is **no Nyquist obstruction and no resolution threshold** for finitely many nodes. §102.2's
"resolution" open core does not exist.

[CORRECTION to §101.1] This exposes the real gap, which resolution was masking. The Weil form is

  `Q(f) = Σ_{fixed} |f(gamma)|²  +  Σ_{free orbits} 2 Re( f(gamma - i delta) · conj f(gamma + i delta) )`,

and the free-orbit block is hyperbolic *as a form on that orbit's two values*. But `Q` on test
functions is the **pullback** of that form along the evaluation map into the full (infinite) value
space, and the pullback of an indefinite form can be positive semidefinite when its image lies in a
positive cone. Prescribing `u = 1, v = -1` on one orbit does not make `Q` negative: it makes one
summand equal `-2`, which must still beat `Σ_{all other zeros} |f(gamma_rho)|² ≥ 0`. So

> **"negative index = number of free orbits" is not proved and, as stated in §101.1, is false as an
> identity.** What holds is `neg-index ≥ 1` once a single orbit's negative contribution dominates the
> rest, which is exactly the classical easy direction of Weil's criterion, and it needs `Delta` large
> enough that `e^{Delta·delta}` beats the accumulated positive mass.

### 103.3 What stands

Unaffected, and still proved: §101.2's involution (`riemannHypothesis_iff_xiZeroLineConj_fixed`),
§99.3's integrality (`riemannHypothesis_iff_forall_exists_int_one_sub_two_re`), §98.3's Entire-Part
Obstruction, and the abstract lemma `negativeSubspace_inf_radical_eq_bot` itself. Withdrawn: the
prime-count index bound and the resolution open core.

The corrected picture: the index is not a finite count bounded by primes; it is a **density**, and
the free-orbit/hyperbolic decomposition describes the form on the value space rather than on the test
space. The competition between one orbit's hyperbolic block and the positive mass of every other zero
is the actual content, and `Delta` -- the exponential type -- is the parameter that controls it.

### 103.4 Next

The corrected object is sharp and is a single inequality about entire functions:

> For an off-line orbit at height `gamma` with displacement `delta`, and `f ∈ PW_Delta` normalised by
> `‖f‖_{L²(R)} = 1`, how large can
> `|f(gamma - i delta) · f(gamma + i delta)|` be relative to `Σ_{rho ≠ orbit} |f(gamma_rho)|²`?
> The first quantity is at most `e^{2 Delta delta}` by Phragmén--Lindelöf; the second is a
> Plancherel-type mass controlled by the zero density near `gamma`, which is `≈ log gamma / 2 pi` per
> unit height.

So the competition is `e^{2 Delta delta}` against `log gamma`, and a negative direction exists as soon
as `Delta delta ≳ log log gamma`. That is a *usable* dictionary: it says an off-line zero at height
`gamma` is detected by type `Delta ≈ log log gamma / delta`. Making this precise -- with the correct
constant and with the positive mass estimated rather than guessed -- converts the classical easy
direction of Weil's criterion into a quantitative detection theorem, and a quantitative detection
theorem is what any Szegő-density argument needs as input. That estimate, not another criterion, is
the next object.

## §104 — Anti-theatre audit of §§90–103

Session seed `4196616358529678506`. Every result of §§90–103 put through the novelty gate: *would a
competent literature search have produced this?* Verdicts are blunt on purpose.

| § | Claim | Verdict |
|---|---|---|
| 90 | Index-free rigidity: trace bounded on one vertical line ⟹ spectrum real | **REDUCES-TO-KNOWN.** This is the indicator/abscissa theory of Dirichlet series with complex frequencies. A search on "Dirichlet series, complex exponents, Phragmén--Lindelöf indicator" returns it. |
| 91 | `RH ⟺ D(σ) = Σ e^{-σ|γ|}(1-cos σδ) = 0` | **INSIGNIFICANT.** One member of an infinite family of constructible "vanishes iff RH" functionals. Constructing one is an exercise. |
| 92--96 | Why `D` resists (not a Weil pairing; precision floor; self-reference) | **INSIGNIFICANT as science.** These are facts about my own construction, not about zeta. Lab notes. |
| 97 | FE acts trivially in the Poisson coordinate | **INSIGNIFICANT.** A fact about a coordinate I chose. |
| 98 | "Entire-Part Obstruction" | **REDISCOVERED.** That the explicit formula does not determine the real parts is exactly why Weil positivity, not the explicit formula, is the criterion. Standard folklore. I oversold it as "the actual result of §§90--97". |
| 99 | `RH ⟺ 1 - 2 Re rho ∈ Z` | **INSIGNIFICANT.** The strip has width 1, so the only available integer is 0. Calling this "RH is an integrality statement" is rhetoric, not mathematics. |
| 100 | `RH ⟺ sigma(rho) = 1 - conj rho` has no free orbit | **REDISCOVERED.** This is the definition of the critical line together with the standard symmetry of the divisor. |
| 101 | Each free orbit contributes a hyperbolic block | **REDISCOVERED and partly FALSE.** The block computation is how the easy direction of Weil's criterion is proved (Bombieri, *Remarks on Weil's quadratic functional*); and I stated it as an identity for the negative index, which §103.2 had to retract. |
| 102 | `neg-index ≤ #{prime powers ≤ e^Delta}` | **FALSE.** Retracted in §103.1. |
| 103 | The two corrections | Honest, but correcting my own errors is not new knowledge. |

**Net: §§90--103 produced no new scientific knowledge.** The Lean is correct and the corpus grew by
roughly twenty machine-checked declarations, but every one of them formalises either a standard fact,
a trivial equivalence, or an observation about my own construction. This is the outcome the novelty
gate exists to catch, and I did not apply it as I went.

### 104.1 The exact why

Every object built in §§90--103 was a **functional of the zero set**: the trace, the defect, the
energy, the indicator, the Weil form on the divisor. A functional of the zero set can only encode
properties of the zero set. The space of functionals vanishing exactly when RH holds is
infinite-dimensional and free -- exhibiting one costs nothing and proves nothing. Every "criterion"
in §§90--103 is a point in that space.

That is the structural trap, and it is worth naming because it is invisible from inside: each step
felt like progress because each step was a *correct new theorem*. Correctness is not the gate;
distance from the known corpus is.

**Constraint for anything further:** a statement is worth pursuing only if it is *upstream* of the
zeros -- about the object that produces them -- and only if it is **not equivalent to RH**, so that it
could be decided independently and RH would follow. Any new "RH ⟺ X" is disqualified on sight.

### 104.2 What the entropy draw produced, and its attack

`minimal-counterexample` × `watermarks` × `immune-system`.

*Immune system.* A repertoire is shaped not by a rule that builds correct members but by **two
opposing deletions**: negative selection removes strong self-binders, positive selection removes
non-binders. The surviving set is a two-sided window. Applied: do not look for a rule producing
`beta = 1/2`; look for two independent pressures whose window closes to a point.

Zeta has exactly one such pressure and its mirror. The Euler product forbids zeros for `beta > 1`;
positivity of `Λ` transports that inward (`3-4-1`) and saturates at `beta = 1 - c/log t`. The
functional equation then reflects it to `beta > c/log t`. **The two pressures are the same pressure
seen twice.** Self-duality is why every zero-free region yields a *band* of width `1 - 2 c/log t` and
never a line: closing the band requires the single available pressure to travel the full distance
`1/2` on its own.

*Watermarks.* A watermark is imposed at formation, not printed afterwards, and is revealed only under
changed illumination -- so it cannot be forged by post-processing. The formation constraint here is
Poisson summation on `Z ⊂ R` (the theta transformation), which is exactly the functional equation.
§98 already shows an off-line divisor does not violate it: the watermark is *compatible* with free
orbits. So the only formation constraint available is self-dual and blind to RH.

*Minimal counterexample.* A minimal off-line zero has a partner at the **same ordinate**, so
`RH ⟺ rho ↦ Im rho` is injective on the zero set. This puts RH in the category of a
transversality/generic-position statement rather than an estimate -- but genericity arguments say
nothing about the single point `zeta`, which is the classical objection, and the counting version
(`N(T) - N_0(T) ≥ 2·#off-line pairs`) is Levinson's territory and known.

[ATTACKED AND DROPPED] A conjecture that off-line displacement `delta` forces a sign-change gap of `Z`
of length `≫ delta` is refuted by configuration: on-line zeros at `gamma ± epsilon` with an off-line
pair at ordinate `gamma` is not excluded by anything, and `epsilon` is unrelated to `delta`.

### 104.3 Honest position

Every conjecture I could generate this turn reduced, on attack, to a known target (Levinson
saturation, `LI`, zero-density, Weil positivity). That is itself the finding: **at this frontier the
reachable statements are known, and the unreachable ones are unreachable because zeta supplies only
one non-self-dual input -- the Euler product -- whose transport range is `c/log t`.**

So the next real question is not another criterion but:

> **What is a second, independent, non-self-dual arithmetic input?**

Not the functional equation (self-dual, §104.2). Not the explicit formula (residue-only, §98). Not
positivity of `Λ` alone (saturates at `1 - c/log t`). Candidates worth a genuine literature audit
before any further construction: the pair-correlation/moment structure of `zeta` (independent of both
FE and Euler), the `Λ`-values' multiplicative *independence* across primes rather than their
positivity, and the second-order structure of `Φ` (Pólya's kernel), which is a formation-level object
not yet used anywhere in this card.

This card's analytic branch is closed. Continuing it would produce more correct, worthless theorems.

## Cross-confirmation from the pair-correlation and Gaussian-width lanes (2026-09-08, appended by a parallel session)

Two worst-case detection thresholds computed independently of this card (STATUS CANNOT-332, CANNOT-333;
cards `offline-isolation-dichotomy.md`, memory `gaussian-width-dictionary`) are instances of the `1/δ` law
with the scale identified:

- **Height-centered Gaussian family** `e^{−w(t−c)²}`, `c ≈ γ`. An *isolated* zero at displacement `δ` is seen at
  width `w ≍ log log γ / δ²` (amplitude-limited: `e^{wδ²}` must beat the on-line background `log γ/√w`), which
  is smaller than `1/δ`. The *worst configuration* — a tapered arithmetic-progression block of spacing
  `2π/((1+Δ) log γ)` with an analytic displacement profile — is invisible until the first Poisson alias
  `e^{(1+Δ)δ log γ − ((1+Δ) log γ)²/(4w)}` reaches `O(1)`, i.e. `w ≍ (log γ)/(4δ)`. So the family's worst-case
  detection parameter is `λ_detect ≍ (log γ)/(4δ)`: the `1/δ` law with scale `(log γ)/4`.
- **Montgomery pair form** at scale `x = T^α` (bandwidth `α ≤ 1`). The same tapered block is invisible at every
  `α ≤ 1`; it is first seen at `log x ≥ (1+Δ) log T` with `Δ ≥ 2δ₀√α/w`, i.e. `α_detect − 1 ≍ δ`: here the
  parameter is a *frequency excess* proportional to `δ` rather than `1/δ`, because the pair form's growth in
  the displacement is `x^{δ}` (exponential type) rather than the Gaussian's `e^{wδ²}`.

Both agree with §1: detection needs the alias/complex-growth term, never the harmonic main term. The
prime-side cost is `e^{w}` (Gaussian) or `T^{1+Δ}` (pair form) in prime length, which is the wall recorded
in CANNOT-332. The isolated-zero threshold `log log γ/δ²` shows the law's exponent is family- and
configuration-dependent; the uniform statement holds for the worst configuration.
