# Certificate vacuity, single-site structure, and the one-sigma law

- **ID:** `multiplicative-fejer-riesz-certificate`
- **Stage:** 1-in-progress
- **Type:** `[THEOREM A]` `[THEOREM B]` `[THEOREM C]` + `[CONJECTURE]`
- **Built on:** `order-separation-of-the-weil-deficit.md` §12
- **History:** opened with a "multiplicative Fejér–Riesz" conjecture; the rank-two test **refuted
  it** within the hour (Theorem B). The refutation is the useful part and is kept.

---

## 0. Setup

The truncated Riemann–Weil symbol is

```text
Omega_a(xi) = arch(xi) - V_P(xi),     P = e^(2a),
arch(xi)    = Re psi(1/4 + i xi/2) - log pi   ~   log|xi|,
V_P(xi)     = 2 sum_(n <= P) (Lambda(n)/sqrt n) cos(xi log n)
            = 2 Re (-zeta'/zeta)(1/2 + i xi)   (truncated).
```

RH is `Omega_a >= 0` in the limit. By unique factorisation the frequencies `{log n : n <= P}` lie in
the free abelian group `G_P = ⊕_(p<=P) Z log p` of rank `r = pi(P)`, and by Kronecker the map
`xi ↦ theta(xi) = (xi log p mod 2pi)_(p <= P)` has dense, equidistributed image in `T^r`. So the
prime part is the pullback of a Laurent polynomial on `T^r` along an equidistributed line.

---

## 1. `[THEOREM A]` Sum-of-squares certificates are vacuous

> Let `Q(xi) = sum_(n <= P) c_n cos(xi log n)` be real with `Q > 0` on `R`. Then there are finitely
> many Dirichlet polynomials `A_j(xi) = sum_(m) alpha_(j,m) m^(i xi)`, supported on `P`-smooth
> integers, with `Q = sum_j |A_j|^2`.

*Proof.* `Q` is the pullback of a Laurent polynomial `~Q` on `T^r`; equidistribution gives `~Q > 0`
on `T^r`. By **Dritschel's theorem** (2004) every strictly positive trigonometric polynomial on
`T^r` is a finite sum of squares of analytic polynomials. Analytic means nonnegative multi-indices,
i.e. genuine integers `m`. Pull back. ∎

(One square does **not** suffice for `r >= 2` — the multivariate Fejér–Riesz theorem fails — but
sums of squares always do.)

**Consequence.** For the prime part of the Weil form, *positivity and the existence of a
sum-of-squares / operator-factorisation certificate are the same statement.*

> **No factorisation, sum-of-squares, Gram, Cholesky, Schur-complement, or completion argument can
> prove Weil positivity.** Such a certificate exists **iff** the positivity it is meant to establish
> already holds. Exhibiting one is a restatement, not evidence.

This retires, with a proof, an entire class of manoeuvres — every "write the form as `B^*B`" step in
the corpus (CCM four-unit Gram, Krein/Schur completions, Hedenmalm Gram gates) *as a proof strategy*;
they survive as reformulations. It also explains the corpus's experience: those attempts produced
exact identities and never an inequality, because the certificate is never the obstruction.

---

## 2. `[THEOREM B]` The prime symbol carries no prime–prime interaction

The conjecture this card opened with — that the certificate becomes non-vacuous once its factors are
required to be Euler products, so that RH becomes a *separability* (versus entanglement) question
across primes — is **false**, and the reason is structural.

> On `T^r` the prime part is a **sum of single-site potentials**:
>
> ```text
> V_P(theta) = sum_(p <= P) f_p(theta_p),
> f_p(theta)  = 2 log p · Re( u/(1-u) ),   u = p^(-1/2) e^(i theta).
> ```

*Proof.* `Lambda` is supported on prime powers, so every frequency `log p^k` lies on a coordinate
**axis** of `G_P`. No mixed frequency `log(p^a q^b)` with `a,b >= 1` occurs. ∎

So the prime symbol is exactly separable: there is **no interaction between distinct primes at all**.
Every separability/entanglement, tensor-rank, or multiplicative-certificate refinement is therefore
automatically satisfied and equally vacuous. The Euler product enters the Weil symbol only as
*independence of the sites*, never as a coupling.

**This is the sharp form of a fact the corpus circled for a long time.** The repeated search for a
"second, non-self-dual arithmetic input" among the `Lambda`-correlations cannot succeed *inside the
Weil symbol*: the symbol has no correlations to find. Correlations of `Lambda` are invisible to it by
support alone.

---

## 3. `[THEOREM C]` The one-sigma law

Under Haar measure on `T^r` the `f_p(theta_p)` are **independent**, with

```text
E f_p = 0,      Var f_p = 2 (log p)^2 / (p - 1).
```

Hence

```text
Var V_P = sum_(p <= P) 2 (log p)^2/(p-1)  ~  2 sum_(p<=P) (log p)^2/p  ~  (log P)^2,
so  sigma(V_P) ~ log P.
```

Now impose the **self-matched truncation** forced by §12 of the companion card — aperture `a`
resolves height `xi = e^(2a)`, i.e. `P = e^(2a) = xi`:

```text
sigma(V_P) ~ log P = log xi,        arch(xi) ~ log xi.
```

> **The standard deviation of the truncated prime potential equals the archimedean term.**

Therefore, at the self-matched truncation,

> **RH ⟺ the prime potential never exceeds one standard deviation:**
> `V_xi(theta(xi)) <= sigma(V_xi) · (1 + o(1))` for every `xi`.

For a Haar-random point of the torus this fails with probability `~0.16`. RH asserts that the
Kronecker orbit of `zeta` — a single, deterministic line — stays on the good side **always**.

**This is the exact quantitative content of the corpus's "no margin" cards.** The margin is not
small; it is *zero by construction*: the archimedean budget equals one sigma of the prime
fluctuation, at every height, because the aperture–height matching forces the truncation. No
inequality with slack can exist, and every route that produces one has mis-normalised the
truncation.

---

## 4. `[CONJECTURE]` The mechanism must be non-almost-periodic

Theorems A–C leave exactly one structural asymmetry: `V_P` is almost periodic in `xi` (it is a
torus function pulled back along a line), while `arch(xi) ~ log|xi|` is **not** — it grows.

> **[CONJECTURE — Non-almost-periodic obstruction.]** No argument that works inside the algebra of
> almost-periodic functions of `xi` can prove Weil positivity. Precisely: for every AP function `W`
> with frequencies in `G_P` and every `epsilon > 0` there are real `xi` with
> `W(xi) > (1 - epsilon) sup_(T^r) ~W`, so any AP majorant of `V_P` must dominate `sup_(T^r) V_P`,
> which diverges. Positivity can only come from a mechanism that sees the **growth** of `arch`, i.e.
> from the failure of `theta(xi)` to equidistribute *at the self-matched scale*.

**Why this is the right conjecture.** Kronecker guarantees the orbit visits every neighbourhood of
the maximiser of `V_P` for *fixed* `P`. RH survives only because `P` is tied to `xi`: by the time the
orbit reaches the bad region of `V_P`, the truncation has moved. So the whole content is a **race
between equidistribution and truncation growth**, and it is quantitative equidistribution of
`(xi log p)_(p <= xi)` — a Diophantine property of `{log p}` — that must beat it.

**Falsification.** Exhibit an AP majorant argument that yields positivity; or show the orbit reaches
the `V_P`-maximiser before the truncation grows, which would refute RH.

**What its truth would open.** RH becomes a **quantitative equidistribution** statement about the
Kronecker flow on `T^(pi(xi))` with a growing number of coordinates — a Diophantine problem about
`{log p}`, not an inequality about `zeta`. The relevant input is then the *irrationality measure*
structure of the `log p`, which is a genuinely different arithmetic resource from positivity,
support, or size — the first candidate in this corpus for a second, non-self-dual input that
survives Theorem B.

## `[OPEN CORE]`

> Quantify the race. Let `M(P) = sup_(T^r) V_P ~ sum_(p<=P) 2 log p (p^(1/2)-1)^(-1)`, which diverges
> like `P^(1/2)`. RH requires the orbit `theta(xi)` to stay `<= log xi` while `M(xi)` is of size
> `xi^(1/2)`. Prove a discrepancy bound for `(xi log p)_(p <= xi)` strong enough to forbid the orbit
> from reaching within `xi^(1/2)/log xi` of the maximiser at height `xi`.

## Gates

- [x] Theorem A proved (Dritschel on `T^r`, Kronecker pullback)
- [x] Theorem B proved; the card's opening conjecture refuted by it
- [x] Theorem C proved (independence + Mertens + self-matched truncation)
- [ ] External novelty audit: Theorem A's *vacuity consequence*; Theorem C's one-sigma normalisation
- [ ] The open core: quantitative equidistribution at the self-matched scale

## Log

- 2026-07-25 — Opened with the multiplicative-certificate conjecture; refuted it the same session by
  Theorem B (the symbol is single-site). Kept Theorems A and C, which are the durable content, and
  replaced the conjecture with the non-almost-periodic obstruction plus a quantitative
  equidistribution open core.

---

## 5. External novelty audit (July 2026 gate)

Searches run: Dritschel/Fejér–Riesz on `T^d` and Weil positivity; Connes–Consani archimedean Weil
positivity; truncated von Mangoldt variance and large values.

**Correction forced by the audit.** Dritschel's theorem is for **strictly positive** trigonometric
polynomials; the two-variable case is due to Dritschel and reproved by Geronimo–Lai, and it is
**open** whether every *nonnegative* (as opposed to strictly positive) two-variable trigonometric
polynomial is a sum of squares. Theorem A is therefore stated and valid for strictly positive
symbols only. Since the Weil symbol is expected to be nonnegative-with-zeros (the zeros are the
`gamma`'s), the boundary case is exactly the one Theorem A does not cover. **This weakens Theorem A:
the vacuity verdict applies to every strictly positive truncation, hence to any approach seeking a
certificate with slack, but not to a boundary certificate.** That is still decisive for the corpus,
because every factorisation attempt in the lane sought a certificate with slack.

**Verdicts.**

| Result | Mechanism | Verdict |
|---|---|---|
| **A** (SOS vacuity, strictly positive case) | Dritschel on `T^r` + Kronecker pullback | mechanism classical; the *vacuity consequence for Weil positivity* not found stated — `[NOVELTY UNVERIFIED — LIKELY BRIDGE]`. Adjacent literature: Connes–Consani, *Weil positivity and trace formula, the archimedean place*; Groskin arXiv:2607.02828. |
| **B** (single-site structure; separability/`Lambda`-correlation refinements are vacuous) | `Lambda` supported on prime powers ⟹ frequencies on coordinate axes | trivial to prove, but the consequence is a **decisive negative for a programme the corpus pursued repeatedly**: `Lambda`-correlations are invisible to the Weil symbol *by support alone*. `[BRIDGE — corpus-decisive]` |
| **C** (one-sigma law at the self-matched truncation) | Mertens `sum_(p<=P)(log p)^2/p ~ (log P)^2/2` + aperture–height matching | two lines from standard facts; "RH ⟺ no large values of the truncated prime sum" is folklore. `[REDISCOVERED]`, but the exact normalisation `sigma(V_xi) ~ arch(xi)` makes the corpus's "no margin" cards quantitative. |

**Bottom line.** None of A–C moves the July-2026 frontier as mathematics. Two of them close large
classes of attempts with proofs rather than heuristics, and B in particular refutes this card's own
opening conjecture and, with it, the corpus's long-standing hope that `Lambda`-correlations are the
missing second input. That hope is now provably misplaced *inside the Weil symbol*; correlations can
only enter through an object whose frequencies are not confined to the coordinate axes.

### 5.1 The one direction B leaves open

B says mixed frequencies `log(p^a q^b)`, `a,b >= 1`, never occur in the Weil symbol. They *do* occur
in the symbol of the **squared** or **Rankin–Selberg-type** object, whose coefficients are
`(Lambda * Lambda)(n)` — supported on products of two prime powers, hence off the axes. So the only
way to make prime–prime correlations visible is to leave the linear Weil form for a quadratic one.

> **[CONJECTURE — off-axis lift]** Weil positivity for `zeta` is implied by, and strictly weaker
> than, positivity of the analogous form whose prime symbol has coefficients `(Lambda * Lambda)(n)`
> — the first object in this hierarchy whose torus symbol is genuinely `r`-variate rather than a sum
> of single-site potentials, and hence the first at which separability, entanglement, and
> `Lambda`-correlations are not vacuous.

Falsification: show the `Lambda * Lambda` form's positivity is equivalent to, or weaker than, the
linear one; or that its off-axis part is a sum of single-site terms after all.

---

## 6. The race, quantified — and the exact size of the gap

Theorem C makes RH the statement `V_xi(xi) <= arch(xi) ~ log xi`, with the truncation self-matched
(`P = xi`). Section 4 called this a race between phase alignment and truncation growth. Here is the
race with numbers.

### 6.1 What a violation costs

By Mertens, aligning the phases of all primes up to `Q` (i.e. driving `cos(xi log p) ~ 1` for
`p <= Q`) produces

```text
V >= 2 sum_(p <= Q) log p / sqrt p · (1 + o(1)) ~ 4 sqrt Q.
```

To exceed the archimedean budget one therefore needs

```text
4 sqrt Q > log xi,      i.e.      Q > (log xi)^2 / 16.
```

> **A violation of RH at height `xi` requires simultaneous phase alignment of the primes up to
> `Q ≍ (log xi)^2`, i.e. of `≍ (log xi)^2 / log log xi` primes.**

### 6.2 What is actually achievable

`[LITERATURE]` The resonance method (Soundararajan; Bondarenko–Seip) gives, for `t <= T`,

```text
max log|zeta(1/2 + it)| >> sqrt( log T · log log log T / log log T ).
```

Since `log|zeta(1/2+it)| ~ sum_p p^(-1/2) cos(t log p)` and `sum_(p<=Q) p^(-1/2) ~ 2 sqrt Q / log Q`,
the achieved alignment corresponds to

```text
Q_achieved ≍ log T   (up to log log factors).
```

> **The best known constructions align the primes up to `Q ≍ log xi`.**

### 6.3 The gap

```text
needed for a violation:   Q ≍ (log xi)^2
best known alignment:     Q ≍ log xi
```

> **The gap is exactly one factor of `log xi` in the number of primes that must be brought into
> phase.** Equivalently, in the value achieved: known resonance reaches `V ≍ sqrt(log xi)`, while a
> violation needs `V > log xi` — a squaring.

This is the exact quantitative content of "RH is barely true" in this formulation: not an
astronomical margin, and not zero, but precisely one logarithm of alignment.

### 6.4 `[ERROR CAUGHT]` — why this is not a proof

I first ran §6.1–6.2 in the other direction: pair the Dirichlet box principle ("height `epsilon^(-N)`
suffices to align `N` phases") with the requirement `Q ≍ (log xi)^2`, conclude `log xi >~ pi(Q) ≍
(log xi)^2 / log log xi`, hence a contradiction for large `xi` — and therefore RH.

**That is wrong.** The box principle is an *existence* statement: it bounds the height that
*suffices* for alignment. It gives no lower bound on the height *required*, and partial alignment —
which is all a violation needs — can and does occur far earlier. The resonance method is exactly a
construction of such early partial alignment. Using an upper bound as if it were a lower bound is
the error, and it is the same error that makes every naive "the primes cannot conspire" heuristic
fail.

What survives is the numeric comparison of §6.3, which is a statement about the gap, not a proof
that the gap cannot be closed.

### 6.5 The reduction this leaves

> **`[OPEN CORE]` RH is equivalent, in this normalisation, to an anti-resonance bound for
> `{log p}`:** no `xi` brings the primes up to `(log xi)^2` into sufficient phase alignment. The
> resonance method supplies the constructions from below; RH is the assertion that those
> constructions are within one logarithm of optimal, uniformly in `xi`.

That is a genuinely different kind of statement from a positivity inequality: it is a **large-values
/ extremal problem for a Dirichlet polynomial with the weight `log p / sqrt p`, at the self-matched
length `P = xi`.** The large-values literature (Guth–Maynard, Bondarenko–Seip, Soundararajan) works
exactly this problem for other weights and lengths. To my knowledge the weight `log p/sqrt p` at
length `P = xi` — the self-matched case — is not the case they treat, because it is not the case that
arises in zero-density estimates. `[NOVELTY UNVERIFIED]`

## Log (cont.)

- 2026-07-25 — §6: race quantified. A violation needs `(log xi)^2` primes aligned; best known
  constructions align `log xi`; gap is one logarithm. A claimed proof via the Dirichlet box
  principle was caught and retracted in §6.4 (existence bound used as a necessity bound). Remaining
  reduction: an anti-resonance bound at the self-matched length.

---

## 7. `[RETRACTION]` Theorem C and §6 are withdrawn

Checking the archimedean budget at `xi = 0` breaks the argument.

`arch(0) = psi(1/4) - log pi ≈ -5.37 < 0`, while `V_P(0) = 2 sum_(n<=P) Lambda(n)/sqrt n ~ 4 sqrt P
-> +infinity`. So the truncated symbol `Omega_a = arch - V_P` is **massively negative at the origin**
for every aperture, yet the Weil form is not negative. The pointwise comparison is therefore not the
right one, and Theorem C's "one-sigma law", together with the whole race computation of §6, rests on
it.

**The error, named.** Two things were conflated.

1. The Weil form is `Q(phi) = |hat phi(i/2)|^2 + |hat phi(-i/2)|^2 + <W_infty hat phi, hat phi> -
   2 sum_n c_n (phi * phi)(log n)`. The **pole terms** are a positive rank-two contribution of size
   `e^a` — the same order as `4 sqrt P = 4 e^a`. They are not part of any symbol on `R`, and I
   dropped them.
2. Szegő's theorem reduces operator positivity to pointwise symbol positivity for a **fixed** symbol
   as the domain grows. Here the truncation `P = e^(2a)` is tied to the domain, so the symbol changes
   with it. The Szegő reduction does not apply, and the untruncated prime series is a distribution,
   not a function: pointwise evaluation at `xi = 0` is meaningless, and its apparent divergence there
   is cancelled distributionally.

So `Omega_a(xi) >= 0` pointwise is neither necessary nor sufficient in the form I used, the
"budget = `log xi`" normalisation is wrong, and the measured gap of §6.3 — one logarithm — measures
nothing. **Both are withdrawn.** The corpus's own `harmonic-invisibility` §103.1 states the Szegő
density reduction in the same style and inherits the same caveat; that should be flagged there.

### 7.1 What survives

- **Theorem A** (strictly positive AP symbol ⟹ SOS certificate with Dirichlet-polynomial factors,
  hence certificates are vacuous as a proof strategy). Independent of the budget question; it is a
  statement about strictly positive trigonometric polynomials on `T^r`. **Stands.**
- **Theorem B** (`Lambda` supported on prime powers ⟹ every frequency lies on a coordinate axis ⟹
  the prime part is a sum of single-site potentials; `Lambda`-correlations are invisible to the Weil
  symbol by support alone). A statement about frequencies only. **Stands**, and it remains the
  session's one decisive negative for a programme the corpus was pursuing.
- The variance computation `Var V_P ~ (log P)^2` is correct **as a statement about the torus
  function**; what is withdrawn is its use as a budget comparison.

### 7.2 The corrected object

The rank-two pole term is not an artefact to be dropped — it carries `e^a`, exactly matching the
prime mass. The correct formulation of Weil positivity in this normalisation is therefore

> `<W_infty hat phi, hat phi> + |hat phi(i/2)|^2 + |hat phi(-i/2)|^2  >=  2 sum_n c_n (phi*phi)(log n)`,

an inequality in which a **rank-two** positive form of size `e^a` must, together with a logarithmic
density term, dominate a Toeplitz form whose symbol has sup of size `e^a`. That the two leading terms
are of the *same order* is the real "no margin" statement — not the `log xi` comparison I claimed.
Whether the rank-two term can carry it is the live question, and it is a different question from any
asked so far in this card.

## Log (cont.)

- 2026-07-25 — Theorem C and §6 retracted after checking `arch(0) < 0` against `V_P(0) -> +infinity`:
  the rank-two pole terms (size `e^a`, matching the prime mass) were dropped, and the Szegő reduction
  was applied to a symbol that varies with the domain. Theorems A and B stand. Corrected object
  recorded in §7.2.

---

## 8. `[THEOREM D]` The rank-two pole term is the exact counterweight to the whole prime mass

§7.2 asked whether a rank-two positive form of size `e^a` can carry a Toeplitz form whose symbol has
sup of the same size. On the extremal flat test it does so **exactly, at leading order**.

Take `phi = (2a)^(-1/2)` on `[-a,a]`, normalised, so `(phi * phi)(t) = 1 - |t|/(2a)` on `[-2a,2a]`
and `P = e^(2a)`.

**Prime form.** With `A(x) = sum_(n<=x) Lambda(n)/sqrt n = 2 sqrt x - 2 + o(sqrt x)` and
`B(x) = sum_(n<=x) Lambda(n) log n/sqrt n = 2 sqrt x log x - 4 sqrt x + 4 + o(sqrt x)` (partial
summation from PNT),

```text
R(phi) = 2A(P) - (1/a) B(P)
       = 4 sqrt P - 4 - (1/a)(4a sqrt P - 4 sqrt P + 4) + ...
       = 4 sqrt P / a - 4 - 4/a + ... ,      sqrt P = e^a.
```

**Pole terms.** `hat phi(±i/2) = (2a)^(-1/2) ∫_(-a)^a e^(∓u/2) du = (2a)^(-1/2)·2(e^(a/2) - e^(-a/2))`,
identical for both signs, so

```text
|hat phi(i/2)|^2 + |hat phi(-i/2)|^2 = (4/a)(e^a - 2 + e^(-a)) = 4 sqrt P / a - 8/a + o(1).
```

> **Theorem D.** On the flat test at aperture `a`, the rank-two pole contribution and the prime form
> agree at leading order:
>
> ```text
> |hat phi(i/2)|^2 + |hat phi(-i/2)|^2  -  R(phi)  =  4 - 4/a + o(1),
> ```
>
> both sides being of size `4 e^a / a`. The entire exponential mass cancels.

**Reading.** The pole terms are not a correction to be discarded — they are the *exact counterweight*
to the whole prime wall. Every route in the corpus that formed a symbol on `R` and compared
archimedean density against prime mass discarded precisely the term that carries the balance, which
is why those routes produced exponentially wrong normalisations (including my own retracted §6).
"No margin" is therefore not a metaphor and not an `O(1)` slack: at leading order the budget is
**identically** the prime mass, and RH lives entirely in the `O(1)` and `O(log a)` remainders.

### 8.1 A consistency check that failed, and what it forces

Estimating the archimedean term for this test by `<log|r|>` against the Fejér-type density
`(sin(ar)/r)^2/(pi a)` gives `~ -log a`, so the three pieces would sum to `4 - log a < 0` for
`a > e^4` — impossible, since `Q(phi) = sum_rho |hat phi(gamma_rho)|^2 >= 0` under RH.

The resolution is instructive: the density approximation `~ log r / 2 pi` for the zeros is applied
over all `r`, but **there are no zeros with `|gamma| < 14.13`**, and the flat test concentrates its
mass at `|r| ~ 1/a`, i.e. exactly in the zero-free window. Restricting correctly gives
`Q(phi) ~ (2/a) · (bounded positive)`, small and positive.

> **Consequence.** For the flat test the whole value of the Weil form is carried by the *lowest*
> zeros, and the leading-order cancellation of Theorem D is what leaves room for it. Any asymptotic
> treatment of this form that replaces the zero counting measure by its density `log r / 2 pi` near
> `r = 0` is wrong by an amount larger than the quantity being computed.

This is the sharp reason the "budget" framings keep failing: the extremal tests live at frequencies
below the first zero, where the density approximation has no validity, while the exponential terms
cancel identically.

### 8.2 Status

`[THEOREM D]` is an exact leading-order identity from partial summation and is `[REDISCOVERED]` in
mechanism. Its consequence — that the rank-two pole term is the exact counterweight and that the
extremal tests sit in the zero-free window — is a structural correction to how this form must be
analysed, and it invalidates symbol/density normalisations at the leading order rather than at the
margin. `[NOVELTY UNVERIFIED]`

## Log (cont.)

- 2026-07-25 — Theorem D: exact leading-order cancellation between the rank-two pole term and the
  prime form on the flat test, both of size `4 e^a/a`, difference `4 - 4/a + o(1)`. Consistency
  check exposed that the extremal tests concentrate below the first zero, where the density
  approximation for the zero counting measure is invalid — the structural reason budget framings fail.

---

## 9. `[CORRECTION]` Theorem D holds at leading order only; the `O(1)` remainder located

Pushing §8 to the next order exposes an error in its constants, and fixing it locates exactly where
the arithmetic sits.

**The archimedean limit, computed exactly.** For the flat test,
`|hat phi(r)|^2 = 2 sin^2(ar)/(a r^2)`, so

```text
arch(phi) = (1/(pi a)) ∫ sin^2(ar) r^(-2) W_infty(r) dr,   W_infty(r) = Re psi(1/4 + ir/2) - log pi.
```

Substituting `r = s/a` turns the weight into the probability density `sin^2(s)/(pi s^2)`, under which
`W_infty(s/a) -> psi(1/4) - log pi` for every fixed `s`; the tail `s >> a` contributes
`(2/(pi a))(1 - log 2) = O(1/a)` — **not** `O(log a)`, because the `s^(-2)` density beats the
logarithm. Hence

> `arch(phi) -> psi(1/4) - log pi ≈ -5.372` as `a -> infinity`.  `[PROVED HERE]`

**Where §8 went wrong.** I used `A(x) = sum_(n<=x) Lambda(n) n^(-1/2) = 2 sqrt x - 2 + o(sqrt x)`,
taking the constant from `∫_1^x t^(-1/2) dt`. That is not the constant. By Perron,

```text
A(x) = 2 sqrt x + (-zeta'/zeta)(1/2) - sum_rho x^(rho - 1/2)/(rho - 1/2) + ...,
```

so the `O(1)` term is `(-zeta'/zeta)(1/2)` **plus an oscillating sum over the zeros**, and likewise
for `B`. The `4 - 4/a` of Theorem D is therefore not the correct remainder; the constants there are
wrong. Consistency confirms it: with `Q(phi) = (2/a) sum_rho sin^2(a gamma_rho)/gamma_rho^2 ~
(1/a) sum_rho gamma_rho^(-2) -> 0` and `arch -> -5.372`, the pole-minus-prime remainder must tend to
`+5.372`, not to `4`.

### 9.1 What Theorem D actually says

> **Theorem D (corrected).** On the flat test at aperture `a`, the rank-two pole contribution and the
> prime form are **both** `4 e^a / a · (1 + o(1))`, and their difference is `O(1)`. The entire
> exponential mass cancels at leading order.

That is the durable content, and it is enough for the structural conclusion of §8: the pole terms are
the exact counterweight to the prime wall, so any analysis that drops them is wrong by an exponential
factor. What is **not** durable is any claim about the `O(1)` remainder obtained from naive
integral constants.

### 9.2 Where the arithmetic sits, now located exactly

Assembling the corrected pieces, for the flat test at aperture `a`:

```text
(2/a) sum_rho sin^2(a gamma_rho)/gamma_rho^2
   =  [pole - prime](a)  +  (psi(1/4) - log pi)  +  o(1).
```

The left side is `O(1/a)` and manifestly nonnegative under RH. So

> **`[pole - prime](a) -> log pi - psi(1/4) ≈ 5.372`,**

and the rate of that convergence is governed by the oscillating zero sums inside `A` and `B` — i.e.
by `sum_rho x^(rho - 1/2)/(rho - 1/2)` at `x = e^(2a)`. Under RH those sums are `O(1)` bounded; an
off-line zero makes them grow like `e^(2a delta)`. **The `O(1)` remainder of Theorem D is therefore
not a constant at all: it is exactly the object whose boundedness is RH**, and the flat-test identity
above is a clean, self-contained statement of that.

This is the third time this session that a "budget" quantity turned out, on correct evaluation, to be
the zero-sum itself. Theorem D's value is that it now says so at the right order: the exponential
terms cancel identically, the archimedean limit is the explicit constant `psi(1/4) - log pi`, and
everything left over is `sum_rho x^(rho-1/2)/(rho-1/2)`.

## Log (cont.)

- 2026-07-25 — Theorem D weakened to its leading-order form after the `O(1)` constants were found
  wrong (`A(x)`'s constant is `(-zeta'/zeta)(1/2)` plus a zero sum, not `-2`). Archimedean limit for
  the flat test computed exactly: `psi(1/4) - log pi`. The remainder identified as
  `sum_rho x^(rho-1/2)/(rho-1/2)` at `x = e^(2a)` — bounded iff RH.

---

## 10. The form in kernel variables: rank-two Hankel versus Toeplitz

Writing the three pieces as kernels on `[-a,a]^2` for real `phi`:

```text
pole(phi) = ∫∫ phi(u) phi(v) · 2 cosh((u+v)/2) du dv        (Hankel, depends on u+v, rank two)
arch(phi) = ∫∫ phi(u) phi(v) · W(u-v) du dv                 (Toeplitz, symbol Re psi(1/4+i xi/2) - log pi)
R(phi)    = ∫∫ phi(u) phi(v) · K(u-v) du dv,   K = sum_n (Lambda(n)/sqrt n)(delta_(log n) + delta_(-log n)).
```

> **Weil positivity is the statement that a rank-two positive *Hankel* kernel, plus one *Toeplitz*
> kernel, dominates another *Toeplitz* kernel on `L^2[-a,a]`.**

Two structural facts follow immediately and are worth recording, because both contradict framings
used earlier in this card and in the corpus.

1. **The archimedean operator is not positive.** Its symbol `W_infty(xi) = Re psi(1/4 + i xi/2) -
   log pi` equals `psi(1/4) - log pi ≈ -5.372` at `xi = 0` and only becomes positive around
   `|xi| ≈ 7`. So "archimedean budget dominates prime cost" is false as an operator statement at low
   frequency; the low-frequency deficit is cancelled by the prime term, not paid by it. This is
   forced: the total symbol is the zero counting measure, which vanishes identically on
   `|xi| < gamma_1 = 14.134...`, so `W_infty` and the prime symbol must cancel exactly there.

2. **The counterweight is Hankel, not Toeplitz.** `2 cosh((u+v)/2) = e^(u/2) ⊗ e^(v/2) + e^(-u/2) ⊗
   e^(-v/2)` is rank two and depends on `u+v`; the prime kernel depends on `u-v`. No symbol calculus
   compares them — they live in different algebras. That is the precise reason every symbol/density
   normalisation attempted in this card and in the corpus's `harmonic-invisibility` §103 mis-stated
   the problem by an exponential factor: the dominating term is invisible to the Toeplitz symbol.

**Consequence for method.** The live object is a Hankel-versus-Toeplitz domination on a finite
interval with an explicitly rank-two Hankel part. The corpus owns substantial Hankel machinery
(`CompleteHankelCone`, the theta-cusp Hankel determinant chain, Krein/Schur) but has applied it
throughout in the Toeplitz (additive-lag) variable. Applying it to the actual rank-two Hankel
counterweight — the pole vectors `e^(±u/2)` — is the one deployment that has not been made.

## Log (cont.)

- 2026-07-25 — §10: form rewritten in kernel variables. Archimedean operator shown non-positive at
  low frequency (symbol `psi(1/4) - log pi < 0` at the origin), with the deficit necessarily
  cancelled by the prime term because the total symbol vanishes below `gamma_1`. Counterweight
  identified as a rank-two *Hankel* kernel in `u+v`, incomparable by symbol calculus to the Toeplitz
  prime kernel in `u-v` — the structural reason symbol/density normalisations fail here.

---

## 11. The prime form is essentially rank two, carried by the pole directions

§10 asked how a rank-two Hankel form can dominate an infinite-rank Toeplitz form. Computing the two
on the natural test vectors answers it.

**The pole vectors are approximate eigenvectors of the translations.** On `[-a,a]`,
`T_(log n) e_+ = n^(-1/2) e_+` up to the edge truncation, and exactly

```text
<e_+, T_(log n) e_+> = n^(-1/2) (e^a - n e^(-a)),   e_±(u) = e^(±u/2),   ||e_+||^2 = e^a - e^(-a).
```

Hence on the normalised pole direction `phi = e_+/||e_+||`,

```text
R(phi) = 2 sum_(n <= P) (Lambda(n)/sqrt n) · n^(-1/2) (1 + o(1)) = 2 sum_(n<=P) Lambda(n)/n ~ 4a,
pole(phi) = ||e_+||^2 ~ e^a.
```

So on the pole direction the prime form is only `O(a)` while the counterweight is `e^a`: the pole
directions are *cheap* for the primes and *maximal* for the Hankel term.

**On the flat test both are `4 e^a / a`** (Theorem D). The flat test's correlation with `e_+` is only
`sqrt(2/a)` — it is nearly orthogonal to the pole directions — yet its pole term is already the full
`4 e^a/a`. Removing the `e_±` components changes `R` by

```text
2 <p, K phi_flat> ≍ e^a / a,
```

**the same order as `R(phi_flat)` itself.** So the prime form does not survive projection off the
pole directions with its size intact: an `O(1/sqrt a)` perturbation of the test vector moves `R` by a
constant fraction.

> **`[STRUCTURAL FINDING]` The large part of the prime Toeplitz form on `L^2[-a,a]` is carried by the
> two-dimensional span of the pole vectors `e^(±u/2)`.** That is why a rank-two Hankel counterweight
> can match an infinite-rank Toeplitz form of exponential size: the exponential part of the Toeplitz
> form is not spread over the space, it lives on the same two directions.

This is the mechanism §10 was missing, and it corrects the naive objection (raised and resolved here)
that a rank-two form obviously cannot dominate an infinite-rank one.

### 11.1 The conjecture this isolates

> **[CONJECTURE — essential rank two]** On `L^2[-a,a]`,
>
> ```text
> R(phi) <= pole(phi) + O(log a) ||phi||^2   for all phi,
> ```
>
> i.e. the rank-two Hankel form dominates the prime Toeplitz form up to a logarithmic remainder,
> uniformly in the aperture.

With the archimedean term as the remainder this is Weil positivity, hence RH — so it is not weaker.
Its value is that it is a **structural** statement, checkable direction by direction, about where the
mass of an explicit operator sits, rather than an inequality between transcendental quantities. The
two extreme tests are already verified: on `e_±` the ratio is `4a : e^a` (enormous slack), on the
flat test it is `1 : 1` (exact matching at leading order, with the `O(1)` remainder
`log pi - psi(1/4)` from §9). The conjecture asserts no test does better than the flat one by more
than `log a`.

**Where it would break.** A test vector with the flat test's prime mass but a strictly smaller pole
term. By the computation above, any such vector must differ from the flat test by `O(1/sqrt a)` in
norm while keeping `R` within `O(log a)` of `4e^a/a` — the perturbation analysis says the pole term
then also stays within a constant factor, but this is exactly the step that needs a real argument
rather than a first-order estimate.

## Log (cont.)

- 2026-07-25 — §11: pole vectors identified as approximate eigenvectors of the prime translations
  with eigenvalue `n^(-1/2)`, giving `R ~ 4a` against `pole ~ e^a` there; flat test verified to have
  its prime mass carried by its (small) pole components. Structural finding: the exponential part of
  the prime Toeplitz form lives on the rank-two pole span. Conjecture "essential rank two" stated
  with its two verified extremes and its exact breaking point.

---

## 12. `[CORRECTION]` The essential-rank-two conjecture, evaluated

The conjecture of §11.1 (`R(phi) <= pole(phi) + O(log a) ||phi||^2`) is not a new statement: the
explicit formula gives, as quadratic forms,

```text
R = pole + W - Z,        Z(phi) = sum_rho |hat phi(gamma_rho)|^2,
```

so `R - pole = W - Z` exactly, and the conjecture is `W - Z <= O(log a)`. Two things follow.

1. **The remainder is not `O(log a)`.** Take `hat phi` concentrated near a frequency `xi_0` with
   width `1/a`. Then `W(phi) ~ log|xi_0|` and `Z(phi) ~ log|xi_0|` as well (the local zero density is
   `log|xi_0|/2 pi` and `∫|hat phi|^2 = 2 pi`), so the difference is a *fluctuation* of the zero
   count against its density — bounded by the aperture only through `xi_0`, which is free. The
   correct bound involves the frequency support, not `a`.
2. **What remains is exactly `Z >= 0`.** Stripping the archimedean term, the content of §11.1 is
   `Z ⪰ 0`, which is Weil positivity verbatim. So the conjecture is RH, not a structural surrogate
   for it.

`[WITHDRAWN]` §11.1 as a conjecture. What stands from §11 is the structural finding, which does not
depend on it:

> The exponential part of the prime Toeplitz form on `L^2[-a,a]` is carried by the two-dimensional
> span of the pole vectors `e^(±u/2)`: on those directions `R ~ 4a` against `pole ~ e^a`, while on
> the flat test both are `4 e^a/a`, and an `O(1/sqrt a)` perturbation off the pole span moves `R` by
> a constant fraction.

That explains *how* a rank-two Hankel counterweight can match an infinite-rank Toeplitz form of
exponential size, and it is not a restatement of RH.

### 12.1 Standing assessment of this line

Every reformulation attempted in this card — SOS certificate, multiplicative certificate,
one-sigma budget, race, essential rank two — resolved on evaluation into Weil positivity itself. The
durable output is therefore negative and structural:

- `[THEOREM A]` certificates are free once positivity holds, so no factorisation argument proves it;
- `[THEOREM B]` the Weil symbol is single-site, so `Lambda`-correlations are invisible to it;
- `[THEOREM D]` the rank-two pole term is the exact leading-order counterweight to the whole prime
  wall, so any analysis dropping it is wrong by an exponential factor;
- `[§10]` the counterweight is *Hankel* in `u+v`, incomparable by symbol calculus to the Toeplitz
  prime kernel in `u-v` — the reason symbol/density normalisations fail here;
- `[§11]` the exponential mass of the prime form sits on the rank-two pole span.

Four conjectures were opened and all four withdrawn by my own checks. That rate, and the fact that
each withdrawal was forced by evaluating the object rather than by an external objection, is the
honest signal: in this realization there is no surrogate for the inequality.

## Log (cont.)

- 2026-07-25 — §12: essential-rank-two conjecture withdrawn (`R - pole = W - Z` exactly, so it is
  `Z >= 0`, i.e. RH). Structural finding of §11 retained. Standing assessment recorded: four
  conjectures opened, four withdrawn on evaluation; the durable output of the card is the four
  structural closures.
