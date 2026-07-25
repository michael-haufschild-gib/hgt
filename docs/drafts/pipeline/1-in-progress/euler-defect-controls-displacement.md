# Euler defect controls displacement

**Stage:** 1 — live conjecture, no proof.
**Predecessor:** `5-failed/downstream-functionals-of-the-zero-set.md` (§§90–104 of the harmonic-
invisibility card). That route died because every object built was a functional *of the zero set* and
so could only ever yield `RH ⟺ X`. This card is built to violate that: the statement below is about
**coefficients**, is a claim about a whole family, and has `RH` as one degenerate case rather than as
its content.

## Why this and not another criterion

Two facts pin the direction.

1. **Self-duality.** The functional equation makes the problem exactly self-dual, so a zero-free
   region on one side reflects to the other and always yields a *band*, never a line. It cannot
   select `Re rho = 1/2`.
2. **Davenport–Heilbronn.** [LITERATURE] The Epstein/DH Dirichlet series have zeta-type functional
   equations, no Euler product, and provably possess zeros off the critical line. So the functional
   equation alone is *demonstrably insufficient*, and multiplicativity is the ingredient that puts
   zeros on the line.

Everything in the literature I am aware of treats this qualitatively — "Euler product ⟹ RH" as the
Selberg-class heuristic. The question nobody seems to have posed is the **quantitative** one.

## The Euler defect

For a Dirichlet series `L(s) = Σ a_n n^{-s}` with `a_1 = 1`, write its logarithmic derivative

  `-L'/L (s) = Σ_{n ≥ 2} b_n n^{-s}`.

`L` has an Euler product **iff** `b_n` is supported on prime powers. Define the **Euler defect**

  `d(L) := Σ_{n not a prime power} |b_n| n^{-1/2}`,

the mass of the log-derivative's coefficients sitting off the prime powers, weighted at the critical
abscissa. `d(L) = 0` exactly when `L` has an Euler product.

## The conjecture

> **[CONJECTURE — Euler Defect Bound]** There is a class `S₁` of degree-one Dirichlet series with a
> zeta-type functional equation and polynomially bounded coefficients, and an increasing function
> `F : [0,∞) → [0,1/2]` with `F(0) = 0`, such that for every `L ∈ S₁`
>
>   `sup { |Re rho - 1/2| : L(rho) = 0, 0 < Re rho < 1 } ≤ F(d(L))`.
>
> **Strong form:** `F` may be taken linear near `0`, i.e. displacement `≍ d(L)` for small defect.

This is *not* a reformulation of RH. It asserts a **uniform** relation across a family; RH is the
single point `d = 0`. It could be false while RH is true (if some `L` with small defect has a zero
far off the line), and its truth would prove RH.

## What is genuinely unknown to me

I do not know whether this is true, and I do not believe it can be settled by literature search:
the quantity `d(L)` is not, as far as I am aware, a studied invariant, and the DH literature
establishes *existence* of off-line zeros without relating their displacement to any measure of
non-multiplicativity.

## Consistency check already performed (by reasoning, not computation)

Take `L_eps = zeta + eps·g` with `g` sharing zeta's functional equation and not multiplicative.
Then `d(L_eps) = O(eps)`. For `eps` small, `|zeta| >> eps|g|` away from zeta's zeros, so no new zeros
appear; near each zero `rho_0` of zeta, Rouché moves the zero by `O(eps)`. Hence

  `displacement(L_eps) ≤ displacement(zeta) + O(eps) = displacement(zeta) + O(d(L_eps))`.

So in the perturbative regime the conjecture holds **with linear `F`**, provided `displacement(zeta)`
is itself `0` — i.e. the perturbative regime is consistent with the strong form and cannot refute it.
This is a genuine constraint on `F`: any `F` must be at least linear near `0`, and the conjecture's
content lives entirely in the **non-perturbative** regime `d = O(1)`, which is exactly where DH sits.

## Falsification tests, in order

1. **DH displacement.** For the Davenport–Heilbronn family (a one-parameter combination of two
   Dirichlet `L`-functions with a common functional equation), compute `d` and the actual off-line
   displacement as the parameter varies. If displacement stays bounded away from `0` while `d → 0`
   along some sub-family, the conjecture is **dead**. This is the decisive test and it is finite.
2. **Degenerate limits.** At parameter values where the DH combination degenerates to a single
   Dirichlet `L`-function, `d → 0` and the conjecture demands displacement `→ 0`. Does the off-line
   zero migrate to the critical line, or escape to `Im s = ∞`? **Escape to infinity would not
   falsify the conjecture but would show `F` cannot be uniform in height** — forcing a
   height-dependent refinement `|Re rho - 1/2| ≤ F(d, Im rho)`, which is a different and weaker
   statement. I regard this as the most likely outcome and the most informative one.
3. **Convexity.** If `F` exists it should be sub-additive under the natural operation `L₁ ⊗ L₂`.
   Failure of sub-additivity would indicate `d` is the wrong invariant and should be replaced by a
   multiplicative-energy-type quantity rather than an `ℓ¹` mass.

## What its failure would teach

If test 1 kills it, the lesson is that displacement is *not* controlled by the size of the
non-multiplicative part but by its **arithmetic structure** — e.g. by whether the off-prime-power
support of `b_n` is equidistributed or concentrated. That would redirect to: which *shape* of
non-multiplicativity produces off-line zeros. That question is also not in the literature I know, and
it is the natural successor conjecture.

## Status

`[CONJECTURE]`. No proof, no computation performed. The next action is test 1, which requires the
`d`-value and displacement for the DH family — a finite determination, and the first thing on this
card that can come out either way.

---

## TEST PERFORMED — the conjecture is FALSE in its stated (uniform) form

Test 2 of the list above, carried out by reasoning; no computation.

Take `g_alpha(s) = L(s, chi_1) + alpha·L(s, chi_2)` with `chi_1, chi_2` of the same conductor and the
same root number, so every `g_alpha` satisfies one and the same functional equation, and
`d(g_alpha) = O(alpha)`. Near a zero `rho_1` of `L(chi_1)` write `L(chi_1)(s) ≈ c·(s - rho_1)` with
`c = L'(chi_1)(rho_1)`. Then

  `g_alpha(s) ≈ c·(s - rho_1) + alpha·L(chi_2)(rho_1)`,

so the zero is displaced by

  **`alpha · |L(chi_2)(rho_1)| / |L'(chi_1)(rho_1)|`.**

The perturbative response is `alpha / |L'(rho)|`, and **`1/|L'|` is unbounded over the zero set**: it
blows up precisely where consecutive zeros are close, and the liminf of normalised gaps is `0`
unconditionally. So for **any** `alpha > 0`, however small, there are heights at which the induced
displacement is of order one. The off-line zeros escape to large height, but their displacement does
**not** tend to `0` with `d`.

`[FALSIFIED]` The uniform form fails. The surviving height-dependent form
`|Re rho - 1/2| ≤ F(d(L), Im rho)` is too weak to give RH, since RH needs uniformity in height.

## The exact why, and what it forbids

The killing mechanism is not about zeta and not about the choice of `d`. It is that **displacement
responds to a coefficient perturbation like `1/|L'(rho)|`, which is unbounded**. Any invariant of the
coefficients that is *continuous* under `L ↦ L + eps·g` inherits this: an arbitrarily small
continuous perturbation can produce an order-one displacement somewhere in the zero set.

> **[SUCCESSOR CONJECTURE — Non-perturbative barrier]** No true statement has the form
> "small non-multiplicativity implies small displacement" when non-multiplicativity is measured by
> *any* norm on the coefficients `b_n` that is continuous under `L ↦ L + eps·g`. Consequently any
> proof of "Euler product ⟹ RH" must use a feature of multiplicativity that is **discontinuous** in
> the coefficients.

This is sharp and falsifiable: exhibit one continuous norm for which the implication holds, and it
dies. It also makes a positive prediction about where the working ingredient lives. The features of
the Euler product that are discontinuous in the coefficients are exactly the **discrete** ones:

- `Λ(p^k) = log p` for every `k` — the log-derivative's coefficients take values in a *discrete* set
  `{log p}`, not merely small values off the prime powers;
- the support of `b_n` is a *discrete arithmetic set* (prime powers), a condition no small
  perturbation preserves;
- the residues of `-L'/L` at zeros are positive **integers**.

So the prediction is: the mechanism by which multiplicativity forces the critical line is
**arithmetic discreteness, not analytic size.** Every route in the retired card
(`5-failed/downstream-functionals-of-the-zero-set.md`) measured size. That is a second, independent
reason those routes could not work, and it was not visible from inside them.

## Steering

The next conjecture must be built on a discontinuous invariant. The candidate with the most structure
is the value set of the log-derivative's coefficients: for an Euler product `b_n ∈ {log p} ∪ {0}`,
a set with no accumulation point except `∞`. The question to pose next — and it is not one I can
answer or look up:

> Does the discreteness of `{b_n}` alone, together with the functional equation, force the zeros onto
> the critical line? Formally: let `L = Σ a_n n^{-s}` satisfy a zeta-type functional equation and
> suppose `-L'/L = Σ b_n n^{-s}` has all `b_n` in a fixed discrete subset `V ⊂ C` with `0 ∈ V`. Does
> it follow that the displacement is bounded by a function of the *geometry of `V`* — vanishing when
> `V = {0} ∪ {log p}`?

Davenport–Heilbronn is the discriminator again but now in the right variable: its `b_n` are **not**
discrete — the combination's log-derivative has coefficients spread over a continuum. If a
non-multiplicative `L` with *discrete* `b_n` and off-line zeros exists, the successor dies at once.
Constructing or excluding such an `L` is the immediate finite task.

---

## CORRECTION — the falsification above used the wrong mechanism

The displacement formula `alpha·|g(rho)| / |L'(rho)|` is right, but the claim that its real part is
generically nonzero is **wrong**, and the error matters.

If `L_1` and `g` share a functional equation and have real coefficients, then both are **real on the
critical line**: from `g(s) = g(1-s)` and `g(conj s) = conj g(s)` one gets `g(1/2+it) = conj g(1/2+it)`.
Consequently at an on-line zero `rho` of `L_1`, `L_1'(rho) ∈ iR`, and

  `delta rho = -alpha·g(rho)/L_1'(rho) ∈ R/(iR) = iR`  — **purely imaginary.**

To first order an FE-preserving, real perturbation moves zeros **along** the critical line and never
off it. The `1/|L'|` blow-up is real but it is a blow-up *in the along-line direction*, which is
harmless. `[SELF-CORRECTED]`

### The actual mechanism: collision, not displacement

On the critical line `Ξ` is a **real** function of a real variable and its zeros are real. A real
perturbation keeps it real, so its zeros stay real **until two of them collide and split into a
conjugate pair**. That is the only way an off-line zero can appear in this class. Near a collision,
`Ξ_alpha(t) ≈ Ξ''·(t - t_0)²/2 + alpha·g(t_0)`, so the pair splits with

  **`delta ≍ sqrt( alpha·|g| / |Ξ''| )`  — square-root, not linear —**

and, decisively, a **threshold**: no off-line zero at all until `alpha` exceeds the local minimum of
`|Ξ|` between the two zeros.

This also explains Davenport--Heilbronn correctly. The DH combination has coefficients `(1 ± i·tau)/2`
and is **not** real on the critical line — different root numbers. Its off-line zeros do not come from
collisions at all; they come from the failure of reality. So DH is not a counterexample to the
perturbative statement, it is a different phenomenon, and I had conflated them.

### Revised conjecture, with an exponent and a threshold

> **[CONJECTURE — Collision Threshold]** For `L` in the *real* FE class (real coefficients, self-dual
> root number), off-line zeros exist at height `T` if and only if the non-multiplicative part exceeds
> the typical local minimum of the Euler part on the critical line at that height:
>
>   `d(L) ≳ m(T) := ` typical local minimum of `|Ξ|` between consecutive zeros at height `T`,
>
> and when they exist the displacement obeys `delta ≍ sqrt( d(L) / m(T) ) · (gap at height T)`.

The exponent `1/2` and the threshold are both predictions, and both are new relative to the linear
form I conjectured before the correction.

### The consequence, which is the sharpest thing on this card

`m(T)` is governed by the **value distribution of `|zeta|` on the critical line**. By Selberg's central
limit theorem `log|zeta(1/2+it)|` is asymptotically Gaussian with variance `(1/2)log log T`, so the
typical local minimum decays like

  `m(T) ≈ exp( -c·sqrt(log log T) )`.

Therefore a non-multiplicative perturbation of size `alpha` first produces an off-line zero at height

  **`T ≈ exp exp ( (log(1/alpha))² / c² )`  — doubly exponential in `log(1/alpha)`.**

That is a falsifiable, quantitative prediction which no reformulation of RH could produce, and it is
the reason the uniform Euler Defect Bound fails while a height-dependent version survives: for any
`alpha > 0` a collision height exists, but it is *doubly exponentially* far out.

### Steering

The Euler product's role is now specific rather than rhetorical: it must **prevent collisions at every
height**, i.e. force `m(T)` to stay above the non-multiplicative background at all `T`. Since `m(T)`
is a statement about small values of `|zeta|` on the critical line, the next question — and it is not
one I can look up —

> Does the Euler product force a *lower* bound on the local minima of `|Ξ|` between consecutive zeros,
> in terms of the local gap? Equivalently: is there an unconditional lower bound
> `max_{t ∈ (gamma_n, gamma_{n+1})} |Ξ(t)| ≥ c · (gamma_{n+1} - gamma_n)^A` for some fixed `A`?

A bound of that shape is exactly what forbids a collision, hence what forbids an off-line pair, and it
is a statement about `zeta` alone with no perturbation in sight. Small gaps make it hard precisely
where `1/|L'|` blew up — so the two phenomena are the same phenomenon, and this is the first
formulation on this card where that is visible.

---

## LITERATURE AUDIT — performed after the fact, which was the error

I asserted twice that a question "could not be looked up" without searching. I searched. All three
of the last two turns' claims are known.

**1. "Lower bound `max |Ξ|` between consecutive zeros in terms of the gap."** I had already reduced
this to a lower bound for `|zeta'(rho)|`. That is the **discrete negative moments** problem. Lower
bounds for `J_k(T) = Σ_{0<Im rho ≤ T} |zeta'(rho)|^{2k}`, `k < 0`, are known **only under RH and
simplicity of the zeros**; unconditionally there is essentially nothing.
`[REDISCOVERED — known open problem]`

**2. "Euler defect controls displacement."** The family I constructed — linear combinations of
Dirichlet `L`-functions sharing a functional equation — is a studied object, motivated in the
literature by exactly the Epstein/Davenport--Heilbronn phenomenon I cited. **Montgomery conjectured
that under natural conditions 100% of the zeros of such a linear combination lie on the critical
line**, and Selberg proved a positive proportion. My conjecture lives inside a named existing
conjecture. `[REDISCOVERED]`

**3. "Collision, not perturbation."** This is the standard de Bruijn--Newman picture. In the
documented heat-flow dynamics, *tangencies occur precisely when two branches representing the paths
of two conjugate zeros collide on the critical line* — the mechanism I presented as a correction is
the textbook description of zero dynamics under the flow. `[REDISCOVERED]`

### The procedural error, named

The `hgt-fields-medalist` protocol puts the external SOTA audit in **Gate 1, before conjecturing**. I
inverted it every turn: conjecture, then assert unlookupability, then (sometimes) attack. Asserting
that something cannot be found without attempting to find it is the precise mechanism that turned
this card into theatre. The searches cost four minutes.

**Rule, binding for this card:** no `[CONJECTURE]` label may be applied before a recorded literature
audit of its exact statement. A conjecture without a preceding audit is to be treated as
`[NOVELTY UNVERIFIED]` and is not evidence of anything.

## Frontier facts actually established (Gate 1, belatedly)

- Record proportion of zeros on the critical line: **41.7%** (Pratt--Robles--Zaharescu--Zeindler,
  2020), of which **40.7%** are additionally simple.
- 2025 work on **short mollifiers**: linear combinations of derivatives of `zeta` adapted to
  Levinson's method give a positive proportion of critical zeros **regardless of how short the
  mollifier is**, and — the load-bearing finding — *optimising the linear combination has a more
  pronounced effect than refining the mollifier when the mollifier is short*.

That last point relocates the bottleneck. The standing assumption in this card (and in my §104
analysis, where I asserted the barrier was "mollifier length") is **wrong**: the binding constraint in
the short-mollifier regime is the choice of the differential operator, not the length of the Dirichlet
polynomial. Any next conjecture on this card must be made against that edge, not against the one I
assumed.

## Status

Card downgraded. The Euler Defect Bound and its collision-threshold successor are
`[REDISCOVERED]`, not open conjectures. The doubly-exponential threshold estimate remains
`[NOVELTY UNVERIFIED]` — it was not searched and is not claimed.
