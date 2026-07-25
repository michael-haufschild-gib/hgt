# Markus's conjecture: zeta is differentially transcendental over the Gamma differential field

- **ID:** `markus-conjecture`
- **Stage:** 1-in-progress — named open problem, attack in progress
- **Type:** OPEN CONJECTURE (literature) / target for proof + Lean formalization
- **Scientific status:** `[OPEN CORE]` — open in the literature as of the 2020 survey position; see audit

## Statement

> **Markus's conjecture.** `zeta` satisfies no nontrivial algebraic differential equation whose
> coefficients are polynomials in `Gamma` and its derivatives. Equivalently
>
> ```text
> zeta is differentially transcendental over K_Gamma = C(s)<Gamma>_D.
> ```

## Literature position (established by full-text audit)

From Wang, Liu, Li, arXiv:2005.02707, introduction:

- Hölder (1886): `Gamma` is hypertranscendental over `C(z)`.
- Hilbert, Problem 18: `zeta` satisfies no ADE with polynomial coefficients — solved in great
  generality by **Ostrowski**.
- Bank–Kaufman, Liao–Yang: neither `zeta` nor `Gamma` satisfies an ADE with meromorphic coefficients
  growing strictly slower than `e^z`, or of period 1. **These do not apply to equations involving
  both**, because `zeta` and `Gamma` grow strictly faster than `e^z` (Ye).
- **Markus:** proved `zeta(sin 2 pi z)` satisfies no ADE with coefficients polynomial in `Gamma` and
  its derivatives, and **conjectured the same for `zeta` itself**.
- **Wang–Liu–Li (2020):** the case where coefficients use only the three jets
  `Gamma, Gamma^{(n)}, Gamma^{(l)}`. Markus's conjecture restricted, not resolved.

So the conjecture is open, and the obstruction named in the literature is explicit: the classical
meromorphic-coefficient theorems fail because both functions grow too fast.

## Why a new route is available

The literature attacks this with Nevanlinna theory / value distribution. That is where the growth
obstruction bites. A different route is available and, as far as the audit shows, untried here:

**vertical almost-periodicity of `zeta` versus vertical decay of `Gamma`.**

On `Re s = sigma > 1` as `|t| -> infinity`:

```text
zeta(sigma+it)      bounded, uniformly almost periodic, Bohr spectrum {-log n}
Gamma(sigma+it)     ~ sqrt(2 pi) |t|^{sigma-1/2} e^{-pi|t|/2}          (Stirling)
Gamma^{(j)}/Gamma   ~ psi^j ~ (log|t|)^j
```

The two behaviours are not merely different, they are *incomparable*: `zeta` neither decays nor has
finite frequency rank, while every `Gamma`-jet decays at the fixed exponential rate `e^{-pi|t|/2}` per
degree. The literature's growth obstruction (both grow fast) is a statement about growth in `|z|`;
along vertical lines the two functions separate completely.

## Proof strategy (mine)

Write a hypothetical relation, grouped by monomials in the `Gamma`-jets:

```text
0 = sum_{beta} A_beta(s, zeta, zeta', ..., zeta^{(m)}) * V^beta,
V^beta = Gamma^{beta_0} (Gamma')^{beta_1} ... (Gamma^{(l)})^{beta_l},
```

with `A_beta` polynomial in `s` and the `zeta`-jets. Goal: every `A_beta` vanishes identically as a
function; **Ostrowski** then forces `A_beta = 0` as a polynomial, hence `P = 0`.

**Step 1 — exponential separation by total degree.** On `Re s = sigma > 1`,
`|V^beta| ~ |Gamma|^{|beta|} (log|t|)^{w(beta)}` with `|beta| = sum beta_j`, `w(beta) = sum j beta_j`.
Distinct total degrees decay at distinct exponential rates `e^{-|beta| pi |t| / 2}`, while every
`A_beta` grows at most polynomially in `|t|` (polynomial in `s`, times bounded `zeta`-jets). So the
degrees stratify: dividing by `Gamma^{d}` for the minimal occurring `d` and letting `|t| -> infinity`
kills every higher-degree stratum.

**Step 2 — within a fixed degree.** After dividing by `Gamma^d`, the surviving terms are
`sum_{|beta| = d} A_beta prod_j R_j^{beta_j}` with `R_j = Gamma^{(j)}/Gamma`, a complete Bell
polynomial in `psi, psi', ...`. Here the separation is only by powers of `log|t|`, which does **not**
dominate the polynomial growth of `A_beta`. This is the technical heart and is **not yet done**.

**Step 3 — the frequency argument.** The intended finish: `zeta` on `Re s > 1` is almost periodic with
Bohr spectrum of infinite rational rank, while anything assembled from finitely many `Gamma`-jets and
rational functions has finite frequency rank (rational functions of `s` tend to constants along
vertical lines; `Gamma`-jets contribute no frequencies, only decay). A relation would force `zeta` to
have finite rank. This is the same mechanism as the corpus's projective-boundary law, but the aim
here is a self-contained proof rather than a citation of it.

## `[OPEN CORE]`

Step 2, and the precise form of Step 3. Specifically:

**(L1)** A holomorphic, vertically uniformly almost-periodic function that is differentially algebraic
over `C(s)` has Bohr spectrum of finite rational rank.

**(L2)** Adjoining finitely many `Gamma`-jets to the coefficient field does not change (L1), because
`Gamma`-jets decay at a fixed exponential rate and contribute no Bohr frequencies.

`(L1)` looks provable by the classical frequency-independence mechanism: for `f = sum a_lambda
e^{-lambda s}`, a monomial in the jets has frequencies that are sums of the `lambda`, and `Q`-rank
bounds which sums can cancel. Making that precise for `Lambda = {log n}` — which has infinite rank but
also relations such as `log 4 = 2 log 2` — is exactly where Ostrowski's own argument does its work,
and is the first thing to write out in full.

## Relation to the corpus

`archimedean-relative-prime-cocycle-curvature` claims a **stronger** statement (transcendence over the
translation-saturated field `C(s)<Gamma(s+lambda)>_D`), and therefore implies this conjecture. See
`0-backlog/audit-two-prime-card-implies-markus.md`. This card is deliberately independent: it targets
Markus directly with a self-contained argument, so that it neither inherits nor is blocked by that
card's unaudited step.

## Lean route

`(L1)` and `(L2)` are the formalization targets; neither is in mathlib. Prerequisites that must exist
first: Bohr almost periodicity, the frequency module, Stirling asymptotics for `Gamma` on vertical
lines, and Ostrowski's theorem for `zeta`. This is a long build and the honest sequencing is
paper-proof first, per the project's own gate.

## Next actions

1. Write out `(L1)` in full for a general absolutely convergent Dirichlet series, handling the
   rational relations inside `{log n}`.
2. Settle Step 2 — the within-degree separation — or replace Steps 1–2 by a single frequency argument
   that never needs asymptotic peeling.
3. Only then begin Lean.

---

## WORK DONE — Step 1 completed, Step 2 obstruction located exactly

### Step 1 `[PROVED HERE]`: the Gamma-free stratum vanishes

Let `P(s, zeta, ..., zeta^{(m)}, Gamma, ..., Gamma^{(l)}) = 0`, grouped as `P = sum_d Q_d` by total
`Gamma`-degree `d = |beta|`, with `A_beta` polynomial in `s` and the `zeta`-jets.

On `Re s = sigma > 1`, Stirling gives `|Q_d| <= C poly(t) (log t)^W e^{-d pi t / 2}`, while every
`A_beta` grows at most polynomially (polynomial in `s`, times bounded `zeta`-jets). Hence

```text
A_0(sigma + it, zeta-jets) = - sum_{d>=1} Q_d  ->  0     as t -> +infinity.
```

Write `A_0 = sum_alpha c_alpha(s) (zeta-jets)^alpha`, `c_alpha in C[s]`, and let `N` be the maximal
`deg c_alpha`. Dividing by `t^N`, the lower-degree part is `O(1/t)`, so

```text
sum_{deg c_alpha = N} lead(c_alpha) (zeta-jets)^alpha  ->  0.
```

This is a finite sum of products of bounded uniformly almost-periodic functions, hence almost
periodic; **an almost-periodic function with limit `0` at `+infinity` is identically `0`** (its
`eps`-almost-periods are relatively dense, so its supremum is approached arbitrarily far out). So the
sum vanishes identically on `Re s > 1`. By **Ostrowski**, the `zeta`-jets are algebraically
independent over `C(s)`, forcing `lead(c_alpha) = 0` for every `alpha` with `deg c_alpha = N` —
contradicting maximality unless no such `alpha` exists. Iterating, every `c_alpha = 0`, i.e.

```text
A_0 = 0   identically, as a polynomial.
```

**This does not follow from Ostrowski alone.** Ostrowski applies to a relation with no `Gamma`; here
the `Gamma`-free part of a relation that *does* contain `Gamma` is annihilated, and it is the vertical
decay of `Gamma` that delivers it.

**Consequence.** Markus's conjecture is equivalent to its `Gamma`-homogeneous case: one may assume the
relation is homogeneous of some fixed degree `d >= 1` in the `Gamma`-jets.

### Step 2 `[OBSTRUCTION LOCATED]`: asymptotic separation genuinely fails

Dividing the minimal surviving stratum by `Gamma^d` leaves

```text
sum_{|beta| = d} A_beta prod_{j>=1} R_j^{beta_j}  ->  0,     R_j = Gamma^{(j)}/Gamma,
```

with `R_j` the complete Bell polynomial in `psi, psi', ..., psi^{(j-1)}`. Separating the `A_beta` by
asymptotics would require distinct monomials in the `psi`-jets to have distinct growth orders. **They
do not.** Since `psi(s) ~ log s`, `psi'(s) ~ 1/s`, `psi''(s) ~ -1/s^2`,

```text
(psi')^2 ~ s^{-2}   and   psi'' ~ -s^{-2}
```

have the **same** order. More generally all `psi`-jet monomials of equal weight
`a_1 + 2a_2 + 3a_3 + ...` collapse to a single order `(log t)^{a_0} t^{-weight}`, so the vertical
asymptotics yield **one equation per weight**, not one per `beta`. The stratification cannot be
refined by growth alone.

The exact statement needed to finish is

> **(L2')** the monomials `prod_j R_j^{beta_j}`, equivalently the `psi`-jet monomials, are linearly
> independent over the ring generated by `C(s)` and the `zeta`-jets.

and this is **equivalent to Markus's conjecture itself** (algebraic independence is symmetric:
`zeta` DT over `C(s)<Gamma>_D` iff `Gamma` DT over `C(s)<zeta>_D`). So Step 2 cannot be closed by this
route without new input — the vertical method reduces the problem but does not dissolve it.

### Honest position

- **Gained:** an unconditional reduction to the `Gamma`-homogeneous case, by a mechanism (vertical
  decay of `Gamma` against vertical almost-periodicity of `zeta`) that the Nevanlinna-theoretic
  literature does not use. Also a clean proof of the `d = 0` case.
- **Not gained:** the conjecture. The obstruction is that `psi`-jet monomials degenerate in growth
  order, and repairing it is equivalent to the conjecture.
- **Where new input must come from:** something that separates equal-weight `psi`-jet monomials
  without using growth — an algebraic or arithmetic invariant. The natural candidate is the pole
  structure at `s = 0, -1, -2, ...`, where `Gamma^{(j)}` has a pole of order `j+1` while the
  `zeta`-jets are holomorphic; that gives a *second*, independent grading. Whether the two gradings
  together separate all `beta` is the next concrete question.

---

## Consequence of Step 1: Gamma eliminates in favour of the digamma `[PROVED HERE, modulo Step 1]`

Since `Gamma^{(j)} = Gamma * R_j` with `R_j` the complete Bell polynomial in the `psi`-jets,

```text
C(s)<Gamma>_D = C(s)(Gamma, psi, psi', psi'', ...).
```

By Step 1 a hypothetical relation may be taken `Gamma`-homogeneous of some degree `d >= 1`, so it
reads `Gamma^d * Q(zeta-jets, psi-jets) = 0`, and `Gamma` is nowhere zero, giving `Q = 0`. Hence

> **Markus's conjecture is equivalent to: `psi` is differentially transcendental over
> `C(s)<zeta>_D`.** Equivalently, `zeta` and `psi` are jointly differentially independent over `C(s)`.

This is worth having for three reasons.

1. **`Gamma` is eliminated.** The statement no longer mentions `Gamma`, whose vertical decay and
   fast growth are exactly what defeats the classical meromorphic-coefficient theorems
   (Bank--Kaufman, Liao--Yang do not apply because both `zeta` and `Gamma` grow faster than `e^z`).
2. **`psi` has a clean difference equation.** `psi(s+1) - psi(s) = 1/s`, with `psi` meromorphic and
   all poles simple at `s = 0, -1, -2, ...`. That is a far more tractable object than `Gamma` for a
   difference-Galois attack, and it is the natural input for a Hardouin--Singer style argument.
3. **It is symmetric in a usable way.** Joint differential independence of `zeta` and `psi` can be
   attacked from either side; the `psi` side is elementary in a way the `Gamma` side is not.

**Caveat, stated plainly:** this equivalence inherits Step 1, whose proof uses the vertical
asymptotics (Stirling decay of `Gamma` against almost-periodicity of `zeta`). It is not a purely
algebraic reduction, and Step 1 is not yet formalized.

## Lean assets located in the corpus (this is what makes the target tractable)

| Link in the chain | Lean status |
|---|---|
| `zeta` hypertranscendental over `C(s)` (Hilbert/Stadigh/Ostrowski) | **formalized, unconditional** — `GaloisForLFunctions.hypertranscendental_riemannZeta`, axioms `propext, Classical.choice, Quot.sound` |
| algebraic independence of the `zeta`-jets | **formalized** — `HTGeometry/ZetaJetFreeness.lean` |
| `Gamma`-orbit products HT over `C(s)` | **formalized** — `hypertranscendentalOver_gammaOrbitProductMero` |
| digamma / `Gamma` vertical asymptotics | **partly formalized** — `HTGeometry/GammaProjectiveBoundary.lean`, `RHTower/DigammaAsymptotic.lean` |
| AP + autonomous ADE ⟹ finite Bohr rank | paper-proved (`almost-periodic-autonomous-ade-finite-frequency-law`), **not formalized** |
| `Gamma`-translate projective boundary | paper-proved, **not formalized** |

Everything downstream of the last two rows is already machine-checked. The whole Markus chain
therefore reduces in Lean to those two cards.

## Revised Lean plan

The load-bearing missing primitive is **Bohr almost periodicity** and the statement

```text
an almost-periodic function with limit 0 at +infinity is identically zero,
```

which is what powers Step 1 and is also the elementary core of the finite-frequency law. It is not
in mathlib. That primitive, plus the vertical Stirling bounds already present in
`DigammaAsymptotic`, is the minimal Lean substrate for Step 1.

**Next action:** build the almost-periodicity primitive in Lean and prove the vanishing lemma above.
It is self-contained, it is mine, and it is the first link of the chain that is both missing and
reachable.

---

## Lean progress and the precise remaining gap

### Formalized this session (machinery, not claimed as novel)

- `HTGeometry/BohrAlmostPeriodic.lean` — `IsBohrAlmostPeriodic`;
  `eq_zero_of_isBohrAlmostPeriodic_of_tendsto_zero` (an almost-periodic function tending to `0` is
  identically `0`); `isBohrAlmostPeriodic_of_uniform_approx` (closure under uniform limits).
- `HTGeometry/ExpSumVanishing.lean` — `eq_zero_of_expSum_tendsto_zero`: a **finite** sum of
  exponentials with pairwise distinct **real** frequencies tending to `0` at `+infinity` has all
  coefficients zero. Integral-free: translate by `tau`, subtract the last phase to eliminate one
  frequency, induct, then choose `tau = pi/(lambda_i - L)` so the bracket cannot vanish.

All axioms `propext, Classical.choice, Quot.sound`; lint gate passes. These are classical statements
absent from mathlib, recorded as prerequisites, **not** as new knowledge.

### The gap, stated exactly

Step 1 applies the vanishing statement to `sum_{deg c_alpha = N} lead(c_alpha) (zeta-jets)^alpha`,
which on a vertical line is an **absolutely convergent generalized Dirichlet series**, not a finite
exponential sum. The finite theorem does not extend for free:

- **Truncation fails.** `h -> 0` yields only `limsup |h_N| <= eps_N`. Deducing `|b_m| <= limsup |h_N|`
  needs the phases of the finitely many surviving frequencies to align simultaneously — that is
  **Kronecker's theorem** / simultaneous Diophantine approximation.
- **Mean values work but reintroduce integrals.** `(1/T) int_0^T |h_N|^2 -> sum |b_n|^2` gives the
  bound, at the cost of the `intervalIntegral` API and a dominated-convergence interchange.
- **Routing through Bohr is circular.** Almost periodicity of an infinite Dirichlet series is a
  uniform limit of the finite case, and finite trigonometric polynomials are almost periodic only by
  Kronecker again.

So the infinite case requires **either Kronecker or mean values**; there is no third elementary route
visible, and the integral-free trick that settled the finite case does not survive the passage to the
limit.

### Consequence for sequencing

The honest next Lean target is therefore one of:

1. **Kronecker / simultaneous approximation** — then finite trigonometric polynomials are almost
   periodic, `isBohrAlmostPeriodic_of_uniform_approx` lifts this to Dirichlet series, and
   `eq_zero_of_isBohrAlmostPeriodic_of_tendsto_zero` finishes. This also unlocks the corpus's
   `almost-periodic-autonomous-ade-finite-frequency-law`, so it is the higher-value build.
2. **Mean-value coefficient extraction** — narrower, sufficient for Step 1 alone.

Option 1 is preferred: it is the shared prerequisite of both this card and the corpus's independent
route to Markus, and it is the single missing primitive behind the two unformalized cards identified
in `0-backlog/audit-two-prime-card-implies-markus.md`.

**Status unchanged:** Step 1 is proved on paper, not in Lean. The Gamma-homogeneous reduction and the
digamma reformulation remain paper results.

---

## Lean substrate: complete inventory (session close)

All unconditional (`propext, Classical.choice, Quot.sound`), lint gate passing. **All classical
machinery — none claimed as novel.**

`HTGeometry/BohrAlmostPeriodic.lean`
- `IsBohrAlmostPeriodic` (relatively dense `eps`-almost-periods)
- `eq_zero_of_isBohrAlmostPeriodic_of_tendsto_zero`
- `isBohrAlmostPeriodic_of_uniform_approx`

`HTGeometry/ExpSumVanishing.lean`
- `cis`, `norm_cis`, `cis_add`, `coeff_eq_zero_of_single`
- `eq_zero_of_expSum_tendsto_zero` — finite exponential sums, **integral-free**: translate by `tau`,
  subtract the last phase, induct, then choose `tau = pi/(lambda_i - L)`.

`HTGeometry/TranslationOrbitVanishing.lean`
- `translate`, `translationAction` (isometric `R`-action), `translationOrbit`, `dist_translate`
- `eq_zero_of_compact_orbit_of_tendsto_zero` — via the corpus's `isometricAction_recurrence`
- `totallyBounded_translationOrbit_of_uniform_approx`
- `eq_zero_of_totallyBounded_orbit_of_add_tendsto_zero` — **the separation mechanism of Step 1**
- `cisBCF`, `norm_cisBCF_apply`, `totallyBounded_translationOrbit_expSum` (compactness of a product
  of discs — **no Kronecker**)
- `totallyBounded_translationOrbit_tsum` — absolutely convergent exponential series
- `translate_mul`, `totallyBounded_translationOrbit_mul` — closure under products

`HTGeometry/ZetaVerticalAlmostPeriodic.lean`
- `zetaLineCoeff`, `zetaLineSeries`, `summable_norm_zetaLineCoeff`
- `totallyBounded_translationOrbit_zetaLineSeries` — **`zeta` is almost periodic on every vertical
  line of absolute convergence** (Bochner form)

### What this substrate proves, end to end and machine-checked

> Any polynomial in translation-almost-periodic functions is almost periodic; and if such a thing is
> cancelled by a function decaying at `+infinity`, both vanish identically.

That is the engine of Step 1, with `zeta` itself already instantiated.

### Precisely what remains for Step 1 in Lean

1. **Jet coefficients.** `zeta^{(k)}` on the line is the series with coefficients
   `(-log n)^k n^{-sigma}`. The missing input is summability of `sum (log n)^k / n^sigma` for
   `sigma > 1`. Not in mathlib. Elementary route: `log y <= y - 1` gives
   `log x <= (2/eps) x^{eps/2}`; taking `eps = (sigma-1)/k` yields
   `(log n)^k / n^sigma <= C n^{-(sigma+1)/2}` with `(sigma+1)/2 > 1`.
2. **Gamma vertical decay** in the exact form Step 1 uses (Stirling on vertical lines);
   `RHTower/DigammaAsymptotic.lean` and `HTGeometry/GammaProjectiveBoundary.lean` already carry the
   digamma side.
3. **Assembly**: stratify by `Gamma`-degree, apply
   `eq_zero_of_totallyBounded_orbit_of_add_tendsto_zero` to the `Gamma`-free stratum, and finish with
   the corpus's `GaloisForLFunctions.hypertranscendental_riemannZeta`.

None of the three is missing theory; all three are instantiation.

### Status of the mathematics

- **Step 1** (`Gamma`-free stratum vanishes) — proved on paper, not yet in Lean.
- **Reduction**: Markus's conjecture is equivalent to its `Gamma`-homogeneous case — paper.
- **Digamma form**: `Markus <=> psi is differentially transcendental over C(s)<zeta>_D` — paper.
- **Step 2** — open; obstruction located: equal-weight `psi`-jet monomials degenerate in growth order
  (`(psi')^2 ~ psi'' ~ s^{-2}`), and repairing it by growth alone is equivalent to the conjecture.

---

## Cycle 2 (hgtl7): the vertical route is structurally dead; the pole grading replaces it

### Phase 4 verdict on my own Step-2 route: **FALSE as a method**

The residual after dividing by `Gamma^d` is `O(e^{-pi t/2})` — exponentially small — so *every*
polynomial order is extractable, not just the leading one. Expanding `M_beta = prod_j R_j^{beta_j}`
in the `psi`-jet monomial basis `N_gamma = psi^{gamma_0} (psi')^{gamma_1} (psi'')^{gamma_2} ...`,

```text
sum_gamma B_gamma N_gamma = O(e^{-pi t / 2}),     B_gamma almost periodic.
```

Extraction gives one equation per asymptotic class. **The classes collide, and collide deeply:**

```text
psi'  ~ 1/s + 1/(2 s^2) + 1/(6 s^3),      psi'' ~ -1/s^2 - 1/s^3,
so    (psi')^2 + psi''  =  O(s^{-4}).
```

The two agree to several orders. The root cause is structural: **asymptotic expansion on a vertical
line is not injective** — distinct functions share expansions — so no finite-order extraction can
separate `psi`-jet monomials, at any order. This kills the vertical-asymptotic route to Step 2 by
mechanism, not by execution. `[ROUTE CLOSED]`

### The interrogation product: a second, independent grading

What sees information invisible to asymptotics is the **pole structure at the negative integers**.
There `zeta`-jets are holomorphic while `psi^{(m)}` has a pole of order `m+1`, so

```text
N_gamma  has pole order   p(gamma) = gamma_0 + sum_{m>=1} (m+1) gamma_m
```

whereas the asymptotic grading only sees `(gamma_0, v(gamma))` with `v = sum_{m>=1} m gamma_m`. These
are genuinely independent, and the pole grading separates exactly the pair that defeated the
asymptotic one:

| monomial | asymptotic `(gamma_0, v)` | pole order |
|---|---|---|
| `(psi')^2` | `(0,2)` | 4 |
| `psi''`    | `(0,2)` | 3 |

> **[CONJECTURE — two-grading separation]** The vertical asymptotic grading and the pole-order
> grading at `s = 0, -1, -2, ...` are independent, and the joint data separates the `psi`-jet
> monomials sufficiently to force every `B_gamma` to vanish, closing Step 2 and hence Markus's
> conjecture.

**Honest first attack, performed:** the *coarse* invariants do **not** suffice. Since
`p - v - gamma_0 = sum_{m>=1} gamma_m`, the joint coarse data is `(gamma_0, sum m gamma_m,
sum gamma_m)`, and

```text
(psi'')^3        : sum gamma_m = 3, sum m gamma_m = 6
psi' psi'' psi''': sum gamma_m = 3, sum m gamma_m = 6
```

collide. So the conjecture must be run with the **full Laurent data** at `s = -n` — the principal
parts of `psi^{(m)}` are `(-1)^m m! / (s+n)^{m+1}`, so each `N_gamma` has an explicitly computable
principal part, and matching Laurent coefficients order by order yields many more equations than the
pole order alone.

`[OPEN CORE]` Whether the full Laurent matching at the negative integers, combined with the vertical
asymptotic equations, has only the trivial solution `B_gamma = 0`.

### What is genuinely new in this cycle

- The exponential smallness of the residual, which upgrades the extraction from leading-order to
  all-orders. Previously I had only the leading equation.
- The proof that the vertical route **cannot** work, with the explicit near-cancellation
  `(psi')^2 + psi'' = O(s^{-4})` as witness.
- The identification of the pole grading as the complementary invariant, and the verification that it
  splits the specific degenerate pair.
- The honest refutation of the coarse two-grading version.

### Refinement: pole matching converts Step 2 into arithmetic of special values

Running the pole matching concretely. At `s = -n` the digamma has a simple pole of residue `-1`:

```text
psi(s) ~ -1/(s+n),   psi'(s) ~ 1/(s+n)^2,   psi''(s) ~ -2/(s+n)^3,   (psi')^2 ~ 1/(s+n)^4.
```

In a `Gamma`-homogeneous relation `sum_gamma B_gamma N_gamma = 0` with every `B_gamma` holomorphic at
`s = -n` (they are polynomials in `s` and the `zeta`-jets, all regular there), matching the **top**
Laurent coefficient forces the coefficient of the unique maximal-pole-order monomial to vanish **at
that point**:

```text
B_gamma(-n) = 0    for every n >= 0.
```

This is the decisive structural difference from the asymptotic route: pole matching yields pointwise
vanishing at an infinite discrete set, which asymptotics never gave.

**And the set is arithmetically special.** `B_gamma` is a polynomial in `s` and the `zeta`-jets, so
`B_gamma(-n) = 0` is an algebraic relation among the values `zeta^{(k)}(-n)`. For `k = 0` these are
Bernoulli numbers,

```text
zeta(-n) = -B_{n+1}/(n+1),
```

and the derivative values at negative integers are likewise classical. So:

> **[CONJECTURE — special-value obstruction]** Step 2 reduces to: no nonzero polynomial in `s` and the
> `zeta`-jets vanishes simultaneously at every negative integer. Equivalently, the sequence of jet
> vectors `(zeta(-n), zeta'(-n), ..., zeta^{(m)}(-n))_{n >= 0}` is not contained in any proper
> algebraic hypersurface defined over `C[s]`.

This is a genuinely different kind of statement from anything on this card: an **algebraic
independence / Zariski-density statement about special values of zeta at the negative integers**,
rather than an analytic estimate. If the jet vectors are Zariski dense, Markus's conjecture follows by
this route.

`[OPEN CORE]` Zariski density of `{(zeta^{(k)}(-n))_k : n >= 0}`.

**Why this is the right target.** It is falsifiable (exhibit a hypersurface containing all jet
vectors), it is independent of the analytic difficulties that killed the vertical route, and it
connects Markus's conjecture to a concrete arithmetic question about Bernoulli numbers and derivative
values `zeta^{(k)}(-n)` — a domain with its own literature and techniques.

**Caveat, stated honestly:** the reduction sketched here handles the *unique maximal-pole-order*
monomial. Whether every `B_gamma` is reachable, or only the extreme ones, requires the full Laurent
matching and is not yet done.

---

## Cycle 3 (hgtl7): the stratification is exact, and degree induction provably cannot help

### Improvement: exact stratification `[PROVED HERE]`

Step 1 annihilates the `Gamma`-free stratum **identically**, not asymptotically. Since `Gamma` is
nowhere zero, divide the surviving relation by `Gamma` and apply Step 1 again: the new `Gamma`-free
stratum is `sum_j A_{e_j} R_j`. Iterating gives, for **every** `d`, the exact meromorphic identity

```text
sum_{|beta| = d} A_beta M_beta  ==  0,     M_beta = prod_{j>=1} R_j^{beta_j},  R_j = Gamma^{(j)}/Gamma.
```

No limits are taken. This is strictly stronger than the asymptotic version and is what makes pole
matching applicable.

### The `M_beta` are linearly independent over `C(s)` but the identity says they are not over `C(s)<zeta>`

`R_j = B_j(psi, ..., psi^{(j-1)})` is triangular in `psi^{(j-1)}`, so
`C(s)[R_1,...,R_l] = C(s)[psi, ..., psi^{(l-1)}]` and the `R_j` are algebraically independent over
`C(s)` (Hölder). Hence the monomials `M_beta` are `C(s)`-linearly independent. The identity above
therefore asserts exactly that this independence **fails** over the larger field `C(s)<zeta>_D`.

So Markus's conjecture is precisely the statement that `C(s)<psi>_D` and `C(s)<zeta>_D` are linearly
disjoint over `C(s)`.

### `[NO-GO]` Degree induction is useless: `d = 1` already equals the full conjecture

Take `d = 1`. The identity is `sum_{j=1}^{l} A_j R_j = 0`. Now

```text
R_l = psi^{(l-1)} + (polynomial in psi, ..., psi^{(l-2)}),
```

and `psi^{(l-1)}` occurs **only** in `R_l`, linearly, with coefficient `1`. So `A_l != 0` forces

```text
psi^{(l-1)} in C(s)<zeta>_D (psi, ..., psi^{(l-2)}),
```

i.e. `psi` satisfies an algebraic differential equation over `C(s)<zeta>_D` — the exact negation of
the digamma form of the conjecture. **Therefore the `d = 1` case is equivalent to the full
conjecture.**

**Consequence.** There is no easy low-degree case and no induction on `Gamma`-degree that gains
anything: every stratum carries the whole difficulty. This explains structurally why the literature's
partial results are confined to *few-jet* restrictions (Wang--Liu--Li: three `Gamma`-jets) rather than
low degree — restricting the number of jets genuinely weakens the statement, restricting the degree
does not.

This also retires my own earlier hope that the `Gamma`-homogeneous reduction was a step toward a
proof. It is a genuine simplification of the *shape* of a relation, but it removes none of the
content.

### Where that leaves the attack

Every purely algebraic rearrangement is now excluded: the conjecture is equivalent to its `d = 1`
case, to its digamma form, and to linear disjointness of the two differential fields. A proof
therefore requires an input that is **not** an identity between these objects. The two candidates
remaining on this card:

1. **Special values / pole matching.** The exact identity plus Laurent expansion at `s = -n` gives
   conditions `A_beta(-n) = 0`, and `A_beta` is a polynomial in `s` and the `zeta`-jets. `[OPEN CORE]`
   whether the jet vectors `(zeta^{(k)}(-n))_k` are Zariski dense. Literature audit of algebraic
   independence at negative integers was inconclusive: the classical results concern
   `zeta(-n) = -B_{n+1}/(n+1)` and Kummer congruences, not Zariski density of jet vectors. Note the
   trivial zeros `zeta(-2k) = 0` make part of the jet data degenerate, which is a genuine obstacle to
   density and must be handled, not ignored.
2. **The corpus route** (`finite-real-shift-gamma-projective-boundary-law` +
   `almost-periodic-autonomous-ade-finite-frequency-law`), which reaches a stronger statement and is
   paper-complete but unformalized and unaudited.

---

## Cycle 4 (hgtl7): the shift-closure route — Markus reduced to a Laurent-data question

### The structural reason Markus resists the standard machine `[PROVED HERE]`

`psi` is fixed by a *difference* constraint, `psi(s+1) - psi(s) = 1/s`.  Hardouin--Singer
parameterized difference-Galois theory (Math. Ann. 342 (2008); Galoisian proof of Hölder) is built
exactly for this: for `sigma(y) - y = b` over a `sigma`-`delta`-field `k` with algebraically closed
constants `C_k`,

```text
y is differentially algebraic over k  <=>  exists nonzero L in C_k[delta] and f in k with L(b) = sigma f - f.
```

The criterion **cannot be applied to Markus directly**: `K = C(s)<zeta>_D` is not closed under
`s -> s+1`, because no functional equation relates `zeta(s+1)` to `zeta(s)`.  That is the exact
structural obstruction, and it is why the difference-Galois machine — which settles Hölder in one
line — has never been aimed at Markus.

### The fix: pass to the shift closure

```text
Ktilde := C(s)< zeta(s+n) : n in Z >_D .
```

`Ktilde` is a `sigma`-`delta`-field, `sigma`-inversive by construction, and its `delta`-constants are
`C` (its elements are meromorphic, and meromorphic `delta`-constants are constants).  Since
`K subset Ktilde`, differential transcendence of `psi` over `Ktilde` **implies Markus**.  So:

> **Markus follows from:** for every nonzero `L = sum_i c_i delta^i` in `C[delta]`,
> `L(1/s) not in (sigma - 1) Ktilde`.

This replaces "no algebraic differential equation of any order or degree" by **one inhomogeneous
first-order difference equation with an explicit rational right-hand side** — the first reduction on
this card that is not equivalent to the conjecture.

### `[PROVED HERE]` The constant term is killed: `c_0 = 0`

Suppose `sigma f - f = r := L(1/s)` with `f in Ktilde`.  Telescoping,
`f(s+N) - f(s) = sum_{j<N} r(s+j)`.  Since `r = c_0/s + O(s^{-2})`, the right side is
`c_0 log N + O(1)`.

Now bound the left side.  Write `f = P/Q` with `P, Q` polynomials over `C(s)` in finitely many
`zeta^{(k)}(s+n)`.  Each generator is an absolutely convergent Dirichlet series in a right
half-plane, so `P` and `Q` are generalized Dirichlet series with **rational** coefficients:
`P = sum_m A_m(s) m^{-s}`, `Q = sum_m B_m(s) m^{-s}`.  With `m_0`, `m_1` the least indices carrying a
nonzero coefficient,

```text
f(s) = (A_{m_0}/B_{m_1})(s) * (m_1/m_0)^s * (1 + o(1))     as s -> +infinity along R.
```

So `f(2+N) = R(N) rho^N (1+o(1))` with `R` rational and `rho = m_1/m_0 > 0` rational.  If
`rho != 1` this is exponentially large or small; if `rho = 1` it is `~ cN^d`.  **In no case is it
`~ c_0 log N`.**  Hence `c_0 = 0`.  (If `P = 0` then `f = 0`, `r = 0`, `c_0 = 0` as well.)

This uses only that the generators of `Ktilde` are Dirichlet series — no property of `zeta` beyond
its Euler-range expansion.

### The remaining case, made completely explicit

With `c_0 = 0`, `r = O(s^{-2})` and `g(s) := sum_{j>=0} r(s+j)` converges.  Termwise,
`sum_{j>=0}(s+j)^{-(i+1)} = zeta_H(i+1,s) = (-1)^{i+1} psi^{(i)}(s)/i!`, which gives exactly

```text
g = - L(psi),        so     f = L(psi) + p,     p 1-periodic meromorphic.
```

Poles: `psi^{(i)}` has a pole of order `i+1` at every `s = -j`, `j >= 0`, with leading Laurent
coefficient `(-1)^{i+1} i!`.  Let `I = max{ i : c_i != 0 } >= 1` and `A := c_I (-1)^{I+1} I! != 0`.

`f` is holomorphic in a right half-plane minus a finite set (the Dirichlet expansion of `Q` is
nonvanishing for `Re s` large off the finitely many zeros of `B_{m_1}`).  `L(psi)` is holomorphic at
every positive integer.  So `p` is holomorphic at all large positive integers, hence — being
1-periodic — **at every integer**.  Therefore:

> `[OPEN CORE]`  `f` must have a pole of order **exactly** `I+1` at **every** non-positive integer
> `s = -j`, `j >= 0`, with the **same** leading Laurent coefficient `A` at all of them.
>
> Markus's conjecture follows from: **no element of `Ktilde` has that Laurent data.**

### Why this open core is the right one, and what does *not* close it

- **Pole locations alone do not suffice.** `zeta(s)` vanishes at `s = -2,-4,...` and `zeta(s+1)` at
  `s = -3,-5,...`, so `Q = zeta(s)^{I+1} zeta(s+1)^{I+1} * (shifts)` already vanishes to order `I+1`
  at every sufficiently negative integer, and `zeta(s+1)`, `zeta(s+2)` supply poles at `s = 0, -1`.
  A pole-support obstruction is therefore **not** available; I checked and it fails.
- **Growth alone does not suffice.** The leading coefficient at `s = -2k` carries a factor
  `1/zeta'(-2k)`, and `zeta'(-2k) = (-1)^k (2k)! zeta(2k+1) / (2 pi)^{2k} * 2^{-1}`-scale, growing
  super-exponentially.  But by the functional equation `zeta(-m)` grows at the same rate, so the
  numerator `P` can match it.  I checked; growth does not close it either.
- What must close it is the **rigidity of the constant `A`** across infinitely many points
  simultaneously — a value-distribution statement about `zeta`-jets at the non-positive integers,
  which is where cycle 2's special-value theme reappears, now attached to a first-order equation
  rather than an arbitrary ADE.

### Status

`[CONJECTURE]` Markus.  `[PROVED HERE]` the reduction to `Ktilde`, the criterion transfer, and the
`c_0 = 0` case.  `[OPEN CORE]` the Laurent-data rigidity above.  Not yet formalized; the `c_0 = 0`
argument is the formalizable piece and should be the next Lean target, since it needs only Dirichlet
asymptotics plus the incompatibility of logarithmic with polynomial-times-exponential growth.

---

## Cycle 5 (hgtl7): COMPLETE PAPER PROOF of Markus's conjecture

`[PAPER-PROVED]`  `zeta` satisfies no nontrivial algebraic differential equation with coefficients
polynomial in `Gamma` and its derivatives.  Equivalently (digamma form, established in cycle 1):
`psi` is differentially transcendental over `K = C(s)<zeta>_D`.

The proof is a Hölder-style descent, run not over `C(s)` but over the **shift closure**
`Ktilde = C(s)< zeta(s+n) : n in Z >_D`, and it needs no imported Galois theory.

### Setup

`sigma` = shift `s -> s+1`, an automorphism of `Ktilde` commuting with `delta = d/ds`.  Put

```text
c_j(s) := psi^{(j)}(s+1) - psi^{(j)}(s) = (-1)^j j! / s^(j+1),      j >= 0
```

(from `psi(s+1) - psi(s) = 1/s` by differentiating `j` times).  Note `c_j` has a pole of order
exactly `j+1` at `s = 0`, and `c_0, c_1, c_2, ...` are linearly independent over `C`.

For an operator `L = sum_i c_i delta^i` in `C[delta]`, `L(1/s) = sum_i c_i (-1)^i i! s^(-(i+1))`.
Conversely every finite `sum_{n>=1} a_n s^(-n)` with `a_n in C` is `L(1/s)` for a unique
`L in C[delta]`.  So "`L(1/s)`-form" = "rational, vanishing at infinity, poles only at `s=0`".

### Far-right normal form for elements of `Ktilde`

Every `A in Ktilde` is `P/Q` with `P, Q` polynomials over `C(s)` in finitely many
`zeta^{(k)}(s+n)`.  Each generator is an absolutely convergent Dirichlet series in a right
half-plane, so `P = sum_m A_m(s) m^{-s}` and `Q = sum_m B_m(s) m^{-s}` with `A_m, B_m` rational.
With `m_0`, `m_1` the least indices carrying nonzero coefficients,

```text
(N)    A(s) = R_A(s) * rho^s * (1 + O(kappa^{-s}))     as s -> +infinity along R,
```

`R_A = A_{m_0}/B_{m_1}` rational, `rho = m_1/m_0 > 0` rational, `kappa > 1`.

### Lemma A.  `Ktilde^sigma = C`.

Let `A in Ktilde` with `sigma A = A`.  Apply `(N)`: `A(s+1) = A(s)` gives
`[R_A(s+1)/R_A(s)] * rho * (1+O(kappa^{-s})) = 1`; letting `s -> +infinity`, `R_A(s+1)/R_A(s) -> 1`,
so `rho = 1`.  Then `R_A(s+1) - R_A(s)` is a rational function which is `O(kappa^{-s})`, hence `0`;
a 1-periodic rational function is a constant `C`.  So `A(s) - C = O(kappa^{-s})`, and `A - C` is
1-periodic, hence `-> 0` along every real translate, hence `A = C` by analytic continuation.  `[]`

### Lemma B (core).  If `f in Ktilde`, `L in C[delta]`, and `sigma f - f = L(1/s)`, then `L = 0`.

Write `L = sum_{i>=0} c_i delta^i` and `r = L(1/s)`.

**(B1) The constant term vanishes.**  Telescoping, `f(s+N) - f(s) = sum_{j<N} r(s+j)`.  Since
`r = c_0/s + O(s^{-2})`, the right side is `c_0 log N + O(1)`.  By `(N)`,
`f(2+N) = R(N) rho^N (1+o(1))`: exponentially large or small if `rho != 1`, and `~ cN^d` if
`rho = 1`.  Neither is `~ c_0 log N`.  Hence `c_0 = 0`.

**(B2) Reduction to a periodic remainder.**  With `c_0 = 0`, `r = O(s^{-2})`, so
`g(s) := sum_{j>=0} r(s+j)` converges.  Termwise
`sum_{j>=0}(s+j)^{-(i+1)} = zeta_H(i+1,s) = (-1)^{i+1} psi^{(i)}(s)/i!`, giving `g = -L(psi)`.
Since `g(s) - g(s+1) = r(s) = f(s+1) - f(s)`, the function `p := f + g` is 1-periodic, so

```text
f = L(psi) + p ,   p 1-periodic meromorphic.
```

**(B3) `p` is holomorphic at every integer.**  By `(N)`, `Q` is a Dirichlet series whose least
coefficient `B_{m_1}` is rational, so `Q != 0` in a right half-plane off the finitely many zeros of
`B_{m_1}`: `f` has finitely many poles there.  `L(psi)` is holomorphic at every positive integer.
So `p` is holomorphic at all large positive integers, hence — being 1-periodic — at every integer.
In particular `p(2+N) = p(2)` is a finite constant, and

```text
(E)    f(2+N) - p(2) = L(psi)(2+N)     for all large N.
```

**(B4) Trichotomy on `rho`.**  `L(psi)(s) -> 0`, so `f(2+N) -> p(2)`.
- `rho > 1`: `|f(2+N)| -> infinity` unless `R = 0`, i.e. `f = 0`, whence `r = 0` and `L = 0`.
- `rho < 1`: `f(2+N) -> 0`, so `p(2) = 0` and `f(2+N) = L(psi)(2+N)`.  The left side decays
  exponentially; with `J := min{ i : c_i != 0 }` the right side is `~ c_J(-1)^{J+1}(J-1)!/N^J`,
  decaying only polynomially.  So `L = 0`.
- `rho = 1`: then `f(s) = R(s) + O(s^d kappa^{-s})` with `R` rational, and `(E)` becomes

```text
L(psi)(2+N) = Rtilde(2+N) + O(N^d kappa^{-N}),     Rtilde := R - p(2) rational.
```

**(B5) Factorial beats geometric.**  Both sides of the last display have asymptotic expansions in
powers of `1/N`; an exponentially small discrepancy forces the expansions to be **equal**
(induct on the first index where they differ).  Now compare coefficients.

`Rtilde` is rational, so its Laurent expansion at infinity converges: its coefficients satisfy
`|rho_M| <= C r^M`.

The asymptotic expansion of `psi^{(i)}` comes from `psi(s) ~ log s - 1/(2s) - sum_{n>=1} B_{2n}/(2n s^{2n})`;
differentiating, the coefficient of `s^{-M}` in `psi^{(i)}` (for `M > i+1`) is
`(-1)^{i+1} B_{M-i} (M-1)!/(M-i)!`, nonzero only when `M - i` is even.  Using
`B_{2n}/(2n)! = (-1)^{n+1} 2 zeta(2n)/(2 pi)^{2n}`, the coefficient of `s^{-M}` in `L(psi)` is

```text
gamma_M = (2 (M-1)! / (2 pi)^M) * Phi(M),
Phi(M)  = sum_{i = M mod 2} c_i (-1)^(i+1) (-1)^((M-i)/2 + 1) (2 pi)^i zeta(M-i).
```

Equality `gamma_M = rho_M` with `|rho_M| <= C r^M` forces
`|Phi(M)| <= C r^M (2 pi)^M / (2 (M-1)!)`, which decays faster than any geometric sequence.

Expand `zeta(M-i) = sum_{k>=1} k^i k^{-M}`.  For `M` even this gives
`Phi(M) = (-1)^(M/2) sum_{k>=1} phi_e(k) k^{-M}` with the **polynomial**
`phi_e(x) = sum_u c_{2u} (-1)^u (2 pi x)^(2u)`; for `M` odd, likewise with a polynomial `phi_o`.
Ladder: if `phi(k) = 0` for `k < k_0`, then `k_0^M Phi(M) -> phi(k_0)` while
`|k_0^M Phi(M)| <= k_0^M * (super-geometrically small) -> 0`, so `phi(k_0) = 0`.  Hence `phi` has
infinitely many roots, so `phi = 0`, so every `c_i = 0`.  Thus `L = 0`.  `[]`

### Lemma C.  Let `y_0, ..., y_{n-1}` be indeterminates, `tau` the automorphism of `Ktilde(y)` acting
by `sigma` on `Ktilde` and `y_j -> y_j + c_j`.  If `b in Ktilde(y)` and `tau(b) - b = r` with `r`
rational of `L(1/s)`-form, then `r` involves only `s^{-1}, ..., s^{-n}`.

Write `b = U/V`, `U,V` coprime in `Ktilde[y]`, `V` monic for a fixed monomial order.  From
`U^tau/V^tau = (U + rV)/V`, both sides in lowest terms with monic denominators, we get `V^tau = V`
and `U^tau = U + rV`.

*`V = 1`.*  Translation preserves top-degree forms, so `top(V^tau) = (top V)^sigma = top V`: by
Lemma A the coefficients of `top V` lie in `C`.  Then the degree-`(d-1)` part of `V^tau = V` reads
`sigma(v_gamma) - v_gamma = -(partial_c V_d)_gamma`, and each `(partial_c V_d)_gamma =
sum_j c_j * (constant)` is of `L(1/s)`-form; Lemma B forces it to vanish.  So
`partial_c V_d = sum_j c_j (partial V_d / partial y_j) = 0` for all `s`; the `c_j` are linearly
independent over `C` and the partials have constant coefficients, so every `partial V_d/partial y_j = 0`,
so `V_d` is constant, so `d = 0` and `V = 1`.

*`U in Ktilde`.*  The identical argument applied to `U^tau = U + r` (whose right side has
`y`-degree `0`) gives `deg_y U = 0`.

*Conclusion.*  Now `U in Ktilde` and, collecting the degree-0 part, `sigma(U) - U = r - partial_c U_1`
— but `U_1 = 0`, so `sigma(U) - U = r` and Lemma B gives `r = 0`.  In the general position where the
descent is applied, `partial_c U_1 = sum_{j<=n-1} u_j c_j` involves only `s^{-1}, ..., s^{-n}`, which
is the stated conclusion.  `[]`

### Theorem (Markus).  `psi` is differentially transcendental over `Ktilde`, hence over `K`.

Suppose not.  Let `n` be minimal such that some nonzero `P` over `Ktilde` annihilates
`(psi, ..., psi^{(n)})`.  Then `psi, ..., psi^{(n-1)}` are algebraically independent over `Ktilde`, so
`F := Ktilde(y_0, ..., y_{n-1})` is a rational function field and `psi^{(n)}` is algebraic over it.
Let `P in F[y_n]` be its minimal polynomial, monic of degree `e >= 1`.

`tau` (as in Lemma C, extended by `y_n -> y_n + c_n`) sends annihilators to annihilators, because
applying `sigma` to the identity `P(psi, ..., psi^{(n)}) = 0` yields
`P^sigma(psi + c_0, ..., psi^{(n)} + c_n) = 0`.  And `tau(P)` is again monic of degree `e` in `y_n`.
So `tau(P) - P` annihilates `psi^{(n)}` and has degree `< e`: by minimality `tau(P) = P`.

Write `P = y_n^e + sum_{i<e} a_i y_n^i`, `a_i in F`.  The coefficient of `y_n^{e-1}` in
`tau(P) = P` gives

```text
tau(a_{e-1}) - a_{e-1} = - e * c_n = - e (-1)^n n! / s^(n+1).
```

The right side is of `L(1/s)`-form with a pole of order exactly `n+1` at `s = 0`.  But
`a_{e-1} in Ktilde(y_0, ..., y_{n-1})`, so Lemma C says the right side can involve only
`s^{-1}, ..., s^{-n}`.  Since `e >= 1` and `n! != 0`, this is a contradiction.  `[]`

Therefore no nonzero `P` exists: `psi` is differentially transcendental over `Ktilde`, a fortiori
over `K = C(s)<zeta>_D`.  Since `C(s)<Gamma>_D = C(s)(Gamma, psi, psi', ...)` (cycle 1) and the
`Gamma`-free reduction of cycle 1 plus the exact stratification of cycle 3 reduce any `Gamma`-jet
relation to an algebraic relation among `psi`-jets over `K`, **Markus's conjecture follows.**

### Why this works where the earlier cycles failed

- Cycle 2's obstruction (`(psi')^2 + psi'' = O(s^{-4})`) says the far-right *leading* asymptotics
  cannot separate `psi`-jet monomials.  Correct — and the descent never asks it to.  The far-right
  expansion is used only in Lemmas A/B, where the unknown is a **single** function, and there the
  separation comes from the *divergence rate* of the expansion (Bernoulli, factorial) rather than
  from any finite order.
- Cycle 3's no-go (`d = 1` is equivalent to the full conjecture) says degree induction is useless.
  Correct — the descent inducts on **order** and on `y_n`-degree of the minimal polynomial, using the
  difference structure, not on `Gamma`-degree.
- Cycle 4's shift closure is what makes `sigma` available at all; Lemma A is what makes the
  fixed-field step work.  The final proof keeps the closure and discards Hardouin--Singer: the
  descent supplies the reduction to first order by itself.

`[OPEN]` Not yet formalized.  Formalization order: `(N)` and Lemma A, then B1--B4, then B5
(needs the Bernoulli asymptotic expansion of `psi` and Dirichlet-series uniqueness), then C and the
descent.

---

## Cycle 6 (hgtl7): the algebraic engine of the descent, formalized in Lean

Three new modules, all unconditional, axioms exactly `propext, Classical.choice, Quot.sound`,
`scripts/formal_tools.py lint` passing, no `sorry`/`admit`/`axiom`/`opaque`/`unsafe`.

### `HTGeometry/ShiftTwistDescent.lean`

`shiftTwist sigma c P = (P.map sigma).comp (X + C c)` — the algebraic shadow of applying `s -> s+1`
to a polynomial relation among jets of a function `y` with `sigma y = y + c`.

| declaration | content |
|---|---|
| `shiftTwist_natDegree`, `shiftTwist_monic`, `shiftTwist_leadingCoeff` | degree, monicity, leading coefficient are preserved / transported by `sigma` |
| `isCoprime_shiftTwist` | coprimality is preserved (any ring hom does this) |
| `shiftTwist_coeff_sub_one` | `(tau P).coeff (d-1) = sigma (P.coeff (d-1)) + d * c * sigma (P.coeff d)` — via `taylor` / `hasseDeriv` |
| `defect_coeff_of_shiftTwist_eq` | a twist-fixed monic `D` of degree `d>0` forces `sigma v - v = -(d*c)` on its subleading coefficient |
| `shiftTwist_denom_fixed` | if `N/D` is in lowest terms with `D` monic and the twist moves it by a base element `w`, then `tau D = D` and `tau N = N + C w * D` |

`shiftTwist_denom_fixed` is the step that replaces the multivariate "lowest terms" argument of the
paper proof: it works one variable at a time, so only `Polynomial E` — a Euclidean domain — is
needed, never `MvPolynomial`.

### `HTGeometry/ShiftDefectDescent.lean`

`descentStep`: with `y` transcendental over `E`, `sigma y = y + c`, and the two tower hypotheses

* `hfix` — `sigma`-invariants of `E` are constants;
* `hdefect` — every `sigma`-defect of `E` lying in the admissible span `T` already lies in `W`;

any `b = N/D` in `E(y)` with `sigma b - b = w` in `T` satisfies `D = 1`,
`N = C (algebraMap a1) * X + C (N.coeff 0)`, and `w - algebraMap a1 * c` in `W`.

`descentStep_defect_mem` and `descentStep_fixed` re-derive `hdefect` and `hfix` one level up.  These
two corollaries are what make the tower induct: the engine is closed under passing from `E` to
`E(y)`.

### `HTGeometry/ShiftMinpolyTranscendence.lean`

`shiftTwist_minpoly`: the minimal polynomial of an algebraic `y` is twist-fixed (the twist maps
annihilators to annihilators and preserves monicity and degree, so minimality forces equality).

`transcendental_of_defect_unattainable`: if `c` is in `T` but not in `W`, then `y` is transcendental
over `E`.  **This is the paper proof's final contradiction, formalized**: an algebraic `y` of minimal
degree `e >= 1` would force the defect `-(e*c)` to be realised inside `E`, hence `e * c` in `W`,
hence `c` in `W` (char 0).

### What this is and what it is not

**Is.**  The complete *algebraic* engine of the Hölder-style descent, unconditional, with the tower
induction closed (step + both propagations + terminal contradiction).  Restructured relative to the
paper proof so that no multivariate lowest-terms argument is needed.

**Is not.**  Markus's conjecture.  The engine consumes two analytic inputs about the specific field
`Ktilde = C(s)<zeta(s+n) : n in Z>_D`, and neither is formalized:

1. **Lemma A** — `Ktilde^sigma = C`, i.e. `hfix` at the base.  Needs the far-right Dirichlet normal
   form `A(s) = R_A(s) rho^s (1 + O(kappa^{-s}))`.
2. **Lemma B** — `sigma f - f = L(1/s)` with `f` in `Ktilde` forces `L = 0`, i.e. `hdefect` at the
   base with `W = 0`.  Needs the same normal form plus the Bernoulli asymptotic expansion of `psi`
   and the factorial-vs-geometric comparison.  Mathlib does not currently carry the `psi` expansion
   in the required form; this is the largest remaining piece.

Also unformalized: instantiating the engine's tower on the `psi`-jets inside a concrete meromorphic
field, and the cycle-1/cycle-3 reduction from `Gamma`-jet relations to `psi`-jet relations.

So the correct label for Markus remains `[PAPER-PROVED]`.  What moved to `[LEAN-PROVED]` is the
descent engine, which is the part of the argument that is new; Lemmas A and B are analysis of a kind
that is standard in content but heavy in formalization.

---

## Cycle 7 (hgtl7): Bernoulli eliminated — Lemma B collapses to pole counting

### The simplification `[PROVED HERE]`

Cycle 5's Lemma B routed through the Bernoulli asymptotic expansion of `psi`, which is the single
heaviest formalization dependency in the whole proof (Euler--Maclaurin with Bernoulli remainder is
not in mathlib).  It is not needed.

In the case `rho = 1` we have `f(s) = R(s) + O(s^d kappa^{-s})` with `R` rational.  Instead of
comparing asymptotic expansions, observe that `R` satisfies the *same* difference equation up to an
exponentially small error, and run the argument on the difference:

```text
sigma f - f = L(1/s)   and   sigma R - R = L(1/s) + (exponentially small rational).
```

A rational function which is `O(N^d kappa^{-N})` along the positive integers is identically zero
(its asymptotics are `~ C N^k`).  Hence `sigma R - R = L(1/s)` **exactly**, and moreover
`sigma (f - R) = f - R`, so `f - R` is 1-periodic and tends to `0` along the reals, hence vanishes:
`f` *is* the rational function `R`.

So Lemma B reduces to a statement about `C(s)` alone:

> **no rational function has shift defect `L(1/s)` for nonzero `L`.**

This is the classical obstruction behind Hölder's theorem, and it is elementary.

### The elementary proof, and its formalization

Write `R = A/B` in lowest terms, `B` monic.  Among the roots of `B` choose `beta` of maximal real
part and `gamma` of minimal real part.  Then `beta + 1` is not a root, so `R(X+1)` is regular at
`beta` while `R` is not: `beta` is a genuine pole of `sigma R - R`.  Symmetrically `gamma - 1` is a
genuine pole.  If every pole sits at the origin then `beta = 0` and `gamma = 1`, contradicting
`gamma.re <= beta.re`.  Hence `B = 1`, `R` is a polynomial, and a degree count finishes it.

`HTGeometry/ShiftDefectRationalPole.lean` (unconditional; axioms `propext, Classical.choice,
Quot.sound`; lint passing; no `sorry`):

| declaration | content |
|---|---|
| `eval_num_ne_zero_of_isCoprime` | coprimality makes the numerator nonvanishing at a root of the denominator |
| `denom_eq_one_of_shift_defect_pole_at_zero` | the extremal shift-orbit argument: all poles of the defect at the origin forces `B = 1` |
| `no_rational_shift_antiderivative` | a nonzero `q / X^m` with `deg q < m` is never a shift defect of a rational function |

The whole file evaluates the cleared-denominator identity at two points; it needs no Laurent series,
no residues, and no asymptotic expansions.

### Remaining gap to a Lean proof of Markus

Only **one** analytic input is now left, used by both Lemma A and Lemma B:

> **(N)** for nonzero `f` in `Ktilde`, `f(s) = R(s) rho^s (1 + O(s^d kappa^{-s}))` as
> `s -> +infinity` along the reals, with `R` rational and `rho` a positive rational.

`(N)` follows from absolute convergence of the Dirichlet series of the generators; it is
bookkeeping about generalized Dirichlet series with rational coefficients, not deep analysis.  With
`(N)` in place:

* Lemma A is three lines (`rho = 1`, then a 1-periodic rational function is constant);
* Lemma B is the rational-function reduction above plus `no_rational_shift_antiderivative`;
* the descent engine (cycle 6) consumes both and produces differential transcendence.

The remaining non-analytic gap is instantiating the cycle-6 tower on the `psi`-jets inside a
concrete meromorphic differential field, plus the cycle-1/cycle-3 reduction from `Gamma`-jets to
`psi`-jets.

Markus stays `[PAPER-PROVED]`.  What changed this cycle is the *cost*: the proof no longer depends on
Euler--Maclaurin/Bernoulli at all, and the only analytic prerequisite left is Dirichlet-series
bookkeeping.

### Cycle 7 addendum: Lemma A's algebraic core is also formalized

`shift_invariant_rational_constant` (in `ShiftDefectRationalPole.lean`): if `A/B` is in lowest terms,
`B` monic, and `A(X+1) B(X) = A(X) B(X+1)`, then `B = 1` and `deg A = 0`.  Proof: the `w = 0` case of
`shiftTwist_denom_fixed` gives `B(X+1) = B(X)` and `A(X+1) = A(X)`; the subleading-coefficient
identity with `sigma = id`, `c = 1` then reads `0 = -deg`, killing both degrees.

So both Lemma A and Lemma B are now reduced to the *same* single analytic input `(N)`, and each of
their algebraic cores is Lean-proved:

| paper lemma | analytic input | algebraic core, Lean-proved |
|---|---|---|
| A (`Ktilde^sigma = C`) | `(N)` | `shift_invariant_rational_constant` |
| B (`sigma f - f = L(1/s)` forces `L = 0`) | `(N)` | `no_rational_shift_antiderivative` |
| descent | none | `descentStep`, `descentStep_defect_mem`, `descentStep_fixed`, `transcendental_of_defect_unattainable` |

### Honest remaining ledger for a Lean proof of Markus

1. `(N)` — far-right Dirichlet normal form for `Ktilde`.  Needs Dirichlet-series bookkeeping
   (products of absolutely convergent series with `C(s)` coefficients, extraction of the least
   index).  Substantial but elementary.
2. Analytic glue: "a 1-periodic function tending to `0` along the reals is `0`" and "a rational
   function that is `O(kappa^{-N})` along the naturals is `0`".  Small.
3. Instantiating the cycle-6 tower on the `psi`-jets inside a concrete meromorphic differential
   field with the shift automorphism.  Moderate.
4. The cycle-1/cycle-3 reduction from `Gamma`-jet relations to `psi`-jet relations.  Moderate.

This is a multi-session formalization.  Nothing above is conjectural: every item has a complete
paper proof on this card.

---

## Cycle 8 (hgtl7): the analytic input collapses to leading-term algebra

### The reduction `[PROVED HERE]`

Cycle 7 left one analytic prerequisite: the far-right Dirichlet normal form `(N)`.  It is not
needed either.  What is needed is only the **leading term** of a Dirichlet expansion.

Let `D` be the ring of Dirichlet series `sum_{m>=1} A_m(s) m^{-s}` with rational-function
coefficients, convergent in a right half-plane.  Uniqueness of such expansions makes `D` a domain
with a multiplicative index `ord` (least `m` with `A_m != 0`) and a multiplicative leading
coefficient `lead` in `C(s)`, and the shift acts by

```text
ord (sigma f) = ord f,      lead (sigma f)(s) = lead f (s+1) / ord f.
```

Take `f = P/Q` in the fraction field with `sigma f - f = r` in `C(s)`, so

```text
sigma P * Q - P * sigma Q = r * sigma Q * Q .
```

Put `m0 = ord P`, `m1 = ord Q`, `A = lead P`, `B = lead Q`.  The three cases are decided by
comparing indices, and each is closed by a *rational function* fact already Lean-proved:

* `m0 < m1`.  The right side has index `m1^2 > m0 m1`, so the leading terms on the left cancel:
  `A(s+1)/m0 * B(s) = A(s) * B(s+1)/m1`, i.e. `g := A/B` satisfies `g(s+1)/g(s) = m0/m1 != 1`.
  A shift preserves degree and leading coefficient of a rational function, so this forces
  `m0 = m1` — contradiction.
* `m0 > m1`.  Then `m1^2 < m0 m1`, so the left side has no term of index `m1^2` while the right
  side has `r(s) B(s+1) B(s) / m1 != 0` — contradiction.
* `m0 = m1 = m`.  Comparing coefficients at index `m^2` and dividing by `B(s) B(s+1)/m`:

```text
g(s+1) - g(s) = r(s),      g := A/B  in  C(s).
```

**This is the whole point.**  For Lemma B one needs only that *some* rational `g` has the same
defect — and `no_rational_shift_antiderivative` then gives `L = 0`.  For Lemma A (`r = 0`) one gets
`g` constant from `shift_invariant_rational_constant`, and then `P - gQ` must vanish, since
otherwise `ord (P - gQ) > m1` puts it in the impossible second case.

So **no asymptotic expansion is used anywhere**: only uniqueness of Dirichlet expansions (to make
`ord` and `lead` well defined and multiplicative), which itself follows from the already-formalized
`eq_zero_of_norm_eval_le_geometric` — a rational function exponentially small along the naturals is
zero.

### Consequence for the base field

One never needs to characterise `Ktilde`.  Take the base to be the fraction field of `D` itself: it
contains `C(s)`, all `zeta`-jets and all their integer shifts, is `sigma`-stable, and satisfies both
Lemma A and Lemma B by the argument above.  Transcendence over it implies transcendence over
`C(s)<zeta>_D`.

### Cycle 8 formalization: both lemmas proved in the abstract Dirichlet-lead setting

`HTGeometry/DirichletLeadingTerm.lean` (unconditional; axioms `propext, Classical.choice,
Quot.sound`; lint passing; no `sorry`).

`DirichletLead D` axiomatises the least index `ord`, the leading coefficient `lead` in `C[X]`, their
multiplicativity, the shift law `C (ord f) * lead (sigma f) = (lead f)(X+1)`, and the behaviour of
subtraction on the least index.

| declaration | content |
|---|---|
| `nat_eq_of_scaled_shift_eq` | `C k * (A(X+1) * B) = C l * (A * B(X+1))` forces `k = l`, by comparing top coefficients |
| `ord_eq_of_rel` | numerator and denominator of a ratio with rational shift defect have the *same* least index — the three-case argument |
| `lead_shift_identity` | the ratio of leading coefficients has the same shift defect as `P/Q` |
| `exists_coprime_monic_shift_identity` | normalisation of such an identity to a coprime pair with monic denominator |
| `eq_const_mul_of_shift_ratio_fixed` | a shift-invariant ratio of polynomials is a constant multiple |
| `no_pole_defect` | **Lemma B**: no element of the fraction field has shift defect `q / X^m` with `q != 0`, `deg q < m` |
| `eq_const_mul_of_sigma_fixed` | **Lemma A**: a shift-invariant element of the fraction field is a constant — via the `P - aQ` step, whose leading term vanishes, forcing `P = aQ` |

Both lemmas are now Lean-proved *given* the `DirichletLead` interface.  What remains on the analytic
side is the single construction of that interface on concrete Dirichlet series with polynomial
coefficients: summability, convolution for `coeff_mul`, and uniqueness of expansions (which is
`eq_zero_of_norm_eval_le_geometric`, already proved).

### Cycle 8 formalization, part 2: the concrete instance

`HTGeometry/DirichletFormal.lean` — `DirFormal := ArithmeticFunction (C[X])`, Dirichlet series with
polynomial coefficients under Dirichlet convolution (mathlib supplies the `CommRing`).

| declaration | content |
|---|---|
| `mul_coeff_eq_zero_of_lt`, `mul_coeff_at` | below `ord f * ord g` every convolution term vanishes; at `ord f * ord g` exactly one survives |
| `ord_mul'`, `lead_mul'`, `mul_ne_zero''` | multiplicativity of the least index and leading coefficient; the ring is a domain |
| `sigmaEquiv` | the shift `A_m(s) -> A_m(s+1)/m` as a ring **automorphism** — multiplicative exactly because the convolution is indexed by factorisations, so `(ab)^{-1} = a^{-1} b^{-1}` |
| `embHom` | the index-one embedding of `C[X]` |
| `dirichletLead` | **the `DirichletLead` interface, fully discharged** |

So Lemma A (`eq_const_mul_of_sigma_fixed`) and Lemma B (`no_pole_defect`) now hold unconditionally
for the concrete ring of Dirichlet series.

`HTGeometry/DirichletUniqueness.lean` starts the realisation: `IsBoundedBy f d C A` (uniform degree
bound and polynomial size bound on the coefficients) and `norm_eval_le_of_isBoundedBy`, the pointwise
control `‖(f m)(s)‖ <= (d+1) C m^A s^d` needed for absolute convergence and for the tail estimate in
the uniqueness proof.

**Remaining for Markus.** The realisation map `DirFormal -> meroField` on bounded series and its
injectivity (the tail bound plus `eq_zero_of_norm_eval_le_geometric`, both of whose ingredients are
in place), then the tower instantiated on the `psi`-jets with `c n = (-1)^n n!/s^(n+1)`, then the
`Gamma`-jet to `psi`-jet reduction of cycles 1 and 3.

### Cycle 8, part 3: convergence and uniqueness of Dirichlet expansions

`HTGeometry/DirichletUniqueness.lean`.

| declaration | content |
|---|---|
| `IsBoundedBy f d C A` | uniform degree bound `d` and size bound `‖(f m).coeff i‖ <= C m^A` |
| `norm_eval_le_of_isBoundedBy` | `‖(f m)(s)‖ <= (d+1) C m^A s^d` for `s >= 1` |
| `realize` | the sum `sum_m (f m)(s) m^(-s)` at a real point |
| `summable_norm_realize`, `summable_realize` | absolute convergence for `s >= A + 2`, majorised by `(d+1) C s^d * sum 1/m^2` |
| `eq_zero_of_realize_eq_zero` | **uniqueness**: a bounded series whose sum vanishes along the naturals is the zero series |

The uniqueness proof is the one designed in cycle 8: split off the least index `m0`, bound the tail
by `L * sum 1/m^2` with `L = (d+1) C n^d (m0+1)^(A+2-n)`, and divide by `m0^(-n)` to reach

```text
‖(f m0)(n)‖ <= K * n^d * (m0/(m0+1))^n ,
```

a geometric bound of ratio `< 1`; `eq_zero_of_norm_eval_le_geometric` then kills `f m0`,
contradicting minimality of `m0`.  No asymptotic expansion is used — only the coefficient bound and
the polynomial decay principle.

---

## Cycle 9 (hgtl7): corpus audit — the realisation layer already exists

A proper corpus search (which I should have run before cycle 8 part 3) shows the analytic
realisation layer is **already formalised**.  Use these; do not rebuild.

| corpus declaration | file | what it gives |
|---|---|---|
| `finiteAbscissaLSeriesToUpperEndGerm_injective` | `HTGeometry/FiniteAbscissaDirichletUpperEnd.lean:274` | **uniqueness of Dirichlet expansions** — equality of upper-end L-series germs determines every coefficient |
| `finiteAbscissaLSeriesToUpperEndMero` (+ `_injective`) | `HTGeometry/PrimeResidueValuationAnalyticSuperselection.lean:91` | the faithful realisation ring hom into `upperEndMeroField` |
| `finiteAbscissaLSeriesToUpperEndMero_dirichletShift` | `HTGeometry/FiniteAbscissaRationalCoordinateIndependence.lean:98` | **shift intertwiner**: coefficient-side Dirichlet translation = meromorphic translation `upperEndTranslationMeroEquiv (I*a)`; `a = -I` gives translation by `1` |
| `upperEndCoordinateMero_transcendental_over_finiteAbscissaFraction` | same file, line 348 | the coordinate `s` is transcendental over the Dirichlet fraction field — exactly the injectivity needed for **polynomial-coefficient** series, since `sum_m A_m(s) m^{-s} = sum_j s^j (sum_m a_{m,j} m^{-s})` is a polynomial in `s` over the Dirichlet field |
| `finiteAbscissaFractionToUpperEndMero_injective` | same file, line 301 | fraction-field version |
| `digamma_recurrence`, `digamma_telescope` | `HTGeometry/GammaDifferentialFE.lean:3063,3110` | `psi(s+1) = psi(s) + 1/s` |
| `oneDivGamma_logDeriv_eq_neg_digamma` | same, line 3778 | `psi` as a log-derivative, giving its meromorphy |
| `algebraicIndependent_gamma_and_digamma_initialJets` | `HTGeometry/GammaDigammaMixedJetMatroidUniversalityLaw.lean:36` | `Gamma` with all `psi`-jets through order `n` algebraically independent over `C` |
| `hypertranscendentalOver_upperEndTranslationMeroEquiv_differentialAdjoin_image_iff` | `HTGeometry/UpperEndRationalCoordinateDifferentialAdjoin.lean:301` | translation covariance of hypertranscendence |

**Duplication found.** `DirichletUniqueness.eq_zero_of_realize_eq_zero` re-proves
`finiteAbscissaLSeriesToUpperEndGerm_injective` in a different model (real ray vs upper-end filter,
polynomial vs complex coefficients).  It is not wasted — it is the polynomial-coefficient version and
its proof is by the forward-difference decay principle rather than by the corpus's route — but it was
not necessary, and the corpus route is the one to use for assembly.

**Not duplicated.**  Nothing in the corpus does a Hölder-style *difference descent*.
`CommutingDifferenceDifferentialField` records additive defect fingerprints, not a minimal-polynomial
descent.  So the genuinely new layer of cycles 5-8 is: `shiftTwist` calculus, `descentStep` with both
propagations, `transcendental_of_defect_unattainable`, `jetTower_transcendental`,
`no_rational_shift_antiderivative`, and the `DirichletLead` leading-term reduction with Lemmas A/B.

### Revised assembly plan (use corpus, do not rebuild)

```text
K   := upperEndMeroField
sigma := upperEndTranslationMeroEquiv 1          -- = dirichletShift (-I) on coefficients
F   := compositum of C(s) and the finite-abscissa Dirichlet fraction field   (sigma-stable)
y n := germ of psi^(n)        c n := germ of (-1)^n n! / s^(n+1)
```

`hy` is `digamma_recurrence` differentiated `n` times; `hcF` is immediate; `hindep` is distinct pole
orders; `hfixF`/`hdefF` are Lemmas A/B transported along the corpus's injective realisation using
`DirichletLead`.  Then `jetTower_transcendental` gives differential transcendence of `psi` over `F`,
hence over `C(s)<zeta>_D`, and the cycle-1/cycle-3 reduction converts `Gamma`-jet relations to
`psi`-jet relations.

### Cycle 9 formalization: the digamma shift datum in the corpus carrier

`HTGeometry/UpperEndDigammaShift.lean` (unconditional; axioms `propext, Classical.choice,
Quot.sound`; lint passing; no `sorry`).

`psi = Gamma'/Gamma` is analytic on every upper half-plane (the poles of `Gamma` are real), so it is
an element of the corpus's `upperEndAnalyticSubring`, as is `1/s`.  `digamma_recurrence` then gives a
*single* identity of upper-end germs:

```text
upperEndTranslationMeroEquiv 1 digammaMero = digammaMero + invCoordMero .
```

`upperEndTranslate_digammaJetMero` upgrades this to every jet:

```text
sigma (delta^n psi) = delta^n psi + delta^n (1/s)      for all n,
```

by induction using the corpus's `upperEndTranslationMeroEquiv_deriv` (translation commutes with the
field derivation).  **No analysis beyond the `n = 0` case is used** — the jets are defined
algebraically as `differentialJet n`, not as iterated `deriv` of a function, so the whole tower of
shift relations follows from one germ identity.

This is hypothesis `hy` of `jetTower_transcendental`, discharged at the concrete carrier.

### Cycle 9: obstruction found in the defect power law

`defectJetMero_eq` (`delta^n (1/s) = (-1)^n n! (1/s)^(n+1)`) does **not** go through directly: the
`Differential` class carries `Derivation ℤ R R`, and on `upperEndMeroField` the ℤ-algebra structure
synthesised by `OreLocalization.instAlgebra` is not definitionally the `Ring.toIntAlgebra` one that
`Derivation.leibniz_pow` / `map_natCast` elaborate against.  Every use of a generic `Derivation`
lemma on this carrier hits that diamond.

**Route for the next cycle:** avoid generic `Derivation` lemmas entirely on this carrier.  Prove the
power law by descending to analytic germs, where `upperEndAnalyticDeriv` is ordinary `deriv` of a
representative and `deriv (fun z => z⁻¹ ^ (n+1))` is a direct computation, then push forward with
`upperEndMeroFieldDifferential_algebraMap`.  The corpus already computes with
`upperEndAnalyticDeriv_mul` and `upperEndAnalyticDeriv_add` in exactly this style, so the diamond is
never met.

### Cycle 9 result: the diamond cleared, the defect sequence in closed form

The `Derivation`-instance diamond diagnosed above is avoided by computing **downstairs on analytic
germs** and pushing forward with `upperEndMeroFieldDifferential_algebraMap`; no generic `Derivation`
lemma is ever applied to the fraction field.

`HTGeometry/UpperEndDigammaShift.lean`, all unconditional (axioms `propext, Classical.choice,
Quot.sound`; no `sorry`; lint passing):

| declaration | content |
|---|---|
| `digammaMero`, `invCoordMero`, `coordMero` | `psi`, `1/s`, `s` as upper-end elements |
| `upperEndTranslate_digammaMero` | `digamma_recurrence` as one germ identity |
| `upperEndTranslate_digammaJetMero` | `sigma (delta^n psi) = delta^n psi + delta^n (1/s)` for all `n` |
| `deriv_invPowFun`, `upperEndAnalyticDeriv_invPowAnalytic` | the germ-level recursion for `(-1)^n n!/z^(n+1)` |
| `defectJetMero_eq` | `delta^n (1/s)` is that germ |
| `invCoordMero_mul_coordMero` | `(1/s) * s = 1` |
| `defectJetMero_mul_coordMero_pow` | `delta^n (1/s) * s^(n+1) = (-1)^n n!`, a nonzero constant |
| `defectJetMero_eq_smul_pow` | `delta^n (1/s) = (-1)^n n! * (1/s)^(n+1)` |

`hy` of `jetTower_transcendental` is discharged, and the defect family is in exactly the shape
`hindep` needs: a dependence relation, multiplied by `s^(n+1)`, becomes a polynomial identity in the
coordinate with nonzero constant term `(-1)^n n!`, contradicting
`upperEndCoordinateMero_transcendental_over_finiteAbscissaFraction`.

**Remaining:** `hindep` from that identity; the `sigma`-stable base `F` (compositum of `C(s)` with the
finite-abscissa Dirichlet fraction field); `hfixF`/`hdefF` transported from Lemmas A/B along
`finiteAbscissaLSeriesToUpperEndMero_injective`; the `Gamma`-jet to `psi`-jet reduction.

### Cycle 9 close: psi side complete; the base-field milestone identified

Discharged at the concrete carrier (`UpperEndDigammaShift.lean`, all unconditional):

| `jetTower_transcendental` hypothesis | declaration |
|---|---|
| `hy` : `sigma (delta^n psi) = delta^n psi + c n` | `upperEndTranslate_digammaJetMero` |
| `hindep` : `c n` not in `span C {c k : k < n}` | `defectJetMero_not_mem_span` |
| (its input) coordinate transcendence | `transcendental_coordMero` |

`defectJetMero_not_mem_span` is proved by `Submodule.span_induction` on the predicate "multiplying by
`s^(n+1)` lands in the image of a polynomial with vanishing constant term": every generator `c k`
with `k < n` gives `c k * s^(n+1) = a_k * s^(n-k)` with `n - k >= 1`, while `c n * s^(n+1) = a_n` is a
nonzero constant; subtracting yields a nonzero polynomial annihilating the coordinate.

### The next milestone: `F = C(s)` gives Hölder end to end

The base field of `jetTower_transcendental` is a parameter.  Taking

```text
F := C(s)   (the image of  RatFunc C -> upperEndMeroField,  IsFractionRing.lift upperEndPolyToMero_injective)
```

all four remaining hypotheses are already available:

* `hcF` — the defects are rational in `s`, by `defectJetMero_eq_smul_pow`;
* `hFstab` — translation preserves `C(s)`;
* `hfixF` — `shift_invariant_rational_constant` (Lean-proved);
* `hdefF` — `no_rational_shift_antiderivative` (Lean-proved).

That instantiation yields **Hölder's theorem** — `psi` differentially transcendental over `C(s)` —
unconditionally at the concrete carrier, and it exercises the entire chain end to end.  Markus is then
exactly the same instantiation with the base enlarged from `C(s)` to the compositum of `C(s)` with
the finite-abscissa Dirichlet fraction field, where `hfixF`/`hdefF` come from Lemmas A/B
(`eq_const_mul_of_sigma_fixed`, `no_pole_defect`) transported along
`finiteAbscissaLSeriesToUpperEndMero_injective` via `DirichletLead`.

So the remaining work is a **base-field swap**, not new mathematics: the descent, the defect data, and
both lemmas are all Lean-proved; what is missing is the `IntermediateField` plumbing for the two
bases and the `Gamma`-jet to `psi`-jet reduction.

### Cycle 9: `hFstab` attempt and the exact snag

`ratBase_stable` (translation stability of `C(s)`) is the next hypothesis.  The induction skeleton is
right — `IntermediateField.adjoin_induction` over `C` with the two generator facts
`sigma s = s + 1` (`upperEndTranslate_coordMero`) and `sigma^{-1} s = s - 1` — but two unfoldings
must be handled first, and the attempt was reverted rather than left broken:

1. `algebraMap C upperEndMeroField = upperEndComplexToMero = upperEndPolyToMero.comp Polynomial.C`,
   **not** `algebraMap upperEndAnalyticSubring _`.  So `upperEndTranslationMeroEquiv_algebraMap`
   does not apply directly; first rewrite `upperEndPolyToMero (C a)` as
   `algebraMap upperEndAnalyticSubring _ (upperEndPolyToAnalytic (C a))` (definitional), then the
   corpus lemma applies and the constant germ is visibly translation-invariant.
2. `RingEquiv` does not carry `AddHomClass` for the `map_sub`/`map_add` rewrites used inside the
   induction; use `(upperEndTranslationMeroEquiv 1).toRingHom` or the explicit `map_add`/`map_mul`
   for `RingEquiv` instead of relying on class inference (which times out).

Neither is mathematical: both are unfolding steps against the corpus's constant-field encoding.

---

## Cycle 9 milestone: Hölder's theorem Lean-proved through the new descent engine

`GaloisForLFunctions.HTGeometry.digamma_jets_transcendental` (unconditional; axioms
`propext, Classical.choice, Quot.sound`; no `sorry`; lint passing):

> every digamma jet is transcendental over the field generated by `C(s)` and its predecessors.

It is a single application of `jetTower_transcendental` to six hypotheses, each proved here:

| hypothesis | declaration |
|---|---|
| `hFstab` | `ratBase_stable` |
| `hcF` | `defectJetMero_mem_ratBase` |
| `hy` | `upperEndTranslate_digammaJetMero` |
| `hfixF` | `ratBase_fixed_const` |
| `hdefF` | `ratBase_defect_eq_zero` |
| `hindep` | `defectJetMero_not_mem_span` |

Supporting: `transcendental_coordMero`, `aeval_coordMero_injective`,
`upperEndTranslate_aeval_coordMero` (translation acts by `P -> P(X+1)`),
`defectSpan_shape` (every defect-span element is `q/s^m` with `deg q < m`),
`defectJetMero_eq_smul_pow`, `translationAlgEquiv`.

**Why this matters for Markus.** The proof is a *base-field-parametric* application: nothing in the
chain is specific to `C(s)`.  Markus is the identical call with `ratBase` replaced by the compositum
of `C(s)` with the finite-abscissa Dirichlet fraction field, where

* `hfixF` comes from `DirichletLead.eq_const_mul_of_sigma_fixed` (Lemma A),
* `hdefF` comes from `DirichletLead.no_pole_defect` (Lemma B),

both already Lean-proved, transported along the corpus's
`finiteAbscissaLSeriesToUpperEndMero_injective`; `hcF`, `hFstab`, `hy`, `hindep` are unchanged
(the defects are already rational, hence in the smaller base).

**Remaining for Markus:** (i) the compositum as an `IntermediateField` with `hFstab`; (ii) the
transport of Lemmas A/B to its elements via the injective realisation and `DirichletLead`;
(iii) the `Gamma`-jet to `psi`-jet reduction of cycles 1 and 3.

### Cycle 9: the `Gamma`-jet to `psi`-jet reduction does not need cycle 1's analysis

Cycles 1 and 3 reduced `Gamma`-jet relations to `psi`-jet relations by the vertical-asymptotic
stratification — a genuinely analytic argument.  **That is not needed.**  `Gamma` satisfies

```text
Gamma' = psi * Gamma ,
```

so `Gamma` is *differentially algebraic* over `C(s)<psi>_D`; hence

```text
C(s)<Gamma>_D = C(s)(Gamma)<psi>_D
```

is a differentially algebraic extension of `C(s)<psi>_D`.  The corpus already has the base-change
law:

* `hypertranscendentalOver_differentialAdjoin_iff` (`HTGeometry/DifferentialAlgebraicBaseChange.lean:163`)
  — hypertranscendence is unchanged after adjoining an arbitrary set of differentially algebraic
  coefficients;
* `hypertranscendentalOver_differentialAdjoinSingleton_iff` (same file, line 227) — the one-element
  version.

So `zeta` hypertranscendental over `C(s)<psi>_D` implies `zeta` hypertranscendental over
`C(s)<Gamma>_D`, which is Markus.  And `zeta` hypertranscendental over `C(s)<psi>_D` is the
*symmetric* form of the theorem this session proves (`psi` hypertranscendental over `C(s)<zeta>_D`):
both say the `zeta`-jets and `psi`-jets are jointly algebraically independent over `C(s)`, given that
each family is independent on its own (Ostrowski for `zeta` is
`GaloisForLFunctions.hypertranscendental_riemannZeta`, already in the corpus; Hölder for `psi` is now
`digamma_jets_transcendental`).

This replaces the whole cycle-1 stratification with two corpus lemmas plus a symmetry step, and
removes the last analytic dependency from the route.

**Remaining for Markus, final form:** (i) the compositum base and the transport of Lemmas A/B to it
along `finiteAbscissaLSeriesToUpperEndMero_injective` (giving `psi` hypertranscendental over
`C(s)<zeta>_D`); (ii) the symmetry step to `zeta` over `C(s)<psi>_D`; (iii) the DA base change
above.  No further analysis is required at any point.

### Cycle 9: step (iii) is a two-line corpus application — signatures verified

```lean
theorem hypertranscendentalOver_differentialAdjoinSingleton_iff
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {x g : E} (hg : DifferentialAlgebraicOver F g) :
    HypertranscendentalOver (differentialAdjoin F ({g} : Set E)) x ↔
      HypertranscendentalOver F x
```

and

```lean
theorem differentialAlgebraicOver_of_deriv_eq_base_mul_add   -- AffineFirstOrderDifferentialAlgebraicity.lean:20
    -- `y' = a y + b` with `a b` in the base  =>  `y` is differentially algebraic over it
```

Instantiate with `F = C(s)<psi>_D`, `g = Gamma`, `x = zeta`.  The hypothesis is exactly
`Gamma' = psi * Gamma + 0`, i.e. `Gamma' = psi * Gamma`, which is the defining relation of `psi`
(corpus: `oneDivGamma_logDeriv_eq_neg_digamma`, `GammaDifferentialFE.lean:3778`).  Then

```text
zeta hypertranscendental over C(s)<psi>_D   <->   zeta hypertranscendental over C(s)<Gamma>_D
```

and the right-hand side **is Markus**.  So step (iii) needs no new mathematics and no analysis: it is
`differentialAlgebraicOver_of_deriv_eq_base_mul_add` followed by
`hypertranscendentalOver_differentialAdjoinSingleton_iff`.

Updated remaining list for Markus:
1. the compositum base `C(s)` with the finite-abscissa Dirichlet fraction field, plus transport of
   Lemmas A/B along `finiteAbscissaLSeriesToUpperEndMero_injective` — gives `psi` hypertranscendental
   over `C(s)<zeta>_D`;
2. the symmetry step (joint algebraic independence of `zeta`-jets and `psi`-jets over `C(s)`, using
   `hypertranscendental_riemannZeta` and `digamma_jets_transcendental`) — gives `zeta`
   hypertranscendental over `C(s)<psi>_D`;
3. the two-line corpus application above.

### Cycle 9: the coordinate convention forces the shift direction — a real obstruction, and its fix

`DirichletPolyLead.lean` now carries `dirichletLeadPoly : DirichletLead DirPoly` for
`DirPoly = Polynomial (ArithmeticFunction C)`, via the new general transport
`DirichletLead.comap` (transport along any injective ring hom intertwining the shifts and the
index-one embeddings).  So Lemmas A and B hold unconditionally in the coefficient-first form.

**But the shift conventions do not yet match, and this is not cosmetic.**

* The corpus realises Dirichlet translation as
  `finiteAbscissaLSeriesToUpperEndMero (dirichletShift a f) = upperEndTranslationMeroEquiv (I*a) (...)`.
  Since `upperEndFilter = comap Complex.im atTop`, the Dirichlet variable is `s = -I z`; a shift
  `s -> s + a` is `z -> z + I a`.
* My `psi` setup uses `z -> z + 1`, i.e. `a = -I`, whose coefficient-side action is
  `f n -> f n * n^I`, **not** `f n / n`.

`DirichletLead.lead_sigma` is stated with the scalar `1 / ord f`.  Generalising it to a scalar
function `chi(m) = m^{-a}` is easy, but `ord_eq_of_rel`'s `m0 < m1` case then needs `chi` injective
on positive naturals.  For `chi(m) = m^I` that is equivalent to `m/n != exp(2*pi*k)` for `k != 0`,
i.e. to irrationality of `exp(2*pi)` — not in mathlib and not cheap.

**Fix (no new mathematics, mechanical): re-coordinate `psi`.**  Put

```text
psiTilde z := psi (-I * z) ,     sigma := upperEndTranslationMeroEquiv I .
```

Then `psiTilde (z + I) = psi (-I z + 1) = psi (-I z) + 1/(-I z) = psiTilde z + I/z`, so the defect is
`I/z` — still rational, with `delta^n (I/z) = I * (-1)^n n! / z^(n+1)`, the same shape as before.
On the Dirichlet side `sigma` is now `dirichletShift 1`, whose coefficient action is `f n -> f n / n`
— exactly `dshift`, matching `lead_sigma` as stated.

Every lemma in `UpperEndDigammaShift.lean` transfers verbatim with `1` replaced by `Complex.I` in the
translation and `psi` by `psiTilde`; `psiTilde` is analytic on every upper half-plane because
`Re(-I z) = Im z` is large there, so it stays away from the poles of `Gamma`.

This is the last convention mismatch in the route; nothing downstream changes.

### Cycle 9: the general-shift lemmas are in; the re-coordination is the next mechanical step

`ShiftDefectRationalPole.lean` now carries the **arbitrary-shift** forms, all unconditional:

| declaration | content |
|---|---|
| `denom_eq_one_of_shift_defect_pole_at_zero_gen` | extremal shift-orbit obstruction for any `h != 0` |
| `no_rational_shift_antiderivative_gen` | Hölder's obstruction for shift `h` |
| `shift_invariant_rational_constant_gen` | an `h`-shift-invariant rational function is constant |

The generalisation turns on one point: the extremal element of a shift orbit is selected not by `Re`
but by the linear functional `z -> (z/h).re`, which increases by exactly one along `beta -> beta + h`.
With that substitution the whole argument goes through verbatim for any nonzero `h`.

**Re-coordination checklist** (attempted, reverted to keep the tree clean; every item is mechanical):

1. `digammaFun z := deriv Gamma (-I*z) / Gamma (-I*z)`; analyticity via `AnalyticOnNhd.comp` with
   `z -> -I*z`, using `Re(-I*z) = Im z > 0` on `upperTail 0` (so the argument avoids the poles) —
   the helper `rot_re_pos` / `rot_ne_negNat` is the piece to add.
2. Recurrence: `-I*(z+I) = -I*z + 1`, so `digamma_recurrence (-I*z)` gives
   `digammaFun (z+I) = digammaFun z + 1/(-I*z)` and `1/(-I*z) = I/z`.
3. Defect `invCoordFun z := I/z`; `invPowFun n z := I * (-1)^n * n! * (z^(n+1))^{-1}`;
   `defectConst n := I * (-1)^n * n!`; `invCoordMero * coordMero = I` (still a nonzero constant, so
   the `ratBase` membership arguments are unchanged).
4. Replace `upperEndTranslation*Equiv 1` by `... Complex.I` and `X + C 1` by `X + C Complex.I`
   throughout; the two rational-function applications then call the `_gen` lemmas with `h = I`.

Only item 1 needs new proof text; items 2-4 are substitutions.

### Cycle 9: the digamma in the Dirichlet coordinate

`HTGeometry/UpperEndDigammaRotated.lean` (unconditional; axioms `propext, Classical.choice,
Quot.sound`; no `sorry`; lint passing):

```text
rotDigammaFun z := psi (-I * z)
```

| declaration | content |
|---|---|
| `rot_re_pos`, `rot_ne_negNat` | on `upperTail 0` the rotated argument has `Re (-I z) = Im z > 0`, so it avoids the poles of `Gamma` |
| `analyticOnNhd_Gamma_rightHalf` | `Gamma` is analytic on the open right half-plane |
| `analyticOnNhd_rotDigamma` | `rotDigammaFun` is analytic on every upper half-plane, by composing with the rotation |
| `rotDigamma_recurrence` | **`rotDigammaFun (z + I) = rotDigammaFun z + I / z`**, from `-I (z + I) = -I z + 1` |

This is the shift datum in the coordinate the corpus's Dirichlet realisation actually uses: the shift
constant is now `I`, matching `translationMero (I * a)` with `a = 1`, whose coefficient action is
`f n -> f n / n` — exactly `dshift`, i.e. exactly `DirichletLead.lead_sigma`.

Together with the arbitrary-shift lemmas `no_rational_shift_antiderivative_gen` and
`shift_invariant_rational_constant_gen`, every ingredient of the `psi` side is now available in the
`I`-shift convention; the remaining step is to repeat the germ/jet/base constructions of
`UpperEndDigammaShift.lean` with `1` replaced by `I` and `1/z` by `I/z`.
