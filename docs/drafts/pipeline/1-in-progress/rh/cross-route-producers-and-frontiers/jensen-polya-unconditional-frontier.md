# The Jensen–Pólya lane: exact frontier, the corpus's blind spot, and why the slick route is closed

- **ID:** `jensen-polya-unconditional-frontier`
- **Stage:** 1-in-progress
- **Type:** CONTEXTUALIZATION + two structural findings
- **Scientific status:** `[LITERATURE STATUS VERIFIED]` `[TWO FINDINGS DERIVED HERE]`
  `[NOT AN RH PROOF]` `[FINDINGS NOT CLAIMED NOVEL — see section 6]`
- **Why this lane:** it satisfies all four conditions I require of a target: precisely stated, open
  in the literature, RH-bearing, and matched by an existing corpus substrate
  (`XiCTaylorTheta*`, ~40 modules on the Taylor coefficients of Xi via theta tails).

## 1. Pólya's criterion and the exact literature frontier

For `d, n ≥ 0` define `gamma(n)` by `(-1 + 4z^2) Lambda(1/2 + z) = sum_n gamma(n) z^(2n)/n!` and

```text
J^(d,n)(X) := sum_(j=0)^d binom(d,j) gamma(n+j) X^j.
```

**Pólya (1927):** RH is equivalent to hyperbolicity (all roots real) of `J^(d,n)` for every `d, n`.

Verified status as of July 2026:

| result | statement | unconditional? |
|---|---|---|
| Csordas–Norfolk–Varga 1986; Dimitrov–Lucas 2010 | `d ≤ 3`, all `n ≥ 0` | **yes, by analysis** |
| Griffin–Ono–Rolen–Zagier 2019 (PNAS) | for each `d`, hyperbolic for all `n ≫_d 1` | yes |
| Griffin–Ono–Rolen–Thorner–Tripp–Wagner, *Adv. Math.* 2022, Thm 1.1 | there is `c > 0` with `J^(d,n)` hyperbolic for `d ≥ 1`, `n ≥ c e^(d/2)` | yes |
| ibid. Thm 1.2 | if `RH_m(T)` and `d ≤ floor(T)^2` then `J^(d,n)` hyperbolic for all `n ≥ m` | **no** — needs RH verified to height `T` |
| ibid. Cor 1.3 (with Platt's `RH_0(3.06 × 10^10)`) | `d ≤ 9.36 × 10^20`, all `n ≥ 0` | no (rests on a computation) |
| Chasse | `d ≤ 2 × 10^17`, all `n ≥ 0` | rests on a computation |

**The uncovered region is exactly `d > 9.36 × 10^20` together with `n < c e^(d/2)`, and that region is
all of RH.** Under this project's "no computations" rule the honest pure-analysis frontier is
**`d = 4`, all `n`** — CNV and Dimitrov–Lucas stop at `d = 3`.

Also note: hyperbolicity of `J^(d,n)` for all `d` at the *single* shift `n = 0` is already
equivalent to RH, since `J^(d,n)` hyperbolic for all `d` at fixed `n` says exactly that the `n`-th
derivative lies in the Laguerre–Pólya class. So the lane does not need every `n`.

## 2. Corpus blind spot: the whole lane is easy-direction only

`formal_tools.py research` over the Laguerre/Pólya surface returns
`XiLaguerrePolya.lean` and `LaguerreInequality.lean`, and **every theorem in them is `_of_rh`**:
`xi_laguerrePolya_of_rh`, `xi_laguerre_inequality_of_rh`, `xiPairedPolynomial_eval_eq_product_of_rh`,
`xiCanonicalProduct_laguerre_re_of_rh`. The corpus assumes RH and deduces the Laguerre inequality.
There is **no Jensen polynomial, no hyperbolicity predicate, and no unconditional Turán inequality**
anywhere in the tree.

This is precisely the failure mode the novelty gate exists to catch: an entire RH-equivalent lane
present in the corpus only in its trivial direction. Recorded as a finding, not as work done.

## 3. Finding A — the barrier is the saddle point, and it explains `e^(d/2)` exactly

Why does the unconditional method stop at `n ≥ c e^(d/2)`?

Write the classical kernel `Phi(u) = sum_(k≥1) (2 pi^2 k^4 e^(9u/2) − 3 pi k^2 e^(5u/2)) e^(−pi k^2 e^(2u))`,
so that `Xi(t) = 2 int_0^inf Phi(u) cos(ut) du` and the *un-normalized* even moments are

```text
b_n = 2 int_0^inf Phi(u) u^(2n) du  >  0.
```

The Laplace exponent is `2n log u + log Phi(u)`, and for large `u` the `k = 1` term dominates with
`log Phi(u) ≈ 9u/2 − pi e^(2u)`. The saddle satisfies `2n/u ≈ 4 pi e^(2u) − 9/2`, i.e.

```text
e^(2u) ≈ n/(2 pi u),        u_n = (1/2) log n − (1/2) log log n + O(1).
```

The expansion of the integrand about the saddle produces corrections in powers of `1/u_n`, so **the
natural asymptotic parameter of the Xi Taylor coefficients is `1/u_n ≍ 1/log n`**. The Hermite
comparison needs `d` terms of that expansion, hence `d ≲ log n`, hence `n ≳ e^(c d)`. That is
Theorem 1.1's `e^(d/2)`, and the match is not a coincidence: it is the same saddle.

**Consequence stated as a target, not a theorem:** any method that reaches the region `d ≫ log n`
must avoid expanding `gamma(n)` in the saddle parameter. Substituting `v = pi k^2 e^(2u)` turns the
moments into incomplete-Gamma derivatives `int_a^inf v^(s−1) e^(−v) (log(v/a))^(2n) dv`, exact and
asymptotic-free — but the asymptotics of `Gamma^((2n))(s)` have their own saddle at `v log v ≈ 2n`,
i.e. `log v ≈ log n − log log n`, so the logarithmic parameter reappears. **The `1/log n` scale is a
property of the double-exponential decay of the theta kernel, not an artifact of the method.**

## 4. Finding B — there is no positive-kernel integral form of the Jensen polynomials, and the
   renormalization is what destroys it

The slick attack is this. If `gamma(n) = int_0^inf Psi(v) v^n dv` for a positive `Psi`, then by the
binomial theorem

```text
J^(d,n)(X) = int_0^inf Psi(v) v^n (1 + vX)^d dv,                      (*)
```

and hyperbolicity questions for such "moment polynomials" are classical and comparatively easy.

**`(*)` is impossible.** A Stieltjes moment sequence is log-*convex* by Cauchy–Schwarz:
`(int Psi v^n)^2 ≤ (int Psi v^(n−1))(int Psi v^(n+1))`. But the Turán inequality
`gamma(n)^2 − gamma(n−1) gamma(n+1) ≥ 0` — log-*concavity* — is a **theorem** (Csordas–Norfolk–Varga,
unconditional). Both can hold only in the degenerate geometric case, which `gamma` is not. Hence no
positive `Psi` exists and `(*)` is unavailable.

What makes this informative is *where* the sign flips. The un-normalized moments `b_n` **are** a
Stieltjes moment sequence of the positive kernel `Phi`, so `{b_n}` is log-convex for free. The
Jensen sequence is the renormalization

```text
gamma(n) = n! b_n / (2n)!  =  sqrt(pi) · b_n / (4^n Gamma(n + 1/2)).
```

**The factor `n!/(2n)!` is exactly what converts free log-convexity into the log-concavity that
RH needs.** So the entire difficulty of the lane sits in a Gamma-factor renormalization of a
manifestly positive moment sequence — the positivity of `Phi` is free and carries the wrong sign,
and every unconditional theorem in the lane (CNV, Dimitrov–Lucas, GORZ) is an estimate of how much
the renormalization overturns.

That reframing is the one thing here I would defend as worth having: it says the lane's obstruction
is not "control the zeros" but "beat a Gamma-factor against a Laplace-saddle", and it locates the
fight in a single explicit ratio.

## 5. What Theorem 1.2 says about the lane's ceiling

`RH_m(T)` and `d ≤ floor(T)^2` gives hyperbolicity for `n ≥ m`. Read backwards: **degree-`d`
hyperbolicity is controlled by the zeros up to height about `sqrt(d)`.** So the Jensen–Pólya
formulation is a *filtration of RH by height*, and the unconditional analytic method reaches only the
levels where the local zero statistics have already washed out into the Hermite limit. The route does
not escape needing individual zeros; it postpones them.

Anyone proposing this lane as a "new route to RH" should be shown this paragraph first.

## 6. Novelty, stated hostilely

- Section 1 is literature, verified against the sources, not derived here.
- Section 3's saddle computation is the standard asymptotic analysis of the Xi Taylor coefficients;
  GORZ's own method is built on the same expansion, so they certainly know its range. What I have not
  found stated anywhere is the explicit identification "`e^(d/2)` **is** the saddle parameter
  `1/log n` costed `d` times", but I would not bet on it being unstated in the community.
- Section 4's ingredients are each classical: Stieltjes moment sequences are log-convex; the Turán
  inequality is CNV's theorem. **The composition — hence no `(*)`, hence the difficulty is exactly
  the `n!/(2n)!` renormalization — I have not seen written down**, and it is the useful part. It is
  also the kind of remark an expert would produce in a minute if asked, so I claim it as orientation,
  not as a result.
- Nothing here advances `d = 4`.

## Gates

- [x] literature frontier established exactly, with sources
- [x] corpus blind spot established (`_of_rh` only)
- [x] Finding A: `e^(d/2)` identified with the saddle parameter
- [x] Finding B: no positive-kernel form; the renormalization is the obstruction
- [ ] `d = 4`, all `n`, by analysis
- [ ] a comparison family whose expansion parameter is not `1/log n`
- [ ] Lean: an unconditional statement in this lane — anything at all
- [ ] independent audit (Codex)

## Sources

- Pólya, *Über die algebraisch-funktionentheoretischen Untersuchungen von J. L. W. V. Jensen* (1927).
- Csordas, Norfolk, Varga, *The Riemann hypothesis and the Turán inequalities*, Trans. AMS (1986).
- Dimitrov, Lucas, *Higher order Turán inequalities for the Riemann xi-function*, Proc. AMS (2010).
- Griffin, Ono, Rolen, Zagier, *Jensen polynomials for the Riemann zeta function and other
  sequences*, PNAS 116 (2019). https://www.pnas.org/doi/10.1073/pnas.1902572116
- Griffin, Ono, Rolen, Thorner, Tripp, Wagner, *Jensen polynomials for the Riemann xi-function*,
  Adv. Math. (2022). https://arxiv.org/abs/1910.01227

## Log

- 2026-07-27 (Claude): opened after concluding that today's other work was infrastructure. Chose this
  lane because the corpus has ~40 modules on the Xi Taylor coefficients and *zero* unconditional
  theorems about their hyperbolicity. Verified the literature frontier directly from the sources
  rather than from memory — my recollection of the thresholds was wrong before checking.

## 7. The total-positivity reformulation, and the live 2026 literature — reconnaissance before investment

Continuing Finding B, the natural next reformulation is classical and I state it only to place the
literature:

```text
Xi(i z) = G(z^2),   G(w) = sum_n c_n w^n,   c_n = b_n/(2n)! > 0,
```

and by Aissen–Schoenberg–Whitney together with Edrei–Thoma, `G` lies in the Laguerre–Pólya class with
only negative real zeros **iff `{c_n}` is a Pólya frequency sequence**, i.e. iff the Toeplitz matrix
`(c_(j−i))` is totally positive. Since the minors of a Toeplitz matrix are Jacobi–Trudi determinants,
this reads:

```text
RH  <=>  s_lambda({c_n}) >= 0  for every partition lambda,
```

nonnegativity of every Schur determinant in the Xi Taylor coefficients. The Turán and higher-Turán
inequalities are the hook and small-rectangle cases.

**This is not new, and I checked before spending time on it.** Two 2026 preprints are working exactly
this ground:

- **arXiv:2602.01248**, *The Riemann Xi-function from primitive Markovian cycles I*. Constructs a
  scaling-limit trace kernel from finite reversible Markov dynamics on discrete cycles; proves
  **unconditionally** that the logarithmic kernel lies in `PF_inf`, yielding a canonical
  Laguerre–Pólya function via Schoenberg–Edrei–Karlin, and that the completed kernel coincides with
  the classical theta kernel. Their stated remaining obligation is **one analytic problem: identify
  that Laguerre–Pólya function with `Xi(2·)`**. Archimedean throughout — no Euler products, no primes.
- **arXiv:2602.20313**, *On the Pólya Frequency Order of the de Bruijn–Newman Kernel: Certified
  Failure at Order Five*. Proves `K(u) = Phi(|u|)` is **not** `PF_5`, by a certified `5x5` Toeplitz
  minor with negative determinant at `(u_0,h) = (0.01, 0.05)`. Version 2 withdrew a stronger global
  sign claim from version 1 as unsound.

### 7.1 One remark that puts the second paper in its place

`Phi(|·|)` **cannot be a Pólya frequency function at all**, and this needs no computation. Its
bilateral Laplace transform is

```text
int_(-inf)^(inf) Phi(|u|) e^(-su) du = 2 int_0^inf Phi(u) cosh(su) du = Xi(is),
```

entire of order one because `Phi` decays doubly exponentially. A `PF` function's bilateral Laplace
transform equals `1/Psi(s)` with `Psi` entire of Laguerre–Pólya type, hence is **zero-free** on its
strip of convergence. `Xi(is)` has zeros — the zeros of zeta, wherever they are. So `Phi(|·|)` is not
`PF_inf`, unconditionally and independently of RH.

The content of arXiv:2602.20313 is therefore **entirely the finite order**: `PF_5` is a genuine
finite-order determinantal condition not implied by the above, and pinning the failure at exactly
order five is real information. But the paper should not be read as evidence against the
total-positivity programme in general, and in particular it does **not** conflict with
arXiv:2602.01248: those authors' kernel is a different object whose transform is `1/Psi`, not `Xi`.
Anyone in this corpus who meets both papers should be handed this paragraph so the two are not
mistakenly set against each other.

### 7.2 Consequence for this project

- My Finding B and the total-positivity reformulation are **not novel**; they are the working frame of
  an active 2026 programme. Recorded as orientation only. The `[FINDINGS NOT CLAIMED NOVEL]` tag on
  this card stands.
- The lane's *open* point is now sharply named by other people: identify the canonically constructed
  `PF_inf` Laguerre–Pólya function with `Xi(2·)`. That is an identification problem, not an estimate
  — the same shape as this corpus's Deninger obligations, and the same shape my own
  `linear-kills-quadratic-survives` §5c predicts for a quadratic route: it dies **unbuilt**, not blind.
- The corpus asset that nobody has connected to this is the `HilbertMetric` theorem area (graded
  Plücker partitions, determinant positivity laws). Total positivity is Plücker positivity; if the
  corpus is to contribute here, that is the door.

## Gates (revised)

- [x] literature frontier established exactly, with sources
- [x] corpus blind spot established (`_of_rh` only)
- [x] Finding A: `e^(d/2)` identified with the saddle parameter
- [x] Finding B: no positive-kernel form; the renormalization is the obstruction
- [x] Phase-4 check against 2026 literature: the total-positivity reformulation is **not novel**
- [x] remark 7.1: `Phi(|·|)` is not `PF` for a trivial transform-theoretic reason
- [ ] `d = 4`, all `n`, by analysis
- [ ] a comparison family whose expansion parameter is not `1/log n`
- [ ] connect `HilbertMetric` Plücker positivity to the Toeplitz total-positivity statement
- [ ] Lean: an unconditional statement in this lane — anything at all
- [ ] independent audit (Codex)

## Sources (added)

- arXiv:2602.01248, *The Riemann Xi-function from primitive Markovian cycles I: A canonical
  construction*.
- arXiv:2602.20313, *On the Pólya Frequency Order of the de Bruijn–Newman Kernel: Certified Failure
  at Order Five* (v2).

## 8. Phase-4 verdict: REDISCOVERED. And the correction to Finding A.

### 8.1 Finding A was wrong about *where* the exponential comes from

I diagnosed the `e^(d/2)` threshold as the saddle parameter `1/log n` costed `d` times. **That is not
right, and the correction matters because it changes what an attack should target.**

Recompute. With `gamma(n) = sqrt(pi) b_n/(4^n Gamma(n+1/2))`:

```text
log((2n)!/n!) = n log n + 2n log 2 - n + O(log n),   so   d^2/dn^2 [-log((2n)!/n!)] = -1/n,
L(n) := log b_n,   L'(n) = 2 log u_n,   L''(n) = 2 u_n'/u_n ≈ 1/(n u_n) ≈ 2/(n log n).
```

Hence `(log gamma)''(n) ≈ 2/(n log n) - 1/n = -(1/n)(1 - 2/log n)`, and the Turán inequality
`gamma(n)^2 ≥ gamma(n-1) gamma(n+1)` holds with **margin `(1/n)(1 - 2/log n)`**, positive exactly for
`n > e^2`. Equivalently, in the moment form derived in section 4,

```text
Turán  <=>  b_n^2/(b_(n-1) b_(n+1))  ≥  (2n-1)/(2n+1),
```

with the left side `≈ 1 - 2/(n log n)` and the right side `≈ 1 - 1/n`. So the whole inequality is a
race between `1/n` (from the Gamma factor) and `2/(n log n)` (from the moment log-convexity), and the
Gamma factor wins by `log n`. Sharp, and it makes the mechanism visible.

Now the third derivative: `(log gamma)'''(n) ≈ (1/n^2)(1 - 2/log n)`, while the Hermite renormalization
scale is `delta(n) ≈ ((log gamma)'')^(1/2) ≈ n^(-1/2)`. So

```text
(log gamma)''' / delta^3  ≈  (1/n^2)/(n^(-3/2))  =  n^(-1/2),
```

**algebraic in `n`, with no logarithm.** The per-order error in the Hermite comparison is therefore
`O(n^(-1/2))`, not `O(1/log n)`.

**So the exponential threshold is not an expansion-parameter problem. It is a *stability* problem:**
preserving hyperbolicity of the degree-`d` Hermite polynomial under coefficient perturbation was
being required to relative accuracy `e^(-cd)`, and `e^(-cd)` against an `n^(-1/2)` error gives
`n ≳ e^(2cd)`. The exponential lives in the perturbation tolerance, not in the asymptotics.

### 8.2 The natural attack, and why it is not mine

If the exponential is a *conditioning* artifact — the monomial basis of the renormalized variable is
badly conditioned for `H_d`, whose coefficients alternate with sizes `~ d!` — then re-running the
perturbation argument in the orthonormal Hermite basis (where basis values are `O(d^(-1/4))`
uniformly on the bulk) should give a tolerance polynomial in `1/d` and hence a **polynomial**
threshold `N(d)`.

Searching before investing: this is already the direction of published and in-progress work, with
thresholds of the shape `N(d) = O(d^(5/2))` / `O(d^4)` reported. The idea is not available to claim.

### 8.3 Verdict and what it teaches

**Verdict: `REDISCOVERED`.** Every idea I generated in this lane today — the moment representation,
the failure of a positive-kernel Jensen form, the total-positivity/Pólya-frequency reformulation, the
Schur-determinant form, and the polynomial-threshold attack — is in the literature, three of them in
work from 2019–2026.

The lesson is not about this lane. It is about method:

> **A lane with a century of literature and active strong groups will not yield novelty to a fresh
> derivation, however careful. The corpus confers no advantage where the corpus has nothing.**

The corpus's blind spot here (section 2) is real and worth fixing eventually, but fixing it is
formalization of known mathematics, not new knowledge. Neither corpus nor mathlib has *any*
total-positivity machinery — no `TotallyPositive`, no PF sequences, nothing — so even the
formalization is a from-scratch project with no prior art, and it would be infrastructure.

**Redirect.** Effort should go where the corpus has *more* than the literature. Two candidates, and
only one is really corpus-native:

1. the PSWF/prolate substrate — but Slepian, Dunster and Connes–Consani–Moscovici are strong there,
   and today's audit showed the live obligations are already named by others;
2. the **Deninger arithmetic-cohomology substrate** — dozens of `deninger-*` cards and `DAC_*`
   interface modules. Deninger's programme has a thin literature and nobody outside this project has
   formalized any of it. Its named obligation (`DAC_ARITHMETIC_CALDERON_GREEN_INTERMEDIATE_EXTENSION`,
   with the "nuclear cohomology before Hilbert completion" prescription) is an *identification*
   problem of exactly the shape `linear-kills-quadratic-survives` §5c predicts.

That is where the next cycle goes.

## Gates (revised again)

- [x] Phase-4 verdict assigned: `REDISCOVERED`
- [x] Finding A corrected: the exponential is a perturbation-stability tolerance, not an expansion
  parameter; per-order error is `O(n^(-1/2))`
- [x] exact Turán margin `(1/n)(1 - 2/log n)`, and its moment form
- [x] confirmed: no total-positivity machinery in corpus **or** mathlib
- [ ] (parked) `d = 4`, all `n`, by analysis
- [ ] (parked) Lean: an unconditional statement in this lane

## Log (continued)

- 2026-07-27 (Claude): ran Phase 4 properly and the lane came back `REDISCOVERED` on every idea.
  Recorded the correction to Finding A because the wrong diagnosis would have sent the next cycle at
  the expansion parameter instead of the perturbation tolerance. Redirecting to the one substrate
  where this corpus is ahead of the literature rather than behind it.

## 8. The Gamma factor computed exactly: an inverse Pochhammer weight, and the Laguerre model

§4 located the difficulty of this lane in the renormalization `γ(n) = n!·b(n)/(2n)!` and stopped at
the qualitative statement that it converts free log-convexity into the log-concavity RH needs. That
factor can be computed in closed form, and doing so changes what the lane looks like.

### 8.1 The exact weight

For every shift `j`,

```text
(n+j)! / (2n+2j)!  =  ( n! / (2n)! ) · ∏_{i=1}^{j} 1/(2(2n+2i−1))
                   =  ( n! / (2n)! ) · 1/(4^j (n+½)_j) ,
```

an identity of naturals after clearing denominators:

```text
(n+j)! · (2n)! · ∏_{i<j} (4n + 4i + 2)  =  n! · (2n+2j)!    -- factorial_pochhammer_law
```

Hence, discarding the common positive factor `n!/(2n)!` and substituting `X = 2Y`,

```text
J^(d,n)(X)  ∝  ∑_{j=0}^d  C(d,j) · m(n+j) / (n+½)_j · Y^j ,          m(k) = b(k) .
```

**The Gamma renormalization is exactly an inverse Pochhammer weight `1/(n+½)_j` on the moments.**

### 8.2 Consequence at `d = 2`: the dispersion window

At `j = 1, 2` the weight gives `(2n+3)/(2n+1)`, so with `D n := m(n)m(n+2)/m(n+1)² − 1`,

```text
Turán at n   ⇔   (2n+1)·m(n)m(n+2) ≤ (2n+3)·m(n+1)²   ⇔   D n ≤ 2/(2n+1) .
```

For a moment sequence `m(k) = ∫ sᵏ dμ`, `D n` is exactly the **squared coefficient of variation of
the tilted probability measure `sⁿ dμ / m(n)`**: with `π ∝ sⁿ dμ`,
`D n = Var_π(s)/(E_π s)²`. So the two ends of the inequality have opposite status:

| end | statement | source |
|---|---|---|
| `0 ≤ D n` | Hankel positivity, `∫ sⁿ(s−c)² dμ ≥ 0` | **free** from positivity of `μ` |
| `D n ≤ 2/(2n+1)` | the tilted measure is *concentrated* | the entire content of Turán |

This is the same asymmetry the corpus meets in the Weil-form lane (`positivity-creators-versus-
transporters`): positivity of the source supplies a **lower** bound and the criterion needs an
**upper** one. Here the gap is quantified exactly — the free bound is `0`, the needed bound is
`2/(2n+1)`, and nothing about positivity of `Φ` distinguishes them.

*Where Ξ actually sits.* By §3's saddle, the tilted measure `Φ(u)u^{2n} du` concentrates at
`u_n ≈ ½ log n` with width `≈ √(u_n/8n)`, so in `s = u²` the coefficient of variation squared is
`≈ 1/(2n·u_n) ≍ 1/(n log n)`, against a threshold `2/(2n+1) ≍ 1/n`. **The Turán inequality holds for
Ξ with a factor `log n` of slack.** (Saddle heuristic, stated as such; the rigorous version is CNV.)

### 8.3 The model is Laguerre, and Hermite is its degeneration

Take the extreme concentrated case, `μ = δ_t` with `t > 0`, so `m(k) = tᵏ` and `D n = 0`. Then

```text
J^(d,n)(X) ∝ ∑_j C(d,j) (tX/2)^j / (n+½)_j = ₁F₁(−d ; n+½ ; −tX/2)
           ∝ L_d^(n−½) ( −tX/2 ) ,
```

using `∑_j C(d,j) w^j/(b)_j = ₁F₁(−d;b;−w)` and `L_d^(α)(x) = C(d+α,d)·₁F₁(−d;α+1;x)`. Since
`α = n − ½ > −1` for every `n ≥ 0`, the generalized Laguerre polynomial has `d` **simple positive**
roots, so `J^(d,n)` has `d` simple **negative** roots.

> **The exact finite-`n` model for the Jensen polynomials of a Gamma-renormalized moment sequence is
> the generalized Laguerre polynomial `L_d^(n−½)`.**

This is the structural point of this section. GORZ's model is the **Hermite** polynomial `H_d`,
obtained as `n → ∞`; and Hermite is precisely the classical `α → ∞` degeneration of `L_d^(α)`. So the
Laguerre model is the finite-`n` refinement of the GORZ model, and it is exact at every `n` — no
asymptotics, no saddle, no `1/log n`. **The parameter that killed the GORZ route below `n ≍ e^(d/2)`
does not appear in it.**

The attack this suggests for the open case `d = 4`, all `n`: treat `J^(4,n)` as a perturbation of
`L_4^(n−½)`, whose four roots are explicit and separated, and bound the perturbation by the
dispersion data of §8.2 — the higher-cumulant analogues of `D n`. The `d = 2` case above is exactly
this program carried out at first order, where the perturbation bound is the single number
`2/(2n+1)`.

### 8.4 Lean

`HTGeometry/GammaRenormalizedTuranWindow.lean`, axiom-clean, registered, `lake build` green:

```text
factorial_pochhammer_law        (n+j)!·(2n)!·∏_{i<j}(4n+4i+2) = n!·(2n+2j)!
jensenGamma_mul_pochhammer      real form of the same
turan_iff_weighted              γ-Turán ⇔ (2n+1)·m(n)m(n+2) ≤ (2n+3)·m(n+1)²   (no positivity needed)
turan_iff_dispersion_le         γ-Turán ⇔ D n ≤ 2/(2n+1)
dispersion_nonneg               Hankel positivity ⇒ 0 ≤ D n
turan_iff_dispersion_mem_window γ-Turán ⇔ D n ∈ [0, 2/(2n+1)]
hankel_nonneg_of_measure        ∫ sⁿ(s−c)² dμ ≥ 0 supplies the Hankel form
```

All statements are about an arbitrary sequence or an arbitrary positive measure — nothing about ζ
enters — so they are reusable for any Gamma-renormalized moment problem. This is the corpus's first
unconditional statement in the Jensen lane; §2 recorded that every previous one was `_of_rh`.

### 8.5 Novelty, stated hostilely

- The Pochhammer identity is elementary and certainly known to anyone who has written
  `(n+j)!/(2n+2j)!` down; it is stated here because the corpus had it nowhere and because §8.3 needs
  it in closed form.
- The dispersion window is a restatement of Turán. Its content is the **exact threshold** `2/(2n+1)`
  paired with the free lower end `0`, and the reading of `D n` as a coefficient of variation. I did
  not find this pairing in CNV, Dimitrov–Lucas, GORZ or GORTTW, nor by search; it is the kind of
  remark an expert produces in a minute, so I claim it as orientation.
- **§8.3 is the part I would defend.** That the finite-`n` model is Laguerre rather than Hermite, and
  that GORZ's Hermite is its `α → ∞` degeneration, is a structural statement about the lane, it is
  exact, and it identifies a model that does not carry the `1/log n` expansion parameter that §3
  showed is intrinsic to the saddle route. I have not seen it stated. It is not a theorem about ζ and
  it is not RH; it is a change of model, and the test of whether it is worth anything is whether the
  `d = 4` perturbation argument closes.

## Gates (revised)

- [x] literature frontier established exactly, with sources
- [x] corpus blind spot established (`_of_rh` only)
- [x] Finding A: `e^(d/2)` identified with the saddle parameter
- [x] Finding B: no positive-kernel form; the renormalization is the obstruction
- [x] the renormalization computed in closed form: inverse Pochhammer `1/(n+½)_j`
- [x] `d = 2`: exact dispersion window `[0, 2/(2n+1)]`, Lean, unconditional
- [x] the finite-`n` model identified as `L_d^(n−½)`; Hermite is its degeneration
- [ ] Laguerre root separation for `α = n−½`, quantitatively
- [ ] `d = 3` reproved as a second-order dispersion bound (checks the method against Dimitrov–Lucas)
- [ ] `d = 4`, all `n`, by analysis
- [ ] independent audit (Codex)

## 9. The perturbation program, and an error in my own first estimate of it

§8.3 gives an exact model; turning it into a theorem means bounding the perturbation off it. Setting
`t = m(n+1)/m(n)` and

```text
m(n+j) = m(n) · t^j · (1 + ε_j) ,     ε_0 = ε_1 = 0 ,   ε_2 = D n ,
```

the `ε_j` are exactly the normalized higher moment ratios of the tilted measure, and

```text
J^(d,n)  ∝  ∑_j C(d,j) (tY)^j/(n+½)_j · (1 + ε_j)  =  ₁F₁(−d; n+½; −tY)  +  ∑_{j≥2} C(d,j)(tY)^j/(n+½)_j · ε_j .
```

Two structural remarks that are solid:

- **Constant `ε` moves nothing.** If `ε_j ≡ ε` the perturbation is `ε·P₀` and the roots are unchanged.
  Only the *variation* of `ε_j` in `j` matters, and `ε_0 = ε_1 = 0` normalizes the first two away. So
  the governing quantity is a second-difference of `log(1 + ε_j)`, i.e. the multiplicative cumulants
  of the tilted measure — of which `D n` is the first.
- **Multiplier sequences do not shortcut it.** `{1/(b)_j}` *is* a Pólya–Schur multiplier sequence
  (`∑_j z^j/(j!(b)_j) = ₀F₁(;b;z) ∝ z^((1−b)/2) I_{b−1}(2√z)` has only real negative zeros for
  `b > 0`), so it preserves hyperbolicity. But the object it would act on is the **unrenormalized**
  Jensen polynomial `∑_j C(d,j) m(n+j) Y^j = ∫ sⁿ(1+sY)^d dμ`, and that is not hyperbolic: at `d = 2`
  with `μ = δ_1 + δ_M` its discriminant is `−4(M−1)² ≤ 0`. This is Finding B again, in the form that
  matters: the renormalization cannot be applied *after* a hyperbolic step, because there is no
  hyperbolic step to apply it after.

**And the error, recorded because I nearly published it.** My first scaling pass estimated the
perturbation as `‖δP‖ ≈ 2^d·σ²d²` against `|P₀′| ≈ 2^d/√(2n)` at the roots, concluding hyperbolicity
for `d ≲ √(n log n)` — exponentially better than GORTTW's `d ≲ 2 log n`. **That is wrong.** At a root
`x_k ≈ α ≈ n` the terms `C(d,j)(−x_k)^j/(b)_j` alternate in sign with magnitudes `≈ C(d,j)`, so `P₀`
and `P₀′` there are the result of massive cancellation in a sum of absolute size `2^d`; `|P₀′|` is not
`2^d/√(2n)` and the ratio is not what I computed. No improvement over the literature is claimed, and
the `√(n log n)` figure should not be quoted.

What survives the error is the shape of the obligation, which is now precise:

> **[OPEN CORE]** Bound `|∑_{j≥2} C(d,j) z^j/(b)_j · ε_j|` at the roots of `₁F₁(−d;b;−z)`, `b = n+½`,
> relative to `|P₀′|` there — i.e. control the alternating-sum cancellation, not the term sizes.

That is a Laguerre-basis version of the same cancellation problem the saddle route meets, but with
one difference that is the reason to try it: **it is exact at every finite `n`**, so the small-`n`
region — the region `d ≤ 3` occupies and `d = 4` needs — is not out of range by construction.

## Log

- 2026-07-27 (Claude): §8 added. Chose this lane by the test that killed the two previous ones — an
  RH-bearing invariant must be (i) computable from unconditional data and (ii) sensitive to motion of
  the zero divisor. Hyperbolicity passes both; hypertranscendence fails (ii); the Deninger
  polarization fails (i). §9 records a scaling error I caught before quoting it.

## 10. The superposition law, and a common-interlacer criterion that avoids the cancellation

§9's open core was to control an alternating sum at the roots. The cancellation disappears if the
Jensen polynomial is not expanded at all.

### 10.1 The identity

Exchanging the sum over `j` with the integral over `μ` in `m(n+j) = ∫ s^{n+j} dμ` gives, exactly,

```text
J^(d,n)(2Y) · (2n)!/n!  =  ∫₀^∞ s^n · Q_{d,n}(sY) dμ(s) ,
     Q_{d,n}(z) := ∑_{j=0}^d C(d,j) z^j / ∏_{i<j}(4n+4i+2)  ∝  ₁F₁(−d; n+½; −z/4) ∝ L_d^(n−½)(−z/4).
```

> **The Jensen polynomial of a Gamma-renormalized moment sequence is a positive superposition of one
> universal Laguerre polynomial, with the argument rescaled by the integration variable.**

Every summand is hyperbolic with the *same* root pattern, dilated: if `x_1 < … < x_d` are the roots
of `L_d^(n−½)`, the `s`-member of the family has roots `Y = −4x_k/s`.

### 10.2 The criterion

Positive combinations of hyperbolic polynomials sharing a **common interlacer** are hyperbolic. Here
the root sets are the fixed pattern dilated by `1/s`, so a common interlacer exists as soon as the
`d` root ranges `{−4x_k/s : s ∈ supp μ}` are pairwise disjoint. With `supp μ ⊆ [s₋, s₊]` that is

```text
s₊ / s₋  ≤  min_{1≤k<d}  x_{k+1}/x_k .
```

> **Criterion.** If `μ ≥ 0` is supported in `[s₋, s₊] ⊂ (0,∞)` and `s₊/s₋ ≤ min_k x_{k+1}/x_k` for the
> roots `x_k` of `L_d^(n−½)`, then `J^(d,n)` is hyperbolic.

Exact, non-perturbative, valid at every finite `n`, and the whole obstruction is now one classical
quantity: **the consecutive root ratios of generalized Laguerre polynomials at parameter `α = n − ½`.**
No alternating sum is evaluated anywhere.

### 10.3 What it gives, and the wall it confirms

For large `α` the roots of `L_d^(α)` cluster at `α` with spread `√(2α)`: `x_k ≈ α + √(2α)·h_k` with
`h_k` the Hermite roots. So `min_k x_{k+1}/x_k ≈ 1 + √(2/n)·min_k(h_{k+1}−h_k) ≈ 1 + c/√(dn)`. The
theta kernel's tilted measure has relative width `≈ 1/√(n log n)` (§3's saddle). Matching gives

```text
d  ≲  const · log n ,
```

the **same** threshold as GORTTW's `n ≥ c e^(d/2)`, reached by a structurally different route. That is
worth recording as confirmation rather than as progress: §3 argued the `1/log n` scale is a property
of the double-exponential decay of `Φ` and not an artifact of the saddle method, and this is
independent evidence for that — a method with no asymptotic expansion in `1/log n` anywhere hits the
same wall.

What differs is the **constant**, and for this lane the constant is the whole question: the open
target is `d = 4` at *small* `n`, where a factor of five in the threshold is the difference between
"all `n`" and "all `n` above some unverifiable bound". The interlacing criterion is exact at every
`n`, so unlike the saddle route it can in principle be evaluated there. That is the reason to
continue with it.

### 10.4 The honest remaining obligations

1. **Root ratios of `L_d^(α)` at `α = n − ½`, for small `n` and `d ≤ 4`, without numerics.** This is
   the new open core and it is a classical orthogonal-polynomial question, not an RH question.
2. **The theta measure is not compactly supported.** `Φ > 0` on all of `[0,∞)`, so `s₊/s₋ = ∞` and
   the criterion does not apply directly. It needs a core/tail split with a quantitative gap
   argument — available because the interlacing criterion produces a root separation, not merely
   hyperbolicity.
3. mathlib has `Polynomial.hermite` and **no Laguerre polynomials at all**, so (1) has to be built
   before it can be checked formally.

Neither (1) nor (2) is claimed to be close. What has changed is that the obstruction is now a named
classical estimate about a named classical family, rather than a cancellation problem inside an
asymptotic expansion.

### 10.5 Lean (added)

```text
pochWeight, pochWeight_pos           the weight ∏_{i<j}(4n+4i+2) = 4^j (n+½)_j
jensenPolyEval                       the Jensen polynomial of the renormalized sequence
modelPoly                            Q_{d,n}, the universal Laguerre model
jensenPolyEval_mul_factor            clearing the Gamma factor
jensenPolyEval_superposition         J = the w-average of modelPoly with argument scaled by s i
```

All axiom-clean, all about arbitrary sequences and arbitrary finitely supported positive weights.

## Gates (revised again)

- [x] the renormalization computed in closed form: inverse Pochhammer `1/(n+½)_j`
- [x] `d = 2`: exact dispersion window `[0, 2/(2n+1)]`, Lean, unconditional
- [x] the finite-`n` model identified as `L_d^(n−½)`; Hermite is its degeneration
- [x] superposition law: `J^(d,n)` is a positive average of dilates of one Laguerre polynomial (Lean)
- [x] common-interlacer criterion stated; cancellation problem of §9 removed
- [x] independent confirmation of Finding A: a second method hits the same `d ≲ log n` wall
- [ ] consecutive root ratios of `L_d^(α)`, `α = n−½`, small `n`, `d ≤ 4`, without numerics
- [ ] core/tail split for the non-compactly-supported theta measure
- [ ] Laguerre polynomials in Lean (mathlib has none)
- [ ] `d = 4`, all `n`, by analysis
- [ ] independent audit (Codex)

## 11. §8.3 is rediscovered, my counterexample was false, and the kernel route has a 2026 no-go

Codex demanded the classical Jensen/Laguerre/₁F₁ search before I claimed novelty for §8.3. He was
right on every count.

### 11.1 The Laguerre model is published

**arXiv:2410.06403 (Oct 2024), *Universality for roots of derivatives of entire functions via finite
free probability*.** Verbatim from the text: *"the Laguerre polynomials, which are related to the
Hermite polynomials … do appear naturally in our approach"*; **Conjecture 1.5 (Laguerre
Universality)**: *"For a large class of functions `f`, the unshifted even Jensen polynomials of
`f^(2n)` converge, after rescaling, to the generalized Laguerre polynomials"*; and **Proposition 1.6**,
*"whose proof follows from direct computation of coefficients"*, concerns **the even Jensen
polynomials of cosine**.

The point-mass model `μ = δ_t` **is** cosine: `Φ = ½(δ_{√t} + δ_{−√t})` has cosine transform
`cos(√t x)`. So §8.3 — "the exact finite-`n` model of the Gamma-renormalized Jensen polynomials is
`L_d^(n−½)`" — is the Laguerre form of the even Jensen polynomials of cosine, by direct coefficient
computation, published. **§8.3: `REDISCOVERED`.**

§10.1 goes with it. Once the model is cosine, the "superposition law" says the Jensen polynomial of
`Ξ = ∫Φ(u)cos(ux)du` is the `Φ`-average of the Jensen polynomials of `cos(ux)` — this is **linearity
of the Jensen polynomial in its coefficient sequence**, applied to the Fourier representation. Not a
law. I overweighted it because I reached it through Pochhammer → ₁F₁ → Laguerre, which hides how
short the direct argument is.

### 11.2 A false statement of mine, corrected

I asserted that `e^{−u⁴}` is a positive even log-concave kernel whose cosine transform has non-real
zeros, and used it to argue that any log-concavity-based criterion is degree-capped. **That is
false.** By the **de Bruijn–Ilieff criterion** — if `φ` is even entire and `φ′` lies in the
Laguerre–Pólya class, then the Fourier transform of `e^{φ(it)}` has only real zeros — take
`φ(z) = −z⁴`, so that `φ(it) = −t⁴`; `φ′(z) = −4z³` is a real polynomial with all zeros real, hence in
`LP`. So the Fourier transform of `e^{−u⁴}` **has only real zeros**. The same applies to every
`e^{−u^{2m}}`.

So the log-concavity route is *not* refuted by that example, and the argument I gave Codex for its
being capped is withdrawn.

### 11.3 …but the kernel route is classical, and stronger than what I proposed

The de Bruijn–Ilieff criterion is exactly a **creator**: it produces real-rootedness unconditionally
from structure of the kernel, with no positivity-transport step. It is also strictly stronger than
the Brascamp–Lieb/log-concavity bound I was about to build, and it is 75 years old. The programme
built on it is classical:

- **Pólya (1926).** Keep only the `n = 1` term of `Φ` and replace `e^{9u/2}`, `e^{5u/2}` by
  `2cosh(9u/4)`, `2cosh(5u/4)`. The resulting `Ξ*` has **only real zeros**. (The mechanism is exactly
  de Bruijn–Ilieff: the symmetrized kernel is `e^{φ(iu)}` with `φ′ ∈ LP` — for the model
  `e^{−2π cosh 2u}` one gets `φ′(z) ∝ sin 2z`, which is in `LP`.)
- **de Bruijn (1950).** `Ξ_λ` has only real zeros for `λ ≥ 1/8` — the de Bruijn–Newman story.

**What fails for the true `Φ`** is now precisely locatable and is *not* a technical nuisance: the
`n ≥ 2` terms of the theta sum, and the replacement of `e^{ku/2}` by `2cosh(ku/4)`. Every real-rooted
approximation in this lane is obtained by discarding exactly those, and the discarded part is what
carries the arithmetic.

### 11.4 The 2026 result, and the dichotomy it forces

**arXiv:2602.20313 (2026), *On the Pólya Frequency Order of the de Bruijn–Newman Kernel: Certified
Failure at Order Five and the Toeplitz Threshold Phenomenon*.** For `K(u) = Φ(|u|)`: the kernel is
proved **not PF₅** — an explicit `5×5` Toeplitz minor is certified negative at `(u₀,h) = (0.01,0.05)`,
with eight further certified configurations. At the central configuration `D₂, D₃, D₄ > 0`, but global
`PF₄` is **not** established. The paper states outright that it does not resolve RH.

That last disclaimer is structurally necessary, and the reason is worth recording because it kills a
tempting bridge:

> **Dichotomy.** RH is equivalent to the Jensen sequence `{γ(n)}` being a Pólya frequency sequence of
> **infinite** order (Aissen–Schoenberg–Whitney + Edrei). The theta kernel is **not** `PF₅`. Hence a
> theorem of the form *"`{γ(n)} ∈ PF_r` ⟹ `Φ ∈ PF_r`"* implies **¬RH**. Any such transfer is a
> disproof strategy, not a proof strategy.

So kernel total positivity and moment-sequence total positivity are **decoupled above order four**,
and no amount of work on the kernel's Toeplitz minors can climb the Jensen ladder. This is the
sharpest form I can give of why the whole "regularity of `Φ` ⟹ hyperbolicity" family stops: it is not
that the estimates are hard, it is that the two total-positivity orders are different invariants and
one of them is provably finite.

### 11.5 Status of the lane

| item | verdict |
|---|---|
| §8.3 Laguerre model | `REDISCOVERED` (arXiv:2410.06403, Prop. 1.6) |
| §10.1 superposition law | linearity; not a law |
| §10.2 interlacing criterion | a **transporter**; correct, but consumes a bound nobody has |
| §8.2 dispersion window | restatement with an explicit constant; orientation only |
| `e^{−u⁴}` counterexample | **false**, withdrawn (de Bruijn–Ilieff) |
| Brascamp–Lieb creator | subsumed by de Bruijn–Ilieff, 75 years older and stronger |
| kernel-regularity route as a whole | capped: **not `PF₅`**, and the dichotomy of §11.4 forbids the transfer |
| Lean modules | unconditional and corpus-new; new-in-Lean is not novelty |

The lane is not dead — `d = 4`, all `n`, by analysis is still open and still RH-bearing — but every
route into it that goes through **properties of the kernel** is now either classical or capped, and
the corpus should not spend on them. What remains open is a genuinely `Ξ`-specific inequality on the
moment sequence itself, which is what Codex said before I started.

## 12. The correct engine for the ladder, and why `d = 4` is squeezed under our own rules

§11 removed every route into this lane that goes through the kernel. What remains is the moment
sequence, attacked one degree at a time. Two elementary facts organise that, and the corpus had
neither.

### 12.1 The Jensen ladder

```text
d/dX J^(d+1,n) = (d+1) · J^(d,n+1)                     derivative_jensenPoly
```

Immediate from `(i+1)·C(d+1,i+1) = (d+1)·C(d,i)`. Consequences:

- **Downward is free.** By Rolle, `J^(d+1,n)` hyperbolic ⟹ `J^(d,n+1)` hyperbolic. So the known
  `d ≤ 3` results are implied by any `d = 4` result, and give nothing towards it.
- **Upward is a sign test.** A real polynomial whose derivative is hyperbolic is itself hyperbolic
  **iff** it alternates in sign at the derivative's roots. Since `J^(3,n+1)` is hyperbolic for all `n`
  (Dimitrov–Lucas), with roots `r₁ < r₂ < r₃`:

```text
J^(4,n) hyperbolic  ⇔  γ(n+4)·J^(4,n)(r₁) ≤ 0,  γ(n+4)·J^(4,n)(r₂) ≥ 0,  γ(n+4)·J^(4,n)(r₃) ≤ 0.
```

**Three sign inequalities, not a degree-six discriminant.** This is the right shape for the open
target and it consumes the known `d = 3` theorem as input rather than starting over.

### 12.2 One of the three quartic conditions is already free

For `ax⁴+bx³+cx²+dx+e` all-real requires `Δ ≥ 0`, `P = 8ac − 3b² ≤ 0`, `D ≤ 0`. Here
`a = γ(n+4), b = 4γ(n+3), c = 6γ(n+2)`, so

```text
P = 48 (γ(n+2)γ(n+4) − γ(n+3)²) ≤ 0    ⇔    Turán at n+3 ,
```

which is Csordas–Norfolk–Varga. **So `d = 4` needs only `D ≤ 0` and `Δ ≥ 0`.** Elementary, but it is
the first move in any attack and it was not recorded anywhere in the tree.

### 12.3 The squeeze, stated plainly

The literature's route to small `n` is Theorem 1.2 of GORTTW: `RH_m(T)` verified to height `T` gives
hyperbolicity for `d ≤ ⌊T⌋²`, `n ≥ m`. That is **zero data**, i.e. a computation. Our rules forbid it.

The alternative is to prove the sign inequalities of §12.1 at small `n` from the integral
representation without ever evaluating `γ(k)`. But `γ(0), …, γ(8)` are specific transcendental
constants — Taylor coefficients of `ξ` at `½`, equivalently Keiper/Li data — and a polynomial
inequality among them is not a soft consequence of positivity or regularity. Every soft route (kernel
positivity, log-concavity, total positivity, de Bruijn–Ilieff) is what §11 showed to be classical or
capped.

> **The `d = 4`, all-`n` target is squeezed: the accessible-by-analysis part is classical, and the
> remaining part is a numerical fact about specific transcendental constants, which our own rules
> forbid.**

This is not a claim that `d = 4` is out of reach in general — GORTTW reach far past it with a
computation. It is a claim about what this project can honestly deliver here, and it should be
recorded before anyone spends another cycle on it.

### 12.4 Lean

`HTGeometry/SignAlternationHyperbolicity.lean`, axiom-clean, registered, build green:

```text
Hyperbolic                              p.roots.card = p.natDegree
exists_root_of_sign_change              IVT: a sign change yields an interior root
card_roots_toFinset_ge_of_alternating   d alternations ⟹ d distinct real roots
hyperbolic_of_alternating               deg ≤ d + d alternations ⟹ hyperbolic
jensenPoly, natDegree_jensenPoly_le     the Jensen polynomial as a `Polynomial ℝ`
derivative_jensenPoly                   d/dX J^(d+1,n) = (d+1)·J^(d,n+1)
```

The corpus previously had **no** hyperbolicity predicate and **no** Jensen polynomial, so the open
target could not be stated in the tree at all. That is the same defect that killed the finite-phase
route in `hypertranscendence-frontier-order-one.md` §12 — a conclusion consumed by an object nobody
had defined — and it is now fixed prophylactically rather than after three cycles of plumbing.

## Gates (final for this card)

- [x] literature frontier established exactly, with sources
- [x] corpus blind spot established (`_of_rh` only); now partially repaired
- [x] Finding A: `e^(d/2)` identified with the saddle parameter
- [x] Finding B: no positive-kernel form; the renormalization is the obstruction
- [x] the renormalization computed in closed form: inverse Pochhammer `1/(n+½)_j`
- [x] `d = 2`: exact dispersion window `[0, 2/(2n+1)]`, Lean, unconditional
- [x] Laguerre model — **`REDISCOVERED`** (arXiv:2410.06403 Prop. 1.6)
- [x] kernel route capped — Pólya/de Bruijn classical; not `PF₅` (arXiv:2602.20313); §11.4 dichotomy
- [x] the ladder and the sign certificate, in Lean; `P ≤ 0` free from CNV
- [x] the squeeze recorded: `d = 4` all `n` is not deliverable under this project's rules
- [ ] independent audit (Codex)

## 13. §12.3 was wrong: `d = 4` is not squeezed, it is open

**Correction.** §12.3 claimed that the small-`n` region of `d = 4` is "a numerical fact about specific
transcendental constants that our own rules forbid us to establish." That is not supported and I
withdraw it. Csordas–Norfolk–Varga (1986) proved `d = 2` for **all `n ≥ 0`** and Dimitrov–Lucas
(PAMS 2011) proved `d = 3` for **all `n ≥ 0`**, both unconditionally and without verified zero data.
Two prior results occupy exactly the range I declared inaccessible. What I actually established is
narrower and correct: *GORTTW's* route past `d = 3` consumes a computation. That says nothing about
whether another analytic argument reaches `d = 4`, and the precedent says it might.

So `d = 4`, all `n`, is an **open analytic problem of the same kind that was solved twice before**,
and it is back on the table.

## 14. Exact reduction of `d = 4` to three numbers

The reduction below is exact, unconditional, and makes the target finite-dimensional.

### 14.1 The `ε`-form

Put `t = m(n+1)/m(n)` and define `ε j` by `m(n+j) = m(n)·t^j·(1 + ε j)`, so `ε 0 = ε 1 = 0` and

```text
1 + ε j = E_π[s^j] / E_π[s]^j ,        π ∝ sⁿ dμ ,
```

the normalized moment ratios of the tilted measure. Then, exactly,

```text
J^(d,n)(2Y)·(2n)!/n!  =  m(n) · ( Q_{d,n}(tY) + P_{ε,d,n}(tY) ) ,
    Q_{d,n}(z) = ∑_j C(d,j) z^j/∏_{i<j}(4n+4i+2)        (the model, ∝ L_d^(n−½))
    P_{ε,d,n}(z) = ∑_j C(d,j)·ε j·z^j/∏_{i<j}(4n+4i+2)  (the perturbation, same basis)
```

`jensenPolyEval_eq_model_add_perturbation`, in Lean, axiom-clean. Since `ε 0 = ε 1 = 0`,

> **`J^(4,n)` is hyperbolic iff the three numbers `(ε2, ε3, ε4)` lie in an explicit semialgebraic
> region `H_b ⊂ ℝ³`, `b = n + ½`.**

No asymptotics, no saddle, no `1/log n`. The region is cut out by `Δ ≥ 0`, `D ≤ 0`, `P ≤ 0`, and
**`P ≤ 0` is free** (§12.2, it is Turán at `n+3`), so `H_b` is cut out by two conditions.

### 14.2 The perturbation is one-dimensional to leading order

With `L = log s` and `κ_r` the cumulants of `L` under `π`,

```text
log(1 + ε j) = C(j,2)·κ₂ + (j³−j)/6·κ₃ + … ,
```

so to first order `(ε2, ε3, ε4) = κ₂·(1, 3, 6)`. The open problem therefore has a **one-parameter
leading form**: how far along the fixed direction `(1,3,6)` can one move from the origin before the
quartic `Q_{4,n} + κ·G` loses hyperbolicity, where

```text
G(z) = 6z²/(b)₂ + 12z³/(b)₃ + 6z⁴/(b)₄ .
```

Call the answer `κ*(b)`. Two checks that the framework is right:

- **`d = 2` gives `κ*(b) = 1/b` exactly.** §8.2's window `D n ≤ 2/(2n+1)` is `κ₂ ≤ 1/(n+½)`. So the
  `d = 2` constant is exactly `1`, in units of `1/b`.
- **Scaling at `d = 4`.** `Q_{4,n}` has roots `≈ −(b + √(2b)·h_k)` (`h_k` Hermite), gaps `≈ √(2b)`,
  leading coefficient `1/(b)₄`. At `z ≈ −b` the perturbation nearly cancels: `G(−b) = −6/b + O(b⁻²)`
  (the `6 − 12 + 6 = 0` cancellation). Balancing `κ|G|` against `|Q′|·gap` gives `κ*(b) ≍ 1/b`, the
  **same order** as `d = 2`.

### 14.3 What that would give, and what is still missing

For the theta measure `κ₂ ≍ 1/(n log n)` (§3's saddle) against a threshold `κ*(b) ≍ c₄/b ≍ c₄/n`. The
ratio is `1/(c₄ log n)`, so **`d = 4` would follow for every `n` with `log n ≥ 1/c₄`** — and the
entire question becomes the size of one explicit constant. That is a materially better position than
"beat `e^(d/2)`", because `c₄` is computable in closed form from a quartic discriminant.

Three obligations remain, and none is claimed done:

1. **`κ*(b)` in closed form**, or a rigorous lower bound. Pure algebra: the discriminant of the pencil
   `Q_{4,n} + κG` as a polynomial in `κ` with coefficients rational in `b`.
2. **`κ₃, κ₄` control.** §14.2's one-parameter reduction is leading order. The exact condition uses
   `(ε2, ε3, ε4)` independently, so the higher cumulants of `log s` under the tilted theta measure
   need unconditional bounds. This is the step where the `d = 2` case was free (it has no `κ₃`).
3. **A rigorous `κ₂` bound**, replacing the saddle heuristic. This is where a Brascamp–Lieb-type
   variance bound from log-concavity of the tilted density is the natural tool — subsumed for
   *hyperbolicity* by de Bruijn–Ilieff (§11.3), but **not** subsumed for *bounding a cumulant*, which
   is what is needed here.

Obligation 3 is the one that reverses §11.3's verdict in a limited way: de Bruijn–Ilieff is stronger
as a route to real-rootedness, but it says nothing about `Var_π(log s)`, and that is the quantity this
reduction consumes.

### 14.4 Novelty, stated hostilely

The perturbation-off-a-model framing is GORZ's; theirs expands in `1/log n` and is asymptotic. §14.1
is **exact at every `n`**, which is the only reason it is worth writing down, and even so it is a
change of variables, not a theorem. §14.2's `(1,3,6)` direction and the `6 − 12 + 6 = 0` cancellation
are computations, not insights. **The one thing here that would be a result is `κ*(b)`**, and it is
not proved. Recorded as a program with three named obligations, not as progress.

## Gates (revised)

- [x] §12.3 overclaim withdrawn — `d = 4` all `n` is open, not excluded
- [x] exact `ε`-reduction to a semialgebraic region in `ℝ³`, in Lean
- [x] `P ≤ 0` free from CNV; `d = 4` needs two conditions, not three
- [x] leading direction `(1,3,6)`; `d = 2` calibrates the constant to exactly `1`
- [ ] `κ*(b)` in closed form or bounded below — **pure algebra, the next task**
- [ ] unconditional bound on `κ₂ = Var_π(log s)` for the tilted theta measure
- [ ] unconditional bounds on `κ₃, κ₄`
- [ ] independent audit (Codex)

## 15. `κ*(b)` computed: the Wronskian collapses, and the degree-four constant is `2/3`

§14's obligation (1) was "`κ*(b)` in closed form, or a rigorous lower bound — pure algebra." Here it
is, to leading order, together with the exact algebra it rests on.

### 15.1 The perturbation is the Euler operator, and the pencil is affine

In the Pochhammer basis `A(z) = ∑ c_j z^j`, `c_j = C(d,j)/(b)_j`, the second-cumulant perturbation is
`B(z) = ∑ C(j,2) c_j z^j`, i.e.

```text
A + κB = (1 + (κ/2)·z²D²) A = p(θ)A ,     p(j) = 1 + κ·C(j,2),  θ = z d/dz .
```

**No universal `κ ≠ 0` works.** By Pólya–Schur a symbol `{p(j)}` preserves hyperbolicity of all
polynomials with real zeros of one sign iff `∑ p(j) z^j/j!` lies in the Laguerre–Pólya class. Here

```text
∑_j (1 + κ C(j,2)) z^j/j!  =  e^z (1 + κz²/2) ,
```

whose zeros are `±√(−2/κ)`: purely imaginary for `κ > 0`, and real *of opposite signs* for `κ < 0`.
So `{1 + κC(j,2)}` is a first-kind multiplier sequence only at `κ = 0`. Hyperbolicity for `κ ≠ 0` is
therefore a property of the **specific** model, never a universal preservation — which is why the
constant has to be computed rather than quoted.

### 15.2 The Wronskian collapse

The pencil is affine in `κ`, so eliminating `κ` from `A + κB = 0`, `A′ + κB′ = 0` gives

```text
W(z) = A′B − AB′ = 0 ,      κ = −A(z)/B(z) .
```

Antisymmetrizing `W = ∑_{j,k} C(k,2) c_j c_k (j−k) z^{j+k−1}` by swapping `(j,k)`:

```text
C(k,2)(j−k) + C(j,2)(k−j) = −(j−k)²(j+k−1)/2 ,
```

so, **exactly**,

```text
W(z) = −(z/2) · ∑_{m≥2} (m−1)·S_m·z^{m−2} ,      S_m = ∑_{j<k, j+k=m} (k−j)²·c_j·c_k .
```

The coefficients of `W/z` are the **squared-gap-weighted convolution of the coefficient sequence with
itself**, all of one sign. Consequences, both proved in Lean at `d = 4`:

- `wronskian_collapse` — the identity, by `ring`;
- `criticalQuintic_pos_of_nonneg` — for positive `c_j` the critical polynomial is strictly positive on
  `z ≥ 0`, so every critical point lies on the negative axis, where the model's roots are.

### 15.3 Degeneracy, and the constant

Write `z = −b·w` and `c_j = C(d,j)b^{−j}ρ_j`, `ρ_j = 1 − C(j,2)/b + O(b^{−2})`. At `d = 4`:

```text
criticalQuintic = b^{−2} [ 24(1−w)^5 + (1/b)·R(w) + O(b^{−2}) ] ,
R(w) = 216w^5 − 840w^4 + 1248w^3 − 864w^2 + 264w − 24 = 24(w−1)³(9w² − 8w + 1) .
```

Two facts drop out and neither is guessable:

1. **The leading term is `24(1−w)^5`** — the five critical points coalesce at `w = 1`, i.e. `z = −b`.
2. **The correction vanishes to order three at `w = 1` as well.** So the degeneracy is *not* broken at
   order `b^{−1/5}`; factoring `(w−1)³` out of both terms leaves

```text
−(w−1)² + (9w² − 8w + 1)/b = 0   ⟹   w = 1 ± √(2/b)  ⟹   z = −b ∓ √(2b) .
```

At those points, with `δ = ±√(2/b)`,

```text
A(−b(1+δ)) = δ⁴ − (6/b)(1+δ)²δ² + O(b^{−2}) = 4/b² − 12/b² = −8/b² ,
B(−b(1+δ)) = 6(1+δ)²δ² + O(b^{−2}) = 12/b ,
```

hence

```text
κ*(b) = |A/B| = (8/b²)/(12/b) = 2/(3b) + O(b^{−2}) .
```

**`κ*(b) ≈ 2/(3b)` at `d = 4`.** The `d = 2` case is the same computation with one critical point,
`z = −b` exactly, and gives `κ* = 1/b` **exactly** — `degreeTwo_criticalKappa` in Lean, and it agrees
with the independently derived window `D n ≤ 2/(2n+1)` of §8.2. Two derivations, one number.

**A `b^{−2/5}` estimate is what a first pass gives and it is wrong.** Reading off `(1−w)^5` alone
predicts the critical points split at `|1−w| ≍ b^{−1/5}` and hence `κ* ≍ b^{−2/5}`. That ignores that
`R(w)` also vanishes to order three at `w = 1`; the true splitting is `b^{−1/2}` and the true
tolerance is `≍ 1/b`. Recorded because the wrong answer is an order of magnitude too optimistic and is
what the natural shortcut produces.

### 15.4 What this would give

With `κ₂ ≍ 1/(n log n)` for the tilted theta measure (§3's saddle) and `b = n + ½`:

```text
1/(n log n) ≤ 2/(3n)   ⟺   log n ≥ 3/2   ⟺   n ≥ 5 .
```

So the leading-order arithmetic predicts `d = 4` hyperbolicity for **every `n ≥ 5`**, leaving five
cases. That is a very different picture from `n ≥ c·e²`, and it is the first quantitative statement in
this lane that is not an asymptotic in `1/log n`.

**It is not a theorem, and three gaps are load-bearing:**

1. `κ*(b) = 2/(3b) + O(b^{−2})` is leading order; a rigorous lower bound on `κ*` for all `b ≥ ½` is
   needed, and the `O(b^{−2})` term is not controlled.
2. The reduction to the single parameter `κ₂` drops `κ₃, κ₄`. The exact condition is a region in `ℝ³`
   (§14.1); the one-parameter section is the leading term of a curve through it.
3. `κ₂ ≍ 1/(n log n)` is a saddle heuristic, not a bound.

All three are finite, named, and of a kind that has been done before in this lane. None is a
literature question — they are estimates.

### 15.5 Lean

`HTGeometry/JensenPerturbationWronskian.lean`, axiom-clean, registered, build green:

```text
modelA, perturbB, modelA', perturbB'      the pencil and its derivatives
hasDerivAt_modelA, hasDerivAt_perturbB    they are the derivatives
gapConv                                   S_m, the squared-gap convolution
wronskian_collapse                        A′B − AB′ = −(z/2)·∑ (m−1)S_m z^{m−2}
criticalQuintic, criticalQuintic_pos_of_nonneg   critical points are all negative
critical_kappa_eq                         κ = −A/B at a critical point
degreeTwo_critical_values, degreeTwo_criticalKappa   κ* = 1/b exactly at d = 2
```

### 15.6 Novelty, stated hostilely

The Wronskian elimination is standard for affine pencils. The **collapse formula** — that the
Wronskian of `A` against `½z²A''` has coefficients `−(m−1)S_m/2` with `S_m` the squared-gap
convolution — is a two-line antisymmetrization and I would expect it to be known in the
hyperbolicity-preserver literature, though I have not found it. The Pólya–Schur computation
`∑(1+κC(j,2))z^j/j! = e^z(1+κz²/2)` is immediate. **The one thing I would defend as new is the pair of
numbers: `κ*(b) = 1/b` exactly at `d = 2` and `2/(3b) + O(b^{−2})` at `d = 4`**, together with the
double degeneracy of `R` at `w = 1` that produces the second. Even that is a computation, not an idea;
its value is that it converts "beat `e^{d/2}`" into "check five values of `n`".

## Gates

- [x] `κ*(b)` at `d = 4`, leading order: **`2/(3b)`**; at `d = 2`: **`1/b` exactly** (Lean)
- [x] Wronskian collapse formula, Lean, axiom-clean
- [x] no universal multiplier sequence: `e^z(1+κz²/2)` is not `LP` for `κ ≠ 0`
- [x] the `b^{−2/5}` shortcut identified as wrong, with the reason
- [ ] rigorous lower bound on `κ*(b)` for all `b ≥ ½` (control the `O(b^{−2})`)
- [ ] the `ℝ³` region, not just the `(1,3,6)` section: `κ₃, κ₄` bounds
- [ ] rigorous `κ₂ = Var_π(log s)` bound for the tilted theta measure
- [ ] the residual small-`n` cases

## 16. Gap (3): the creator, and it is Brascamp–Lieb on the log-tilt

§15's obligation (3) was "a rigorous `κ₂` bound replacing the saddle heuristic." That is the one of
the three which is `Ξ`-specific, and it is the *creator* Codex correctly said was missing. Here is the
mechanism, its calibration, and its exact accounting against the literature.

### 16.1 The log-tilt is log-concave, uniformly in `n`

`κ₂ = Var_π(log s)` with `π ∝ u^{2n}Φ(u)du` and `s = u²`, so `κ₂ = 4·Var_π(log u)`. Set `L = log u`.
The density of `L` is `∝ exp((2n+1)L + log Φ(e^L))`, and **the tilt is linear in `L`, so it drops out
of the second derivative**:

```text
−(log-density)''(L)  =  u·|(log Φ)'(u)|  +  u²·(−(log Φ)''(u)) ,      u = e^L .
```

Both terms are nonnegative as soon as `Φ` is decreasing and log-concave. `LogTiltConcavity.lean`,
axiom-clean: `hasDerivAt_logTiltDensity`, `hasDerivAt_logTiltSlope`, `logTilt_curvature_nonpos`,
`logTilt_curvature_eq`, `logTilt_curvature_neg`. The curvature bound is **uniform in `n`** — the point
of passing to `L`.

`Φ` decreasing on `[0,∞)` is classical; **log-concavity of the theta kernel in the Fourier
representation of `ξ` is also classical**, with more than one published proof. So both hypotheses are
imported, not derived.

### 16.2 The bound, and its exact calibration

One-dimensional Brascamp–Lieb for a log-concave density `e^{−V}` gives `Var(f) ≤ E[f′²/V″]`; with
`f = L`:

```text
κ₂ = 4·Var_π(L)  ≤  4·E_π[ ( u|(log Φ)′(u)| + u²(−(log Φ)″(u)) )^{−1} ] .
```

Two regimes, and the calibration is the point:

- **Using log-concavity only** — i.e. keeping the `u^{2n}` tilt in the `u` variable instead, where
  `V″ ≥ 2n/u²` — one gets `Var(log u) ≤ 1/(2n)`, hence `κ₂ ≤ 2/n`. Sharp: for `Φ(u) = e^{−u}` the
  tilted law is `Γ(2n+1)` and `Var(log u) = ψ′(2n+1)`, so the bound is attained in the log-linear
  case. **Against the `d = 2` requirement `κ₂ ≤ 1/(n+½)` this is short by exactly a factor 2.**
- **Including the curvature term.** At the saddle `u_n ≈ ½log n` one has `u|(log Φ)′| ≈ n` and
  `u²(−(log Φ)″) ≈ 2n u_n`, so the curvature is `≈ 2n(1 + u_n)` and `κ₂ ≲ 4/(n(2+log n))`. Against
  `d = 2`'s `1/(n+½)` that closes for `n ≥ 8`; against `d = 4`'s `2/(3b)` (§15) it closes for
  `n ≥ 55`.

So the factor-2 shortfall is exactly the content of the Turán inequality that log-concavity alone
cannot supply, and it is closed by the double-exponential decay of `Φ` entering through `(log Φ)″`.
That is a precise account of *where* CNV's theorem lives, in a form that generalizes to every degree.

### 16.3 Why this is the missing direction

The corpus's standing diagnosis (`positivity-creators-versus-transporters`) is that source positivity
yields **lower** bounds while every RH criterion consumes an **upper** bound. This is an upper-bound
engine and it is driven by a different property of the source:

| source property | mechanism | direction |
|---|---|---|
| `Φ > 0` | Hankel positive semidefinite, Cauchy–Schwarz | **lower** bounds on moment ratios |
| `Φ` decreasing, log-concave | Brascamp–Lieb on the log-tilt | **upper** bound on `Var(log s)` |

It is also **not** subsumed by §11.3's de Bruijn–Ilieff verdict. That criterion is stronger as a route
to real-rootedness and makes the log-concavity route redundant *there*; it says nothing whatever about
`Var_π(log s)`, which is the quantity the perturbation reduction of §14–§15 consumes. My §11.3 claim
that the log-concavity engine is "subsumed, 75 years older and stronger" was therefore too broad, and
is corrected here to: subsumed for hyperbolicity, not subsumed for cumulant bounds.

### 16.4 Novelty, stated hostilely

Every ingredient is classical: log-concavity of the theta kernel (published, several proofs),
one-dimensional Brascamp–Lieb (1976), the reduction to the log variable (elementary). **The
combination is what I could not find**: searching for Brascamp–Lieb, or log-concave variance bounds,
against the Turán/Jensen/`ξ` literature returns nothing. What would be a result is not the inequality
but the calibration — that log-concavity alone lands within a factor 2 of the Turán inequality and
that the residual factor is exactly the kernel's curvature term — and that is a computation.

Two things this does **not** do, stated plainly. It does not reprove CNV (it is a factor 2 short
without the curvature term, and the curvature term needs a rigorous lower bound on `−(log Φ)″`, which
I have not established). And it does not touch `κ₃, κ₄`, which §15's gap (2) still needs.

## Gates

- [x] gap (3) mechanism identified and reduced to two classical inputs
- [x] log-tilt curvature identity, uniform in `n`, in Lean, axiom-clean
- [x] calibration: log-concavity alone is a factor 2 from Turán; curvature closes it
- [x] §11.3 overbroad claim corrected — subsumed for hyperbolicity, not for cumulants
- [ ] rigorous lower bound on `−(log Φ)″(u)`, explicit in `u`
- [ ] one-dimensional Brascamp–Lieb in Lean (mathlib has none)
- [ ] gap (1): rigorous lower bound on `κ*(b)`; gap (2): `κ₃, κ₄`

## 17. Gap (3a) reduced: the mixture identity, and the theta kernel's log-concavity margin

The remaining analytic input is a rigorous lower bound on `−(log Φ)″(u)`. `Φ` is a **sum**, and
log-concavity is not inherited by sums, so this needs the mixture identity. Writing
`Φ = ∑_k φ_k`, `a_k = (log φ_k)′`, `c_k = −(log φ_k)″`, `w_k = φ_k/Φ`:

```text
Φ″Φ − (Φ′)² = ½ ∑_{j,k} φ_j φ_k [ (a_j − a_k)² − c_j − c_k ] ,
```

hence, exactly,

```text
−(log Φ)″  =  E_w[c]  −  Var_w[a] .
```

**A mixture of log-concave functions is log-concave exactly when the mean curvature beats the
variance of the log-slopes.** (Classical in the log-concavity literature; recorded because it is the
tool and the corpus has nothing on mixtures.)

### 17.1 The single term

For `φ_1(u) = (2π²e^{9u/2} − 3πe^{5u/2})e^{−πe^{2u}}`, writing `log φ_1 = 5u/2 + log(2π²e^{2u} − 3π)
− πe^{2u}`:

```text
−(log φ_1)″(u) = 4πe^{2u} + 24π³e^{2u}/(2π²e^{2u} − 3π)²  >  4πe^{2u}     for u ≥ 0
```

(the bracket is positive for `e^{2u} > 3/(2π)`, i.e. for all `u ≥ −0.29`). Each `φ_k` is log-concave
on `u ≥ 0` with curvature `≥ 4πk²e^{2u}`.

### 17.2 The mixture correction is exponentially small

With `x = πe^{2u} ≥ π` for `u ≥ 0`, the weights are `w_k ∝ k⁴e^{−k²x}`, so `w_2/w_1 = 16e^{−3x}`.
Leading order: `E_w[c] ≈ 4πe^{2u}E_w[k²] ≈ 4πe^{2u}` and `Var_w[a] ≈ 4π²e^{4u}Var_w[k²] ≈
4π²e^{4u}·9·16e^{−3x}`. The log-concavity condition `E_w[c] ≥ Var_w[a]` becomes

```text
144·x·e^{−3x} ≤ 1 ,      x = πe^{2u} ≥ π ,
```

and at `x = π` the left side is `≈ 0.036`. **So `Φ` is log-concave on `u ≥ 0` with roughly a
thirty-fold margin at the worst point, and the margin improves double-exponentially.** A rigorous
bound of the shape

```text
−(log Φ)″(u)  ≥  3π e^{2u}      for all u ≥ 0
```

is therefore a finite tail estimate, not a delicate one.

### 17.3 What that closes

In the `u` variable the tilted potential has `V″ = 2n/u² + (−(log Φ)″) ≥ 2n/u² + 3πe^{2u}`, so
Brascamp–Lieb gives

```text
κ₂ = 4·Var_π(log u)  ≤  4·E_π[ 1/(2n + 3π u² e^{2u}) ] .
```

The integrand is decreasing in `u`, so the bound follows from a lower tail estimate for `π` — and `π`
is log-concave (§16.1), so its lower tail is exponential with explicit constants. That is the last
step and it is standard.

Against the requirements: `d = 2` needs `κ₂ ≤ 1/(n+½)`, `d = 4` needs `κ₂ ≤ 2/(3(n+½))` (§15). With
`u ≈ u_n ≈ ½log n` the bracket is `2n + 3πu_n²e^{2u_n} ≈ 2n(1 + O(log n))`, so both close for
explicit `n`, and the residual small-`n` cases are what remains.

### 17.4 Honest accounting

Nothing in §17 is a theorem yet. The mixture identity is exact and classical; §17.1 is a
differentiation; §17.2 is a leading-order estimate whose rigorous form needs the tail of `∑_{k≥2}`
handled explicitly; §17.3 needs a log-concave lower-tail bound. **All four are finite estimates on
explicit functions with no open input.** That is the difference between this and every other lane
examined in this card: the obstructions here are arithmetic, not conceptual.

## Gates

- [x] mixture identity `−(log Φ)″ = E_w[c] − Var_w[a]`
- [x] per-term curvature `−(log φ_k)″ > 4πk²e^{2u}` on `u ≥ 0`
- [x] mixture correction is `O(x e^{−3x})`, margin `≈ 30×` at the worst point `u = 0`
- [ ] rigorous `−(log Φ)″(u) ≥ 3πe^{2u}` with the `k ≥ 2` tail handled
- [ ] log-concave lower-tail bound for `π`, giving `E_π[1/(2n + 3πu²e^{2u})]`
- [ ] one-dimensional Brascamp–Lieb in Lean
- [ ] gap (1) `κ*(b)` rigorous; gap (2) `κ₃, κ₄`

## 18. Gap (2) closes, and it does not need cumulants at all

§15's obligation (2) was to control `κ₃, κ₄`, because the reduction of the hyperbolicity region to the
one-parameter direction `κ₂·(1,3,6)` is only a leading-order truncation of a cumulant series. That
obligation dissolves: **both bounds on `ε j` are Jensen inequalities, and neither expands anything.**

### 18.1 The two-sided bound

With `π` a probability measure on `(0,∞)`, `s = e^L`, and `L` centred (`E_π[L] = 0`, a harmless
normalization since `ε j` is scale-invariant):

```text
1 + ε j = E[s^j]/E[s]^j = E[e^{jL}]/E[e^L]^j .
```

- **Lower.** `x ↦ x^j` is convex on `[0,∞)`, so `E[s^j] ≥ E[s]^j`, i.e. `ε j ≥ 0`. This is the free
  half — precisely the log-convexity that §4's Finding B identified as carrying the wrong sign — and
  no hyperbolicity criterion can consume it.
- **Upper.** `E[e^L] ≥ e^{E[L]} = 1` by Jensen, so the denominator is `≥ 1` and

```text
ε j  ≤  E_π[e^{jL}] − 1 .
```

`MomentRatioTwoSided.lean`, axiom-clean: `pow_expectation_le`, `epsilon_nonneg`, `epsilon_zero`,
`epsilon_one`, `epsilon_le_expMoment`, `epsilon_mem_Icc`.

### 18.2 Why this closes the gap

The entire perturbation `(ε₂, …, ε_d)` is now sandwiched between `0` and **one exponential moment of
the centred log-variable**. For a log-concave `π` — which §16.1 establishes for the tilted theta
measure, uniformly in `n` — the centred exponential moment obeys `E[e^{jL}] ≤ exp(C j² Var(L))` in the
range `j√Var(L) ≲ 1`, by the standard sub-exponential bound. Hence

```text
0 ≤ ε j ≤ exp(C j² κ₂) − 1 ,
```

with `κ₂ = Var_π(L)` the *only* free quantity. **No third or fourth cumulant appears anywhere.** The
validity range is `d·√κ₂ ≲ 1`, i.e. `d ≲ √(n log n)` — far beyond `d = 4`.

So §15's three obligations reduce to two:

| was | now |
|---|---|
| (1) rigorous `κ*(b)` | unchanged — algebra on the quintic pencil |
| (2) `κ₃, κ₄` bounds | **closed**: Jensen, both sides, plus log-concavity of `π` |
| (3) rigorous `κ₂` bound | unchanged — §16–§17, reduced to two finite estimates |

### 18.3 Honest accounting

Both inequalities are Jensen and the sub-exponential bound for log-concave measures is classical.
What changes is the *shape* of the argument: replacing a cumulant expansion by a two-sided sandwich
removes a truncation whose error was never estimated, and it makes the perturbation a function of one
number rather than three. That is bookkeeping, not a theorem — but it was load-bearing bookkeeping,
because the one-parameter reduction was the weakest link in §15 and it was stated as a leading-order
approximation with no error control.

The `ε j ≥ 0` half deserves a note: it is *exactly* the free positivity that the corpus's
`positivity-creators-versus-transporters` card says every lane gets for nothing and no lane can use.
Here it is visible as one half of a sandwich whose other half is the entire problem — which is the
cleanest illustration of that diagnosis anywhere in this card.

## Gates

- [x] gap (2) closed — two-sided Jensen sandwich, Lean, axiom-clean
- [x] the perturbation depends on `κ₂` alone; validity `d ≲ √(n log n)`
- [ ] gap (1): rigorous lower bound on `κ*(b)` for all `b ≥ ½`
- [ ] gap (3a): rigorous `−(log Φ)″(u) ≥ 3πe^{2u}` with the `k ≥ 2` tail
- [ ] gap (3b): log-concave lower-tail bound for `π`
- [ ] 1-D Brascamp–Lieb in Lean (mathlib has none)
- [ ] the residual small-`n` cases

## 19. Discharging, not interfacing — and one error the discharge exposed

Audit first. Every module in §8–§18 is unconditional in the strict sense — no `sorry`, `admit`,
`axiom`, `opaque` or `unsafe`, and `#print axioms` returns `[propext, Classical.choice, Quot.sound]`
throughout. But every one is a **general lemma with hypotheses**, and until this section exactly one
`ξ`-side hypothesis had been discharged (`hankel_nonneg_of_measure`, which supplies the *free*
direction). That is the same defect diagnosed in `prime_frequency_forces_transcendence` — a
conclusion consumed by a hypothesis nobody produced — reproduced in my own work.

### 19.1 The corpus already had the theta atom's exact curvature

Searching before building, as mandated: `RHTower/ThetaCusp/ThetaCuspFinitePrimeSource.lean` defines

```text
thetaCuspSeed t = 2π(2πt⁴ − 3t²)e^{−πt²} ,   thetaCuspSourceTerm x n = e^{x/2}·thetaCuspSeed(n e^x) ,
```

which is exactly `2·φ_n` for the kernel of §17. And `PrimeArchThetaBornWittenGroundState.lean`
already proves the Born–Witten normal form:

```text
(log φ_n)′ = −2·B_n ,   B_n′ = thetaCuspBornWittenCurvature n x = 2·scale + 3·scale/weight² ,
```

with `scale = π n² e^{2x}` and `weight = scale − 3/2`. Translating: `c_n = 2·curvature =
4πn²e^{2x} + 6πn²e^{2x}/weight²`, which is **identical** to the formula derived by hand in §17.1
(`4y + 24y/(2y−3)²`, `y = πn²e^{2x}`). The corpus had the whole per-atom computation formalized;
§17.1 re-derived it.

### 19.2 What is now discharged

`RHTower/ThetaAtomLogCurvature.lean`, axiom-clean, registered, `lake build` green:

```text
thetaCuspAtomLogSlope, thetaCuspAtomLogCurvature       a n x = −2B_n ,  c n x = 2·curvature
hasDerivAt_thetaCuspSourceTerm_logSlope                φ′ = a·φ            — no free hypotheses
hasDerivAt_thetaCuspSourceTerm_second                  φ″ = (a² − c)·φ     — no free hypotheses
two_mul_thetaCuspMorseScale_le_curvature               the correction term is nonnegative
thetaCuspAtomLogCurvature_floor                        c n x ≥ 4π n² e^{2x}   for n ≥ 1, x ≥ 0
thetaCuspAtomLogCurvature_uniform_floor                c n x ≥ 4π e^{2x}
thetaCuspTruncated_logCurvature_ge                     mixture bound at the actual theta atoms
```

The last one instantiates `MixtureLogConcavity.mixture_curvature_ge` at the theta source and
**discharges its curvature hypothesis `hC` outright**. What remains in it is a single hypothesis,
`hE`: a bound on the weighted variance of the atom log-slopes. That is the honest state — one
hypothesis, named, about a specific explicit quantity.

### 19.3 The error the discharge exposed

§16 and §17 assumed `Φ` is **decreasing** on `[0,∞)` and used it as a term-wise property. It is not
term-wise. With `a(y) = 5/2 + 4y/(2y−3) − 2y` and `y = πn²e^{2u}`, solving `a = 0` gives
`4y² − 15y + 7.5 = 0`, i.e. `y = (15 ± √105)/8`, so

```text
a₁ > 0  for  y ∈ (0.5941, 3.1559)  and  y₁(0) = π = 3.1416 < 3.1559 .
```

**The first atom is increasing at `u = 0`**, with maximum at `πe^{2u} = 3.1559`, i.e. `u ≈ 0.00227`.
Only the `n ≥ 2` atoms are decreasing there, and the cancellation that makes `Φ′(0) = 0` is between
`w₁a₁ ≈ +0.0442` and `w₂a₂ ≈ −0.0440` — a coincidence only if one forgets that `Φ′(0) = 0` is forced
by **evenness**, i.e. by the theta functional equation.

Consequence: the hypothesis `(log Φ)′ ≤ 0` of `LogTiltConcavity` cannot be discharged term by term at
all. It must come from `Φ` even together with `Φ` log-concave, which give monotonicity on `[0,∞)` for
free. So the dependency is

```text
theta functional equation  ⟹  Φ even  }
mixture curvature bound    ⟹  Φ log-concave  }  ⟹  Φ decreasing on [0,∞)  ⟹  LogTilt hypotheses
```

and the functional equation is an input that must be imported, not derived from the series. This only
became visible on attempting the discharge; §16–§17 read as if the monotonicity were elementary.

## Gates

- [x] audit: all modules unconditional, axiom-clean; but interfaces, not producers
- [x] corpus search first — the per-atom Born–Witten curvature was already formalized
- [x] `hC` discharged at the actual theta atoms (`thetaCuspAtomLogCurvature_floor`)
- [x] `φ′ = aφ` and `φ″ = (a²−c)φ` discharged at the actual theta atoms
- [x] error found: `Φ` is **not** term-wise decreasing; `φ₁` increases up to `u ≈ 0.00227`
- [ ] `hE`: weighted variance of the atom log-slopes — the one remaining hypothesis
- [ ] `Φ` even, from the theta functional equation (import, then combine)
- [ ] the truncation-to-series step
- [ ] gap (1) `κ*(b)` rigorous; 1-D Brascamp–Lieb in Lean

## 20. `hE` reduced to a combinatorial variance, using the corpus's own identity

The one hypothesis left in `thetaCuspTruncated_logCurvature_ge` was `hE`, a bound on the weighted
variance of the atom log-slopes. It is now reduced to a bound on the weighted variance of the
**squared atom indices**, with an explicit constant, and the reduction uses a corpus theorem rather
than a new derivation.

### 20.1 The gap identity was already in the tree

`PrimeArchThetaAtomLikelihoodRatio.thetaCuspBornWittenSuperpotential_sub_eq_scaleDifference_mul`:

```text
B_n − B_m = (scale_n − scale_m) · (1 + (3/2)/(w_n w_m)) ,      w = scale − 3/2 .
```

Since `a_n = −2B_n`, this is exactly the identity §19.3 derived by hand
(`a_j − a_k = −(y_j − y_k)[2 + 12/((2y_j−3)(2y_k−3))]`, the two brackets agreeing because
`2y − 3 = 2w`). Third time in two sections that a hand derivation reproduced formalized corpus
material; the corpus-search mandate is earning its place.

### 20.2 What is now proved

`RHTower/ThetaAtomLogCurvature.lean` (extended), axiom-clean, `lake build` green:

```text
pi_le_thetaCuspMorseScale               π ≤ scale_n            for n ≥ 1, x ≥ 0
pi_sub_le_thetaCuspBornWittenWeight     π − 3/2 ≤ w_n
logSlopeLipschitz                       Λ := 2 + 3/(π − 3/2)²
thetaCuspAtomLogSlope_sub_eq            the exact gap, from the corpus identity
thetaCuspAtomLogSlope_sub_sq_le         (a_n − a_m)² ≤ Λ²(scale_n − scale_m)²
thetaCuspLogSlopeVariance_le            ∑∑ φφ(a−a)² ≤ Λ² ∑∑ φφ(scale − scale)²
```

So the analytic content of `hE` is discharged: **the log-slope variance is Lipschitz-controlled by
the Morse-scale variance**, with `Λ = 2 + 3/(π − 3/2)² = 3.1133…` — the same constant §19.2 obtained
from a derivative bound, here obtained exactly.

### 20.3 What remains, stated exactly

Since `scale_n = π n² e^{2x}`, the surviving requirement is purely combinatorial:

```text
Var_w(n²)  ≤  1/(Λ² π e^{2x}) ,        w_n = φ_n/Φ ,
```

which by `Var ≤ E[(n²−1)²]` and `w_n ≤ φ_n/φ_1` follows from

```text
∑_{n≥2} (φ_n/φ_1)(n²−1)²  ≤  1/(Λ² π e^{2x}) .
```

The corpus supplies the ratio machinery (`thetaCuspAtomLikelihoodRatio`, antitone in `x`;
`summable_thetaCuspHigherAtomLikelihoodRatios`), so what is missing is one explicit bound
`φ_n/φ_1 ≤ C n⁴ e^{−π(n²−1)e^{2x}}` and a geometric tail. §19.2's numbers say the inequality holds at
the worst point `x = 0` with a `1.7×` margin — tight, so the constants cannot be loosened.

### 20.4 Dependency map, honest

```text
[done]  φ′ = aφ, φ″ = (a²−c)φ                    at the actual theta atoms
[done]  c_n ≥ 4π n² e^{2x}                        at the actual theta atoms
[done]  (a_n − a_m)² ≤ Λ²(scale_n − scale_m)²     at the actual theta atoms
[open]  ∑_{n≥2}(φ_n/φ_1)(n²−1)² ≤ 1/(Λ²πe^{2x})   explicit ratio bound + geometric tail
[open]  truncation → full series                  summability is in the tree; the limit is not taken
[open]  Φ even                                    theta functional equation, an import
[open]  1-D Brascamp–Lieb                         absent from mathlib
[open]  κ*(b) rigorous                            algebra on the quintic pencil
```

Everything marked `[done]` is a theorem about `thetaCuspSourceTerm` with no undischarged hypothesis
beyond `n ≥ 1` and `x ≥ 0`. Everything marked `[open]` is named and finite. That is the difference
between this and the four closed lanes, and it is still not a proof of anything about `Ξ`.

## 21. The atom ratio in closed form, discharged

The remaining piece of `hE` was a bound on `φ_n/φ_1`. It has an exact closed form in the Morse
coordinate, and the bound follows from `s₁ ≥ 3` alone.

### 21.1 Closed form

With `s_n = thetaCuspMorseScale n x = π(n e^x)²`, the atom is exactly

```text
φ_n = e^{x/2} · 2 s_n (2 s_n − 3) e^{−s_n}          (thetaCuspSourceTerm_eq_morse)
```

— the seed's `2π(2πt⁴ − 3t²)` is `2s(2s − 3)` and its exponent is `−s`. Since `s_n = n² s₁`
(`thetaCuspMorseScale_eq_sq_mul`),

```text
φ_n/φ_1 = n²·( n² + 3(n²−1)/(2s₁ − 3) )·e^{−(n²−1)s₁} .
```

### 21.2 The bound, from `s₁ ≥ 3`

`π > 3` gives `s₁ = πe^{2x} ≥ π > 3` on `x ≥ 0`, and the algebraic core is

```text
2(ms)(2ms − 3) ≤ 2m²·2s(2s − 3)      for s ≥ 3, m ≥ 1      (morse_ratio_algebra)
```

— the difference is `2ms(2ms − 6m + 3)`, nonnegative because `2ms ≥ 6m > 6m − 3`. Taking `m = n²`:

> **`φ_n ≤ 2n⁴ e^{−(n²−1)s₁} · φ₁`** for `n ≥ 1`, `x ≥ 0`  (`thetaCuspSourceTerm_le_ratio_bound`),

axiom-clean, no undischarged hypothesis. This is the last analytic ingredient of `hE`; what remains
is arithmetic on the resulting series.

### 21.3 The arithmetic that remains

`Var_w(n²) ≤ ∑_{n≥2}(φ_n/φ_1)(n²−1)² ≤ 2∑_{n≥2} n⁴(n²−1)² e^{−(n²−1)T}`, `T = s₁ ≥ π`, against the
requirement `1/(Λ²T)` with `Λ = 2 + 3/(π−3/2)²`. The `n = 2` term is `288 e^{−3T}`; at `T = π` that is
`0.0231` against `1/(Λ²π) = 0.0328`, and the `n ≥ 3` tail starts at `10368 e^{−8π} ≈ 1.4 × 10^{−7}`.
For `T > π` the comparison is `288 Λ² T e^{−3T} ≤ 1`, which is `0.70` at `T = π` and decreasing.

**Margin `1.42×` at the worst point.** So the chain closes, but only just — and the residual work is
(i) a geometric bound for the `n ≥ 3` tail and (ii) the elementary inequality `288Λ²Te^{−3T} ≤ 1` for
`T ≥ π`, which is an analytic fact about `e`, not a numerical verification.

### 21.4 Ledger

```text
[done] φ′ = aφ, φ″ = (a²−c)φ                       thetaCuspSourceTerm, no free hypotheses
[done] c_n ≥ 4π n² e^{2x}                           thetaCuspAtomLogCurvature_floor
[done] (a_n − a_m)² ≤ Λ²(s_n − s_m)²                thetaCuspAtomLogSlope_sub_sq_le
[done] φ_n ≤ 2n⁴e^{−(n²−1)s₁}·φ₁                    thetaCuspSourceTerm_le_ratio_bound
[open] the two elementary estimates of §21.3
[open] truncation → full series
[open] Φ even — theta functional equation (import)
[open] 1-D Brascamp–Lieb (absent from mathlib)
[open] κ*(b) rigorous
```

Four items discharged against the actual theta source, none of them an interface. The lane is still
short of any statement about `Ξ`, and the two remaining estimates in §21.3 are where the `1.42×`
margin lives — if either is looser than claimed, the log-concavity conclusion fails and the whole
`κ₂` route with it.

## 22. `REDISCOVERED`: §16–§21 is `ThetaCuspKernelLogConcavity.lean`

The module I have been reconstructing for four sections exists, is unconditional, and is stronger
than what I built. Its own header:

> *"The first theta atom has a large explicit negative logarithmic curvature. This file keeps the full
> `x`-dependent Gaussian in the higher-atom comparison and proves that **the score variance of the
> complete atom mixture cannot exhaust that curvature**. The result is an unconditional,
> computation-free proof that `thetaCuspFullSource` is **strictly log-concave on the nonnegative
> half-line**. The proof repairs the missing perturbation step in the 2026 log-concavity preprints.
> It does not prove RH: order-two total positivity is strictly weaker than the all-order condition."*

"Score variance cannot exhaust the curvature" **is** the mixture identity `−(log Φ)″ = E_w[c] −
Var_w[a]` of §17. Item by item:

| built in §19–§21 | already in the corpus | verdict |
|---|---|---|
| `thetaCuspSourceTerm_le_ratio_bound` | `thetaCuspSourceTerm_le_first_dynamic` | identical — same `2n⁴`, same exponent |
| `thetaCuspAtomLogCurvature_floor` | `thetaCuspBornWittenLogCurvature_bounds` | identical, and the corpus also has the upper bound |
| `hasDerivAt_thetaCuspSourceTerm_second` | `iteratedDeriv_two_thetaCuspSourceTerm_eq` | identical |
| `thetaCuspAtomLogSlope_sub_eq` | `thetaCuspBornWittenSuperpotential_sub_eq_scaleDifference_mul` | identical up to `×(−2)` |
| `pi_le_thetaCuspMorseScale` | `thetaCuspLogConcavityScale_gt_three` | identical |
| `mixture_curvature_ge` (truncated) | `thetaCuspLogConcavityNumerator_neg_all` | corpus proves it for the **full series** |
| — | `strictConcaveOn_thetaCuspLogSource : StrictConcaveOn ℝ Set.univ` | the conclusion, on **all of ℝ** |

And the tail arithmetic of §21.3 that I flagged as the fragile step is
`ThetaCuspKernelLogConcavity.tsum_thetaCuspLogConcavityTailWeight_{four,six,eight}_le`, with the
geometric majorants already proved.

**`RHTower/ThetaAtomLogCurvature.lean` is deleted, unregistered, oleans cleaned.**

### 22.1 The corpus is already at order four on the source side

`ThetaCuspFullReflectionFourthTuran.lean` — *"Every estimate is symbolic and unconditional. No zero
data or Riemann-hypothesis assumption is used"* — proves

```text
160 < (log Φ)⁗(x) + 4·((log Φ)″(x))²        for x > 0
```

(`thetaCuspLogSource_fourthTuran_gt_one_hundred_sixty`), plus
`thetaCuspSourceReflectionFourthHankel_pos`. So the fourth-order source Turán inequality is done,
unconditionally, and the second-order one (log-concavity) is done for the full series on all of `ℝ`.

### 22.2 What this costs, and what it changes

Five hand derivations in this card reproduced formalized corpus material: the per-atom curvature
(§17.1), the log-slope gap (§20.1), the atom ratio (§21.1), the tail weights (§21.3), and the mixture
argument itself (§17). **The corpus-search mandate was followed for the Jensen/Pólya lane and not for
the theta-kernel lane**, because I reached the kernel from the Jensen side and never searched for it
under its own name. The search that would have caught it is `research "theta kernel log-concavity"`,
one call, at the top of §16.

What it changes: the `κ₂` route's *inputs* are not open — they are proved. The corpus's own note says
why that is not enough, in the same words as §11.4: **order-two total positivity is strictly weaker
than the all-order condition.** So the open question is not the log-concavity of `Φ`; it is whether
the corpus's order-four source inequality transfers to hyperbolicity of `J^(4,n)`, which is the
Jensen-side statement none of the source-side modules makes.

That transfer is the only thing in this card that is neither built nor known, and it is what §14's
`ε`-reduction and §15's `κ*(b)` were for.

## Gates (revised)

- [x] §16–§21 identified as `ThetaCuspKernelLogConcavity` — duplicate deleted
- [x] `Φ` strictly log-concave on `ℝ`, full series: **corpus, unconditional**
- [x] fourth-order source Turán `160 < (log Φ)⁗ + 4((log Φ)″)²`: **corpus, unconditional**
- [ ] transfer: source-side order-four inequality ⟹ `J^(4,n)` hyperbolic — the actual open step
- [ ] `κ*(b)` rigorous (§15) — still the algebra that would consume such a transfer

## 23. Correction to §15.3 (2026-09-06): `κ*(b) = 1/(2b)`, not `2/(3b)`

§15.3's expansion `A(−b(1+δ)) = δ⁴ − (6/b)(1+δ)²δ² + O(b⁻²)` drops the `+3/b²` term of §14.2's own
`δ⁴ − 6δ²/b + 3/b²`, which is of the same order as the two it keeps at `δ ≍ b^{−1/2}`; the critical points
`w = 1 ± √(2/b)` and the value `2/(3b)` are artefacts of that omission. Exactly, `(b)₄·A(−b) = 3b² − 18b`, and
in the variable `δ = t/√b` the leading-order perturbed quartic is `He₄(t) + 6K·He₂(t) = t⁴ − 6(1−K)t² +
3(1−2K)`, `K = κb`, which is hyperbolic iff `K ≤ 1/2` (inner roots collide at `z = −b`). Hence
`κ*(b) = 1/(2b)(1 + O(b^{−1/2}))`, and §15.4's "`n ≥ 5`" becomes `u_n ≥ 3/2`, i.e. `n ≳ 90` at leading
order. The general law is `He_d + (K/2)He_d''` with threshold `K*(d) = 1/⌊d/2⌋`. Successor card:
`jensen-quartic-dispersion-transfer.md`, which also records that the transfer is anisotropic (transverse
tolerance `≍ 1/b²`), so §18's box sandwich cannot be used and a two-sided dispersion bound is required.
