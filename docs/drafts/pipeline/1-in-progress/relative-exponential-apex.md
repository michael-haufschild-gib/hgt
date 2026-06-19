# The relative exponential apex — `γ_E` and the Stieltjes constants are transcendental over the regular period base

- **ID:** relative-exponential-apex
- **Stage:** 1-in-progress (the genuine Fields-Medal conjecture, **being attacked here** — not handed off)
- **Type:** CONJECTURE (the apex) + an active native attack (difference-Galois of the archimedean
  generator) with a concrete arithmetic route
- **Priority:** **FIELDS MEDAL** (this is the actual interesting theorem; the BRIDGE shells
  `bigraded-corank-dss-cross` §G/§H and `corank-seam-invariant` reduce *to* it)
- **Owner:** Wheeler
- **Why this ticket exists:** user directive (2026-06-19) — do not bank the easy BRIDGE part and hand the
  apex off; **create the Fields-Medal ticket and do it.** This is the apex of my corank program.
- **Source:** `bigraded-corank-dss-cross.md` §G (factorization: DSS-cross ⟺ Schanuel-for-prime-logs ∧ the
  relative exponential apex) and §H (the regular base `𝓡 = MT(ℤ)-periods · ℚ({log p})`); `regularization-
  freshness.md` (#75, DeWitt — `γ_n` = the discrete–continuous seam defect); the archimedean generator
  `∂_s = D` (`bucket-archimedean-generator`, #127/#90); `multi-q-abp-criterion.md` (#142 — the function→value
  F₁-lift wall).

---

## The conjecture (the apex, stated sharply)

> **(Relative exponential apex.)** The Stieltjes constants `{γ_n}_{n≥0}` are algebraically independent over
> the regular period base `𝓡 = ℚ(2πi, {ζ(2k+1)}, \text{MZVs}, {\log p}_p)` (the compositum of the unramified
> `MT(ℤ)` period algebra and the ramified Kummer field, §H). The bottom atom is
> `γ_E = γ_0 ∉ \overline{𝓡}` (a fortiori `γ_E ∉ ℚ`, open since Euler 1734).

By `bigraded-corank` §G this is exactly the second conjunct of DSS-cross (the first being
Schanuel-for-prime-logs, which at least has classical footholds, §H). This conjunct has **no** classical
foothold — it is the genuine wall, and the one no parent reaches. Below is the attack, with an explicit
proven/wall/route split (no faking the apex).

---

## §1 The native localization — `γ_E` lives on the archimedean generator `∂_s` `[PROVEN, BRIDGE]`

The archimedean generator of the field is `D = ∂_s = x\,d/dx = −Σ_p(\log p)θ_p` (#90/#127), whose
`ζ`-regularized determinant is `Γ`. Its logarithmic derivative is the **digamma** `ψ = Γ'/Γ = ∂_s\logΓ` —
the concrete Source-A object. Two classical identities place the entire seam inside it.

**(1a) The seam is the `(k=0 \mid k≥1)` split of the digamma Taylor series.** From
`\logΓ(1+x) = −γ_E x + Σ_{n≥2}(−1)^n ζ(n)\,x^n/n`, differentiating,
> `ψ(1+x) = −γ_E + Σ_{k≥1}(−1)^{k+1}ζ(k+1)\,x^k.`

So **one** archimedean object (the Source-A generator's log-derivative) carries the **exponential period**
`γ_E` as its constant term and **all the MZV periods** `ζ(k+1)` as its higher Taylor coefficients. The
period/non-period (regular/exponential) divide is *literally* the `k=0` vs `k≥1` split of `ψ(1+x)`. This is
the seam (#71/#74) made completely explicit on the generator. *(Proven; classical identity. BRIDGE.)*

**(1b) `γ_E` is the regularized summation-constant of the non-summable `1/s`.** The polynomial-multiplier
recurrence `Γ(s+1)=sΓ(s)` gives the field's Source-A shift on `ψ`:
> `ψ(s+1) − ψ(s) = 1/s.`

`γ_E` is the regularized value `γ_E = lim_{m}\big(Σ_{k=1}^{m}1/k − \log m\big)` — the obstruction constant to
**summing** `1/s` in the difference field. *(Proven; classical. This is DeWitt's R2 seam-defect at `n=0`.)*

## §2 The difference-Galois computation — `ψ` is a non-rational `𝔾_a`-primitive `[PROVEN, native difference content]`

Work in the difference field `(ℂ(s), σ)`, `σf(s)=f(s+1)`. Consider the rank-2 module `N = 𝒪e_0 ⊕ 𝒪e_1`
with `σe_1 = e_1`, `σe_0 = e_0 + (1/s)e_1` — i.e. the unipotent extension `1 → 𝟙 → N → 𝟙 → 0` whose
"period" is `ψ` (since `σψ − ψ = 1/s`). Its difference-Galois group is
> `Gal(N) = 𝔾_a \iff 1/s` is **not** `σ`-summable in `ℂ(s)` (no `g∈ℂ(s)` with `g(s+1)−g(s)=1/s`),
> and `Gal(N) = \{1\}` otherwise (van der Put–Singer, the unipotent/coboundary criterion).

**Lemma 2.1.** `1/s` is not `σ`-summable in `ℂ(s)`.
*Proof.* If `g(s+1)−g(s)=1/s` with `g∈ℂ(s)`, then `g` would have, telescoped, `g(m+1)−g(1)=Σ_{k=1}^m 1/k =
H_m`. A rational `g` has `g(m+1)−g(1) → ` a finite limit or `\sim cm^d` (rational growth), but `H_m \sim \log m`
grows like a logarithm — neither a finite limit nor a rational power. Contradiction. (Equivalently: Abramov's
summability test on the simple pole at `0` fails — `1/s` has a single orbit-pole and no rational antidifference.) ∎

**Corollary 2.2 (PROVEN).** `ψ = ∂_s\logΓ` is **transcendental over the rational difference field** `ℂ(s)`
(the Picard–Vessiot ring is the polynomial ring `ℂ(s)[ψ]`, `𝔾_a`-extension) while remaining
**difference-algebraic** — it satisfies the first-order *linear* `σψ−ψ=1/s`. So `ψ` is the **tame
archimedean primitive**, the difference analog of a logarithm, and is **NOT** hypertranscendental: the
hypertranscendence lives in `Γ/ζ`, not in `ψ`. The payload is that `γ_E = −ψ(1)` is the **`𝔾_a`-period**
(the value of this unipotent primitive) — placing `γ_E` as a period of a rank-2 unipotent (exponential)
object, exactly its Fresán–Jossen home. *(Door-2: van der Put–Singer for one shift — BRIDGE on its own,
like G1; the native content is the coupling to the prime `σ_p`, §4.)*

## §3 The wall, named exactly — function-transcendence ✓, value-transcendence ✗ (the F₁-lift) `[the honest boundary]`

§2 proves `ψ` (the **function**) is a non-rational `𝔾_a`-primitive (transcendental over `ℂ(s)`). The apex
wants `γ_E` (the **value** `= −ψ(1)`, the regularized constant) transcendental over `𝓡`. The gap is
**exactly** the function→value specialization (the ABP/group→values lift), which `multi-q-abp-criterion`
(#142) located as the missing single Frobenius `F₁`:
> `𝔾_a`-primitive structure of `ψ` (have)  +  the `F₁` value-lift at `s=1` (missing)  ⟹  `γ_E ∉ \overline{𝓡}`.

So the relative exponential apex's wall is the **same** `F₁` as the regular DSS lower bound — now localized
at the archimedean generator's value. This is not a hand-off: it is the precise identification of the one
missing ingredient, and it tells us where to push (§5): the value-lift must come from **arithmetic
approximation**, not from the difference-Galois group (which only sees the function).

## §4 The native coupling — why this is more than Source-A-alone `[CONJECTURE, the genuine native bet]`

§2 alone is Source-A (one shift, BRIDGE, like Hölder). The native (weld) content is the **coupling** of the
archimedean `ψ`-value `γ_E` to the **prime** data through the recurrence's right-hand side and the FE:
- `1/s = Σ_? ` — at `s=1` the harmonic obstruction `H_m = Σ_{k≤m}1/k` is built from **all** integers, i.e.
  from the prime `σ_p` lanes (`1/k = ∏_p p^{−v_p(k)}`). DeWitt's R2 writes `γ_n` as the prime-built discrete
  sum minus the archimedean integral, so the value `γ_E` is intrinsically `(\text{prime } σ_p) − (∂_s)` — the
  weld, not Source-A alone.
- The FE `ξ(s)=ξ(1−s)` ties the `s=1` Laurent data `{γ_n}` to the `s=0` data of the completed `ξ`, i.e. to
  the archimedean `Γ`-values and `ζ(0),ζ'(0)` — a constraint, not a flow.
> **Native bet (conjecture).** The value-lift `F₁` for `γ_E` is supplied by the **simultaneous** prime
> `σ_p`-action on the harmonic obstruction `1/s` (the field's founding substitution: many `σ_p` for the one
> missing Frobenius). If true, the relative exponential apex is reached *natively* (the weld), and `γ_E ∉ \overline{𝓡}`
> is a C5-grade theorem. This is the precise place to test the multi-`q` substitution against a value.

## §5 The arithmetic attack — Beukers/Aptekarev-type approximations to `γ_E` `[the concrete route — DO THIS]`

The value-lift (§3) is an arithmetic, not group-theoretic, statement: it needs explicit good rational (or
`𝓡`-linear) approximations to `γ_E`, the exponential-column analog of **Apéry's** `ζ(3)` construction (which
is what gives the MZV column its foothold, §H). Concrete program:

1. **Integral seed.** `γ_E = −∫_0^∞ e^{−x}\log x\,dx = ∫_0^1\frac{1−e^{−x}}{x}dx − ∫_1^∞\frac{e^{−x}}{x}dx`
   (Gompertz split). Build Beukers-type double integrals
   `I_n = ∫∫ R_n(x,y)\,e^{−(x+y)}\,…` with `R_n` chosen (Rodrigues/Laguerre shifted) so that
   `I_n = a_n γ_E + b_n + (𝓡\text{-combination})` with `a_n,b_n` rational and controlled denominators
   `d_n = \mathrm{lcm}(1,…,n)` (the prime-built denominator — where the `σ_p` enter explicitly).
2. **Saddle/asymptotics.** Bound `|I_n|` (small) and `|a_n|,|b_n|` (large) to get an irrationality-measure /
   linear-independence inequality. The Laguerre/Gompertz pairing is the known obstacle: `γ_E` couples to the
   **Gompertz constant** `δ = ∫_0^∞ e^{−x}/(1+x)dx` (recalled: the Aptekarev–Rivoal program proves a joint
   `trdeg ≥ 1` for `(γ_E, δ)` — *flagged to verify against sources, not banked*). The native upgrade we want
   is `γ_E` against the **whole** regular base `𝓡`, using the `\mathrm{lcm}(1,…,n)` denominators as the
   prime/`σ_p` channel.
3. **The decisive test.** Does the prime-built denominator `d_n=\mathrm{lcm}(1,…,n)` (PNT: `\log d_n \sim n`)
   beat the integral's decay enough to force `γ_E ∉ ℚ`? This is the same `P_S = p_N`/PNT mechanism as the
   zero-estimate uniformity (#14) — the `σ_p` simultaneity entering as the denominator. **This is the genuine
   computation/估 to push**, and the cleanest place a native (multi-`q`) input could beat the classical
   single-construction barrier.

## Door / grade
- **§1–§2: PROVEN, BRIDGE** (classical identities + van der Put–Singer; the difference-transcendence of `ψ`).
- **§3: the exact wall** (function→value F₁-lift = #142), honest, not handed off — it says *which* tool is missing.
- **§4: CONJECTURE, the native bet** (multi-`q` substitution supplies the value-lift) — the C5-grade target.
- **§5: the concrete arithmetic attack** (Beukers/Aptekarev approximations with `lcm` denominators) — the
  doable hard work, the exponential-column analog of Apéry.
- **Apex grade: FIELDS MEDAL**, open. Nothing here claims `γ_E ∉ ℚ`; §§1–2 are proven, §§4–5 are the attack.

## Gates
- [x] 0 → 1: conjecture stated; native localization on `∂_s` proven (§1); difference-Galois `𝔾_a` proven
  (§2, Lemma 2.1); the wall named as the #142 value-lift (§3); native bet (§4) and arithmetic route (§5) posed.
- [ ] 1 → 2: **either** prove a genuine value result (an irrationality/linear-independence measure for `γ_E`
  over a piece of `𝓡` via §5) **or** prove the native bet §4 (multi-`q` supplies the lift). Each is real
  Fields-Medal-grade progress; partial measures (e.g. `γ_E ∉ ℚ(\log p\text{'s, finite set})`) count.
- [ ] 2 → 3: formalize whatever value bound is achieved.
- [ ] 3 → 4: "the exponential column of DSS: `γ_E` over the regular periods."

## Cross-references
- `bigraded-corank-dss-cross.md` §G/§H — this ticket IS their apex (the second DSS-cross conjunct).
- `corank-seam-invariant.md` — the regular-column apex (Schanuel-for-prime-logs) is the sibling conjunct.
- `multi-q-abp-criterion.md` (#142) — the function→value F₁-lift named in §3.
- `regularization-freshness.md` (#75, DeWitt) — `γ_n` = seam defect; coordinate (his freshness = this apex).
- `baker-for-stieltjes.md` / `g2-dss-lower-bound.md` — the analytic DSS lower-bound lane; §5 is the
  exponential-column construction feeding it.

## Log
- 2026-06-19 (Wheeler) — created in 1-in-progress as the **Fields-Medal apex** of the corank program (user
  directive: stop banking shells, do the apex). **Proven (§1–§2):** `γ_E = −ψ(1)` sits on the Source-A
  generator `ψ=∂_s\logΓ`; the digamma Taylor at 1 splits the period/non-period seam as `(k=0\mid k≥1)`
  (`−γ_E` vs `{ζ(k+1)}`); `ψ(s+1)−ψ(s)=1/s` with `1/s` non-summable (Lemma 2.1) ⟹ `ψ` transcendental over
  `ℂ(s)` (non-rational `𝔾_a`-primitive, NOT hypertranscendental — it solves the linear `σψ−ψ=1/s`); `γ_E`
  is the `𝔾_a`-period. **Wall named (§3):** the function→value lift = the missing `F₁`
  (#142), same as the regular DSS — not handed off, precisely located. **Native bet (§4):** multi-`q` `σ_p`
  on the harmonic obstruction supplies the lift (C5-grade). **Attack (§5):** Beukers/Aptekarev approximations
  to `γ_E` with `lcm(1,…,n)` (prime/`σ_p`) denominators — the exponential analog of Apéry's `ζ(3)`, the
  concrete hard work to push next.
</content>

## §5★ Executed — the Laguerre γ-blindness obstruction, and the precise multi-`q` break `[§5.1 PROVEN; §5.2 sharp native route]`

Doing §5, not sketching it. The first concrete output is a rigorous theorem that **explains the wall** and
pins exactly what a winning construction must do.

### §5.1 The γ-blindness lemma `[PROVEN]`
Use the moment `∫_0^∞ x^k e^{−x}\log x\,dx = Γ'(k+1) = k!\,ψ(k+1) = k!(H_k − γ_E)` (`H_0=0`, `ψ(1)=−γ_E`),
and the Laguerre polynomial `L_n(x)=Σ_{k=0}^n \binom{n}{k}\frac{(−x)^k}{k!}` (`L_n(0)=1`).

> **Lemma 5.1.** For every `n ≥ 1`, `∫_0^∞ L_n(x)\,e^{−x}\log x\,dx = −\dfrac1n ∈ ℚ.`

*Proof.* `∫_0^∞ L_n e^{−x}\log x = Σ_{k=0}^n \binom{n}{k}\frac{(−1)^k}{k!}·k!(H_k−γ_E)
= −γ_E\,Σ_{k=0}^n\binom{n}{k}(−1)^k + Σ_{k=0}^n\binom{n}{k}(−1)^k H_k.`
The first sum is `(1−1)^n = 0` for `n≥1`, so `γ_E` cancels identically. The second is the classical
`Σ_{k=1}^n(−1)^k\binom{n}{k}H_k = −1/n` (check `n=1:−1`; `n=2:−2+\tfrac32=−\tfrac12`; in general from
`Σ(−1)^k\binom{n}{k}H_k = −Σ_{k=1}^n \frac1k\binom{n}{k}(−1)^{k-1}\!\cdots = −\tfrac1n` via Abel summation on
`H_k−H_{k−1}=1/k` and `Σ_{k≥j}(−1)^k\binom{n}{k} = (−1)^j\binom{n−1}{j−1}`). ∎

**Reading (the obstruction, precisely located).** The natural orthogonal/Padé construction against the
`γ_E`-integral is **γ-blind**: the `γ_E`-coefficient is `Σ_k c_k` with `c_k=\binom{n}{k}(−1)^k`, and Laguerre
orthogonality forces `Σ_k c_k = (1−1)^n = 0`. This is the rigorous reason `γ_E` resists an Apéry-style proof:
the very orthogonality that makes the remainder small **also kills `γ_E`**. The Diophantine tension is exact:
> small remainder ⟸ near-orthogonality (`Σ_k c_k ≈ 0`)   vs   `γ_E` retained ⟸ `Σ_k c_k ≠ 0`.
A single flat-measure construction cannot have both. (This is also why the SOTA reaches only the *joint*
`γ_E`–Gompertz `δ` results: the second integral `δ=∫_0^∞\frac{e^{−x}}{1+x}dx` is what survives the
orthogonality, coupling in.)

### §5.2 The multi-`q` break — decouple "small" from "γ-blind" `[the sharp native route]`
Lemma 5.1 turns the native bet (§4) into a precise demand. The two requirements collide **only for a single
flat measure**. The field's apparatus offers a way out: choose the coefficients orthogonal w.r.t. the
**prime-weighted (multi-`q`) measure** — small remainder *in the multi-`q` norm* — while keeping `Σ_k c_k ≠ 0`
w.r.t. the flat measure, so `γ_E` is retained. Concretely:
- **Friable / prime-scaled construction (ties to #103, DeWitt).** Replace the single flat `e^{−x}` measure by
  the prime/friable structure. **Caveat (self-correction):** the friable `ζ_S(s)=∏_{p∈S}(1−p^{−s})^{−1}` has
  **no** pole at `s=1` (the pole needs infinitely many primes), so there is **no** friable Stieltjes constant
  `γ_E^{(S)}→γ_E` — that earlier phrasing was wrong. The correct coupling is the **#124 pairing**
  `H=F·(s−1)ζ` (`F` a friable log-`p` polynomial): it produces ℚ-linear forms in `{γ_n}` with
  `ℚ({\log p})`-coefficients (jointly, by no-isolation #124), a *multi-variable* Hermite–Padé whose
  orthogonality is prime-weighted — **not** the flat one that zeroes `Σ_k c_k`. The self-contained
  bottom-rung version (no friable machinery needed) is the exact integral criterion in **§6**.
- **The prime denominator is the channel.** The harmonic obstruction `H_m` has denominator `\mathrm{lcm}(1..m)
  = ∏_{p≤m}p^{⌊\log_p m⌋}` (PNT: `\log\mathrm{lcm}(1..m)∼m`). This `∏_p`-built denominator is precisely the
  `σ_p`-simultaneity entering the arithmetic — the value-lift channel (§4) the single construction lacks.
> **Sharpened native bet (the §1→2 target).** A multi-`q` (friable) Hermite–Padé form
> `Λ_n = a_n γ_E + (𝓡\text{-part}) + r_n` with `a_n∈ℤ`, `Σ`(flat) `≠0` (so `a_n≠0`, γ retained) yet `|r_n|`
> small in the prime-weighted measure and `\mathrm{lcm}`-denominator `d_n` with `d_n|r_n|→0` would give
> `γ_E ∉ \overline{𝓡}`. The whole game is: **prime-weighted orthogonality is not flat-orthogonality**, so it
> need not be γ-blind — this is the exact point where the multi-`q` substitution can beat the classical wall.

### §5.3 Honest status
§5.1 is a proven theorem (the γ-blindness obstruction, with the exact `Σc_k` criterion). §5.2 is a concrete,
non-hand-wavy attack: it says precisely what must be engineered (prime-weighted orthogonality with `Σ`(flat)`≠0`)
and where (the friable #103 auxiliary, `\mathrm{lcm}` denominators). No irrationality measure is claimed yet;
the next executable step is to write the 2-prime friable Hermite–Padé form and test whether `Σ`(flat)`≠0`
survives prime-weighted near-orthogonality (the smallest decisive computation, finite-base by G1).

## Log (cont.)
- 2026-06-19 (Wheeler) — **executed §5 (partial), real content.** §5.1 **Lemma 5.1 (PROVEN):**
  `∫_0^∞ L_n(x)e^{−x}\log x\,dx = −1/n`, so the flat-measure orthogonal construction is **γ-blind**
  (`γ_E`-coeff `= Σ_k c_k = (1−1)^n = 0`); the exact Diophantine tension is small-remainder (`Σc_k≈0`) vs
  γ-retained (`Σc_k≠0`) — the rigorous reason `γ_E` resists Apéry and SOTA reaches only joint γ–δ. §5.2 the
  **multi-`q` break**: prime-weighted (friable, #103) orthogonality is not flat-orthogonality, so it need not
  be γ-blind; the `\mathrm{lcm}(1..n)` (=∏_p) denominator is the `σ_p` value-lift channel. Sharpened the §4
  native bet into a concrete `Σ`(flat)`≠0`-under-prime-orthogonality target; next step = the 2-prime friable
  Hermite–Padé form (finite-base, G1-computable). No runpod yet (algebra by hand); the 2-prime test may want one.

## §6 The exact γ_E-retention criterion and the concentration mechanism `[PROVEN refinement; sharpens §5.1]`

Lemma 5.1 used one Laguerre family. The criterion behind it is exact and basis-free — and it turns the
attack into a fully explicit construction problem.

> **Proposition 6.1 (γ-coefficient = the constant moment).** For any polynomial `P(x)=Σ_k a_k x^k`, write
> `I[P] := ∫_0^∞ P(x)\,e^{−x}\log x\,dx`. Then
> `I[P] = −γ_E·\Big(∫_0^∞ P(x)e^{−x}dx\Big) + Σ_k a_k\,k!\,H_k`,
> so the **`γ_E`-coefficient of `I[P]` is exactly `−∫_0^∞ P(x)e^{−x}dx = −Σ_k a_k k!`**.

*Proof.* `∫_0^∞ x^k e^{−x}\log x\,dx = k!(H_k−γ_E)`; sum against `a_k`; `Σ_k a_k k! = ∫_0^∞ P e^{−x}`. ∎

**Corollary 6.2 (exact retention dichotomy).** `I[P]` retains `γ_E` `⟺` `∫_0^∞ P e^{−x} ≠ 0` `⟺` `P` is **not
`e^{−x}`-orthogonal to the constant `1`**. Laguerre `L_n` (`n≥1`) is `e^{−x}`-orthogonal to `1`, so it is
γ-blind (Lemma 5.1, reproven exactly and basis-free).

**The construction problem, made fully explicit.** Seek integer polynomials `P_n` (`\deg = n`) with
- `A_n := ∫_0^∞ P_n e^{−x}dx ∈ ℤ\setminus\{0\}` — the `γ_E`-coefficient (the "`q_n`"),
- `B_n := Σ_k a_k k! H_k ∈ \tfrac1{\mathrm{lcm}(1..n)}ℤ` — rational, prime-built denominator,
- `I[P_n] = −A_n γ_E + B_n` **small**.
Then `|A_n γ_E − B_n| = |I[P_n]|`, and `\mathrm{lcm}(1..n)·|I[P_n]| → 0` with `I[P_n]≠0` would force
`γ_E ∉ ℚ` (and refined weights would push toward `γ_E ∉ \overline{𝓡}`).

**The geometric mechanism (why this is not hopeless and where it bites).** `\log x` vanishes at `x=1`
and is `O(1)` elsewhere, so `I[P_n]` small **with** `A_n≠0` forces the mass of `P_n e^{−x}` to **concentrate
at `x=1`**: expanding `\log x = (x−1) − \tfrac12(x−1)^2 + \cdots`,
`I[P_n] = ∫P_n e^{−x}[(x−1)−\tfrac12(x−1)^2+\cdots] = A_n·\big(\langle x−1\rangle − \tfrac12\langle(x−1)^2\rangle+\cdots\big)`,
where `\langle\cdot\rangle` is the `P_n e^{−x}/A_n` average. So the right family is **shifted/Jacobi-type
polynomials peaked at `x=1`** (orthogonal to low moments *about `x=1`*), NOT the origin-orthogonal Laguerre
(which over-kills, zeroing `A_n` itself). This is the precise, executable construction: make `P_n` kill the
moments `\langle(x−1)^j\rangle` for `1≤j<n` (analytic budget: `|I[P_n]|` small) while `A_n = ∫P_n e^{−x}≠0`
(γ retained). The arithmetic budget is `\mathrm{lcm}(1..n)` (`\log∼n`, PNT); the analytic budget is the
saddle at `x=1`. **The apex is exactly whether the analytic decay beats the prime denominator.**

**Honest status.** Prop 6.1 / Cor 6.2 are proven (exact, basis-free). The concentration mechanism is a
rigorous reduction to an explicit, finite-to-write construction (shifted polynomials peaked at `x=1`). No
measure is claimed to beat the bound — that is the apex. But the attack is now a concrete inequality between
two explicit budgets, not a sketch; and Cor 6.2 says precisely which constructions are even in the running
(`∫Pe^{−x}≠0`). Next executable: write `P_n(x)=` the degree-`n` polynomial orthogonal to `(x−1)^j` (`1≤j<n`)
under `e^{−x}` with `∫P_n e^{−x}=1`, compute `A_n,B_n,|I[P_n]|` for small `n` (by hand to `n=3`, then a
bounded runpod script), and read off whether `\mathrm{lcm}(1..n)|I[P_n]|→0`.

## Log (cont.)
- 2026-06-19 (Wheeler) — **self-corrected §5.2** (friable `ζ_S` has no `s=1` pole ⟹ no `γ_E^{(S)}`; the
  friable coupling is the #124 `F·(s−1)ζ` pairing, joint forms in `{γ_n}∪{\log p}`). **§6 added (PROVEN):**
  Prop 6.1 — the `γ_E`-coefficient of `∫P e^{−x}\log x` is exactly `−∫P e^{−x}`; Cor 6.2 — retain `γ_E` iff
  `P` not `e^{−x}`-orthogonal to `1`. The concentration mechanism reduces the apex to an explicit construction
  (shifted polynomials peaked at `x=1`, killing moments about `1` while `∫Pe^{−x}≠0`) and an explicit budget
  inequality `\mathrm{lcm}(1..n)|I[P_n]| \to 0?`. Next: compute small-`n` cases.

## §7 Executed — derangement moments, the explicit low-order forms, honest budget check `[PROVEN computation]`

Doing §6's "compute small `n`," not deferring it.

**Lemma 7.1 (the central moments are derangements).** `M_j := ∫_0^∞ (x-1)^j e^{-x}dx = \,!j` (subfactorial):
`M_0,M_1,M_2,M_3,M_4,M_5,M_6 = 1,0,1,2,9,44,265`.
*Proof.* `M_j = Σ_{i}\binom{j}{i}(-1)^{j-i}∫x^i e^{-x} = Σ_i\binom{j}{i}(-1)^{j-i}i! = \,!j` (the standard integral
representation of derangement numbers). ∎ — a clean native fact: the `x=1`-centered construction for `γ_E`
runs on the derangement combinatorics of the `e^{-x}` measure.

**The `n=2` form (explicit).** Require `∫P_2 e^{-x}=1` (γ retained, Cor 6.2) and kill `M_1,M_2`-moments
about `1`: `P_2(x) = -¼(x-1)^2 + ½(x-1) + 5/4 = -¼x^2 + x + ½`. Then with `∫x^k e^{-x}\log x = k!(H_k-γ_E)`:
> `I[P_2] = ∫_0^∞ P_2 e^{-x}\log x\,dx = -¼(3-2γ_E) + (1-γ_E) + ½(-γ_E) = ¼ - γ_E`.
So `γ_E = ¼ - I[P_2]`, denominator `4 = \mathrm{lcm}(1,2)·2`... i.e. the rational part lies in `\tfrac14ℤ`.
**But the error `|I[P_2]| = |¼-γ_E| ≈ 0.327` is `O(1)`** — no irrationality.

**Why low order is `O(1)` (honest reading).** Killing finitely many central moments does **not** concentrate
`P_n e^{-x}` at `x=1`: a fixed-degree polynomial times `e^{-x}` keeps `O(1)` mass on `x>2`, where the
`(x-1)`-expansion of `\log x` (radius 1) diverges and contributes `O(1)`. Genuine concentration — hence small
`|I[P_n]|` — is an `n→∞` phenomenon, where `P_n` must oscillate to suppress mass off `x=1`. The rational part
`B_n = Σ a_k k! H_k` then carries denominator `\mathrm{lcm}(1..n)` (`\log∼n`, PNT). So:
> **The apex is exactly the large-`n` competition** `\mathrm{lcm}(1..n)·|I[P_n]| → 0?` — and the low-order
> data confirms there is no shortcut below the asymptotic regime (`n=2` gives error `0.327`, not `o(1)`).

**Honest status.** Lemma 7.1 and the `n=2` form are proven exact computations. They **confirm the wall is the
large-`n` saddle-vs-`lcm` inequality** (not a low-order miracle), and pin the construction's combinatorics
(derangements). No irrationality is obtained — consistent with the apex being open and with the SOTA reaching
only joint `γ_E`–Gompertz results. Next executable: the large-`n` asymptotic of `|I[P_n]|` for the
moment-killing family (saddle point at `x=1`), to decide the budget inequality — the genuine remaining
analysis (bounded runpod script for the numerics of `\mathrm{lcm}(1..n)|I[P_n]|` across `n`).

## Log (cont.)
- 2026-06-19 (Wheeler) — **executed §6's computation (§7, PROVEN).** Lemma 7.1: central moments
  `∫(x-1)^j e^{-x} = \,!j` (derangements `1,0,1,2,9,44,265`). Explicit `n=2` form `P_2=-¼x^2+x+½` gives
  `I[P_2]=¼-γ_E`, error `O(1)` (`≈0.327`) — **no low-order irrationality**, confirming the difficulty is the
  `n→∞` concentration (saddle at `x=1`) vs the `\mathrm{lcm}(1..n)` denominator. Honest frontier result: the
  wall is the large-`n` budget inequality, no shortcut below it. §G now machine-checked by Leaner
  (`3-formalized/bigraded-corank-tower-factorization.md`). Next: large-`n` saddle asymptotic of `|I[P_n]|`.

## §8 Executed — the single-integral construction FAILS (exact numerics); the 2-function object is forced `[NEGATIVE RESULT, data]`

Doing the large-`n` test, not asserting it. Exact computation (`computations/gamma_pade_decay/`, mpmath dps=80,
Fraction-exact `c_i`): the fully-determined `x=1`-centered family `P_n=Σ_{i≤n}c_i(x-1)^i` with
`∫P_n(x-1)^j e^{-x}=[j{=}0]` (`j=0..n`), giving `B_n=∫P_n e^{-x}(\log x+γ_E)∈ℚ` and the irrationality test
`den(B_n)·|B_n-γ_E|→0?`.

**Data (`n=1..22`):**
| n | `err=|B_n-γ_E|` | `den(B_n)` | `den·err` |
|--:|--:|--:|--:|
| 2 | 0.327 | 4 | 1.31 |
| 4 | 0.051 | 288 | 14.8 |
| 8 | 0.174 | 3.4e7 | 5.9e6 |
| 12 | 0.013 | 2.2e12 | 2.8e10 |
| 16 | 0.091 | 5.0e18 | 4.6e17 |
| 22 | 0.063 | 6.7e25 | 4.3e24 |

**Two clean negative facts.**
1. **No convergence.** `err=|B_n-γ_E|` does **not** →0 — it oscillates in `[0.01,0.19]`, never approaching 0.
   `B_n ↛ γ_E`. So this is not even a valid approximation, let alone an irrationality proof.
2. **Denominator explosion.** `den(B_n)` grows super-exponentially (`~10^{26}` by `n=22`), so
   `den·err → ∞` (`~4×10^{24}`) — the criterion fails catastrophically, irrespective of (1).

**Structural reason (why, not just that).** A single polynomial times `e^{-x}` cannot make
`∫P_n e^{-x}\log x` small while keeping `∫P_n e^{-x}=1`: the mass on `x>2`, where `\log x` is `O(1)` and the
degree-`n` polynomial grows, is uncontrolled — killing central moments about `1` only tames the convergent
`(0,2)` part. Concentration at `x=1` is unreachable by one polynomial weight. So the entire **single-integral
route (my §5–§7) is ruled out as a standalone.**

**The redirect (forced object).** Genuine decay needs a **second decaying exponential** — the 2-function
Hermite–Padé / double integral `∫∫ R_n(x,y)e^{-x-y}…`, whose remainder *does* decay geometrically. But that
construction's second linear form involves the **Gompertz constant** `δ=∫_0^∞ e^{-x}/(1+x)dx` (also a
`𝔾_a`/exponential period). **Conclusion (sharpened, consistent with SOTA):** the `γ_E`–`δ` coupling is
**forced**, not incidental — the exponential column's bottom rung is intrinsically the rank-2 pair `(γ_E,δ)`,
matching the joint-only results (one of `γ_E,δ` transcendental). The single-`𝔾_a` picture of §2 is too small;
the right object is the **rank-2 unipotent (γ_E,δ)-system**.

**The native question, now sharp.** Classically the 2-function construction cannot separate `γ_E` from `δ`
(joint results only). The field-specific bet (§4): can the **σ_p-simultaneity decouple `γ_E` from `δ`** — i.e.
does the multi-`q` (friable, prime-weighted) Hermite–Padé break the `(γ_E,δ)` degeneracy that the single
flat construction cannot? **This is the precise, native, still-open crux** — and it is genuinely a question
no parent states (parents only have the coupled pair).

**Honest status.** §8 is a proven negative result (exact data + structural reason): the single-integral
route is dead; the forced object is the rank-2 `(γ_E,δ)` Hermite–Padé. The apex is open; the native crux is
now sharp (σ_p-decoupling of `(γ_E,δ)`). Next: build the rank-2 `(γ_E,δ)` difference/connection object and
test whether the prime-weighted (friable) construction decouples it.

## Log (cont.)
- 2026-06-19 (Wheeler) — **§8: executed the large-`n` test; NEGATIVE result that redirects.** Exact numerics
  (`computations/gamma_pade_decay/`): the single-integral `x=1`-centered family does **not** converge
  (`|B_n-γ_E|` stalls in `[0.01,0.19]`) and its denominators explode (`den·err→∞`, `~4e24` at `n=22`). Ruled
  out, with the structural reason (single `e^{-x}` tail on `x>2` uncontrolled). The forced object is the
  **rank-2 `(γ_E,δ_Gompertz)` Hermite–Padé** (second decaying exponential), so the `γ_E`–`δ` coupling is
  **forced** (matches SOTA joint-only). Sharpened native crux: **does σ_p-simultaneity decouple `(γ_E,δ)`?**
  — a question no parent states. Next: build the rank-2 `(γ_E,δ)` object and test prime-weighted decoupling.

## §9 Convergence + consolidation — the wild kernel is bi-unipotent (σ ∧ ∂_s); the Padé route is dead `[reconciliation]`

The team converged on this apex from three sides; this section pins what is shared, what is mine, and the
one methodological conclusion §8 forces.

**Convergence (read DeWitt `exponential-period-dss-cross`, Professor `stieltjes-exponential-period-realization`).**
- Professor **constructed the floor**: `γ_n ∈ 𝒫^exp`, wild generators `J_m = ∂_s^m Σ_k Γ(s,k)|_{s=1}`, `γ_E=J_1`.
- DeWitt **proved the no-go and built the kernel**: `1→K→G^exp↠G_mot→1`; `K_Λ` pro-unipotent via the
  **∂_s-derivative tower**; `corank^{exp}_n = dim\,gr^n_W K_Λ` is exactly my bigraded `U≥1` column; the
  relativization over `ℚ({log p})` is **automatic** (`K=ker` acts trivially on `G_mot`-data) — so my §3/§4
  structural framing and my id=226 "relative apex" are **subsumed** by his `K`-formulation. The open apex is
  identical from all sides: **independence of the wild tower `{J_n}` over `ℚ({log p})` = the missing exp-`F₁`.**

**My distinct contribution, repositioned — the DIFFERENCE (σ) presentation of the same kernel.** DeWitt's
tower is *differential* (`∂_s`, Gauss–Manin/Stokes). §1–§2 give the *difference* presentation of the same
wild generator:
> `ψ=∂_s\logΓ` satisfies **both** the σ-recurrence `σψ−ψ=1/s` (§2, non-summable ⟹ `𝔾_a`) **and** the
> ∂_s-tower (`ψ^{(m)}(1)=(−1)^{m+1}m!ζ(m+1)` for `m≥1`; `ψ(1)=−γ_E`, §1a). The two generators **commute**:
> `∂_s(σf)=f'(s+1)=σ(∂_s f)`, i.e. `[∂_s,σ]=0` (consistent with #132/#136). So `K_Λ` is **bi-unipotent**:
> one pro-unipotent tower acted on compatibly by the difference `σ` and the differential `∂_s` — the field's
> native `(σ_p,∂_s)` weld, realized on the wild kernel. `γ_E` is the **common base generator** (the `m=0`
> rung of the ∂_s-tower = the non-summability constant of the σ-recurrence).

This is the genuinely native sharpening: the wild kernel is not just a `∂_s`-tower (a parent: exponential
motives / Stokes) but a `(σ,∂_s)`-**bi**-unipotent tower — and the missing `F₁` is the obstruction to it
being motivic **from both generators at once** (which is why neither a pure difference-Galois argument, §2,
nor a pure differential one reaches it alone: each gives the *function*-level `𝔾_a`, neither gives the
*value*-lift; #142).

**The methodological payload of §8 (the dead route — a genuine save).** My §8 proved, by exact numerics, that
the **single-integral Padé/approximation construction is dead** for `γ_E` (no convergence + denominator
explosion; the second exponential forces the `(γ_E,δ)` rank-2 coupling). Consequence for the *whole team's*
apex: **the independence of `{J_n}` over `ℚ({log p})` should NOT be attacked by a classical Apéry/Padé
construction** — that route provably stalls. It must be attacked through the **Galois/Stokes structure of
`K_Λ`** (DeWitt's §7 falsifiable Stokes-graded computation: show `gr^n_W K_Λ ≠ 0`), i.e. via the
**non-collapse of the bi-unipotent tower**, not via Diophantine approximation of the values directly. §8 is
the negative experiment that redirects the effort to the structural (Galois) attack.

**Net (my lane's honest position).** Structural framing → DeWitt's `K` (subsumes my §3/§4). Floor →
Professor's `J_m`. My live, non-duplicated deliverables: (a) the **bi-unipotent (σ∧∂_s) presentation** of
`K_Λ` with `γ_E` as common base generator (above); (b) the **Padé-route no-go** (§8) redirecting the apex
attack to the Stokes/Galois non-collapse. The apex itself (tower non-collapse = exp-`F₁`) stays FIELDS MEDAL,
and is now a single shared target with a sharpened method (Stokes, not Padé).

## Log (cont.)
- 2026-06-19 (Wheeler) — **§9 consolidation after reading DeWitt `exponential-period-dss-cross` + Professor
  `stieltjes-exponential-period-realization`.** Their `K`-kernel / `J_m`-floor subsume my §3/§4 framing and my
  id=226 relativization (automatic, `K=ker`). My non-duplicated content: (a) the **difference (σ) presentation**
  — `γ_E` is the `𝔾_a`-period of `σψ−ψ=1/s`, commuting with DeWitt's `∂_s`-tower (`[∂_s,σ]=0`), so `K_Λ` is
  a `(σ,∂_s)`-**bi-unipotent** tower with `γ_E` the common base generator (native weld on the wild kernel);
  (b) **§8's Padé no-go redirects** the shared apex attack from classical Apéry/Padé (dead) to the
  Galois/Stokes non-collapse of `K_Λ` (DeWitt §7). Apex unchanged (FIELDS MEDAL): tower non-collapse over
  `ℚ({log p})` = exp-`F₁`.

## §10 The function level is Hölder-maximal — the apex is PURELY the value-lift `[NOT NEW — re-derives DeWitt's parametrized-differential-abp-escape; difference-side restatement only]`

> **PRIOR-WORK CORRECTION (2026-06-19, after the "check prior research" reminder).** The core of this section
> is **already proven** in DeWitt's `../2-fully-proven/parametrized-differential-abp-escape.md`: the
> parametrized-`(σ,∂)` "`G_L` big" term is the **full `G_m^∂` of the non-CC archimedean place = the digamma
> residue = Hölder** (via CC = Hardouin–Singer coboundary criterion, #130/#134), prime side CC-trivial, apex =
> value-lift `F₁`. So **§10 is NOT a new result** — at most the *difference-side* (σ-shift, van der Put–Singer
> additive) restatement of DeWitt's differential (`∂_s`, `G_m^∂`) computation, same Hölder conclusion. Credit:
> DeWitt (carrier), Wheeler `multi-q-abp-criterion` §4 (group/value-lift decomposition). The genuinely-new
> content of *this* ticket is §6 (the exact γ-retention criterion) and **§8 (the Padé-route no-go)**, not §10.
> Kept below only for the difference-side presentation.

§9 raised: is there a *function-level* route to the tower non-collapse? The answer is **no**, and it was
already settled (DeWitt, above). The difference-side computation, for the record:

**Proposition 10.1 (function level = Hölder-maximal).** The parametrized `(σ,∂)`-difference-Galois group of
the digamma `ψ` (the σ-primitive of `1/s`: `σψ−ψ=1/s`) over `(ℂ(s),σ,∂)` is the **full** differential
additive group `∂-𝔾_a` — `ψ` is `∂`-transcendental over the difference field. Equivalently, **Γ is
hypertranscendental (Hölder 1887).**

*Proof.* By Hardouin–Singer, the parametrized `(σ,∂)`-Galois of a σ-primitive of `g` is a **proper** `∂`-subgroup
of `𝔾_a` iff some nonzero linear differential operator makes `L(∂)g` σ-summable in `ℂ(s)`. Here `g=1/s`, and
`L(∂)(1/s)=Σ_m c_m(−1)^m m!/s^{m+1}` is a rational function with poles **only at `s=0`**. A rational `f` with a
pole at `0` is σ-summable (`f=σh−h`, `h∈ℂ(s)`) only if `h` carries poles along the entire backward orbit
`{0,−1,−2,…}` — impossible for a rational `h`. So **no** nonzero `L(∂)(1/s)` is σ-summable, hence the group is
the full `∂-𝔾_a`. This is exactly the Hardouin–Singer recovery of Hölder's hypertranscendence of `Γ`. ∎

**Consequence — the apex localized, definitively.** The function-level Galois group is **maximal** (`∂-𝔾_a`,
Hölder): nothing remains to extract at the function level — the wild tower `{ψ^{(m)}}` is fully
`∂`-transcendental *as functions*. **Yet** the value-independence of
`{ψ^{(m)}(1)} = {−γ_E, ζ(2), −2ζ(3), …}` over `ℚ({\log p})` is **not** implied — it is the separate `F₁`
value-lift (#142). Therefore:
> **The `γ_E`/Stieltjes apex is PURELY a value-lift problem.** The function side is Hölder-maximal (proven,
> exhausted); **no** function-level argument — difference-Galois (§2), differential-Galois/Stokes at the
> function level, or §8 Padé-construction — can supply the independence. The entire remaining content is the
> specialization `F₁` (value-lift) = DeWitt's tower non-collapse = the missing single Frobenius.

**The Hölder anchor (the conceptual payload).** The founding theorem of the field — Γ hypertranscendental —
**is exactly the function-side of the `γ_E` apex** (Prop 10.1). The value-side (DSS-cross) is the orthogonal,
still-open `F₁`. So `function/value = Hölder/DSS = the (A)/(B) split` (#125 §E), now **proven at the digamma**:
(A) obstruction/function-level = Hölder (maximal, done), (B) value-relations = DSS (the apex). This is why the
γ_E apex is the cleanest incarnation of the whole field's structure: its function side is literally Hölder.

**Grade.** Prop 10.1 is BRIDGE (Hardouin–Singer = a parent, the standard recovery of Hölder). The payload is
the **definitive closure of the function-level attack** (§8 Padé no-go + §10 Hölder-maximality together
exhaust the function side) and the anchoring of the apex to the founding theorem. Apex (value-lift / tower
non-collapse) stays FIELDS MEDAL, open — but now provably the *only* remaining content.

## Log (cont.)
- 2026-06-19 (Wheeler) — **§10: closed the function-level attack; anchored the apex to Hölder.** Prop 10.1
  (Hardouin–Singer): the parametrized `(σ,∂)`-Galois of the digamma `ψ` (σ-primitive of `1/s`) is the full
  `∂-𝔾_a` — `ψ` `∂`-transcendental ⟺ Γ hypertranscendental (Hölder), via `1/s` having a single pole-orbit so
  no `L(∂)(1/s)` is σ-summable. So the function level is **maximal/exhausted**; combined with §8 (Padé dead)
  and §2 (difference-`𝔾_a`), **no function-level route reaches the independence** — the apex is **purely** the
  `F₁` value-lift. Conceptual anchor: function/value = Hölder/DSS = (A)/(B) split (#125 §E), proven at the
  digamma. The γ_E apex's function side IS the founding theorem. BRIDGE computation; FIELDS-MEDAL apex
  unchanged but now the sole remaining content.

## Log (cont.)
- 2026-06-19 (Wheeler) — **prior-research check (user reminder) caught a duplication: §10 corrected.** Grepping
  the tree for Hardouin–Singer/digamma/Hölder found DeWitt's `../2-fully-proven/parametrized-differential-abp-escape.md`
  already proves §10's core (non-CC digamma residue = full `G_m^∂` = Hölder, via CC=HS; apex = value-lift `F₁`).
  Downgraded §10 from "PROVEN new" to "NOT NEW — difference-side restatement," credited DeWitt + Wheeler §4.
  **Genuinely-new content of this ticket reaffirmed: §6 (exact γ-retention criterion) and §8 (Padé-route
  no-go, exact numerics) — those are not in DeWitt's cards; the structural spine (digamma=Hölder, K-kernel,
  bi-unipotent) is shared/DeWitt's.** Lesson logged: check prior research BEFORE writing structural sections,
  not after.

## §11 A concrete candidate for the missing F₁ — the p-adic crystalline Frobenii `{Frob_p}` = the σ_p simultaneity `[CONJECTURE — new attack-candidate, prior-research-checked: absent from tree]`

The team's apex is "the missing single Frobenius `F₁`" (DeWitt's `K`-kernel value-lift), left **abstract**
("an `M^exp` Frobenius that does not exist over ℚ"). This section poses a **concrete** candidate in the
field's own σ_p vocabulary, with explicit objects, distinct from the dead routes (§8 Padé, §10 function-Galois).

**The observation.** A single *global* Frobenius does not exist over ℚ (corank ∞, #125/#121). But the
**p-adic crystalline Frobenius exists for each prime `p` separately**, and the wild Source-A generator `γ_E`
has explicit p-adic avatars:
- **Morita's p-adic Gamma `Γ_p`** (1975): the continuous p-adic interpolation of `(−1)^n n!`, with the
  p-adic recurrence `Γ_p(s+1) = −s·Γ_p(s)` for `s∈ℤ_p^×` (`= −Γ_p(s)` for `|s|_p<1`) — the **p-adic analog
  of the field's Source-A recurrence `Γ(s+1)=sΓ(s)`** (§1b).
- **Diamond's p-adic log-Gamma** (1977) and the **p-adic Euler/Stieltjes constants** in the Laurent
  expansion of the p-adic `L`-function — the p-adic analogs of `γ_E=−ψ(1)` and the `{γ_n}`, via the p-adic
  digamma `ψ_p=(\log Γ_p)'`.

So the wild digamma `ψ` (§1–§2) has, **for each `p`, a p-adic companion `ψ_p`** with its own p-adic
difference-recurrence: the crystalline Frobenii `{Frob_p}` act, one per prime, on the p-adic realizations of
the exponential motive carrying `γ_E` (Fresán–Jossen exponential motives have p-adic / rigid-cohomology
companions with crystalline Frobenius).

**The conjecture (concretizing F₁ = the founding bet).**
> The "missing single Frobenius `F₁`" is the **synthesis (non-existent over ℚ) of the per-prime crystalline
> Frobenii `{Frob_p}`** on the p-adic realizations of `K_Λ`. The field's **founding bet** — "the simultaneity
> of `{σ_p}` substitutes for the missing single Frobenius" — is, concretely: **the `{Frob_p}` (acting on the
> p-adic `ψ_p` = Morita/Diamond) ARE the `σ_p`**, and the value-lift (complex independence of `{γ_n}` over
> `ℚ({\log p})`) holds **iff** the `{Frob_p}` are jointly generic (no global synthesis collapses them) — a
> p-adic→complex period comparison for the exponential motive.

**What this buys (vs the abstract F₁).**
1. **Explicit objects.** Morita `Γ_p`, Diamond's p-adic constants carry the wild generator p-adically — `F₁`
   is no longer abstract; it has per-prime avatars one can compute with.
2. **The founding bet, concrete.** "Many `σ_p` for the missing single Frobenius" becomes "the per-prime
   crystalline Frobenii `{Frob_p}` for the missing global synthesis" — the σ_p simultaneity given an explicit
   arithmetic carrier.
3. **A live, non-dead route.** The value-lift becomes a **p-adic period-comparison** question (Dwork / rigid
   cohomology / p-adic Hodge for exponential motives) — **different** from the dead Padé route (§8) and the
   exhausted function-Galois route (§10/Hölder). This is the first attack-candidate that survives both §8 and
   §10.

**Honest grade.** CONJECTURE. Morita `Γ_p` and Diamond's p-adic log-Γ are standard (recalled). The
crystalline Frobenius on exponential-motive realizations is framework-level (Fresán–Jossen p-adic companions;
the precise p-adic period theory for these is itself developing). The identification `{Frob_p}=σ_p` and
"`F₁` = their missing synthesis" is the **new conjecture** (my contribution), **not proven** — it proposes a
concrete native mechanism, it does **not** solve the apex. Door: native-flavored (σ_p simultaneity is the
field's core); Door-2 grade pending (p-adic Hodge is a parent — the candidate native content is the
σ_p-synthesis claim). FIELDS-MEDAL apex unchanged. **Prior research checked (grep): the p-adic /
crystalline / Morita / Diamond angle is absent from the pipeline — this is new.**

## Log (cont.)
- 2026-06-19 (Wheeler) — **§11: posed a concrete candidate for the missing F₁** (new, prior-research-checked
  absent). The single global Frobenius is missing over ℚ, but the **per-prime crystalline Frobenii `{Frob_p}`
  exist** and **are** the σ_p; the wild generator `γ_E` has explicit p-adic avatars (Morita `Γ_p`,
  `Γ_p(s+1)=−sΓ_p(s)`; Diamond p-adic log-Γ / p-adic Euler constants). Conjecture: `F₁` = the missing
  *synthesis* of `{Frob_p}`; the founding bet = "{Frob_p} simultaneity substitutes for it"; value-lift = a
  p-adic→complex period comparison. **First attack-candidate surviving both the §8 Padé no-go and the §10
  Hölder function-exhaustion** — a live, distinct route. CONJECTURE; standard p-adic objects (recalled),
  novel σ_p={Frob_p} identification. Apex unchanged (FIELDS MEDAL).

## §12 The p-adic route, concretized — the ℚ-carrier `N`, the identical `1/s` recurrence, and the Iwasawa foothold `[development of §11; defensible core + hedged conjecture]`

§11 is made concrete by one object: the rank-2 difference module of §2.

**(A) The carrier is ℚ-defined, so it has all realizations.** `N`: `σe_0 = e_0 + (1/s)e_1`, `σe_1=e_1`
(§2) has **ℚ-coefficients**. Hence `N` carries:
- a **complex** realization, period `γ_E = −ψ(1)` (§1–§2);
- for each prime `p`, a **p-adic** realization with crystalline Frobenius `Frob_p`, period the **p-adic Euler
  constant** `γ_E^{(p)} := −ψ_p(1)`.
One ℚ-object, one archimedean period, a family of p-adic periods — the explicit substrate of §11.

**(B) The difference structure is realization-independent (checkable).** Diamond's p-adic log-Gamma `G_p`
satisfies `G_p(s+1)−G_p(s) = \log_p s` (Iwasawa p-adic log), so the p-adic digamma `ψ_p=G_p'` obeys
> `ψ_p(s+1) − ψ_p(s) = 1/s`   **— the identical recurrence to the complex `ψ` (§1b).**
So `γ_E^{(p)}` is born from the **same non-summable `1/s`** (§2, Lemma 2.1) in `ℂ_p`: the `𝔾_a`-primitive
structure (§2) and the Hölder-maximal function level (§10) are **realization-independent**. The wild kernel
`K_Λ` is one ℚ-structure; its complex and p-adic periods are its different fibres. *(Recalled-standard:
Morita 1975, Diamond 1977.)*

**(C) The asymmetry that makes the p-adic route live — Gross–Koblitz rigidity.** Unlike the complex side
(`γ_E` has **no** classical foothold, §8), the p-adic side carries genuine extra rigidity:
- **Gross–Koblitz (1979):** Morita's `Γ_p` at **rational** arguments is given by **Gauss sums** — algebraic.
  So `Γ_p`-*values* are far more rigid than complex `Γ`-values. (`Frob_p` = the Gauss-sum/Gauss–Koblitz
  Frobenius made explicit.)
- **The p-adic value-lift, sharpened:** the open question is whether this value-level rigidity **propagates to
  the log-derivative** `γ_E^{(p)}` (the wild generator). I.e. **the p-adic `F₁` is whether Gross–Koblitz
  rigidity reaches `Γ_p'`/`ψ_p` (the derivative), not just `Γ_p` (the value).** This is a *concrete*,
  Iwasawa-theoretic question (Kubota–Leopoldt `ζ_p`, the p-adic regulator, Ferrero–Washington) — machinery the
  **complex side simply does not have**, which is exactly why §11 survives the §8 (Padé) and §10 (Hölder)
  dead ends.

**(D) The native synthesis bet, restated on `N`.** Over `F_q` a single Frobenius rigidifies everything
(`K=1`, value = function, #121/DeWitt §6). Over ℚ: a **single** global Frobenius is missing, but `N` has the
**family `{Frob_p}`** (Gross–Koblitz-explicit per `p`) **plus** the complex realization. The founding bet:
the value-lift (complex `γ_E ∉ \overline{𝓡}`) is controlled by the **joint genericity of `{Frob_p}` across all
`p`** — the σ_p simultaneity as the missing single Frobenius's stand-in, now on an explicit ℚ-carrier with
explicit per-prime Frobenii.

**Honest grade.** (A)(B) are defensible/checkable (Morita/Diamond/the ℚ-coefficient observation); (C)'s
Gross–Koblitz is standard; the **propagation of rigidity to the derivative** and (D)'s synthesis are
CONJECTURE (the new content). This does **not** solve the apex. It delivers: an explicit ℚ-carrier `N` with
complex + p-adic periods; the realization-independence of the §2/§10 structure; and a **live, Iwasawa-theoretic
formulation** of the value-lift that survives §8/§10. Door-2 grade pending (p-adic Hodge/Iwasawa are parents;
the σ_p={Frob_p} synthesis is the candidate native content). FIELDS-MEDAL apex unchanged.

## Log (cont.)
- 2026-06-19 (Wheeler) — **§12: concretized §11 on the ℚ-carrier `N`.** (A) `N` (§2) is ℚ-defined ⟹ one
  complex period `γ_E` + per-prime p-adic periods `γ_E^{(p)}` (Diamond), crystalline `{Frob_p}`. (B) The
  `1/s` recurrence and the `𝔾_a`/Hölder structure (§2/§10) are **realization-independent** (Diamond:
  `ψ_p(s+1)−ψ_p(s)=1/s` in `ℂ_p`). (C) **Gross–Koblitz** makes `Γ_p`-values algebraic — a rigidity the complex
  side lacks; the p-adic value-lift = whether it propagates from `Γ_p` to `ψ_p`/`γ_E^{(p)}` (an Iwasawa /
  Kubota–Leopoldt question). (D) Founding bet on `N`: value-lift ⟺ joint genericity of `{Frob_p}`. Live route
  (Iwasawa machinery, surviving §8/§10); defensible core + hedged conjecture; apex unchanged.

## §13 Rigor correction — `σ_p` (dilation) and `Frob_p` (crystalline) are DISTINCT over ℚ; `F₁` = their common absent synthesis `[self-correction of §11/§12]`

§11/§12 wrote "the `{Frob_p}` **are** the `σ_p`." That is an **overreach** (caught by reasoning, not recall):
they are **two different per-prime structures**, conflated only because they coincide over `F_q`.
- **`σ_p` = the DILATION** `x_p ↦ p^{-1}x_p` — the field's multi-`q` difference structure, geometric /
  combinatorial, on the Bohr ring `R`.
- **`Frob_p` = the CRYSTALLINE Frobenius** — arithmetic, on the p-adic realization of the wild kernel `K_Λ`.

**The kernel of truth (corrected statement).** Over `F_q` the **geometric and arithmetic Frobenius coincide**
(`Frob_q` is simultaneously the dilation `q^{-\deg}` and the arithmetic Frobenius) — a **single** operator,
everything synthesized (`K=1`, value = function, #121). Over ℚ this single operator **splits** into **two
distinct per-prime families** — the dilations `{σ_p}` **and** the crystalline `{Frob_p}` — and **neither has
a global synthesis**.

> **Corrected conjecture.** The missing single Frobenius `F₁` is the **common absent synthesis**: over `F_q`
> the dilation=Frobenius coincidence **is** `F₁`; over ℚ the **splitting** (dilations `σ_p` ⊥ crystalline
> `Frob_p`, neither synthesized) **is** the `F₁`-absence. The σ_p founding bet (dilations stand in for the
> missing single Frobenius) and the crystalline `{Frob_p}` (the arithmetic per-prime structure on the wild
> kernel) are **two shadows of one missing `F₁`**, tied by the `F_q` coincidence — **not identical over ℚ**.

**What survives §11/§12 (unaffected):** the ℚ-carrier `N` with complex + p-adic periods (§12A); the
realization-independent `1/s` recurrence (§12B); Gross–Koblitz rigidity and the Iwasawa value-lift route
(§12C) — these live entirely on the **crystalline/arithmetic** side (`Γ_p`, `Frob_p`), which is correctly
placed. **What is corrected:** only the identification `{Frob_p}=σ_p` (§11) → the two are distinct per-prime
structures coinciding only over `F_q`. The Iwasawa route (Gross–Koblitz `Γ_p→ψ_p`) is on the `Frob_p` side
and stands.

**Honest grade.** A rigor correction (no new theorem) that makes the p-adic conjecture honest and *richer*:
over ℚ the wild kernel carries **two** per-prime structures (geometric dilations, arithmetic Frobenii), whose
**mutual relation + joint non-synthesis** is the `F₁`-absence — a sharper target than the conflated version.

## Log (cont.)
- 2026-06-19 (Wheeler) — **§13: self-corrected the §11/§12 overreach `{Frob_p}=σ_p`.** By reasoning: `σ_p`
  (dilation, geometric, Bohr ring) and `Frob_p` (crystalline, arithmetic, p-adic realization) are **distinct**
  per-prime structures; they **coincide over `F_q`** (single geometric=arithmetic Frobenius) and **split over
  ℚ** (two families, neither synthesized). Corrected conjecture: `F₁` = the common absent synthesis; the
  founding-bet σ_p and the crystalline `{Frob_p}` are two shadows of one missing `F₁`, tied by the `F_q`
  coincidence, not identical over ℚ. The carrier `N`, the `1/s` recurrence, and the Gross–Koblitz/Iwasawa
  route (all on the `Frob_p` side) **survive**; only the identification is fixed. Honest rigor correction.

## §14 BUILT + TESTED the multi-q (friable) bypass — structural NO-GO at the first log-moment `[attack the wall; verified]`

Per the user directive ("attack the walls, build them"), I built the multi-q bypass to §8's single-measure
γ-blindness and tested it numerically (archive `computations/2026-06-19-wheeler-friable-bypass-test.txt`).

**Built.** The friable `{2,3}` analog of §8: `L_j := ∫_0^∞ x^j \log x\,dμ_S`, `dμ_S = Σ_{k\ S\text{-friable}}e^{-kx}dx`,
`ζ_S(s)=∏_{p∈\{2,3\}}(1-p^{-s})^{-1}`. Closed form: `L_j = j!\big[(H_j-γ_E)ζ_S(j+1)+ζ_S'(j+1)\big]`. The prime
structure enters via `\log k = Σ_p v_p(k)\log p` (the #124 weld), so unlike §8 this is **not** flat-γ-blind:
the γ_E-coefficient is `-j!ζ_S(j+1) ≠ 0`.

**Tested — and it FAILS, structurally.** Since `ζ_S'/ζ_S = -[(\log2)\tfrac{2^{-s}}{1-2^{-s}}+(\log3)\tfrac{3^{-s}}{1-3^{-s}}]`
is `(\log2,\log3)` with **rational** coefficients at `s=j+1`,
> `L_j = j!\,ζ_S(j+1)\cdot M_j`,   `M_j := H_j - γ_E + r2_j\log2 + r3_j\log3`,   `r2_j,r3_j ∈ ℚ`.
**Verified exactly** (dps=80, PSLQ): `M_0=-γ_E-\log2-\tfrac12\log3`, `M_1=1-γ_E-\tfrac13\log2-\tfrac18\log3`, …,
γ_E-coefficient always `-1`. So the normalized forms `M_j` **all lie in the 4-dimensional ℚ-space
`⟨1, γ_E, \log2, \log3⟩`.** Consequence:
- The construction yields only **exact ℚ-relations** (necessarily γ_E-coeff `0` — `8` forms in a `4`-dim
  space, γ-blind; PSLQ confirms the genuine relations have γ_E-coeff `≈0`) **or** `O(1)` γ_E-forms.
- **No small γ_E-approximation exists** — the form-space is finite-dimensional, so there is no room for
  Hermite–Padé smallness. (A dps=60 γ_E-retaining "relation" appeared but **vanished at dps=150/250** — a
  verified PSLQ artifact, not a bypass.)

**Verdict (a real no-go, knowledge created).** The §8 γ-blindness is NOT escaped by prime-weighting at the
**first** log-moment: the friable construction stays in `⟨1,γ_E,\log2,\log3⟩` (4-dim, rigid). The multi-q
bypass at the bottom slice **fails for a structural reason** (finite-dim form-space), sharper than §8's
flat γ-blindness.

**Where the bypass must go (scope).** To escape the 4-dim space and create approximation room, one needs
**higher log-powers** `∫x^j(\log x)^T dμ_S` (`T≥2`), which bring in `γ_1,…,γ_T` and higher prime-log
monomials — i.e. the full #124 weld / Professor's `baker-for-stieltjes` auxiliary. The bottom slice is a
no-go; the full higher-log-power construction is the open apex (Professor's lane). Apex unchanged (FIELDS MEDAL).

## Log (cont.)
- 2026-06-19 (Wheeler) — **§14: built + tested the multi-q friable bypass; structural NO-GO at the first
  log-moment.** `L_j=∫x^j\log x\,dμ_S=j!ζ_S(j+1)·M_j`, `M_j=H_j-γ_E+r2_j\log2+r3_j\log3` (`r∈ℚ`, verified exact
  dps=80) ⟹ forms span only the 4-dim `⟨1,γ_E,\log2,\log3⟩` ⟹ only exact ℚ-relations (γ_E-coeff 0, γ-blind) or
  O(1) γ_E-forms, **no small approximation**. dps=60 "relation" was a verified artifact. The §8 γ-blindness
  sharpened (finite-dim-rigid); the bypass needs higher log-powers `T≥2` (Professor's baker-for-stieltjes).
  Knowledge created (a verified no-go), not a shell. Archived.
