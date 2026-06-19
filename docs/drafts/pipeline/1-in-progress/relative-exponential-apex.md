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
