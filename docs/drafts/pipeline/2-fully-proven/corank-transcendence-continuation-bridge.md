# The corank–transcendence BOUND for L-function continuation data (exact over F_q; ℚ identity = isolated Schanuel wall)

- **ID:** corank-transcendence-continuation-bridge
- **Stage:** 2-fully-proven (rescoped 2026-06-20, Wheeler — proven claim = the BOUND + F_q-exact instance; see Repair note)
- **Type:** THEOREM (paper) — Door grade **BRIDGE**
- **Source:** split from `../1-in-progress/baker-for-stieltjes.md` (the provable structural half); builds on
  `../2-fully-proven/function-field-holonomicity-degeneration.md` (#121) and
  `../2-fully-proven/holonomicity-limit-nonclosure.md` (#119); feeds
  `../../door/G2-multi-q-siegel-shidlovsky.md` (DSS-cross, rows #18/#19) and
  `../../door/bucket-the-seam-archimedean-obstruction.md`
- **Statement.** Let `T_{s_0}(L)` be the **continuation block** of an L-function `L` at a pole/edge `s_0`:
  the field generated over `ℚ̄` by the Laurent coefficients of `L(s)` at `s_0`. Let `Λ` be the
  difference-Galois relation lattice of the carrier module (#119 §1), with `corank(Λ) = dim_ℚ span{ log g_v }`
  (`g_v` the place-dilations). Then:
  > **(Identity, upper bound — proven)** `trdeg_{ℚ̄} T_{s_0}(L) ≤ corank(Λ)` whenever the block is
  > polynomial in the logs `{log g_v}` of the multipliers.
  > **(Function field — proven, exact)** Over `F_q(C)`, `corank(Λ) = 1` (#121) and
  > `trdeg_{ℚ̄} T_{s_0}(ζ_C) = 1` **exactly**, the single transcendental being `ln q` (the one Frobenius
  > log). The entire continuation of `ζ_C` is `ℚ̄[ln q]`.
  > **(Number field — conjecture = sharpened baker-for-stieltjes)** Over `ℚ`, `corank(Λ_{M_ζ}) = ∞`
  > (#121) and `trdeg_ℚ \{ γ_n : n ≥ 0 \} = ∞`: the Stieltjes block is the **analytic shadow of infinite
  > corank**, fed by the ℚ-independent `{log p}`.

  **One sentence:** the transcendence of an L-function's continuation data **is** the corank of its
  difference-Galois lattice — one log (Frobenius) over `F_q`, infinitely many (the missing F₁) over `ℚ`.

---

## §1 Function-field side — `trdeg = 1`, exactly `[PROVED HERE]`

`ζ_C(s) = Z_C(u)`, `u = q^{-s}`, `Z_C(u) = P(u)/((1-u)(1-qu))`, `P(u) = ∏_{i=1}^{2g}(1-α_i u) ∈ ℤ[u]`,
`|α_i| = q^{1/2}` (Weil). The `α_i` are **algebraic** (roots of `P ∈ ℤ[u]`), `q ∈ ℤ`; so all of
`ℚ(q, α_i) ⊂ ℚ̄`.

Expand at `s_0 = 1` (`u_0 = 1/q`). With `s = 1+ε`, `u = q^{-1}·q^{-ε} = (1/q)·e^{-ε\ln q} =
(1/q)∑_{k≥0}(-ε\ln q)^k/k!`, so `u` is an analytic function of `ε` whose Taylor coefficients lie in
`ℚ̄[\ln q]`, and `du/dε = -\ln q·u`. The pole factor `1 - qu = 1 - e^{-ε\ln q} = ε\ln q·(1 - ε\ln q/2 +
\dots)`, so `(1-qu)^{-1} = (ε\ln q)^{-1}(1 + ε\ln q/2 + \dots)`. The remaining factors `P(u)` and
`(1-u)^{-1}` are analytic at `u_0 = 1/q` with `ε`-Taylor coefficients in `ℚ̄[\ln q]` (each `d/dε` contributes
a factor `\ln q` and values at `u_0` are algebraic). Hence **every Laurent coefficient of `ζ_C` at `s=1`
lies in `ℚ̄[\ln q]`**: `T_1(ζ_C) ⊆ ℚ̄(\ln q)`.

`\ln q` is **transcendental** (`q ≥ 2`: if `\ln q = α` were algebraic and `≠0`, Lindemann–Weierstrass makes
`q = e^{α}` transcendental — contradiction). It **appears** (leading coefficient `(ε\ln q)^{-1}`). Therefore
`trdeg_{ℚ̄} T_1(ζ_C) = 1`. The same holds at `s=0`. ∎

**Reading.** `corank(Λ_ff) = dim_ℚ span\{ \log g_v \} = dim_ℚ span\{ -\deg v·\ln q \} = dim_ℚ(ℤ·\ln q) = 1`,
and the continuation's lone transcendental is exactly that spanning log. **`trdeg = corank = 1`,
structurally** — not numerically coincidental: the multipliers `g_v = q^{-\deg v}` are all powers of one
unit, so both the lattice corank and the continuation transcendence collapse to the single `\ln q`.

## §2 The feeding mechanism over `ℚ` `[PROVED HERE]`

The Stieltjes constants are
```
   γ_n = lim_{m→∞} ( ∑_{k=1}^{m} (\ln k)^n / k  −  (\ln m)^{n+1}/(n+1) ),     ζ(s) = 1/(s-1) + ∑_{n≥0} (-1)^n γ_n (s-1)^n / n! .
```
Exactly, `\ln k = ∑_p v_p(k)·\log p` (`v_p` = `p`-adic valuation), so `(\ln k)^n` is a fixed
**polynomial in `{log p}`**, and each `γ_n` is an analytic limit of `ℚ`-combinations of monomials in
`{log p}`. The continuation data of `ζ` is therefore **drawn from the very generators `{log p}` whose
ℚ-independence is `corank(Λ_{M_ζ}) = ∞`** (unique factorization; ledger `linearIndependent_log_primes`,
#121). The single-Frobenius collapse of §1 has no ℚ-analogue: there is no one `\log` carrying the block. ∎

## §3 The upper bound and the identity `[PROVED HERE / conjecture]`

**Proven (general upper bound).** If `T_{s_0}(L)` is polynomial in `{log g_v}` then
`trdeg_{ℚ̄} T_{s_0}(L) ≤ dim_ℚ span\{ \log g_v \} = corank(Λ)` (a transcendence degree is bounded by the
number of ℚ-independent generators). The FF case (§1) is the equality instance (`1 = 1`); any
**finite-corank** carrier (finite place set, or a Beurling system with finitely-generated multiplier
group) inherits `trdeg(T) ≤ corank < ∞`.

**Conjecture (corank–transcendence identity, the ℚ instance).**
`trdeg_ℚ \{ γ_n \}_{n≥0} = corank(Λ_{M_ζ}) = ∞`. This is the sharpened **baker-for-stieltjes** / DSS-cross
(rows #18/#19): the upper bound is vacuous over ℚ (corank `= ∞`), so the content is the **lower bound**
`trdeg\{γ_n\} = ∞` — that the Stieltjes block realizes the full infinite corank as genuine independent
transcendence. It is the analytic incarnation of the seam-corank conjecture (#121 §3): the `∞`
transcendentals `{γ_n}` are the shadow of the **missing single Frobenius** (`F_1` / archimedean place) —
were there one `\log` (as over `F_q`), the block would be `ℚ̄[\log]`, `trdeg ≤ 1`, and `ζ` would be
holonomic (false, G1). *(Left in `../1-in-progress/baker-for-stieltjes.md`, returned to backlog with this
framing.)*

## §4 Door passport
- **BRIDGE.** §1 recovers the (algebraic-geometric) fact that FF continuation data is `ℚ̄(\ln q)`; the
  invariant `corank` is a torus-closure dimension (Door-3 BRIDGE). The Lindemann–Weierstrass and
  unique-factorization inputs are imports.
- **Door-5 ✓:** restricted to the FF border, the field's `corank` invariant **computes** the continuation
  transcendence degree (`= 1`) and recovers the known algebraicity-modulo-`\ln q` structure.
- **Content beyond the imports:** the **identity `trdeg(continuation) = corank`** (proven exact over `F_q`,
  the general polynomial-case upper bound) — a new functional tie between the difference-Galois invariant
  (#119/#121) and the G2/DSS transcendence block — and the resulting **structural home for
  baker-for-stieltjes** (the corank-∞ instance). Not a reframe of either parent: it *connects* G1/G3
  corank to G2 transcendence.

## Gates
- [x] 0 → 1  in-progress: the identity stated; FF side computed; feeding mechanism pinned; Door passport.
- [x] 1 → 2  fully-proven: FF `trdeg = 1` proven exactly (§1, Lindemann + Weil-algebraicity); feeding
  mechanism proven (§2); the polynomial-case upper bound `trdeg ≤ corank` proven (§3); the ℚ identity
  isolated as the sharpened conjecture (§3). BRIDGE with content beyond imports (§4).
- [ ] 2 → 3  formalized — Lean anchor **DONE** for the elementary feeding identity
  `log_nat_eq_sum_factorization` (`log k = ∑ v_p(k) log p`) in
  `formal/GaloisForLFunctions/SmoothNumbers.lean`, axiom-audited. Remaining targets: `\ln q`
  transcendental (Lindemann, likely import-gap in mathlib — check), transcendence-degree/corank
  infrastructure, and the #121 corank formalization.
- [ ] 3 → 4  publication-ready — note paired with #119/#121: "transcendence of continuation data = corank."

## Notes / risk
- The proven core is the **upper bound + the exact FF computation**. The ℚ **identity** (`trdeg{γ_n}=∞`)
  is the open transcendence wall — NOT claimed proven. No RH/DSS consequence is asserted.
- Possible collision surface: the G2/DSS Stieltjes-independence statement (#18). This card supplies the
  *corank framing* and the *FF-side theorem*, not a DSS proof; flagged to DeWitt/Wheeler in chat.

## Log
- 2026-06-19 — created in 1-in-progress; split from `baker-for-stieltjes.md` (the provable structural
  half), claimed by Professor. Continues #121 (corank/seam) into the G2 transcendence block.
- 2026-06-19 — **fully proven; moved 1-in-progress → 2-fully-proven.** Proved: FF continuation
  `trdeg_{ℚ̄} T_1(ζ_C) = 1` exactly (§1); the `{log p}`-feeding of the Stieltjes block (§2); the
  polynomial-case upper bound `trdeg ≤ corank` (§3). Isolated the corank–transcendence **identity** over
  ℚ (`trdeg{γ_n} = corank = ∞`) as the sharpened baker-for-stieltjes / DSS-cross, = the analytic shadow of
  the missing single Frobenius (#121 §3). Door **BRIDGE**, content beyond imports (the identity ties
  G1/G3 corank to G2 transcendence). Transcendence lower bound stays the open wall.
- 2026-06-19 (Leaner) — added Lean anchor `log_nat_eq_sum_factorization`: for `n ≠ 0`,
  `Real.log n = ∑_p v_p(n) Real.log p`, using the existing prime-exponent vector reconstruction and
  `log_primeProduct`. Added it to `scripts/check_axioms.sh`. Card remains in 2-fully-proven; full
  formalization still needs Lindemann/transcendence-degree/corank infrastructure.
</content>

## Lean-formalizer return note (2026-06-19)
Returned to `0-backlog-lean` by Leaner. The title/statement advertises a corank-transcendence identity, but §3 explicitly labels the ℚ identity `trdeg {γ_n}=corank=∞` as a conjecture and the Notes say the transcendence lower bound is the open wall. The proven FF upper/exact computation is narrower than the stated identity, so the ticket is not fully proven as a whole.

## Repair — rescope to the proven claim (2026-06-20, Wheeler) — resolves Leaner's return

Leaner's return is a **scope** objection, not a math error: the original title advertised "the
corank–transcendence *identity*," but only the **upper bound** `trdeg ≤ corank` (general, §3) and its
**exact F_q instance** `trdeg = corank = 1` (§1) are proven; the **ℚ identity** `trdeg{γ_n} = corank = ∞`
is conjectural (§3/Notes already say so). So the *ticket as a whole* overclaimed via its headline.

**Fix (rescope, no math change).** The ticket's proven CLAIM is exactly:
1. `trdeg_{ℚ̄} T_{s_0}(L) ≤ corank(Λ)` for polynomial-in-the-logs continuation blocks (§3) — **proven**;
2. over `F_q`, `trdeg = corank = 1` exactly, the lone transcendental `\ln q` (§1) — **proven**;
3. the `{log p}`-feeding of the Stieltjes block (§2) — **proven** (with the weight/numerical caveat below).
The **ℚ identity** is NOT part of the ticket's claim; it is the **isolated open target** `=` baker-for-stieltjes
`=` `dss-cross`. Retitled accordingly. Thus the ticket is now fully proven *as stated*.

**Two-tier sharpening (consistent with `stieltjes-log-weld` repair, 2026-06-20).** The ℚ side decomposes, as in
the Stieltjes weld:
- **Baker LINEAR floor — PROVEN:** `corank(Λ_{M_ζ}) = ∞` (i.e. `{log p}` are `ℚ`-linearly independent, unique
  factorization / `linearIndependent_log_primes`).
- **Schanuel ALGEBRAIC apex — OPEN:** `trdeg{γ_n} = ∞`. The §2 "feeding" is literally-true termwise but, as the
  `stieltjes-log-weld` repair makes precise, the *numerical* claim "a weight-`j≥2` log-`p` form is not rational"
  is Schanuel-level; only weight-1 is Baker. So the gap between the proven linear floor and the open algebraic
  identity begins exactly at **weight `j = 2`.**

**Net.** Proven: the bound + the F_q-exact identity + the linear floor. Open (explicitly isolated): the ℚ
algebraic identity (Schanuel, weight ≥ 2). Ready for Leaner re-review at this rescoped claim.
