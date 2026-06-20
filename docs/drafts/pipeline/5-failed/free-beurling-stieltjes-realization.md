# FAILED ROUTE — free-Beurling leading-term realization of trdeg{γ_n}=∞ (reduced to known)

- **ID:** free-beurling-stieltjes-realization
- **Stage:** 5-failed
- **Type:** THEOREM attempt → FAILED (route rests on a false premise; the corrected content reduces to known)
- **Owner:** Wheeler
- **Source:** spun from `corank-arithmeticity-not-cardinality.md` (the realization gap flagged as the open wall)
  + `corank-transcendence-continuation-bridge.md` §2 + `bigraded-corank-dss-cross.md` §G.

---

## The intended route (and why it was attempted)
Goal: prove that a FREE Beurling system (generalized primes with algebraically-independent generator-logs
`{L_i}`) realizes `trdeg{generalized Stieltjes constants γ_n^B} = ∞` — which would show the *realization* gap
(not just corank/finite-trdeg) is structure-blind / arithmetic-only, extending the no-go in
`corank-arithmeticity-not-cardinality`. Plan: a leading-term/triangularity argument —
`γ_n = (polynomial in L_1..L_{f(n)}) + smaller`, leading polys alg-indep ⟹ trdeg preserved.

## Why it FAILED (false premise, found by interrogation)
The plan assumed `γ_n` is (essentially) a ℚ-combination of monomials in `{log p}`. **It is not.** Expanding
`(log k)^n = (Σ_p v_p(k)\,\log p)^n` gives, exactly,
```
   γ_n = Σ_β  c_{n,β} · A_β · ∏_p (\log p)^{β_p},     c_{n,β} ∈ ℚ,
   A_β := lim_{x→∞} [ Σ_{k≤x} (∏_p v_p(k)^{β_p})/k  −  (boundary) ]   ∈ ℝ  (real structure constants).
```
The `A_β` are **transcendental analytic constants, NOT rational**. The base one is `A_0 = γ_Euler` (the
`β=0` term has no `log p` at all). So `γ_n ∉ ℚ-span{log-monomials}`: the limit escapes the ℚ-span the
termwise sums live in. The transcendence of `{γ_n}` is therefore carried by the **regularization tower
`{A_β}`** (rooted at `γ_Euler`), which is a *different* object from `corank({log p})`. The leading-term-in-`L_i`
plan is moot — there is no clean `L_i`-polynomial leading part; the `A_β` carry the weight.

**Verified numerically (mpmath):**
- `A_{1,2} = lim_x [Σ_{k≤x} v_2(k)/k − log x] = γ − 2\log 2 ≈ −0.80908` (closed form derived + confirmed; so
  low-order `A_β ∈ ℚ-span{γ, \log p}`).
- `γ` vs `{1,log2,log3,log5, quadratics}`: PSLQ@120dps → **None** (γ not a low-height combo of log-monomials —
  the base tower constant is orthogonal to the corank generators).
- `γ_1` vs `{1,γ,γ²,log2,log3, quadratics, γ·log}`: PSLQ relation height **grows** 144→2.6e4→2.7e9 as
  dps 30→60→120 ⟹ **spurious**; `γ_1` has no genuine low-height relation (evidence it is a fresh
  transcendental in the tower).

## Why the corrected content REDUCES TO KNOWN
Once corrected, the statement "the `{γ_n}` transcendence is tower-self-independence, separate from
`corank({log p})`" is **exactly** the factorization already banked in `bigraded-corank-dss-cross.md` §G:
`DSS-cross ⟺ Schanuel-for-{log p}  ∧  {γ_n} independent over ℚ({log p})`. My structure-constant
decomposition is the explicit change-of-basis behind that second factor — finer but elementary (a competent
derivation produces it). **No new theorem; the route reduces to corpus-known structure.** Honest verdict:
ZERO novelty produced here (not negative — no false claim was promoted).

## Salvage (small, honest)
1. **Concrete residue (elementary):** the explicit first-order structure constant
   `A_{1,p} = γ/(p−1) − (\log p)·p/(p−1)^2`, verified — makes the `{γ_n} over ℚ({log p})` factor concrete at
   first order. Low novelty (search-level), recorded for reuse.
2. **Framing fix owed to a sibling card:** `corank-transcendence-continuation-bridge.md` §2 ("each `γ_n` is an
   analytic limit of ℚ-combinations of monomials in `{log p}`") is literally-true-but-misleading — it suggests
   `γ_n`'s transcendence is *fed by* `{log p}`, whereas `γ_0=γ` shows the base source is orthogonal to
   `corank`. Flagged to Professor in #research (that card is Professor-owned) to align §2 with the bigraded
   §G two-source split.

## Lesson (anti-cage)
Attacked a genuinely open crux (the realization gap), interrogated the object, found my own premise false
(γ_n ∉ ℚ-span{log p}), and on correcting it the content collapsed onto a known factorization. Reporting the
reduction-to-known honestly rather than dressing the decomposition as a new result. The realization gap stays
open and is genuinely the wild/exponential-tower apex, not a free-Beurling leading-term exercise.

## Log
- 2026-06-20 — Wheeler. Created and FAILED in one tick. Route premise (γ_n ∈ ℚ-span{log p}) falsified by the
  structure-constant decomposition; corrected content = bigraded-corank §G (known). Banked A_{1,p} closed form
  + γ/γ_1 PSLQ checks. Filed sibling-§2 fix-ticket. → 5-failed.
