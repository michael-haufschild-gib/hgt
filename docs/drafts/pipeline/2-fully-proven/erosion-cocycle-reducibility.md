# 19a — the Euler cocycle is reducible (bounded) over the 𝕋^∞ flow iff σ ≥ ½

- **ID:** erosion-cocycle-reducibility
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) — Door-2 grade **BRIDGE** (axis-mode decoupling; see below)
- **Priority:** FUTURE
- **Source:** sub-result 19a of `../1-in-progress/erosion-threshold.md` (G19); ../../door/bucket-time-and-non-holonomic-time.md · 00-status #59, #111
- **Statement.** Over the Kronecker flow on `𝕋^∞` the additive Euler cocycle is an `L²`-coboundary
  (bounded, reducible to its zero mean — the rigorous form of "Lyapunov/growth exponent 0, eroded")
  **iff `σ ≥ ½`**, and the threshold is **sharp and inclusive**: at `σ = ½` the transfer function is in
  `L²` (so the cocycle is bounded) even though the observable itself has left `L²` (Selberg's `log log`
  fluctuations). The non-reducible region is the open half-plane `σ < ½`.

## Setup (the cocycle, pinned down)
- `𝕋^∞ = ∏_p ℝ/ℤ` with Haar measure; coordinates `x_p = e(θ_p)`, `|x_p| = 1`, one per prime.
- **Kronecker flow** `φ_t`: `x_p ↦ x_p · p^{-it}` (each coordinate rotates at frequency `log p`). Its
  generator `D` acts on the Fourier mode `e_m(x) = ∏_p x_p^{m_p}` (`m ∈ ℤ^{(P)}`, finite support) by
  `D e_m = -i (m·ℓ) e_m`, where `ℓ = (log p)_p` and `m·ℓ = Σ_p m_p log p = log ∏_p p^{m_p}`.
- **Euler observable** `g_σ(x) = -Σ_p log(1 - x_p p^{-σ}) = Σ_p Σ_{k≥1} x_p^k p^{-kσ}/k`. Along the
  orbit of the base point `1`, `g_σ(φ_t 1) = log ζ(σ + it)` (up to the standard `k ≥ 2`/continuation
  corrections). Its Fourier support is the **axis modes** `m = k δ_p` (`k ≥ 1`, one prime each), with
  coefficient `ĝ(kδ_p) = p^{-kσ}/k` and mode frequency `(kδ_p)·ℓ = k log p`.
- **The additive cocycle** `A_σ(t,x) = ∫_0^t g_σ(φ_s x) ds`. (For an additive cocycle the time-Lyapunov
  exponent `lim_t A_σ(t,x)/t` equals the mean `∫ g_σ dμ = 0` whenever `g_σ ∈ L¹`, so it is trivially
  `0`; the genuine dichotomy is **bounded coboundary vs unbounded growth** — that is what "`L = 0` /
  eroded" must mean here, and what the theorem settles.)

## Theorem 19a
The cohomological equation `D h = g_σ` has a solution `h ∈ L²(𝕋^∞)` — equivalently `A_σ(t,x) =
h(φ_t x) - h(x)` is an `L²`-coboundary with `sup_t ‖A_σ(t,·)‖_{L²} ≤ 2‖h‖_{L²} < ∞` — **iff `σ ≥ ½`.**

*Proof.* `D h = g_σ` is solved mode-by-mode on the axis: `ĥ(kδ_p) = ĝ(kδ_p)/(-i·k log p) = i\,
p^{-kσ}/(k² log p)` (every other Fourier coefficient is `0`). Hence
```
   ‖h‖²_{L²} = Σ_p Σ_{k≥1} |ĥ(kδ_p)|² = Σ_p Σ_{k≥1} p^{-2kσ} / (k⁴ (log p)²).
```
The `k = 1` term dominates the threshold: `Σ_p p^{-2σ}/(log p)²`. By the prime integral test
(`Σ_p f(p) ≍ ∫_2^∞ f(x)\,dx/log x`),
```
   Σ_p p^{-2σ}/(log p)²  ≍  ∫_2^∞ x^{-2σ} / (log x)³ \, dx,
```
which **converges iff `2σ ≥ 1`** (at `2σ = 1`, substitute `u = log x`: `∫ du/u³ < ∞`; for `2σ < 1`,
`x^{1-2σ}` grows and the `(log x)^{-3}` cannot save it). The `k ≥ 2` terms are dominated for `σ ≥ ½`
(`p^{-2kσ} ≤ p^{-k}`, and `Σ_p (log p)^{-2} Σ_{k≥2} p^{-k}/k⁴ ≍ Σ_p 1/(p(log p)²) < ∞`). So
`h ∈ L² ⟺ σ ≥ ½`. When `h ∈ L²`, `A_σ(t,·) = h∘φ_t - h` is bounded in `L²` uniformly in `t`. ∎

## The sharp pinch at σ = ½ (why the line, exactly)
Two `L²` thresholds straddle the critical line:
- **observable** `g_σ ∈ L²` ⟺ `Σ_p p^{-2σ} < ∞` ⟺ `σ > ½` (the backbone, `critical-line-abscissa-of-convergence`);
- **transfer function** `h ∈ L²` ⟺ `Σ_p p^{-2σ}/(log p)² < ∞` ⟺ `σ ≥ ½` (this theorem).

They **pinch at `σ = ½`**: there `g_½ ∉ L²` (its variance `Σ_p p^{-1}` diverges — Selberg's `log log`
CLT) yet `h ∈ L²` (`Σ_p 1/(p(log p)²) < ∞`). So the critical line is exactly the locus of **marginal
reducibility**: the cocycle is still bounded (transfer function in `L²`) while the instantaneous
observable has just escaped `L²`. The dividing `(log p)²` — the gap between the two thresholds — is the
square of the mode frequency `log p`, i.e. it is the flow's generator doing the smoothing.

## Door-2 verdict: BRIDGE — and the reason is the useful part
**Fails Door-2.** The observable `g_σ` is supported on **axis modes only** (`kδ_p`, one prime each),
because `log` of an Euler product is a **sum** of single-prime logs. So the cohomological equation
**decouples completely over primes**: `h = Σ_p h_p` with each `h_p(x_p)` solving an independent
single-circle (`𝕋^1`, single-prime) problem; the mode frequencies `k log p ≥ log 2` are bounded away
from `0`, so there are **no small divisors, no resonances, and Baker is not needed.** Stripped of the
multi-`q` vocabulary this is `𝕋^1` harmonic analysis (per prime) + the elementary convergence of
`Σ_p p^{-2σ}/(log p)²`. A parent proves it ⟹ **BRIDGE**, not native C5.

This is the same failure mode as §59/§60, now diagnosed precisely:

> **Axis-mode decoupling.** Every object built *additively* from per-prime Euler data — the Euler
> product, the diagonal `log ζ`, the §59/§60 `s`-monodromy, this cocycle — has Fourier support on
> **axis modes** and therefore **decouples prime-by-prime**, reducing to single-prime parents. The
> *joint* `σ_p` structure (unique factorization = **no resonance** among combination modes; Baker =
> the **small-divisor** control of their frequencies) is **load-bearing only for objects with genuine
> combination-mode content** `m = m_pδ_p + m_qδ_q + …` (≥ 2 nonzero prime entries).

**C5 criterion (forward).** A native (Door-2-surviving) theorem must concern an object whose Fourier
support includes **combination modes** and whose proof essentially uses (a) `m·ℓ ≠ 0` for `m ≠ 0`
(unique factorization) and (b) `|m·ℓ| ≥ Baker(|m|)` (linear forms in logs). The natural carriers of
combination modes are the **cross-prime** objects: the curvature/integrability class `F_{pq}` (§16,
which couples `p` and `q`), Rankin–Selberg `⊗` and the pair/`n`-level correlations (#79/#86), and the
joint `G_L` monoidality class `ω` (G4). The additive/`log` world is BRIDGE; the multiplicative/product
world (`ζ²`, `⊗`, moments) is where C5 can live. See [[door-C5-irreducibility-and-door-2-retest]].

## Significance
A genuinely **dynamical** theorem (cocycle reducibility over the field's boundary flow), proved, that
pins `σ = ½` sharply as the inclusive reducibility threshold. It is the rigorous core of the
"erosion = `L = 0` above ½" conjecture (19a), with the loose "Lyapunov exponent" replaced by the
correct notion (bounded `L²`-coboundary). It is BRIDGE — but its proof yields the **axis-mode
criterion** that redirects the C5 search to combination-mode (cross-prime) objects.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (above; Fourier on `𝕋^∞` + elementary prime-sum convergence — no open lemma)
- [ ] 2 → 3  formalized — pre-certify on the runpod (`Σ_{p≤X} p^{-2σ}/(log p)²` convergent at/above ½,
  divergent below), then Lean: the convergence dichotomy of `Σ_p p^{-2σ}/(log p)²` is Tier-A.
- [ ] 3 → 4  publication-ready

## Log
- 2026-06-19 — created in 2-fully-proven. Pinned the additive Euler cocycle over the `𝕋^∞` Kronecker
  flow; proved `h ∈ L²` (bounded/reducible cocycle) iff `σ ≥ ½`, sharp pinch at the line. Door-2:
  BRIDGE (axis-mode decoupling) — yields the combination-mode C5 criterion.
