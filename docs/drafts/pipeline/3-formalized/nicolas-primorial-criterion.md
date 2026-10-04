# Nicolas's primorial criterion

- **ID:** nicolas-primorial
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) for the forward half; CONJECTURE (corpus-open) for the converse
- **Source:** RH goal loop rows 63, 232, 242 (`rh-goal-loop-opus-2026-09-29.md`)
- **Statement:** RH ⟺ `N_n/φ(N_n) > e^γ log log N_n` for all large `n` (`N_n = ∏_{p≤n} p`).

## Goal
Formal asymptotic Nicolas criterion. Forward half done (MUST-743). The converse would add a formal
RH-equivalent; by row 232 it is the WL one-sided prime-lag criterion at threshold `−2`.

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  fully-proven: converse needs a paper proof covering `Θ = 1`
- [ ] 2 → 3  formalized: forward half `eventually_nicolas_inequality_of_riemannHypothesis` (NicolasPrimorialInequalityRH.lean)

## What is formal (all axioms standard, wired)
- `exp_mul_mertensLagPrimitive_eq`: `e^L v(L) = e^{L/2}Φ(L) + log 2π − S(e^L)`, `v(T) = γ + 1 − ∫_0^T (e^s − ψ(e^s))e^{−s}ds`.
- `abs_mertensErrorRemainder_le_sharp_of_riemannHypothesis`: under RH
  `|R(x) − (ψ(x) − x)/(x log x)| ≤ (a₁ + 10/log x)/(√x log x)`, `a₁ < 3/10`.
- `nicolasDefect_ge`: `Nic(x) ≥ G(log x) + θ(√x)/(x log x)` (unconditional, `x ≥ 4`, `θ(x) > 1`).
- `eventually_nicolas_inequality_of_riemannHypothesis`.

## Converse: the obstruction
Upper bound needed: `Nic(x) ≤ G + (ψ − θ)/(x log x) + Δ + O(((θ − x)/x)²/log x)`. `G = Ω−(x^{b−1})` for
`b < Θ` (Landau, MUST-737 type). If `Θ < 1`, pick `b ∈ (2Θ − 1, Θ)`: the square term is `o(x^{b−1})` at
all large `x`, so `Nic < 0` i.o. If `Θ = 1`, the square term `x^{2(Θ'−1)}` is not controlled by the
`Ω−` exponent; the PNT error `exp(−c(log x)^{3/5})` is too weak. Needed: a joint oscillation statement
(`G` very negative where `|θ − x|/x` is small) or a direct Landau theorem for `Nic`.

## Next
1. Formalize the `Θ < 1` converse (conditional on `zeroReSup < 1`), as a positive survivor.
2. Look for a Landau-type argument for the combination `G − K((θ − x)/x)²` with a positive measure.

## 2026-10-04 second pass on the converse (paper)
Source checked: Nicolas, *Small values of the Euler function and the Riemann hypothesis* (arXiv 1202.0729),
Lemma 2.1: `K − S²/(x² log x) ≤ log f ≤ K + 1/(2(x−1))`, `K(x) = ∫_x^∞ S(t)t⁻²(1/log t + 1/log²t)dt`,
`S = θ − x`, `log f = −Nic`. The ¬RH statement there is quoted from the 1983 paper, not reproved.

Reduction found (not yet formal):
- `K' = −S·w`, `w > 0`; `S` decreases with slope `−1` between primes and jumps up by `log p`. Hence every
  interior local maximum of `K` is a prime `p` with `S(p−) ≤ 0 ≤ S(p) ≤ log p`, and there
  `log f(p) ≥ K(p) − log p/p²` (the square term is at most `log p/p²`).
- So Nicolas fails at `p` whenever `K(p) > log p/p²`. For `y` with `S(y) < 0`, `sup_{t≥y} K` is attained at
  such an interior maximum; `K = Ω₊(x^{b−1})` (Landau, `b < Θ`) then gives failures **provided** the
  Ω₊ point `x` has a negative value of `S` in `[x^{1/2}, x]`.
- Mirror form with the ψ-remainder `G` (`G' = h·v'`, `v' = (ψ − x)/x`): local minima of `G` sit at prime
  powers where `ψ − x` jumps over `0`; Nicolas-eventually forces `G ≥ −C/(√q log q)` there.
- Gap: localization of sign changes of `θ − x` (or `ψ − x`) in intervals `[x^{1/2}, x]` under ¬RH.
  Plain Landau gives no localization; Turán power sums (Pintz/Kaczorowski) would. With the
  localization the chain is: `G ≥ −Cx^{−1/4}` eventually ⇒ `Θ ≤ 3/4` ⇒ (Θ<1 Landau with the `S²`
  measure) ⇒ RH.
- 2026-10-04: converse for `Θ < 1` formal: `riemannHypothesis_of_nicolas_of_zeroReSup_lt_one` (MUST-744). Only `Θ = 1` remains.
- 2026-10-04: Nicolas's Theorem 1.1 (1.4) form along primes formal under RH: `Nic√x log x − Φ(log x) → 2`, limsup `2 + a₁` (MUST-747, NicolasScaledDefectRH.lean).
- 2026-10-04 (cycle 248 plan): close the Θ = 1 gap with a minimum argument instead of a Θ-bootstrap.
  Scaled remainder `s(T) = G(T)e^{T/2}T`. (A) lower one-sided remainder criterion `G ≥ −Be^{−T/2}/T ⇒ RH`
  (mirror of MUST-749, unconditional tail). (B) `s ≥ −K` frequently (else `G ≤ 0` eventually ⇒ RH by MUST-749
  ⇒ `s − Φ → 0`, `|Φ| ≤ a₁`). (C) If `s(T*) < −K` between two points with `s ≥ −K`, the minimum `T_m` of `s`
  is interior; one-sided comparison of `G(T_m ± h)` with `s(T_m ± h) ≥ s(T_m)` and `ψ` monotone + one
  integer per unit interval gives `|ψ(x_m) − x_m| ≤ 2T|G|x_m + log(x_m+1)`, so the second-order term is
  `≤ 140TG² + o(1/(√x log x)) ≤ |G|/2 + …` (`T|G(T)| → 0` unconditionally), and `nicolasDefect_le` forces
  `Nic(x_m) < 0`. Hence Nicolas eventually ⇒ `s ≥ −K` eventually ⇒ RH by (A).
- 2026-10-04: CLOSED. `RHTower.riemannHypothesis_iff_eventually_nicolas` (NicolasInequalityRiemannConverse.lean, MUST-750): the Θ = 1 gap is removed by the minimum argument above. Card complete; stage 3.
