# The Lindelöf frontier: a map of proved method-ceilings

- **ID:** `lindelof-frontier-criticality-map`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / STRUCTURAL MAP — barrier theorems
- **Source:** `../../1-in-progress/lindelof-hypothesis-campaign.md`, cycles 1–33
- **Scientific status:** `[PROVED HERE] [NOT AN LH PROOF] [NEEDS EXTERNAL AUDIT]`
- **Lean:** `HTGeometry.MomentNeutralityLaw`, `HTGeometry.MomentChordPivot`,
  `HTGeometry.ShiftAverageTransfer`, `HTGeometry.MomentResolutionFloor` — axioms
  `[propext, Classical.choice, Quot.sound]` only.
- **Rewritten 2026-07-25** to remove claims retracted in cycles 18, 19, 22, 25, 29 (errata E1–E5).

Notation. `M(A)` = growth exponent of `∫_T^{2T}|ζ(1/2+it)|^A dt`; `m(k) := M(2k)`;
`φ(v)` defined by `meas{t ∈ [T,2T] : |ζ(1/2+it)| > T^v} = T^{1-φ(v)+o(1)}`; `μ := μ(1/2)`;
`Δ_k(N,h)` = Conrey–Gonek error in `Σ_{N<n≤2N} d_k(n)d_k(n+h)`.

---

## 1. The claim

Every unconditional route to `μ(1/2)` examined here terminates at a ceiling, and each ceiling is
`1/4`, `1/6`, or `1/8`. The value `1/8` recurs because it is the resolution floor of the
**independent-signs model** for divisor-correlation errors, which is *exactly correct* in the only
two cases where the answer is known. What remains uncapped is exactly the family of statements
equivalent to, or strictly stronger than, LH.

## 2. The pivot `v = 1/8`, and why

**(2.1) The model.** Model `Δ_k(M,h)` at size `M^{1-1/k}` with signs uncorrelated in `h`. The
off-diagonal of the `2k`-th moment is `Σ_h (Δ_k(M,h)/M)·K(h)` with `K(h) ≪ min(T, M/h)` and
`Σ_{h≤M}K(h)² ≍ 2MT`, so the model predicts error `(1/M)(2MT)^{1/2}M^{1-1/k} = √2·T^{k/4}` at
`M = T^{k/2}`. Its resolution floor is `(k/4)/(2k) = 1/8` — **for every `k`**.

**(2.2) The model is exactly right where anything is known.** `E(T) ≍ T^{1/4}` (`k=1`) and
`E₂(T) ≍ T^{1/2}` (`k=2`), each matched by an `Ω`-result (Good; Ivić–Motohashi). Both equal `k/4`.
So the two verifiable cases confirm the model, and both have resolution floor exactly `1/8`.

**(2.3) Four other characterisations of `v = 1/8`.**
1. `φ ≥ 4v` (4th moment) and `φ ≥ 12v−1` (Heath-Brown) cross exactly at `v = 1/8`, both `= 1/2`.
2. At the self-dual `ζ²` polynomial (length `N ≍ T`), Halász–Montgomery pits `V⁴ = T^{4v}` against
   the Gram off-diagonal, whose square-root-cancellation size is `N^{1/2} = T^{1/2}`; equal at `1/8`.
3. `|ζ| = T^v` forces `|D_N| = N^{1/2+2v}` at the critical block, `= N^{3/4}` exactly at `v = 1/8`
   (the Guth–Maynard threshold).
4. `A/8 − (M(A)−1) ≡ 1/2` on the chord from `(4,1)` to `(12,2)` — the chord slope and the evaluation
   point are both `1/8`, so the gain is constant there (`MomentChordPivot`).

## 3. Barrier theorems

**(3.1) Mean-value criticality.** `∫_0^T|ζ(σ+it)|^{2k} ≪ T^{1+ε}` holds exactly for `σ ≥ 1−1/k`, and
the resulting bound `1/(2k)` equals `(1−σ)/2` there — the Phragmén–Lindelöf line, traced with no
slack, for every `k` and `σ`.

**(3.2) Halász–Montgomery cap.** Granting perfect square-root cancellation for `Σ_{n~N}n^{-iu}`, the
diagonal gives `R ≪ T^{1−4v+ε}` — exactly the fourth-moment bound, and nothing more.

**(3.3) Guth–Maynard inertness.** In the block parameter `N = T^β`, at the self-dual block `β = 1`
the GM terms `T^{8β/5−8v}`, `T^{1+2β/5−8v}` fall below the classical `T^{1−4v}` only for `v > 3/20`,
where the surviving maximum is still `T^{1−4v}`. So at `β = 1` the GM bound **equals** the classical
bound for every `v`; since `β = 1` always binds, GM cannot improve `φ`, any moment, or `μ`.

**(3.4) Moment-neutrality law.** Given `m(j) = 1` and `μ ≤ θ`, `inf_k m(k)/(2k) = min(1/(2j), θ)`.
So a perfect `2j`-th moment improves on `θ` **iff `j > 1/(2θ)`**. With `θ = 13/84` the threshold is
`42/13 = 3.2308`: **the sixth moment conjecture is subconvexity-neutral**, yielding
`13/84 + 1/(28k) → 13/84` and never crossing. The eighth is the first that can help.

**(3.5) The chord is the image of one input.** With the transfer
`m(k) ≤ 1 + max(0, k(a+b−1)/2 − a)` for `Σ_{h≤H}Δ_k(x,h) ≪ H^a x^{b+ε}` (agrees identically with
Ivić's published `k=3` case), the input `(a,b) = (1/2,1)` gives `1+(k−2)/4` for **every** `k` — i.e.
`m(2)=1`, `m(3)≤5/4`, `m(4)≤3/2`, `m(6)≤2`. The entire known unconditional envelope is one point.

**(3.6) The short-interval mean square is neutral at its optimum.** `(1/2,1)` is Cauchy–Schwarz from
`Σ_n|Δ_k(n+H)−Δ_k(n)|² ≪ xH^{1+ε}`, which Ivić calls *"unattainable at present"* for `k>2` (his
Theorem 1 gives `xh^{4/3}`, and only under LH). The unattainable optimum reproduces the chord — it
would improve nothing; `xh^{4/3}` gives `m(3) ≤ 4/3`, `m(6) ≤ 7/3`, strictly worse than known.

**(3.7) Heath-Brown's twelfth moment is at its own ceiling.** His input is the short second moment at
`G ≍ V²`, sharp individually for `G ≥ T^{1/3}` (which alone gives Weyl) and pushed to `G = T^{1/4}`
on average over the large-value set. Under `G = T^{2v}` that range is exactly `v ∈ [1/8, 1/6]`, the
window where `m(6) = 2` is attained. And `G = T^{1/4}` is **sharp**: `E(T) = Ω(T^{1/4})` means the
short second moment fails below it. So `m(6) ≤ 2` is the exact output of the method at its input's
limit — the 48-year absence of improvement is a ceiling, not a gap in effort.

**(3.8) The `Ω` side cannot disprove LH.** Every known `Ω`-result for `max|ζ(1/2+it)|` comes from the
resonance method, whose gain is the Gál/GCD sum, and Bondarenko–Seip proved
`Γ(N) = exp((C+o(1))√(log N loglog N))` — subpolynomial. With a polylogarithmic resonator the output
is `T^{o(1)}`. **No resonance construction can give `Ω(T^c)`, so no known method disproves LH.**
Even the conjecturally correct maximum (Farmer–Gonek–Hughes) is `T^{o(1)}`.

**(3.9) Classical error-term programmes cap at `1/8`.** `μ ≤ θ_{E_k}/(2k)`; the conjecturally optimal
`θ_{E_1} = 1/4` and `θ_{E_2} = 1/2` are sharp by `Ω`-results and both give `μ ≤ 1/8`.

## 4. What the additive-divisor route gives — and the contested exponent

The transfer separates into two independent halves (`ShiftAverageTransfer`):

| input | `(a,b)` | result |
|---|---|---|
| Conrey–Gonek size, no shift cancellation | `(1, 1/2)` | `μ ≤ 1/8` |
| Vinogradov size + square-root shift cancellation | `(1/2, 1−1/k)` | `μ ≤ 1/8` |
| **Conrey–Gonek size + square-root shift cancellation** | `(1/2, 1/2)` | **`m(k)=1` ∀`k`, i.e. LH** |

Either half alone buys exactly `1/8`; together they buy Lindelöf. The two conjectured sizes conflict
for `k ≥ 3`: Conrey–Gonek predict `Δ_k(x,h) ≪ x^{1/2+ε}`; Ivić conjectures `Ω(x^{1−1/k})`, i.e. "the
correlation error is the square of the ordinary divisor error". At `k = 2` both read `x^{1/2}` and
the `Ω` is Motohashi's theorem, so `k = 2` does not discriminate.

**Function-field evidence favours Conrey–Gonek.** Sawin proves square-root cancellation for divisor
sums over short intervals (Duke 2021) and over squarefree progressions with level of distribution
`→ 1` (Acta Math. 2024) in `F_q[t]`, with no `k`-dependent degradation.

## 5. The open core, and where the difficulty sits

Successive formulations, each strictly more concrete:
1. a `GL(3)` Motohashi analogue for `Δ₃` — **input does not exist**;
2. hyper-Kloosterman assembly — **input exists** (Deligne's bound for `Kl_k`), assembly loses;
3. a power saving for `Σ_{m≤x/a} d(m)d₃(am−h)` uniform in `a ≤ x^{1/3}` — the `a=1` case is
   Topacogullari's theorem. The moduli sit at `x^{1/3}`, far inside the level of distribution already
   known for `d₃` (`1/2+1/46`, FKM), so **the level of distribution is not the obstruction**;
4. every ingredient in (1)–(3) is a **theorem over `F_q[t]`** (Sawin), proved geometrically. The
   obstruction is the transfer from `F_q[t]` to `ℤ`, not the truth of the statements.

## 6. Completeness

Capped, with proof: mean-value/large-sieve (`1/4`); Halász–Montgomery (`1/4`); Guth–Maynard (inert);
`E(T)` and `E₂(T)` programmes (`1/8`); Heath-Brown's twelfth moment (`m(6)=2`); additive divisor with
Vinogradov's size (`1/8`); short-interval mean square (neutral); circle-method split (tautological);
resonance (`T^{o(1)}`); `GL(3)` subconvexity for `ζ³` (`1/6`).

Uncapped: the moment conjecture (equivalent to LH); the exponent-pair conjecture (implies LH); the
Conrey–Gonek size with square-root shift cancellation (implies LH).

> **There is no uncapped intermediate.** That is the structural reason the problem is open.

## Novelty audit

Classical and recorded elsewhere: the individual bounds, convexity of `M`, Ivić's transfer, the
`Ω`-results, the ANTEDB ledger, Sawin's and Topacogullari's theorems. New here: the pivot
identification and its five coincidences (§2); the chord–pivot plateau; the moment-neutrality law and
the subconvexity-neutrality of the sixth moment; the chord as the image of `(a,b)=(1/2,1)`; the
neutrality of the short-interval mean square at its conjecturally optimal value; the inertness of
Guth–Maynard at the self-dual block; Heath-Brown's method being at its input's ceiling; the clean
separation of the two transfer halves and the fact that together they give LH; and the observation
that every required ingredient is already a theorem over `F_q[t]`.
Classification: `NEEDS EXTERNAL AUDIT`.

---

## 7. The twelfth ceiling: zero geometry (added cycle 50)

`[PROVED HERE]` Lean: `HTGeometry.JensenZeroGeometry` — axioms `[propext, Classical.choice,
Quot.sound]`. Full proofs: preprint §6.

**(7.1) The Jensen balance is an identity.** For `s₀ = 1/2+it₀`, `L = log(t₀/2π)`, `n_{t₀}(u)` the
two-dimensional zero count in `|s−s₀| < u`, and `0 < R ≤ √T`:

    log|ζ(s₀)| = (R/π)L + 𝔈_R(t₀) − ∫_0^R n_{t₀}(u) du/u + O(R²/T),

where `𝔈_R` is the mean of `log|ζ|` over the circle folded into `Re ≥ 1/2` by the functional
equation. Proof: Jensen for `ξ` on `D(s₀,R)`; the gamma factor is zero-free there, so its log-modulus
is harmonic and cancels.

**(7.2) The exact duality.** The expected potential of an on-line, Riemann–von Mangoldt-correct zero
set is `∫_0^R (u/π)L du/u = (R/π)L` — exactly the `χ`-factor mean, at every radius. Hence
`log|ζ(1/2+it₀)| = 𝔈_R + D_R` with `D_R := ∫_0^R((u/π)L − n_{t₀}(u))du/u`, so **LH ⟺ the zero set has
no logarithmic holes around critical-line points.** This splits Backlund's criterion into a vertical
(count) and a horizontal (displacement) condition.

**(7.3) Inertness.** With `θ_R = arccos(1/(2R))`, `A = R − √(R²−1/4)`,
`I(R) = √(R²−1/4) − θ_R/2`, `J(R) = (1/2π)∫(1/2 − R|cos θ|)_+dθ`, the cancellation

    4(R − I(R)) = 2(θ_R + 2A) = π(1 − 2J(R))

turns the two available inputs (`μ ≤ θ₀` via Phragmén–Lindelöf on the circle; `|β−1/2| ≤ 1/2` plus
Riemann–von Mangoldt for the potential) into `μ ≤ 1/4 + 2J(R)(θ₀ − 1/4)`. Hence the output lies in
`[θ₀, 1/4]` at every radius; `1/4` is the unique fixed point and the map contracts *toward* it, so
iterating raises a subconvex input back to `1/4`; and closing the route on itself gives exactly
`μ ≤ 1/4`. **The Jensen balance is equivalent to the convexity bound and has gain zero.**

**(7.4) The dichotomy.** With the zeros on the line the potential is full, the `χ`-factor cancels
entirely, and the output is `2J(R)θ₀ → 0` — a zero-geometry proof of RH ⟹ LH with contraction ratio
`2J(R)`. So the whole gain is horizontal. The vertical input is worthless: any `S(t) ≤ c_S log t`,
including the unproved `c_S = 0`, leaves the output at `1/4`. The exact intermediate needed is
Backlund's criterion pointwise, i.e. LH. **Exactly circular; no intermediate.**

**Consequence for the completeness list of §6.** Add to "capped, with proof": zero geometry /
Jensen–Backlund (`1/4`, inert). This is the first ceiling in the map that is *not* an analytic
route, and it is the only one whose ceiling is proved by an exact cancellation rather than by an
optimisation.
