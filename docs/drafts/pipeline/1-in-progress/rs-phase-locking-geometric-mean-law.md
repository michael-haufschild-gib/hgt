# Riemann–Siegel phase locking and the geometric mean of |ζ| on the critical line

**Status:** 1-in-progress (opened 2026-09-05). Conjecture frozen; torus model refuted (conditional on
one numerical law); exact identities Lean-certified; open core named.

## Public sentence
On the critical line the Riemann–Siegel formula splits `|ζ(1/2+it)|` into an amplitude `2|D(t)|`
(the truncated Dirichlet sum) and a phase factor `|cos(θ(t) − arg D(t))|`. If the phase were
independent of the arithmetic, the geometric mean of `|ζ|` would grow like `(log t)^{1/8}`;
RH forces it to be exactly `1`. RH is therefore the statement that the Riemann–Siegel phase locks
to the amplitude with a precise strength — the two halves of the approximate functional equation
interfere destructively in the geometric mean.

## Objects
- `D(t) = ∑_{n ≤ N(t)} n^{-1/2-it}`, `N(t) = ⌊√(t/2π)⌋`, `θ` the Riemann–Siegel theta,
  `Z(t) = 2 Re(e^{iθ(t)} D(t)) + O(t^{-1/4})`, `|ζ(1/2+it)| = |Z(t)| = 2|D(t)||cos ψ(t)|`,
  `ψ = θ − arg D`.
- Torus (random-phase) model: replace `(θ(t), t log p)_p` by independent uniform phases;
  `c₀(N) := E log|∑_{n≤N} X_n n^{-1/2}|` (Steinhaus random multiplicative `X`).
- `(L)`: `(1/T)∫_0^T log|ζ(1/2+it)| dt → 0`; by Littlewood's lemma
  `(L) ⟺ ∑_{γ≤T, β>1/2}(β − 1/2) = o(T) ⟺ ∀A>0: N(1/2 + A/log T, T) = o(T log T)`.
  `RH ⇒ N₀(T) ~ N(T) ⇒ (L)`; unconditionally the mean is `≥ −C log T/T` and `O(1)` (Selberg
  density). `(L)` is open: the scenario "59% of zeros in off-line pairs at distance `1/log T`"
  is consistent with every known bound (Conrey 41% on the line, Selberg tails `e^{-A/4}`).

## Frozen conjecture (RS phase-locking law)
1. `c₀(N) = (1/8) log log N + O(1)` (random-model law; pre-divisor, no ζ, no zeros).
2. `(1/T)∫_T^{2T} log|D(t)| dt = c₀(N(T)) + O(1)` (the flow follows the torus for the amplitude).
3. `(1/T)∫_T^{2T} log|cos ψ(t)| dt = −log 2 − c₀(N(T)) + o(1)` (phase locking) — equivalently
   `(L)`; implied by RH.
Ontological reversal: RH is not "where the zeros are" but "how the two AFE halves interfere":
the torus model predicts `E log|ζ| = c₀ → ∞`, RH predicts `0`. What is structurally new: a
pre-divisor statistic (1) whose value is fixed by the arithmetic of the flow, and the identification
of the whole RH-content of the geometric mean with the phase law (3).
Falsifiers: (1) fails if `c₀(N)` saturates; (3) fails if `(L)` fails (a `1/log T`-displacement
cluster of zeros). Parameter-free prediction: the constant `1/8` (and the log-variance slope
`1/4` of the torus amplitude, versus Selberg's `1/2` for `log|ζ|`).

## Evidence (pod, 2026-09-05; all jobs killed after the user's correction — no further runs)
Torus Monte Carlo (Steinhaus, `σ = 1/2`, SE ≤ 0.006): `c₀(3)=0.074, c₀(4)=0.036, c₀(5)=0.115,
c₀(10)=0.113, c₀(100)=0.200, c₀(10³)=0.248, c₀(10⁴)=0.282, c₀(10⁵)=0.303, c₀(2·10⁵)=0.310`;
fit `(1/8)log log N + 0.01` within `0.01` from `N = 10` on. Control `σ = 0.6`: `0.064 → 0.011`
(→ 0, as `E log|F(σ)| = 0` demands). sd of `log|D_N|`: `0.85 (10²) → 0.98 (2·10⁵)`, variance
slope `≈ 1/4` in `log log N`.
Flow, fixed `N`, `t ∈ [10³, 10⁶]`: `N=10: 0.114`, `N=100: 0.200`, `N=400: 0.232`, `N=1000: 0.258`
(torus values reproduced: Weyl regime).
Flow, RS regime `N = N(t)`: `T=10⁵ (N≈126): mean log|D| = 0.198, mean log|Z| = 0.0011`;
`T=10⁶ (N≈399): 0.216, 0.0006`; `T=10⁷ (N≈1262): 0.233, 0.0003`.
So the amplitude follows the torus (within `0.02`), `|ζ|` has geometric mean `1`, and
`E log|cos ψ| = −0.93` at `T = 10⁷` versus `−log 2 = −0.69` for a uniform phase.

## Verdicts (phase 4)
- Torus model of the critical line, as a model of `log|ζ|`: **FALSE** for the log-mean (given (1);
  unconditionally refuted by Selberg's `O(T)` displacement bound once `c₀ → ∞` is proved; refuted
  under RH as soon as `liminf c₀ > 0`). It is also wrong for the log-variance (`1/4` vs `1/2`).
- (1), (2): **SURVIVE PRELIMINARY ATTACK** — pre-divisor, not RH-equivalent, not in the
  literature searched (Harper's low-moment/critical-chaos results concern `∑_{n≤x} f(n)`, not the
  log-mean of the critical Dirichlet polynomial).
- (3): **BRIDGE** (= `(L)` in RS coordinates; weaker than RH, stronger than every known
  proportion result). Not a producer: the locking is Jensen's formula for the real-rooted `Ξ`.
- Relentless interrogation: the only pre-divisor route to (3) is a *source-side* proof that the
  Kronecker flow's log-mean of `Z = 2Re(e^{iθ}D)` is `o(1)` — i.e. an unconditional upper bound
  on the geometric mean of a length-`√t` trigonometric sum whose random-phase version has geometric
  mean `(log t)^{1/8}`. No mechanism is visible; every estimate that transfers from the torus
  (mean values, MV, low moments) transfers the *wrong* value.

## Lean (module `RHTower/RiemannSiegelPhaseTorusLogMean`, wired, axioms clean)
- `circleAverage_log_norm_const_add`: Jensen, `⨍ log‖a + z‖ (‖z‖=R) = log max(R, ‖a‖)`;
- `log_norm_le_circleAverage_log_norm_const_add`: a fresh uniform phase never lowers a log-mean;
- `abs_two_re_mul_eq_norm_conj_add_sq_mul`: `|2Re(zw)| = ‖conj w + z²w‖` on `‖z‖ = 1`;
- `circleAverage_comp_sq`: doubling invariance of the unit-circle average;
- `circleAverage_log_norm_conj_add_mul`, `circleAverage_log_norm_two_re_mul`:
  `⨍_φ log|2Re(e^{iφ}w)| = log‖w‖` — the torus model's prediction is exactly `E log|D|`.
Corpus assets for the deterministic side: `HardyZ`, `gammaHardyPhase`, `hardySEM` (EM-length
approximation, not RS length), `ZetaResidueUnitWeightedLittlewood` (Littlewood identity on
selected rectangles), `EntireWeightedLittlewoodLeftClosure` (zeros on the left edge),
`LevinsonLeftEdgeJensen.integral_log_norm_le_of_meanSquare`.

## Open core `[OPEN CORE]`
Prove (1) (a theorem about Steinhaus random multiplicative Dirichlet polynomials; expected via
Harper-type Euler-product/multiplicative-chaos analysis of `∑_{n≤N} X_n n^{-1/2} = ∫ F(1/2+w)N^w dw/w`),
and prove `(L)`. The RH-relevant residue is exactly `(L)`: a signed first-moment law, not a
positivity, and the first "100 %" statement at the natural scale `1/log T`.

## Next
- Paper proof of (1) or of `c₀(N) ≥ c > 0` (which already refutes the torus model under RH).
- Lean: Littlewood's floor `∫_{-T}^{T} log|ζ(1/2+it)| ≥ −C log T` from the corpus's left-edge
  Littlewood identity plus `ZetaHorizontalArgument`; `RH ⇒ ∫ = O(log T)`.

## 2026-09-05 (ii) — prime cutoff versus size cutoff, Lean

Module `RHTower/SteinhausTorusLogMean` (built, wired, axioms clean). `torusAverage k` is the
iterated unit-circle average (Steinhaus expectation over `k` phases); `torusAverage_congr` (only
torus values matter), `torusAverage_sum_add_const` (single-phase sums), `circleAverage_neg'`,
`circleAverage_log_norm_const_add_mul` (Jensen on the unit circle with a scaled phase),
`circleAverage_log_norm_one_sub_mul` (one Euler factor has log-mean `0` for `0 ≤ r ≤ 1`).

- `torusAverage_log_norm_eulerProduct`: for `0 ≤ r_j < 1`, the torus log-mean of
  `∏_j (1 − r_j z_j)⁻¹` is exactly `0` — **prime-truncated random Euler products have geometric
  mean one at every `σ > 0`**, the critical value included.
- `torusAverage_log_norm_three_pos`: the torus log-mean of `1 + z_2/√2 + z_3/√3` is strictly
  positive — **the size-truncated Riemann–Siegel amplitude has geometric mean `> 1` already at
  length three** (strictness from the arc `|1 + z/√2| < 1/√3` around `z = −1`).

Reading: the two natural random models of the critical line differ in their geometric mean. The
prime-cutoff model (Selberg/Bohr–Jessen) has `E log = 0` and variance `(1/2) log log`, matching
`ζ`; the size-cutoff model (Riemann–Siegel sum with random phases) has `E log = c₀(N) > 0`
(numerically `≈ (1/8) log log N`). The Riemann–Siegel formula converts one into the other through
the phase `θ(t)`; RH says the conversion is exact in the geometric mean. The next paper target is
`c₀(N) → ∞` (a theorem about Steinhaus random multiplicative Dirichlet polynomials); the next
RH-side target is `(L)`.

## 2026-09-05 (iii) — paper notes toward `c₀(N) → ∞` and the mollifier ceiling for `(L)`

**Exact top-layer identity (paper, Jensen).** Split `D_N = S + W` with `S` the `√N`-smooth part
and `W = ∑_{√N<p≤N} X_p p^{-1/2} G_{⌊N/p⌋}`, `G_m = ∑_{k≤m} X_k k^{-1/2}`. Conditionally on the
small primes, `W` is rotation invariant, so `c₀(N) = E log max(|S|, |W|)` exactly, and
`E[|W|² | small] = V := ∑_p |G_{⌊N/p⌋}|²/p`. Every lower bound must come from the gain
`E log⁺(|W|/|S|)`: the geometric mean of the size-truncated sum grows because the large-prime
layer is comparable to the smooth part while the smooth part fluctuates lognormally.

**Bootstrap inequality (paper, needs a small-ball input).** If Steinhaus sums satisfy the
Kolmogorov–Rogozin-type bound `P(|∑ X_j c_j| ≤ ε ‖c‖₂) ≤ Cε`, then
`E[log|W| | small] ≥ ½ log V − C₀`, and since `V ≥ (c/log N) ∑_{m≤N^{1/3}} |G_m|²/m` and
`log` of a weighted mean dominates the weighted mean of `log`,
`c₀(N) ≥ (1/log N^{1/3}) ∑_{m≤N^{1/3}} c₀(m)/m − C₁`.
This is self-consistent for every growth law `c₀(m) = α log log m` and fixes no `α`; growth must
be extracted from the fluctuation gain `E|log|S| − log|W||`, which the data put at
`≍ √(log log N)` per layer. The observed slope `1/8` is consistent with the typical
`|G_m|² ≈ (log m)^{1/4}` and energy `∑ |G_m|²/m ≈ (log N)^{5/4}` far below its mean `(log N)²`.

**Interference reading.** `Z = 2 Re(e^{iθ} D)` and `|ζ| = |D + χ D̄|`; RH says the reflected half
interferes destructively with the Riemann–Siegel sum by the factor `(log t)^{-1/8}` in geometric
mean, while for independent phases the interference is neutral (`circleAverage_log_norm_two_re_mul`).
This is Jensen's formula for the real-rooted `Ξ` in Riemann–Siegel coordinates, not a producer.

**Mollifier ceiling for `(L)` (paper).** For any Dirichlet polynomial `M` with constant term `1`,
Littlewood's lemma gives `(1/T)∫ log|M(1/2+it)| ≥ −o(1)`, and Jensen gives
`(1/T)∫ log|ζ M| ≤ ½ log((1/T)∫|ζ M|²)`. Hence unconditionally
`(1/T)∫_0^T log|ζ(1/2+it)| dt ≤ ½ log(1 + 1/θ) + o(1)` for every admissible mollifier length
`T^θ` (Conrey: `θ < 4/7`, giving geometric mean `≤ 1.66`), i.e.
`∑_{γ≤T, β>1/2}(β − 1/2) ≤ (T/4π) log(1 + 1/θ) + o(T)`. `(L)` needs `θ → ∞` (Farmer's
long-mollifier conjecture); no finite-length mollifier reaches it because the optimal mollified
mean square is exactly `1 + 1/θ`.

## 2026-09-05 (iv) — what a proof of `c₀(N) → ∞` needs, and why the crude route cannot give it

With `A = log|S_N|`, `B = ½ log V_N` (both functions of the primes `≤ √N`), a conditional small-ball
inequality for Steinhaus sums (`P(|∑ X_j c_j| ≤ ε‖c‖₂) ≤ Cε`, Kolmogorov–Rogozin type) plus the
trivial upper tail `E log⁺(|W|²/V) ≤ 1` give `E|log|W| − B| ≤ C`, hence the exact-in-spirit
lower bound `c₀(N) ≥ E max(A, B) − C`. Each branch alone is self-consistent and growthless:
`E B ≥ avg_{m ≤ N^{1/3}} c₀(m) − C'` (PNT weights and concavity of `log`), and `E A ≥ 0` (Mahler
vertex bound). Growth must come from the fluctuation gain `E(A − B)⁺`, and the recursion
`c₀(N) ≥ avg c₀(m) + E(A − B)⁺ − C''` over the tower `N, N^{1/3}, N^{1/9}, …` (about
`log₃ log N` levels) produces `log log N` growth only if the per-level gain exceeds the loss
constant by a fixed margin. Since `A` and `B` are driven by the same small primes, `A − B` has
bounded variance and the gain is `O(1)`; the observed slope `1/8` per unit of `log log N` is far
below the loss constants of the crude inequalities. A proof therefore needs sharp constants
(precise joint asymptotics of the smooth truncation and the large-prime energy), i.e. Harper-level
multiplicative-chaos analysis, not a bootstrap. Recorded so the recursion is not re-derived.

**Mollifier reading of `(L)`.** For any Dirichlet polynomial `M` with constant term `1`:
`E log|ζ| = E log|ζM| − E log|M|`, `E log|M| = (2π/T)·(off-line zero mass of M) + o(1) ≥ 0`, and
`E log|ζM| ≤ ½ log E|ζM|²`. So `(L)` follows from any detector `M` with `E|ζM|² → 1`, and the
optimal finite-length mollified mean square `1 + 1/θ` is the ceiling: `(L)` is exactly Farmer's
`θ → ∞` regime in geometric-mean form. The pre-divisor face of `(L)` is the off-line zero mass of
the mollifier itself, which under RH must equal the Jensen mean `E log|ζM|` — a statement about
zeros of a Dirichlet polynomial, but tied to `ζ` through `E log|ζM|`.
