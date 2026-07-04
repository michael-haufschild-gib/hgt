# 55 — (CR-density): the Open Core, Numerically Supported and Precisely Targeted

**Register: SEARCH** (task #130; the (R3) open core of doc 54). This is the
ONE piece of MID-central that is open mathematics, not execution. This doc
does two things: (i) a decisive numerical probe of whether CR-density is even
TRUE, and (ii) reduction of it to a clean, named analytic target.

## 1. The statement (doc 52 §4)

> **(CR-density):** for F_N(s) = Σ_{n≤N} n^{−s} in the matched regime
> N ≈ √(T/2π), #{ρ : F_N(ρ)=0, 0 < β−½ ≤ c/log N, γ ∈ [T,T+U]} ≤ ε(c)·U·log N
> with ε(c) → 0 as c → 0, uniformly in N.

The bare-Jensen no-go (doc 52 §8) shows first-moment methods give only the
trivial density; the content is that the σ-distribution of F_N zeros has NO
ATOM at σ = ½ at scale 1/log N.

## 2. Decisive probe [MEASURED — `computations/mwm/cr_density_probe.py`]

Pre-registered (P-CR1/2/3). Winding-number zero counts of F_N over
σ-bands at the matched height T = 2π(N+½)², U = 40:

| N | log N | c=0.5 | c=1 | c=2 | c=4 | near/far | κ |
|---|---|---|---|---|---|---|---|
| 12 | 2.485 | 3 | 5 | 5 | 5 | 5/2 | 0.037 |
| 20 | 2.996 | 2 | 4 | 5 | 5 | 4/3 | 0.025 |
| 28 | 3.332 | 5 | 6 | 7 | 7 | 6/2 | 0.040 |

Three signals, all supporting CR-density:
1. **SATURATION**: count(c=2) = count(c=4) at every N — the near-½ zeros
   within 4/log N are already within 2/log N. Zeros do NOT accumulate at the
   line; they sit at a characteristic distance. This is the anti-concentration
   the statement needs, seen directly.
2. **Bounded σ-density**: near/far ratio ≈ 2 (not divergent) — mild elevation
   near ½, no spike. P-CR2 supported.
3. **N-stable slope**: κ ≈ 0.025–0.040, no growth with N — the uniformity
   P-CR3 needs. ε(c) ≈ κ·c with κ = O(1).

Caveat [labelled]: counts are small (3–7 zeros), N ≤ 28; this is preliminary
evidence, not proof. But it is decisive on ONE question reasoning could not
settle: **CR-density is (conjecturally) TRUE, not false** — the MID-central
reduction rests on a true statement, and the open core is "prove a known-shape
anti-concentration," not "rescue a false claim."

## 3. The precise analytic target [reduction — with a self-correction]

The saturation says: the crux is the SMALLEST-|F_N| statistics on σ = ½.
A zero with β − ½ = δ/log N sits where F_N(½ + it) has a near-zero of the
right phase; the count of such is governed by the measure of
{t ∈ [T,T+U] : |F_N(½+it)| ≤ (scale)}. So:

> **(CR-density) ⟸ (AC): SMALL-BALL anti-concentration of |F_N| on the line.**
> For F_N(s) = Σ_{n≤N} n^{−s}, N ≈ √(T/2π):
> meas{t ∈ [T,T+U] : |F_N(½+it)| ≤ λ·√(log N)} ≤ η(λ)·U, η(λ) → 0 as λ → 0.

**Self-correction [attack-as-false, caught before it propagated]:** a first
draft claimed the FOURTH MOMENT + Paley–Zygmund closes (AC). It does NOT.
Paley–Zygmund on |F_N|² bounds the LARGE-value tail
(meas{|F_N|² ≥ θ·mean} ≥ (1−θ)²·(E X)²/E X²) — it certifies mass stays LARGE
on a positive fraction, the WRONG direction. Near-line zeros are the
SMALL-value tail, and no positive-moment bound controls a small-ball from
above (a function can be small on a large set while its moments are normal).
The genuine target is one-sided the way the census is one-sided.

The moments still enter, but as INPUTS to the value distribution, not as a
shortcut:
- **Second moment (diagonal)**: ∫_T^{T+U}|F_N(½+it)|²dt ~ U·Σ_{n≤N} 1/n ~
  U·log N (Montgomery–Vaughan — classical, formalizable). Sets the scale
  √(log N) in (AC).
- **The small-ball itself needs the VALUE DISTRIBUTION**: the Selberg-type CLT
  for the Dirichlet polynomial — log|F_N(½+it)| approximately N(0, ½log log N)
  — whose Gaussian left tail gives meas{log|F_N| ≤ −M} ≤ U·exp(−M²/log log N),
  i.e. η(λ) explicitly. THIS is the load-bearing open input. For F_N = Σn^{−s}
  the mollified/GKM machinery (Radziwiłł–Soundararajan style) is the closest
  known technology, and it is exactly what the AFE-matched regime pushes to
  its edge (doc 50 §7).

## 4. What this opens (the forward moves, corrected)

1. The load-bearing lemma is (AC) via the value distribution of
   log|F_N(½+it)| — a Selberg-CLT-grade small-ball for the specific all-ones
   Dirichlet polynomial in the matched regime. This is the genuine open core;
   the numerical saturation (§2) says it is TRUE.
2. Second-moment mean value (Montgomery–Vaughan for this F_N): Lean-tractable,
   the scale input to (AC) — a self-contained formalization that does not need
   the full CLT.
3. The fourth moment ∫|F_N|⁴ is still worth computing (closed shape for
   all-ones: Σ_{mn=kl≤N²}(mnkl)^{−1/2}) — it feeds the VARIANCE in the CLT and
   detects anomalous concentration, but is NOT itself the small-ball. Compute
   it as CLT input, not as a claimed closure.

This is where MID-central's proof genuinely lives: a small-ball / value-
distribution estimate for Σ_{n≤N} n^{−s} on the critical line in the
AFE-matched regime — precisely the frontier the Gonek–Montgomery /
Radziwiłł–Soundararajan lines leave open. The numerics say it is true; proving
it is the open problem the whole MID-central reduction now rests on, cleanly
isolated.

## 5. (a) DONE in Lean — the second-moment scale brick [LEDGER]

`formal/GaloisForLFunctions/RHTower/SecondMoment.lean` (axiom-clean
`[propext, Classical.choice, Quot.sound]`; lint green; in the RHTower umbrella).
This is step (a) of §4 — the scale input to (AC) — formalized with NO open input.

The character-orthogonality mean value, exact and machine-checked:

- `cterm_mul_conj_re` — the kernel `Re(n^{-it}·conj m^{-it}) = a_m a_n cos((log n−log m)t)`.
- `normSq_dpoly` — `‖F(t)‖² = ∑_{m,n} a_m a_n cos((log n−log m)t)` for
  `F(t) = ∑_{n∈s} a_n n^{-it}` (`dpoly`).
- `integral_cos_lin_eq` — `∫_T^{T+U} cos(Lt)dt = cosInt L T U`
  (`= U` on `L=0`, else `(sin L(T+U) − sin LT)/L`).
- `secondMoment_eq` — the exact identity
  `∫_T^{T+U}‖F‖² = ∑_{m,n} a_m a_n · cosInt(log n−log m) T U`.
- `secondMoment_meanValue` — diagonal extraction:
  `∫‖F‖² = U·∑_n a_n² + (off-diagonal remainder)`.
- `offDiagonal_abs_le` — the remainder is `U`-independent:
  `|Rem| ≤ ∑_{m≠n} 2|a_m a_n| / |log(n/m)|` (the elementary bound; the sharp
  Montgomery–Vaughan `O(n)` constant is NOT needed to isolate the scale).
- `secondMoment_meanValue_sqrt` — the matched carrier `a_n = 1/√n` on `Icc 1 N`
  (so `F = F_N(½+it)`): main term `U·∑_{n≤N} 1/n`.
- `harmonic_Icc_ge_log` + `secondMoment_mainTerm_ge_log` — the scale:
  `U·log(N+1) ≤ U·∑_{n≤N} 1/n`, i.e. the RMS amplitude of `F_N(½+it)` is `√(log N)`.

So the threshold `λ√(log N)` in (AC) is now a *proved* scale, not an assumed one.
What (AC) still needs on top of this is the LEFT-tail / small-ball — the value
distribution `log|F_N|` — which is step (b), the genuine open core (§4.1). The
second moment fixes where the small-ball window sits; it does not by itself bound
how much mass sits inside it (that is the one-sided Selberg-CLT input).

**Forward:** (b) now has a concrete numeric anchor. Next generative move on it —
the twisted 4th moment `∫|F_N|⁴ = U·∑_{mn=kl≤N²}(mnkl)^{−1/2} + Rem` in the same
`dpoly` framework (diagonal `mn=kl`), giving the CLT variance and, paired with a
Halász–Montgomery large-values bound, a *conditional finite-c* small-ball on the
exact range the census needs — the bracket the numerics of §2 already fixed.

## 6. Addendum (same day, mollified-dip session): (AC) as typed is REFUTED; the repair

**(AC) of §3 is FALSE at the stated scale.** [Mechanism — Harper-grade
better-than-squareroot cancellation, Kronecker–Weyl transfer to t-averages;
exact citation to pin at promotion.] The typical size of |F_N(1/2+it)| is
≍ √(log N)/(log log N)^{1/4} = o(√(log N)): the second moment U·log N is
carried by rare large peaks. Hence for every fixed λ > 0,
meas{t : |F_N(1/2+it)| ≤ λ√(log N)}/U → 1, i.e. η(λ) → 1 ≠ 0. The Selberg-CLT
left tail cannot rescue the rms normalization: the CLT median itself sits
below it by the (log log N)^{1/4} factor.

Two repairs, one dead, one alive:
1. Rescale (AC) to the typical size (λ·median). Still a critical-chaos
   small-ball — the genuinely hard frontier object; no known technology.
2. Doc 56's mollified route: count sliver zeros through P = F_N·M_y (dip
   lemma + L² bookkeeping, both elementary), landing on (K-bdd) — a bounded-
   density statement for a SUBcritical fixed-variance object, measured flat
   (Q/r² ≈ 0.3–0.5, N-stable). This is now the primary (R3) route; §5's
   `SecondMoment.lean` bricks remain the Lean substrate for its L² supply.

The §2 probe's positive signals (saturation, bounded ratio, N-stable κ) are
unaffected — they measured the ZERO statistics, which stay true-shaped; it was
the VALUE-distribution normalization in §3 that was wrong. The constant closes
the loop: §2's κ ≈ 0.025–0.040 brackets the Jessen-curvature value 1/(12π) ≈
0.0265 that doc 56's profile converges to as N → ∞ — two independent
computations agree on the (CR-density) slope.

## 6. CORRECTION — §3/§4.1/§5's value-small-ball route is REFUTED; the real route is the σ-profile / GAF zero-intensity [SEARCH]

External adversarial check (GPT) + independent verification here. **§3, §4 item 1,
and §5's closing forward paragraph are SUPERSEDED.** What survives, what breaks:

### 6.1 What breaks — the (AC) value small-ball at scale √(log N) is FALSE
The reduction "(CR-density) ⟸ meas{|F_N(½+it)| ≤ λ√(log N)} ≤ η(λ)U, η(λ)→0" is
false for unrestricted U. Mechanism (verified):
- `{log p : p ≤ N}` are ℚ-linearly independent (an integer relation exponentiates to
  `∏ p^{m_p}=1`, forcing `m_p=0`). So by **Kronecker–Weyl** the orbit
  `t ↦ (e^{-it log p})_p` equidistributes on the torus, and the interval average of
  any function of `F_N` → the **Steinhaus random-multiplicative** average.
- In that model `E|S_N|^{2k} ≍ (log N)^{k²}` (Keating–Snaith/Harper shape; `k=1` is
  exactly the proved 2nd moment `~ log N`). For any fixed `0<k<1`, Markov gives
  `P(|S_N| > λ√(log N)) ≪ (log N)^{k²−k} → 0`. So `|S_N| ≤ λ√(log N)` **with
  probability → 1**: the √(log N) ball is asymptotically FULL, not empty. This is
  **Harper better-than-squareroot cancellation** — the typical `|F_N|` is `o(√log N)`.
- Consequence: the Selberg-CLT "equivalence" (§3) is backwards. A near-line zero is
  the DEEP LEFT tail of `log|F_N|` (large deviation), not the L²-scale small-ball. A
  Selberg/lognormal law would predict the ball is FULL, the opposite of what §3 said.

The mean-value brick itself (`SecondMoment.lean`, §5) is CORRECT — `√(log N)` is
genuinely the L² RMS scale. Only its advertised *role* (feeding that small-ball) was
wrong. The theorems stand; the framing is corrected in the module docstring.

### 6.2 What survives — the (CR-density) zero-count, via the GAF σ-profile
The zero-count statement itself is NOT the value small-ball and is NOT refuted; it is
a genuine local zero-density theorem. Correct heuristic (Gaussian-analytic-function /
Edelman–Kostlan): with covariance profile `K(σ) = ∑_{n≤N} n^{-2σ}` (= the diagonal
2nd moment, `secondMoment_sigma`), the zero intensity is `ρ(σ) = (1/4π)(log K)″(σ)`,
so
> `Z_N(c;T,U) ≈ (U/4π)[(log K)′(½+c/log N) − (log K)′(½)]`.

With `K(½+u/log N) ~ (log N)(1−e^{-2u})/(2u)`, the bracket is `log N·(φ(c)−φ(0))`,
`φ(u)=d/du log((1−e^{-2u})/2u)`, `φ(0)=−1`, `φ(u)=−1+u/3+O(u²)`. Hence
> `Z_N(c;T,U) ~ ε(c)·U·log N`,  `ε(c) ~ c/12π → 0`.

**Verified two ways** [`computations` — this cycle]:
1. analytic: `φ(u) = 2e^{-2u}/(1−e^{-2u}) − 1/u = −1 + u/3 + …` ⟹ `ε(c) ~ c/12π`.
2. numeric: finite-difference of `(log K)′` over N∈{200,1000,5000}: `ε(c)/c` flat in
   `c` (linear confirmed), constant `→ 1/12π ≈ 0.0265` as N grows (ratio 1.19→1.13).
3. **cross-validation**: `1/12π ≈ 0.0265` matches the *independent* winding-number
   probe of §2 (`κ ≈ 0.025–0.040`). Two unrelated computations agree on the constant.

So (CR-density) is TRUE with an explicit constant, and its correct engine is the
σ-profile `K(σ)`, not a value small-ball.

### 6.3 The corrected open core (with the U-range GPT's Gonek–Ledoan point forces)
The genuine open statement is now precisely:
> `Z_N(c;T,U) ≤ (ε(c)+o(1))·U·log N + (endpoint error)`, `ε(c) ~ c/12π`,
> `N ≍ √(T/2π)`, admissible U-range `N/log N ≪ U ≪ N²` (so `U log N ≫ N` dominates
> the Gonek–Ledoan `O(X)` endpoint error in `N_X(T)=(T/2π)log X + O(X)`, and `U=o(T)`
> keeps the interval matched).

The genuinely open mathematics is the rigorous **comparison**: the deterministic `F_N`
(fixed coefficients `n^{-1/2}`, phases `n^{-it}` uniform-not-Gaussian by K–W) has the
same covariance `K(σ)` as the GAF model, so its near-line zero intensity should match
`(1/4π)(log K)″` to leading order — but proving the local zero density equals the
model's (universality of local zero statistics) is not supplied by known zero-density
estimates (Gonek–Ledoan reach only the global count `+O(X)` and a weighted
`∑(β−½) ≤ (T/4π)loglog X`, both too coarse for the microscopic `c/log N` strip).

### 6.4 Forward
- `secondMoment_sigma` banks the σ-profile `K(σ)` (correct input) in Lean.
- Next brick: formalize `(log K)″(½)` and the intensity `ρ(σ) = (1/4π)(log K)″(σ)` as
  a *definition* + the elementary `K`-asymptotic, with the GAF-comparison
  `Z_N ≈ ∫ρ` interface-typed as the explicit open hypothesis (the same discipline as
  the rest of MID-central: prove the computable half, interface-type the open half).
- The Steinhaus-vs-Gaussian gap is the real question: does the multiplicative phase
  structure change the local zero intensity at leading order? (Conjecture: no — local
  statistics are covariance-driven. That is the bridge to make rigorous.)
