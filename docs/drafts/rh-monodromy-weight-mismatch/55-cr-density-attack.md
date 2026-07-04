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

## 7. Synthesis (mollified-dip session, same day): two independent live routes to (CR-density)

§6's refutation of the value small-ball was found independently in the doc 56
session (same mechanism, recorded doc 56 §10); the two positive programs that
remain are DIFFERENT and complementary, and both should run:

- **Route A (§6.2–6.4, this doc): GAF σ-profile universality.** Engine: zero
  intensity ρ(σ) = (1/4π)(log K)″(σ) with K = `secondMoment_sigma`'s profile;
  open core = local-statistics universality (Steinhaus phases vs Gaussian at
  leading order). Explains the exact constant ε(c) ~ c/12π.
- **Route B (doc 56): mollified dip + (K-bdd).** Engine: every sliver zero of
  F_N digs a measurable dip of P = F_N·M_y (proved, L²-only); open core =
  (K-bdd), a FIXED-scale bounded-density statement for the SUBcritical
  mollified sum — measured flat (Q/r² ≈ 0.3–0.5, N-stable, doc 56 §9). Yields
  the consumer-sufficient ε(c) = O(√c) with explicit constants; does not need
  universality.

Cross-constraints: B's admissible window U ≫ N^{1+θ} sits inside A's
Gonek–Ledoan range N/log N ≪ U ≪ N² for θ < 1; B's measured density ≈ 0.1 near
0 is exactly the finite-N shadow of A's intensity at the mollified covariance.
If A's universality bridge stalls, B's anti-concentration is the fallback that
still closes the (R3) consumer (doc 57's Tier 1–2 budget); if B's (K-bdd)
stalls, A's intensity formula is the fallback. Either closes MID-central's
last open input.

## 7. The closed form: ε(c) is the Langevin function; its Taylor tower is ζ at negative odd integers [PROVED HERE (elementary) + CONJECTURE readings]

Prompted by the user's question "is the 1/12 related to 1+2+3+⋯ = −1/12?" — answer: yes,
through a common ancestor, and chasing it yields the closed form of the whole profile.

### 7.1 Closed form [PROVED HERE — calculus]
`φ(u) = d/du log((1−e^{−2u})/2u) = 2/(e^{2u}−1) − 1/u = coth u − 1/u − 1`, so

> **ε(c) = (coth c − 1/c)/4π = L(c)/4π**,  L = the Langevin function.

Bernoulli series `coth u − 1/u = Σ_{k≥1} 2^{2k}B_{2k}u^{2k−1}/(2k)!` + Euler
`ζ(1−2k) = −B_{2k}/2k` give the Taylor tower:

> **ε(c) = −(1/2π) Σ_{k≥1} ζ(1−2k)·(2c)^{2k−1}/(2k−1)! = c/12π − c³/180π + …**

i.e. `ε′(0) = −ζ(−1)/π = 1/12π`; the k-th odd coefficient is a shadow of ζ(1−2k)
(ζ(−1)=−1/12, ζ(−3)=1/120, …). Checked k=2 both ways (−c³/180π). The GAF near-line
zero-density profile of the matched partial sum is the EGF of ζ at negative odd integers.

Mechanism of the kinship [PROVED HERE]: the common ancestor is the Bose/Todd kernel
`1/(e^t−1)`. Zeta regularization reads its Taylor germ via Mellin continuation
(`ζ(s)Γ(s)=∫t^{s−1}/(e^t−1)dt`); our covariance profile reads the SAME germ because the
matched truncation cuts ζ's pole at s=1 with exponential profile —
`K(½+u/logN)/logN → (1−e^{−2u})/2u = e^{−u}·sinh(u)/u`. Same germ, two readings. NOT the
literal continuation to s=−1; no divergent series is regularized in our derivation.

### 7.2 Hard consistency check: Gonek–Ledoan's constant reproduces [VERIFIED reasoning]
Langevin predicts the weighted sum `Σ_{β>½}(β−½) = (U/4π)·∫ c·L′(c)dc ≈ (U/4π)·loglog N`
(since `∫₀^X cL′ = log X + O(1)`, cutoff X ~ log N). Gonek–Ledoan's PROVEN bound is
`(T/4π)·loglog X` — same 1/4π, same loglog. The GAF model is the strip-local
disintegration of the proven weighted theorem; the open GAF-comparison = promoting the
proven average to the strip-local count. This calibrates the model against a theorem.

### 7.3 Correction to §2's reading: "SATURATION" was over-read
Langevin says counts grow ~40% from c=2 (L=0.537) to c=4 (L=0.751), not flat; the §2
winding counts (5–8 zeros) cannot resolve that. Tail is POWER LAW `1−L(c) ~ 1/c`
(not exponential); `ε(∞)=1/4π` per side, total `1/2π` = the full Gonek–Ledoan density —
all zeros at scale O(1)/log N, slow approach. FALSIFIABLE PREDICTION for the
deterministic F_N (a direct test of the GAF-comparison open core): the c-profile of
near-line counts should follow L(c)/4π — ratios ε(1):ε(2):ε(4) = 0.313:0.537:0.751
(×1/4π·UlogN). A larger-U winding probe can accept/reject this against hard saturation.

### 7.4 Wild reading [CONJECTURE — bank the metaphor]
Same 1/12-family as the free boson Casimir energy (−1/24 per chiral half, c=1 CFT) and
Dedekind η's q^{1/24} — all Taylor shadows of 1/(e^t−1). Read the zero gas near σ=½ as a
1D system: `ε′(0) = −ζ(−1)/π` says the linear response of zero density to
distance-from-line is a Casimir-type vacuum coefficient of the truncation — "the
critical line has a vacuum energy," and the zeros' reluctance to leave it is priced by a
zeta-regularized vacuum term. Forward handle: if the intensity slope is a central-charge
shadow, what plays c=1? Does a weighted carrier (smoothing the truncation edge) shift
the effective central charge and hence the 1/12? — a computable question on the K-profile.

## 8. The Casimir rabbit hole, resolved: it is a VARIANCE, not a central charge [PROVED HERE (limit calculus) + probe]

Goal: fail early or extract the lead from §7.4's "critical line has a Casimir
pressure" conjecture. The decisive test (smooth the truncation edge, watch the 1/12)
is exact calculus in the matched limit — run analytically first.

### 8.1 The general weighted-carrier law [PROVED HERE — matched limit]
Log-scale carrier `a_n = W(log n/log N)/√n` (sharp cut = W ≡ 1). Substituting
`n = N^y` in `K_W(½+u/log N) = Σ W(y_n)² n^{−1−2u/log N}`:

> `K_W/log N → κ_W(u) = ∫₀¹ W(y)² e^{−2uy} dy = E_μ[e^{−2uY}]`,

the MOMENT GENERATING FUNCTION of the log-placement measure `μ ∝ W²(y)dy` on [0,1].
Hence `log κ_W` = cumulant generating function, and the GAF intensity gives exactly:

> `ε_W(c) = (E_μ[Y] − E_{μ_c}[Y])/2π`  (`μ_c` = `μ` tilted by `e^{−2cY}` — a Gibbs tilt)
> `ε′_W(0) = Var_μ(Y)/π`
> `ε_W(∞) = E_μ[Y]/2π`  (the right-of-line zero share; mean splits the zeros)

Sharp cut: `μ = Uniform[0,1]` ⟹ `Var = 1/12` ⟹ slope `1/12π`; `mean = ½` ⟹ split
`¼π : ¼π`, total `1/2π` = full density ✓. The §7 Bernoulli/ζ tower is now explained
at one level deeper: **the cumulants of Uniform[0,1] are `B_n/n`** — the ζ(1−2k)
appearance is the uniform-cumulant identity + Euler, nothing more.

### 8.2 Verdict on the conjecture
- **REFUTED (strong form).** Not a central-charge-type invariant: log-scale
  reweighting moves it as a variance. `W² = 2y` (ramp): `Var = 1/18` ⟹ slope
  `1/18π ≠ 1/12π`. Anomalies are rigid under smooth deformation; this is not.
- **PROVED (weak form).** Invariant under EVERY multiplicative-scale smoothing
  `w(n/N)`: such an edge has log-measure `O(1/log N) → 0`, so `μ → Uniform[0,1]`
  regardless of edge shape — `1/12` stable, by measure concentration, NOT conformal
  symmetry. §7.4's stability inference had the wrong mechanism.
- **CORRECTED READING.** Thermodynamic, not vacuum-energetic: `ε_W(c)` is a
  Gibbs-tilt displacement, `ε′_W(0)` a SUSCEPTIBILITY — near-line zero density =
  linear response of the coefficient measure to exponential tilting. "Casimir
  pressure" → "tilting susceptibility." The B₂ kinship with ζ(−1) survives as stated
  in §7.1 (same germ of `1/(e^t−1)`), but its carrier here is statistical (cumulants
  of uniform), not anomalous.

### 8.3 The lead: a parameterized, falsifiable dictionary + a design knob
1. **Parameterized GAF test.** The variance law predicts, for the DETERMINISTIC
   carriers: equal-variance opposite-edge pair `W²=2y` / `W²=2(1−y)` must show the
   SAME near-line slope (`1/18π`), and right:left splits `2/3:1/3`, `1/3:2/3`
   (sharp `½:½`) following the MEAN. Probe pre-registered (P-CAS1/2/3) at
   `computations/mwm/casimir_weighted_probe.py`. This tests the GAF-comparison open
   core with a PARAMETER, not one constant.
2. **The creation-rate design knob [CONJECTURE].** `Var_μ` is tunable: concentrated
   `μ` ⟹ slope → 0 ⟹ near-line births RARE in the GAF model. For MID-central this
   suggests a weighted tower whose `creation_rate` constant is designed small. The
   tension to quantify: AFE fidelity needs mass spread over [0,1]; birth suppression
   wants mass concentrated. The well-posed new question:
   > minimize `Var(μ)` subject to `F_W` remaining an AFE-grade approximation of ζ
   > on the matched window
   — an optimal-mollifier-for-birth-suppression variational problem. Mollifier
   technology reweights for moment control; this objective (suppress the tower
   carrier's near-line births) is native to the cascade program.

### 8.4 Probe adjudication [MEASURED — casimir_weighted_probe.py + casimir_leftband_probe.py, N=28/40, U=60]

Right bands (det/GAF, N=40): sharp 8/3.6, 12/6.7, 13/10.8; ramp 2/1.9, 7/4.0,
15/7.9; iramp 1/2.1, 1/3.7, 1/5.9. Splits fracR: sharp 0.39, ramp 0.70 (GAF 0.62 ✓),
iramp 0.03 (GAF 0.26 ✗✗). Left bands (N=40): sharp 5/3.7, 12/7.0, 15/11.8; ramp
0/1.7, 1/3.2, 5/5.4; iramp 3/2.5, 9/5.4, 21/10.9.

- **P-CAS3 PASS (qualitative + ramp quantitative):** splits ordered by the mean;
  ramp matches GAF; iramp far MORE extreme than the mean law.
- **P-CAS2 as registered (right bands) FAIL — but P-CAS2′/2″ PASS:** iramp's left
  counts exceed its right by ×21 and exceed the GAF one-sided prediction; the
  TWO-SIDED near-line totals of the equal-variance pair agree: ramp 20, iramp 22
  (ratio 0.91; sharp 28 with Var 1/12 > 1/18 ✓ larger). **The variance law survives
  as a two-sided law.** All carriers sit ×1.2–1.5 above finite-N GAF (the known
  finite-N inflation).
- **NEW DISCOVERY — near-line CHIRALITY, invisible to the GAF:** the SIDE of the
  near-line pile-up is set by the deterministic coefficient structure, not by K(σ).
  Monotone-decreasing carriers (iramp; frozen-term ratio W(0)/√K(½) ≈ 0.73) empty
  the RIGHT near-line strip almost completely (1 zero vs sharp's 13 at c=2);
  monotone-increasing carriers (ramp, W(0)=0) empty the LEFT. GAF predicts local
  symmetry; the deterministic zeros are strongly chiral.

### 8.5 The lead this hands to MID-central [CONJECTURE — the E–K route]
(CR-density) counts RIGHT-side near-line zeros only (0 < β−½ ≤ c/log N). The probe
shows a decreasing-weight carrier deterministically COLLAPSES exactly that count
(×8–13 suppression vs sharp at N=40). So the rabbit hole exits onto a new route:

> **Design, don't estimate.** Replace "prove ε(c)→0 for the sharp carrier"
> (value-distribution frontier, open) by "choose a monotone-decreasing tower
> carrier whose right near-line strip is provably near-empty" — an
> Eneström–Kakeya-type POSITIVITY statement (zeros of Σa_n n^{−s} with a_n > 0
> decreasing avoid a right zone), which is elementary-deterministic in kind,
> hence potentially provable AND formalizable, sidestepping the small-ball
> frontier entirely.

Open sub-questions this creates: (i) quantitative E–K for Dirichlet polynomials —
how far right of ½ does strict monotone decrease push the zero support? (Montgomery's
β ≤ 1+loglog/log for a_n=1 is the weak-monotone boundary case); (ii) does the
cascade's birth/push recursion survive a weighted tower (the pushes were derived for
sharp truncation steps Φ_N → Φ_{N+1}); (iii) the finite-N GAF-with-mean correction:
ρ = (1/4π)Δ[log K + h(|m|²/K)] with the frozen n=1 term as mean — computable, would
explain the sharp carrier's ×1.2–1.5 near-line excess.

Register note: the Casimir strong form is dead (§8.2); the corrected invariant
(two-sided Var law) is experimentally supported; the chirality/E–K design principle
is the genuinely new object this hole produced.
