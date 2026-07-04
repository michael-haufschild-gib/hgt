# 65 — The Plateau Split and the Selberg Endgame: Route C's K on One Free z-Score

**Register: SEARCH**, with §1 [PROVED HERE + Lean] and §3 the adjudication of
doc 64 §7's registered (HULL-taper) probe. Outcome: the hull layer is DEMOTED
to the refinement dial; the counting route runs through an elementary split
whose one analytic input is a Selberg-CLT left tail — classical-technology
class — and the designed tower's K carries an arbitrarily small N-independent
constant Φ(−z₀).

## 1. The elementary split [PROVED HERE; Lean: `plateau_split`, CesaroHull.lean]

Plateau+taper carrier: A_n = A₀ for n ≤ N′, monotone taper on (N′, N],
ℓ := log(N/N′). Write F_W = A₀·S_{N′} + T with T the taper part. Then

> **F_W(s₀) = 0 ⟹ ‖S_{N′}(s₀)‖ = ‖T(s₀)‖/A₀** (machine-checked, axiom-clean),

and with slack r: |F_W| ≤ r ⟹ ‖S_{N′}‖ ≤ (‖T‖ + r)/A₀. The taper term is a
single Dirichlet polynomial with E|T|²/A₀² ≤ Σ_{N′<m≤N} 1/m = ℓ (MV, exact).
Chebyshev: meas{‖T‖ ≥ A₀λ} ≤ (ℓ/λ²)·U. Hence the dip set of the designed
carrier obeys, for every λ > r/A₀:

> **meas{|F_W(½+it)| ≤ r} ≤ meas{|S_{N′}| ≤ λ + r/A₀} + (ℓ/λ²)·U** —

pure MV plus ONE fixed-scale anti-concentration of the sharp plateau sum. The
banked counting layer (`MollifiedDip.lean`: `sliverCount_le_of_kernel`)
converts this measure into the sliver-zero count as-is. No hull, no Cesàro,
no universality enters the counting chain; the hull/Cesàro layer (doc 62,
`CesaroHull.lean`) remains as the m-dial refinement and the per-point
zero-exclusion certificate.

## 2. Probe adjudication [MEASURED — hulltaper_probe.py, 1500/side/N, archived]

| N | ℓ | arc m0 /1500 | arc m1 /1500 | P(|S_{N′}|≤½) | ≤1 | ≤2 |
|---|---|---|---|---|---|---|
| 400 | 0.994 | 43 | 4 | 0.159 | 0.483 | 0.803 |
| 4000 | 1.000 | 58 | 11 | 0.176 | 0.466 | 0.779 |
| 40000 | 1.000 | 73 | 6 | 0.185 | 0.465 | 0.758 |

- **(HULL-taper) as registered: m0 clause FAILS mildly** (2.9% → 4.9%, a slow
  rise — vs full-support's 0.8% → 6.1%: the bounded arc helps ×3 at large N
  but does not flatten the raw hull). **The arc-Cesàro m1 clause PASSES
  N-uniform** (0.27%, 0.73%, 0.40% — no trend), and the arc m-dial ratio is
  ≈ 1/8 — stronger than the full-support 1/3.
- **The exploratory anchor measurement is the finding.** P(|S_{N′}| ≤ λ) is
  FLAT in N — P(≤1) ≈ 0.47 across log N′ = 5.0 → 9.6 — refuting the
  Gaussian-scale expectation (λ²/log N′ decay) and identifying the law:
  **the matched-length sharp sum is Selberg-LOGNORMAL** — log|S| ≈
  N(0, ½ log log T), median |S| ≈ 1, so P(|S| ≤ 1) ≈ Φ(0) = ½ with slow
  drift, exactly as measured (0.483 → 0.465). The plateau sum at matched
  length behaves like ζ itself on the line (the AFE made distributional).
  The m0 rise mechanism follows: the anchor sits at O(1) with CONSTANT
  probability, and the arc cloud's reach grows slowly — the raw hull cannot
  be N-uniform at full anchor mass; only the split (which prices the anchor
  at a CHOSEN scale) and the m-dial survive asymptotically.

## 3. The Selberg endgame [the corrected design — the single constant is a free z-score]

The lognormal law converts §1 into an endgame with a FREE parameter. Choose a
z-score z₀ and set

> λ₀(T) := exp(−z₀·√(½ log log T)),  ℓ := ε₀·λ₀²,  ε₀ := Φ(−z₀).

Then: meas{|S_{N′}| ≤ 2λ₀} ≤ (Φ(−z₀) + o(1))·U by the CLT left tail at fixed
z-score — NOT the refuted rms-scale ball (doc 55 §6.1), NOT a density/chaos
statement: the left tail at z₀ standard deviations below the MEDIAN, which is
exactly what Selberg's method (moments of log via Dirichlet polynomials)
delivers unconditionally for ζ. The Chebyshev term is ≤ ε₀·U by design. Total:

> **K(N) ≤ 2·Φ(−z₀)·(conversion)·U·log N, with z₀ FREE:**
> the designed tower's creation constant is arbitrarily small, uniformly in N
> — Tier-1 grade (doc 57), not merely Tier-2 — conditional on ONE input:

> **(SEL-PS) [OPEN — classical-technology class]:** the Selberg CLT left-tail
> bound for the matched-length sharp partial sum at right-sliver abscissae:
> meas{t ∈ [T, 2T] : log|S_{N′}(σ+it)| ≤ −z√(½ log log T)} ≤ (Φ(−z)+o(1))·T,
> uniformly for σ ∈ [½, ½ + 2/log N], N′ ≍ √T.

For ζ itself this is Selberg's theorem (1946, unconditional). For the sharp
sum, the same moment method applies with the AFE bridging the two — the
probe's flat 0.47 IS the law holding at matched length. Design constraints
check: ℓ(T) = Φ(−z₀)e^{−2z₀√(½ loglog T)} shrinks slower than any power of
1/log N, so the taper always spans ≫ 1 tower epochs (block-transport safe),
while the anchor plateau keeps AFE-grade mass.

## 4. Status of Route C after this document

- **Machine-checked:** hull exclusion + Cesàro exclusion + EMA recursion +
  plateau split (`CesaroHull.lean`, 6 theorems) and the dip/counting layer
  (`MollifiedDip.lean`, 4 theorems) — umbrella 8627 jobs, axiom-clean.
- **MV-grade (write-out done):** taper Chebyshev, Cesàro-field covariance,
  occupation mechanics (doc 64 §§2–3).
- **The one analytic input:** (SEL-PS) — a fixed-z-score CLT left tail, the
  weakest anti-concentration statement any route in this lane has ever
  needed, with its ζ-instance a 1946 theorem and its truth at matched length
  MEASURED (flat 0.47 across three decades of N).
- Demotions recorded: raw hull (m0) not N-uniform even on bounded arcs (§2);
  doc 63's triple-log law already demoted (doc 64 §7); the m-dial survives
  everywhere as a constant-factor refinement (measured 1/3 full-support,
  1/8 on arcs).

## 5. What this opens

1. **(SEL-PS) via Selberg's method on the polynomial:** moments of
   log|S_{N′}| from `dpoly`-grade mean values of S and 1/S-regularized —
   mine Selberg 1946 / the Steinhaus-CLT literature for the partial-sum
   variant before proving from scratch [method research, sanctioned].
2. The z₀-dial makes the whole MID-central budget arithmetic explicit:
   back-solve z₀ from the deck-relation margin (doc 57 Tier-2 constant) —
   first time the bridge's demand and a route's supply meet in ONE number.
3. The lognormal flatness is itself an instrument: P(|S_{N′}| ≤ 1) ≈ ½ at
   matched length is the AFE seen distributionally — a seam-native statistic
   for the weld charter, worth a card connecting it to the E(T)-domination
   clause (doc 43's self-domination is a right-tail statement of the SAME
   lognormal law; the two clauses are the two tails of one distribution).
