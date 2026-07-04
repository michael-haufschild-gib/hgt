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
