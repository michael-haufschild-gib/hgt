# 12 — The Turán hybrid: spike recurrence at σ = 1+η, and the race that decides it

Register: SEARCH. §1 is a candidate mechanism with its own refutation trail (two bugs found
and incorporated); §2 is the decisive calculation, open. Companions: 08 §7.2 (single-test
closure), checks/c8-turan-taspect-note.md (the hybrid is literature-absent; both flanks are
proved by power sums), 11 (why the mechanism MUST consume the Euler product — it does).

## 1. The mechanism `[CONJECTURE — candidate, with named failure modes]`

Φ(t) := −ζ′/ζ(1+η+it) is UNIFORMLY (Bohr) almost periodic — unconditionally, from the
absolutely convergent Dirichlet series Σ Λ(n)n^{−1−η−it}. This is exact-class input: 11
Theorem B's counterexample has no such line (its f′/f is not a.p. on any line right of the
zeros) — so this mechanism is invisible to the soft-route closure. The chiasmus resolves:
the Euler product CAN act on the recurrence side, at σ > 1.

A zero ρ₀ = 1−δ+iγ₀ imprints on Re Φ a spike of height ≍ 1/(η+δ) and width η+δ at t = γ₀
(all zero-contributions Re(1/(s₀−ρ)) are POSITIVE at σ₀ = 1+η; on-line zeros give broad
bumps of width ≥ η+1/2). Bohr almost-periodicity forces the ENTIRE profile — spike included
— to recur within ε at every ε-translation number τ, a relatively dense set with gap L(ε).
A recurring narrow spike needs narrow constituents: by Fourier positivity, broad (on-line)
bumps of total local mass M can forge frequency-1/δ content only if M ≳ e^{c/δ}, while the
unconditional local mass bound is M ≤ C log t. So below the FORGING CEILING
t ≤ exp(e^{c/δ}), every recurrence site carries a genuine zero with β ≥ 1 − C′δ; the
quantified Reduction (06 §6 / Ingham, effective) then contradicts the forced linear count
once the height range exceeds T₁ ≈ (C·L(ε))^{1/(1−θ)}.

Refutation trail (both bugs found by attack-as-false, both survivable so far):
(i) the ambient field near γ₀ has size O(log γ₀), not O(1) — the spike is buried in VALUE
for log γ₀ > 1/δ; survived by matching PROFILES (Fourier content is additive and linear, so
the spike's high-frequency signature survives inside an ε-recurrence regardless of ambient
size); (ii) on-line clusters can forge the spike once local mass reaches e^{c/δ} — this
caps the usable height range at the forging ceiling and converts the would-be strip into a
height-dependent region. Output shape IF the mechanism survives §2: a zero-free region of
width ~ c/loglog γ — which would exceed Vinogradov–Korobov and is therefore ALSO the
strongest reason to expect §2 to kill or degrade it. The consistency question is sharp,
quantitative, and ours to settle.

## 2. The race `[OPEN — the decisive calculation]`

Everything reduces to two doubly-exponential scales:
- **Forging ceiling** T_forge(δ) ≈ exp(e^{c/δ}): above it, broad on-line mass can imitate
  the spike and the mechanism sees nothing.
- **Translation-number gap** L(ε, η): Bohr gives finiteness; the effective gap for
  Σ Λ(n)n^{−1−η−it} is governed by simultaneous Diophantine approximation of the phases
  {t log p : p ≤ P(η)} with P(η) the effective series cutoff (P ≈ e^{1/η} weighted terms).
  Kronecker-counting heuristic: matching N ≈ π(P)/… ≈ e^{1/η}/η-many phases to precision ε′
  costs L ≈ (1/ε′)^{N} = exp(c″·e^{1/η}·log(1/ε′)).

The mechanism yields a nontrivial region iff T₁ ≈ L^{1/(1−θ)} < T_forge, i.e. iff the
forging constant c beats the Kronecker constant c″ (with η ≍ δ). Both constants are
computable: c from the Fourier-positivity forging bound (Poisson kernel decay e^{−w|ξ|} vs
local zero-count C log t — C explicit from the Riemann–von Mangoldt formula), c″ from an
effective Kronecker/Weyl bound on the return times of (t log p)_{p ≤ P} — and the DIMENSION
COUNT is the crux: the spike lives at ONE height, so full-line sup-recurrence (all N
phases) may be far more than needed; a WINDOWED recurrence (Stepanov-type, matching the
profile only near γ₀ − τ) needs fewer effective phases and shrinks L. Note what 11 Thm A
gives here for free: Φ is holomorphic in s, so windowed S²-recurrence of Φ on two nearby
lines upgrades to sup-recurrence on the window — the S²-degree is available BECAUSE we are
at σ > 1. The race calculation with the windowed gap is the lane's next proof target; its
outcome is a theorem either way:
- c beats c″ (windowed): a new zero-free region — promote with extreme prejudice after the
  VK-consistency autopsy;
- c″ beats c: the mechanism is dead at σ = 1+η, and the death certificate (recurrence too
  slow vs forging too easy) quantifies EXACTLY how much a.p. rigidity the Euler product
  buys — the first measured constant on the exact-structure side of the wall.

## 3. The race, run (2026-07-03) `[DERIVATION at heuristic grade — every constant named, gaps listed]`

**Side A (forging ceiling).** Broad floor at frequency Ξ: C₀·log γ·e^{−Ξ/2}; spike content
e^{−2δΞ} (η = δ). Detection frequency Ξ₀ = log(C₀ log γ)/(½ − 2δ); spike content there
(C₀ log γ)^{−4δ}; detectable at tolerance ε₀ iff **δ ≤ c₁/loglog γ, c₁ = log(1/ε₀)/4**
(c₁ ≈ 0.17 at ε₀ = ½). Ceiling: log T_forge = e^{c₁/δ}.

**Side B (recurrence gap).** Series cutoff P = (4/εη)^{1/η}; full-line sup-recurrence must
match N ≈ P/log P prime phases to precision ε′ ≈ εδ/C; Kac/equidistribution return time
L_full ≈ ε′^{−N}: loglog L_full ≈ (1/δ)·log(4/εδ).

**Verdict 1 — full-line: DEAD, by a factor ≈ 40–55.** loglog T₁ ≈ (1/δ)log(4/εδ) vs
loglog T_forge = c₁/δ: the inner exponents differ by log(4/εδ)/c₁ ≈ 43× (δ=0.05, ε=0.05)
to 53× (δ=0.01). Death certificate, quantified: full sup-norm Euler recurrence is
doubly-exponentially too slow — the a.p. rigidity the Euler product buys at full-line
sup-norm falls short of spike visibility by a factor ~50 in the inner exponent.

**Verdict 2 — windowed: ALIVE for δ ≲ 0.02.** On a unit window the Dirichlet system's
effective dimension collapses by time–bandwidth: N_eff ≈ (bandwidth)·W/2π =
(1/2πδ)·log(4/εδ) — exponentially below N. Windowed return time:
log L_win ≈ N_eff·log(1/ε′) ≈ (1/2πδ)·(log(1/εδ))². Numerically (ε = 0.05):
| δ | log T₁ (windowed) | log T_forge = e^{0.17/δ} | verdict |
|------|------|------|------|
| 0.05 | 195 | 30 | dead (ceiling too low) |
| 0.01 | 1 417 | 2.4·10⁷ | ALIVE |
| 0.001 | 21 932 | 6.8·10⁷³ | ALIVE |
The mechanism switches on exactly in the rung regime (small δ, σ near 1) and wins its race
there by an enormous margin. The windowed-S²-to-sup upgrading it needs on the profile
window is 11 Theorem A — already proved, and legitimate here because σ = 1+η > 1.

**Output shape + the autopsy.** If made rigorous, the would-be zero-free region is
δ*(γ) ≈ (loglog γ)²/(2π log γ): numerically comparable to Littlewood's loglog γ/log γ at
moderate heights, asymptotically one loglog factor beyond it, and strictly WEAKER than
Vinogradov–Korobov (log γ)^{−2/3} — so no consistency alarm fires; as a REGION this
reduces-to-known (VK is stronger). The lane's actual prize is different: **at every
recurrence site the mechanism forces a COMPANION zero with matched narrow profile —
clustering, the (Rung_δ) hypothesis-to-conclusion step — which neither Littlewood nor VK
provides.** Littlewood's own proof is Diophantine-approximation-flavored; the windowed
mechanism is plausibly a recurrence-strengthened Littlewood — C9 check queued: if the
rigorous version collapses to Littlewood strength, the region is known but the forced
clustering remains the new object.

**Rigor gaps, named (the promotion checklist):**
(a) the time–bandwidth collapse N → N_eff for Dirichlet frequencies restricted to unit
windows (Gram-matrix/prolate-type theorem — the load-bearing new lemma);
(b) effective windowed Kronecker recurrence with positive density (effective Weyl in
N_eff dimensions — standard technology, needs assembling with explicit constants);
(c) the spike-detection converse (Fourier positivity with tolerance ε and the width-slack
constant C′ tracked);
(d) DONE — windowed S² ⟹ sup upgrading = 11 Theorem A.

## 4. The block structure — the lemma (a) attack, and the C9 audit (2026-07-03, night)

### 4.1 Window-to-blocks `[DERIVATION, heuristic grade]`
Majorize the window indicator by a Fejér window w with ŵ supported in |x| ≤ 2: the windowed
recurrence quadratic form becomes BAND-DIAGONAL in log n, and splits over blocks
B_j = {n : log n ∈ [2j, 2j+2)}, j ≤ J = (log P)/2. Each block sum has bandwidth 2 on a
width-1 window — O(1) effective coordinates per block. The recurrence event reduces to
|G_j(τ)| ≤ ε_j := w_j·ρ (ρ = εη/2, w_j = block weight ≈ 2e^{−2jη}, Σ ε_j ≤ ε/2).

### 4.2 Independence + concentration: the measure collapses further `[DERIVATION, heuristic grade]`
Distinct blocks use disjoint PRIMES (prime powers carry O(1) total weight — handled
separately), so under Haar the block sums are INDEPENDENT. Normalized block dispersion
σ_j ≈ √(2j)·e^{−j}: at (η, ε) = (0.01, 0.05), blocks j ≥ 10 have σ_j < ρ = 2.5·10⁻⁴ — the
condition holds there automatically by concentration, at NO measure cost. Only the first
j₀ ≈ log(1/ρ) ≈ 8 blocks pay, generically ρ² each:
> **μ(A_ε) ≥ exp(−C·log²(1/εδ)) — no 1/δ in the exponent.** (Generic γ₀.)
Visit density = μ(A_ε) exactly, by unconditional Weyl equidistribution of the Kronecker
flow ({log p} ℚ-independent — the prime instance of `log_prime_shifts_independent`). NO
effective/gap Kronecker needed: positive density suffices for the Reduction, and positive
density is equidistribution + open-set. T_contra ≈ exp(C·log²(1/εδ)).

Worst-case γ₀ (early block phases aligned, small-ball at an extreme mean): cost degrades
to μ ≥ ρ^{2π(Q)}, Q = e^{2j₀} ≈ (2/εδ)²: log T_contra ≈ poly(1/δ). Numerically at δ = 0.01:
1.6·10⁷ vs ceiling 2.4·10⁷ — worst case is RACE-CLOSE at δ = 0.01, and wins with room for
every smaller δ. Verdict of §§3–4: the mechanism chain survives worst case for δ small.

### 4.3 What the chain now claims, and the posture `[CONJECTURE — extraordinary, quarantined]`
If every heuristic-grade link holds at full rigor, the output is a zero-free region of
width c₁/loglog γ — beyond Vinogradov–Korobov. No known theorem contradicts it (it is not
RH-strength; the forging ceiling is intrinsic), but the strength itself is the strongest
evidence for a hidden gap. QUARANTINE: nothing here is promoted; the chain is a conjecture
factory whose links get proven or refuted ONE AT A TIME.

### 4.4 C9 audit verdicts (checks/c9-littlewood-method-note.md, fetched verbatim)
- Littlewood's loglog region is the de la Vallée Poussin 3-4-1 engine + a sharper ζ UPPER
  bound; explicitly NO Diophantine/Kronecker step (two sources). Our mechanism is NOT a
  recurrence-strengthened Littlewood — different method family entirely.
- Kronecker/recurrence in the literature runs the DUAL direction only: large values /
  Ω-results (Bohr–Landau, Littlewood 1925 |ζ(1+it)| ≥ e^γ log₂t, resonance method), with
  the value-vs-density trade-off quantified. Never zero-location constraints.
- **The recurrence → zero-clustering bridge is ABSENT from the fetched corpus** — as a
  method, 12's mechanism passes the novelty gate. (Absence also means: no known reason it
  works, no known reason it fails. Virgin territory in both directions.)

### 4.5 Promotion ladder (revised; strictly one link at a time)
1. **L1 (probability, cleanest):** block independence + concentration + small-ball for
   random Euler block sums — a self-contained statement about Haar-random multiplicative
   phases; no zeros involved. Fully rigorizable now; Lean-adjacent pieces exist
   (log_prime_shifts_independent supplies the equidistribution input's arithmetic core).
2. **L2 (harmonic analysis):** the Fejér window-to-blocks reduction with explicit constants.
3. **L3 (classical):** the spike-detection converse — Fourier positivity vs the
   O(log t)-smooth ambient (whose frequency-Ξ content is ≤ 1/log t — checked) with the
   width-slack constant C′ tracked.
4. **L4 (done):** windowed S² ⟹ sup = 11 Thm A; Weyl equidistribution = classical.
The chain is only as strong as its weakest link; L1 first, then L2 — either a proof or the
long-sought bug. Both outcomes are theorems about the exact-structure side of the wall.

## 5. L1 opened: rotation invariance, and the self-repair dichotomy (2026-07-03, late)

### 5.1 Rotation invariance kills half of L1 `[DERIVATION — clean]`
The block variable is Y_j = Σ_{p∈B_j} c_p u_p x_p with x_p iid uniform phases and u_p the
fixed γ₀-reference phases. But u_p·x_p is again a uniform phase: **Y_j's distribution is
rotation-invariant and INDEPENDENT of γ₀ entirely.** The reference height enters only
through the ball CENTER m_j (the block mean = the block sum of the Φ-series at γ₀). So L1
reduces to: radial-density lower bounds for the FIXED laws Y_j = Σ c_p x_p at radius
|m_j| — small-ball P(Y_j ∈ B(m_j, ε_j)) ≥ c·(ε_j/s_j)²·(radial factor at |m_j|/s_j).
For CLT blocks (many comparable weights) this is Berry–Esseen/Esseen with explicit
constants; the finitely many sparse early blocks (j ≲ 3) get explicit per-block densities.
The only obstruction left in L1: the radial factor dies when |m_j| ≫ s_j (large
deviation — reaching far beyond the law's bulk).

### 5.2 The self-repair dichotomy `[DERIVATION at proof-strategy grade — the discovery]`
When IS |m_j| ≫ s_j? The means are the block sums of −ζ′/ζ(1+η+iγ₀) — and by
Perron/contour-shift, LARGE block sums at height γ₀ certify ZEROS NEAR γ₀: if ζ were
zero-free in D(1+iγ₀, R) apart from ρ₀, the contour shifts into the disc and the
early-block means decay as |m_j| ≤ w_j·(e^{−2j(R/2−η)}·polylog γ₀ + spike share). So:

> **Either** all early-block means are moderate (|m_j| ≲ K·s_j) — the small-ball is cheap,
> the recurrence fires, and companions appear at the recurrence sites (density
> contradiction); **or** some early-block mean is huge — which by the Perron converse
> certifies companion zeros AT γ₀ itself. The adversarial case IS the conclusion:
> clustering either way. The mechanism is self-repairing.

This replaces §4.2's worst-case degradation entirely: no case analysis over adversarial
γ₀ survives — adversarial means are not an obstruction but the second branch of the
forcing. (The 5/3-power loss from unconditional early-block equidistribution is also
obsolete: no equidistribution of the u_p is needed anywhere — rotation invariance ate it.)

### 5.3 Revised ladder
- **L1 (probability, now half-done):** radial small-ball for Σc_p x_p at radius ≤ Ks_j —
  Berry–Esseen 2d + explicit early blocks. No arithmetic content left.
- **L5 (complex analysis, NEW):** the Perron converse — "no zeros in D(1+iγ₀, R) ⟹
  early-block means decay". Classical-shaped (contour shift); the spike's own share of the
  means must be tracked (it is the one term that does not decay).
- L2 (Fejér window-to-blocks constants), L3 (spike converse), L4 (done).
The chain's claim strength (≈ c/loglog region + forced clustering) is unchanged and stays
QUARANTINED until L1, L5, L2, L3 are theorems. Next action: prove L1 in full.
