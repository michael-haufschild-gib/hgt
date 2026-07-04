# 50 — The Lattice Collapses: the Collective Push Is a Damped Geometric Sum

**Register: SEARCH → promotion draft** (task #150; sharpens doc 49 §2(3)).
Certification: `computations/mwm/lattice_collapse_cert.py` (pre-registered P-L1–P-L4,
all PASS) and `stationary_phase_cert.out` (P-L5 PASS). Lean:
`RHTower/CascadeGeometric.lean` (task #151).

## 1. The collapse [PROVED HERE — two lines]

For integer m, m² ≡ m (mod 2), so the quadratic lattice phase of doc 49 §2
factors exactly:

> e^{−i(4πpm + πm²)} = w^m,  w := e^{−iπ(1+4p)}.

The "Gauss-type" collective push is NOT a Gauss sum at lattice order — it is a
**pure geometric sum** with unit-circle ratio w. (Certified P-L1 to 2·10⁻²⁶.)

## 2. The resonance denominator [PROVED HERE]

> ‖1 − w‖ = 2|sin(π(1+4p)/2)| = **2|cos(2πp)|**.

Zero exactly at p = 1/4, 3/4 (the quarter-phase coherence points of doc 49,
re-derived); maximal (= 2) exactly at p ≡ 0, 1/2 (mod 1). (Certified P-L2.)

## 3. The collective-push master bound [PROVED HERE]

For any **antitone nonnegative amplitude envelope** a₀ ≥ a₁ ≥ … ≥ 0 (the actual
tower amplitudes a_m ≈ 2(N−m)^{−1/2}/‖g‖ qualify on the effective range), Abel
summation against the geometric partial sums gives, for every K:

> ‖Σ_{m<K} a_m w^m‖ ≤ 2a₀/‖1 − w‖ = **a₀/|cos(2πp)|**.

Sharp (P-L3: attained, ratio → 1.0). Consequences:

1. **Bounded, not √M.** Away from quarter-points the whole tail's net push is
   O(a₀) — stronger than doc 49's conjectured square-root cancellation. No Weyl
   differencing is needed at lattice order; `norm_geom_sum_le` (banked) is the
   per-envelope ingredient and `sum_range_by_parts` the assembly.
2. **Marginal dominance quantified.** At p ≡ 0, 1/2: the entire sub-marginal
   tail pushes at most a₀/2 net (‖1−w‖ = 2) — the marginal term is at least
   half of everything, at all orders of the tail.
3. **The only unbounded regime is quarter-phase coherence**, amplification
   1/|cos 2πp|: 1.0 at p=0, 2.72 at the measured survivor edge p = 0.19, 15.9
   at p = 0.24, ∞ at 1/4.

## 4. Where the collapse breaks: the drift [PROVED HERE — exact step angle]

The exact per-entry step angle at offset m from the matched level N
(t = 2π(N+p)², certified P-L4) is Δ(m) ≡ −π(1 + 4p_eff(m)) mod 2π with

> p_eff(m) = p + (m+p)(m+p+1)/(2(N−m)) + (m+p)²/(4(N−m)²) + 1/(6N) + O(m²/N²).

The lattice is locally exact with a slowly drifting rotation number:
dp_eff/dm ≈ m/N. Three scales:
- **m ≲ N^{1/3}**: drift-accumulated phase error 2πm³/(3N) < O(1) — the pure
  collapse governs (doc 49 §4(4)'s effective tail, now with the constant 2π/3).
- **m ~ √N**: p_eff has moved through a full coherence cycle — every tail
  segment of length √N sweeps past a quarter-point once.
- **m ~ N**: the collective sum is the partial sum of the Dirichlet series
  itself; blockwise the bound of §3 applies with p → p_eff(block).

The drift is not an error term: it is the **mixing mechanism** — at frozen
lattice order an aligned pair could ride one phase forever; the drift rotates
every alignment (doc 51 uses this as the de-randomizer).

## 5. The Riemann–Siegel consonance [structure; numerator PROVED via P-L5]

The classical RS correction at t = 2π(N+p)² is
(−1)^{N−1}(t/2π)^{−1/4}·cos(2π(p² − p − 1/16))/cos(2πp): the SAME denominator
as §3. The cascade re-derives the RS resonance denominator from the geometric
collapse — the RS remainder is the equilibrium residue of the birth–death
cascade at the truncation edge. The birth-layer counterpart (certified P-L5,
error exactly (2π/3)d³/N): the marginal term's stationary phase value is

> φ_res(t_p) ≡ πn₀ − 2πd² + π/8 (mod 2π),  d = signed distance of √(t/2π) to
> the nearest integer n₀,

so the resonant push magnitude is B(p) = |cos(π/8 − 2πd²)| — **1-periodic in p
through d(p)²** while the tail push of §3 is ½-periodic. Numerology: B(0) =
0.924, B(1/2) = 0.383 (2.4× suppression), B(1/4) = 1 (strongest births exactly
where the sweep diverges — the collision zone). Gabcke's explicit RS-remainder
bounds become transplantable quantitative input for the birth layer.

## 6. Census grading of the doc 49 predictions [MEASURED — archived data only]

125 archived odd events (census2 + oddclass), 19 mid-band survivors:
- **(P-QP2) PASS, decisive**: 0/19 survivors near p = 1/2 (nearest 0.306;
  uniform-null 0.0042). Survivor support = {d(p) ≤ 0.194} exactly; the middle
  (0.194, 0.855) is EMPTY.
- **(P-QP1) consistent, confounded**: 5/19 within 0.125 of quarter-points
  (null 0.032) — not independent evidence beyond the d ≈ 0 concentration.
- **New measured fact**: births themselves are 1-periodic — 42/106 shallow
  events within 0.125 of p ≡ 0 vs 14/106 near p = 1/2 (uniform: 26.5).
- **Refutation**: the tail-push law ALONE (½-periodic) predicts survivor
  re-appearance at p ≈ 0.35–0.4 (amplification only 1.7); census forbids it.
  The survival law is **phase-value-governed**: support matches
  {2πd(p)² ≤ 0.236 rad} — doc 46's measured Δφ* ≈ 0.23 was this law without
  its mechanism. Named (HOLD-phase); mechanism and bookkeeping in doc 51.

## 7. Position against the printed regime [verified from Roy–You full text]

Roy & You (arXiv:2411.08364, read in full; generalizing Gonek–Montgomery IMRN
2013 no. 20 — G–M's own text paywalled, their theorems as restated there):
Spira: Z̃₁, Z̃₂ satisfy RH; G–M: for fixed N ≥ 3, 100% of zeros of Z̃_N on the
line as T → ∞. Roy–You's counting (their Thm 1.3) holds for T ≥ T_a N^γ, any
γ > 1 — **valid in the matched regime N ~ √(T/2π)** — but the on-line lower
bound (Thm 1.6) carries error O(U log N) from the Littlewood-lemma budget: at
matched length log N = ½log(T/2π), that error is the order of the frame main
term (A/π)U log T. The 100% conclusion degrades to a constant-dependent
proportion: **the mid-band question at matched length lives inside the moment
method's error term.** Their on-line mechanism (eq. 19) is the weld identity —
ζ_N(½+it) = |F_N|e^{iφ}(1 + e^{i(θ−2φ)}) — read as phase-mismatch crossings;
doc 52 transplants it for the creation rate.

## 8. What this opens

1. Doc 51: the de-randomized walk — rotation + drift + (HOLD-phase); the
   survival floor and the derivation of the d ≤ 0.194 support.
2. Doc 52: creation rate via the Roy–You identity — births = tangential
   crossings; A′(t) = θ′ − 2Im(F_N′/F_N) prices births by near-line zeros of
   the NAKED partial sum (no FE) — classical-shaped open lemma.
3. Lean (#151): §1–§3 are fully formalizable now (collapse, denominator,
   Abel-geometric bound); §4's step-angle identity is finite algebra + one
   log-Taylor bound — second pass.
4. The RS consonance invites the reverse transplant: read Gabcke's C₁, C₂, …
   correction hierarchy as higher cascade corrections — candidate exact
   birth-depth law B(p)·(1 + c₁(p)/N + …).
