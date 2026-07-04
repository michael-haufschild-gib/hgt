# 72 — (EFF-M14) Under Attack: Two Walls, the Thickness Dodge, and the Collapse onto the Sharp Truncation

**Register: SEARCH** (task #17, released). Outcome of attack-as-false run on
(EFF-M14) BEFORE proving it: the object as specified (Gaussian 14th moment
of log|ζ|) is doubly unusable at its own onset heights — and the wreckage
reassembles into a simpler, stronger architecture. §§1–5 derivation
[PROVED-sketch where marked]; §6 pre-registered predictions (bind, written
before the §7 run); §7 probe results; §8 corrected design point.

## 1. Wall 1: the zero-dip floor [the missing term in every small-ball estimate of this lane]

Every on-line zero γ of ζ (a positive proportion of all zeros,
unconditionally — Levinson/Conrey) forces |ζ(½+it)| ≤ λ on an interval of
width ≈ 2λ/|ζ′(γ)|. Hence, LINEARLY in λ:

> meas{t ∈ [T,2T] : |ζ(½+it)| ≤ λ} ≥ c_fl(T)·λ·T,
> c_fl = 2·(density)·⟨1/|ζ′(γ)|⟩-grade.

Median-based heuristic: |ζ′(γ)| ~ (logT/2π)·|ζ(half-spacing away)| ⟹
c_fl ≈ 2 (T-independent); the inverse-lognormal mean instead gives
c_fl ~ 2(logT)^{1/4} — but that heavy-tail part double-counts the Gaussian
tail (near-pair events). Truth in between: MEASURED in §7. Consequence at
the doc 71 design point (λ₀ = 5.4e−3, budget αε₀\* = 8.4e−4): the floor
c_fl·λ₀ ≈ 1e−2-grade EXCEEDS the budget by ~10×. **Docs 65/67/69/70/71 all
priced the small-ball by the lognormal tail alone; below λ ≈ e^{−2σ²}-grade
the floor dominates, and the design λ₀ sits deep inside that regime.**
(Consistency: Selberg's CLT is not contradicted — the floor at fixed z is
absorbed by his O((logloglogT)²/√loglogT) error, and this identifies a
concrete mechanism inside that error term.)

## 2. Wall 2: the finite-height moment wall [kills (EFF-M14) as specified]

Gaussian 2k-th moments of the prime sum P_X = Σ_{p≤X} p^{−½−it} need the
diagonal to dominate collisions: s₁ := Σ_{p≤X}1/p ≫ k²·s₂,
s₂ := Σ 1/p² ≈ 0.45. MV forces X^{2k} ≲ T, so s₁ ≈ loglogT − log(2k+1).
At T = 10^17, 2k = 14: s₁ ≈ 3.7 − 2.7 = 1.0 ≪ k²s₂ ≈ 22. **The M14 tier of
doc 71 is a fiction at its own onset: Gaussian 14th moments are available
only where loglogT ≫ 50, i.e. T beyond e^{e^{50}}.** The honest orders at
T ~ 10^13–10^18 are k ≤ 2–3, and even k = 3 is marginal (k²s₂ ≈ 4 vs
s₁ ≈ 2). Sharper form — **the degree-budget principle**: at height T, any
polynomial-method statement (moments, Chernoff, resonance) about the
dominant-variance block (p ≤ 10³ carries ~60% of ½loglogT) is limited to
degree D ≈ logT/log10³ ≈ 4.3 at T = 10^13. At the verified-range boundary
one OWNS the 4th moment and nothing more. This quantifies exactly why the
finite-height meeting is a constants war fought at k = 2.

## 3. The dodge for Wall 1: width-refined counting [structural, Lean-banked]

The floor's dips are THIN: width ~ λ₀·(2π/logT)-grade ≪ h = c/logN (factor
~100 at the design point). The dip lemma (doc 56 §2) guarantees each sliver
zero h of sublevel measure inside a 2h-interval — floor mass per such
window is only ~h·O(λ₀), never the required h. So refine the counting:

> **count ≤ vol(E_thick)/h, E_thick := {t ∈ E : meas(E ∩ [t−2h, t+2h]) ≥ h}**

(same proof: the disjoint dip intervals J_i each hold ≥ h of E, so
E ∩ J_i ⊆ E_thick). And by Fubini–Markov, if E = E_tail ∪ E_floor with
per-window floor mass ≤ h/2, then vol(E_thick) ≤ 8·vol(E_tail): **the floor
exits the budget entirely at an O(1) cost.** Lean: `thick_dips_count_le` +
`thick_part_measure_le` (ThickDips.lean, banked this cycle). Typed residue
**(FLAT-ZERO)**: windows where an anomalously flat on-line zero (near-
multiple) digs a WIDE dip can fake thickness; unconditionally this is a
small-gaps/cluster clause (second moment of local zero counts — Fujii-
grade), kept as a named clause, not solved here. Note it is parity-EVEN
machinery faking parity-odd events — a refinement that counts only odd
events would kill it structurally.

## 4. The collapse: the taper is vestigial; the carrier is the sharp exact-FE truncation

Attack on the taper's Chebyshev pricing found it absurdly wasteful near
onset: pointwise ‖Δ(½+it)‖ ≤ A₀·(N−N′)/√N′ = A₀·Nℓ/√N — at feasibility
Nℓ ≈ 1 this is A₀/√N, EXPONENTIALLY small. Then the question inverts: with
sup-norm accounting the taper term vanishes — so why carry a taper at all?
Setting ℓ = 0 (sharp carrier, Z_W = A₀·g_N, doc 22's anneal object):

- **Domination is trivial:** D_W = E_HL only, pointwise ≤ 1.463 t^{−1/4} +
  0.127 t^{−3/4} (doc 71 §1 items 7–8, explicit). No (DOM-W) threading
  needed at all; boundary threading merely avoids ζ-zero neighborhoods
  (bad measure ~ T^{−1/4}(logT)^{1/4} — negligible).
- **Creation:** dips of Z_g on the line = small values of ζ (transfer exact):
  count ≤ (1/h)·vol(E_thick{|ζ| ≤ λ₀}) ≤ (8/h)·vol{tail part} — the floor
  dodged by §3, the tail priced by §2's honest low moments.
- The plateau split, the taper design, ℓ, α — all scaffolding, now removed.
  **The parity carrier the lane spent docs 61–71 designing is ζ's own
  matched truncation g_N — the doc 22 object — with no free parameters
  except the dip threshold λ₀.** The whole Route C-direct spine reduces to:
  ladder → window relation (on g_N, doc 22) → trivial domination (explicit
  R–S) → thick-dip creation bound → cofinality (C1/C2, doc 70 §3) →
  isolation. Constraint-not-flow sharpened: nothing is designed anymore;
  the only degree of freedom left in the entire bridge is WHERE to read.

## 5. The honest design equation and what is now load-bearing

With the taper gone, feasibility (N·ℓ ≥ 1) disappears; the onset comes only
from R–S validity: λ₀ ≥ 3t^{−1/4}, i.e. **T₀ = (3/λ₀)⁴ = e^{4A},
A := log(1/λ₀)** — brutally sensitive: one unit of A costs e⁴ ≈ 55×. The
budget chain (thickness factor 8 × split fractions × (1+η)) fixes A via the
k=2 tail: A ≈ (3σ⁴(1+η)·(splits)/ε₀\*)^{1/4} + s_B. Meeting the rigorous
boundary 3·10^12 needs A ≤ 6.1; first-pass stacks give A ≈ 7–8 (T₀ ~
10^{13}–10^{16}) — the gap is a factor 2–10 spread across named constants
(thickness 8, splits, η, C′), not a new theorem. Load-bearing chunks, typed:

- **(EFF-M4):** explicit 4th moment of the prime sum(s) — MV explicit
  (Montgomery–Vaughan O\*(3πn)) + Rosser–Schoenfeld Mertens + exact
  collision terms. In reach; k=2 satisfies the §2 corruption condition.
- **(EFF-E):** the Selberg-decomposition chunk: log|ζ(½+it)| = ReP_Y +
  E_smooth + E_zero with E_zero supported in thin zero-dips (→ §3 dodge)
  and E_smooth given effective low moments. THE genuine Selberg-machinery
  effectivization; classical-shaped.
- **(FLAT-ZERO)** clause (§3) and the thickness/split constant stack (§5).
- Dead detours recorded: mollified small-ball detector (V ~ 1/θ ≫ budget —
  zero-proportion tool, not a 1/512 tool; killed twice); (EFF-M14) as
  specified (Wall 2); Chebyshev taper pricing (superseded by sup-norm, then
  by ℓ = 0).

## 6. Pre-registered predictions [written BEFORE the §7 run; these bind]

Probe: Z(t) on [T, T+U], T ∈ {10^6, 10^7, 10^8}, dense grid + refinement;
sublevel decomposition by connected components; zeros and |Z′(γ)| by local
fit. h_acc := 0.25/log√(T/2π).

- **P-F1 (floor law):** meas{|Z| ≤ λ}/(U·λ) → c_fl constant for λ below a
  crossover; c_fl(10^6) ∈ [0.6, 8] (heuristic center ~2–4); growth from
  T=10^6 → 10^8 by factor ≤ 1.3 (i.e. much closer to c_fl ~ 2 const than
  to (logT)^{1/4}-heavy).
- **P-F2 (floor dominance):** at λ = e^{−2σ_T²}-grade (σ² = ½loglogT), the
  floor (zero-dip component mass) is ≥ ½ of the total sublevel measure.
- **P-F3 (thinness — the decision prediction):** at λ ≤ 0.02, the fraction
  of sublevel measure in components of width ≥ h_acc/2 is ≤ 20%. If this
  FAILS (thick floor), §3's dodge dies and the whole §4 architecture needs
  the (FLAT-ZERO) clause quantitatively — record loudly either way.
- **P-F4 (harmonic consistency):** Σ_γ 2/|Z′(γ)| per unit height matches
  the λ→0 slope c_fl within 35%.
- **P-F5 (moment corruption, Wall 2 check):** the empirical ratio
  E(log|Z|)^{6} / [15·σ̂⁶] at T = 10^7 lies in [1.5, 30] (far from Gaussian,
  confirming high moments are corrupted at accessible variance) while
  E(log|Z|)²/σ̂² ∈ [0.7, 1.5] (second moment healthy). σ̂² := measured
  variance of log|Z| itself.

## 7. Probe results [MEASURED — probe_floor.py, runpod, archived; validation vs mpmath: max err 2.2e-6]

T ∈ {10^6, 10^7, 10^8}, U ∈ {3000, 1500, 600}, 10,710 zeros total. Verdicts
against §6 (all five bind):

- **P-F1 PASS.** meas{|Z|≤λ}/(Uλ) is FLAT in λ across [10^{-3}, 5·10^{-2}]
  (e.g. at 10^6: 0.609, 0.607, 0.605, 0.605, 0.607, 0.603 — a 1%-flat
  line). c_fl = 0.61 / 0.64 / 0.68 at 10^{6,7,8} — in band, at its bottom
  edge (the heavy-tail heuristic 2(logT)^{1/4} ≈ 4 was 6× high; the median
  heuristic 2 was 3× high). Growth 10^6→10^8: ×1.11 — slow, roughly
  (logT)^{1/4}-paced.
- **P-F2 PASS (overwhelmingly).** At λ ≤ 0.05 the sublevel set is 100%
  zero-dip components (zerocomp = 1.000); even at λ = 0.01 it is 81–96%.
  The floor is not half the story at design depths — it is the whole story.
- **P-F3 PASS — the dodge is validated.** Thick-fraction (width ≥ h_acc/2)
  at λ = 0.01: 4.5% / 5.7% / 6.5%; at λ = 0.002 (design-λ₀ scale): 0.8% /
  1.1% / 0.0%. The width-refined counting removes ≥ 99% of the floor at
  the design threshold. (Edge-note: at λ = 0.02, T = 10^8 the fraction is
  21.9%, breaching the 20% band — thickness onset moves in slowly; the
  design threshold sits well below it.)
- **P-F4 PASS to three digits.** Harmonic sum Σ2/|Z′(γ)| per unit vs λ→0
  slope: 0.610 vs 0.609; 0.641 vs 0.639; 0.676 vs 0.676. The small-ball at
  depth IS the harmonic zero-sum — the floor mechanism is confirmed
  exactly, not statistically.
- **P-F5 PASS.** μ₂/(½loglogT) = 1.48/1.46/1.46 (top of band): the
  variance carries a stable finite-height offset **σ² = ½loglogT + 0.65**
  (measured 0.63/0.64/0.67). Moment corruption: μ₄/3σ⁴ ≈ 1.5 (all three),
  μ₆/15σ⁶ = 4.1/3.8/3.6 — far from Gaussian at 6th order, mildly declining
  in T, consistent with Wall 2's s₁-vs-k²s₂ mechanism at loglogT ≈ 2.7.

## 8. Corrected design point [arithmetic on §7's numbers]

Sharp-carrier chain: count ≤ (1/h)·vol(thickPart) ≤ (8/h)·vol(tail-part)
[ThickDips.lean] with the floor (≈ c_fl·λ₀·U, c_fl ≈ 0.7–0.8 extrapolated)
excluded by thinness (measured ≥ 99% exclusion; (FLAT-ZERO) clause carries
the unconditional per-window bound — no wide floor dip was observed in
10,710 zeros at λ ≤ 5·10^{-3}). Budget: tail-fraction ≤ ε₀\*/8. Markov at
2k-th moment with MEASURED corruption (η₄ = 0.5, η₆ = 2.6) and split
between prime-chunk and E-chunk:

> A(k=2) ≈ 14 ⟹ T₀ = e^{4(A+1.1)} ~ 10^{26};
> **A(k=3) ≈ 8.8–9 ⟹ T₀ ~ 10^{17.5}** (first-pass stack);
> the 3·10^12 meeting demands **A ≤ 6.1**.

So current certified technology lands the onset in [10^{15}, 10^{18}]
after optimization headroom (thickness constant 8 → ~3, asymmetric splits,
segment-moments at higher k on the collision-free large primes, ε₀\*
harvest), and the meeting at the verified boundary is priced at a factor
e^{2.5}-grade in A beyond that. The precise open instrument this names:

> **(TAIL-6): a certified upper bound meas{t ∈ [T,2T] : log|Z(t)| ≤ −6.1}
> ≤ 2·10^{-4}·T at T ~ 3·10^{12}, by any unconditional method.**

Truth is not the issue — the measured tail there is ~10^{-4}-grade
(lognormal + floor, both measured); low-moment Markov is what is lossy.
The degree-budget principle (§2) says polynomial methods at T ~ 10^{13}
own only the 4th moment on the dominant block — so (TAIL-6) needs either
non-polynomial input (distributional/equidistribution structure of the
small-prime sum — 168 explicit cosines; effective Weyl on a 168-torus) or
the harvest route. Both are typed, finite, and non-open-problem-shaped.

## 9. What this opens

1. The carrier search is OVER in this lane: g_N (doc 22) is the parity
   carrier; every remaining question is about ζ's own value distribution
   (tail at A ≈ 6, floor structure, flat zeros) — the bridge is now a pure
   consumer of classical-shaped effective analytic number theory.
2. The degree-budget principle (§2) is a reusable instrument: it prices ANY
   finite-height polynomial-method claim by D = logT/log(block), and says
   the verified-boundary war is fought exactly at the 4th moment.
3. The thickness refinement (§3) is a new counting primitive for the whole
   dip family (Route B's kernel too): width is a second observable, and
   parity-odd vs parity-even events differ in it. A future odd-only counter
   (width + sign of the dip's deck reading) would remove (FLAT-ZERO).
4. If §7 confirms P-F3, the next executable is (EFF-M4) + (EFF-E) at k = 2
   with the constant stack optimized end-to-end — a bounded, fully
   arithmetic project whose success criterion is one inequality: A ≤ 6.1.
