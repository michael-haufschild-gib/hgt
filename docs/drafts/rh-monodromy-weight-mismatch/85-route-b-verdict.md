# 85 — Route B: the Verdict, Part I. The Premise Falls: Windowed-Divisor Criticality of the Mollified Boundary

**Register: SEARCH, carrying the terminal adjudication of goal #29 (Route B
ground to terminal state).** Companion: doc 84 (the grind ledger — audits,
machines, retractions, probes PREREG-1..5). This document is the
fork-INDEPENDENT half of the verdict: doc 56's premise is broken in a located,
mechanism-derived, measured way. Part II (§6, appended after the P-F5
discriminator lands) adjudicates the surviving branch.

## 1. The located gap [doc-82 class: an unsupported load-bearing citation]

Doc 56 §3 claims V := Σ_{m≥2} b_m²/m = O_θ(1) for P = F_N·M_y, citing
Graham's theorem for the BV taper, flagged [CHECK]. The citation covers ONLY
V_inner = Σ_{m≤N}: for m ≤ N the divisor constraint m/d ≤ N is vacuous and
b_m is the COMPLETE convolution Σ_{d|m} λ_d — Graham's object. For the
boundary band m ∈ (N, Ny] the sums are WINDOWED: b_m = Σ_{d|m, m/N ≤ d ≤ y} λ_d,
outside every complete-sum theorem. The [CHECK] was never run on the band.
The V = O(1) premise was unsupported at the exact place it is load-bearing
(κ², r*(c), and the §5 kernel normalization all consume it).

## 2. The measured law [certified-instrument grade; archive computations/mwm_kbdd/]

Deterministic scans (PREREG-4/5, falsifiable, registered before each run):

> **V(N) = −1.58 + 2.27·loglog N** (rms 2× better than any saturation fit,
> N ∈ [10³, 10⁵]); V_inner decelerates toward its Graham constant; ALL
> unbounded growth is in V_boundary (loglog-linear, share 0.53 → 0.59).
> The fitted law RETRODICTS doc 56 §9's measured V_BV(400) = 2.48 exactly —
> the "stabilizing" reading of N ≤ 400 data was loglog masquerading as a
> plateau. Robust across SIX designs: sharp μ, BV, taper dials y₁ = y^{1/4}
> and y^{3/4}, smooth inner cutoff (P-F8: slope 2.17 — the criticality is
> not the sharp edge's), θ = 1/4 (slower, still growing, and V_inner
> inflates as 1/θ — the two dials fight, doc 84 §12).

## 3. The mechanism, derived [PROVED HERE (sketch) up to the shell resummation]

Write the boundary as m = pk (p ∈ (y, N] the unique large prime — the
coefficient-vanishing lemma, Lean: `RouteBSupport.boundary_coeff_eq_zero`),
u := N/p, window k ∈ (u, uy], constraint d ≥ k/u. Expanding the square,
the (d, e) off-diagonal term carries the k-sum over multiples of [d, e] in
(u, u·min(d,e)] — with weight (1/[d,e])·ln⁺(u·g/max(d,e)), g = gcd(d,e).

> **At u = 1 (top of the p-range) the window contains NO multiple of [d, e]
> unless d = e** — pure geometry: [d,e] ∣ k and k ≤ min(d,e) force
> d = [d,e] = e (Lean: `RouteBSupport.window_diagonal_only`). The Möbius
> off-diagonal cancellation that tames the log-large diagonal
> Σ_d λ_d² ln d / d ≍ ln²y is DISABLED by the truncation geometry, shell by
> shell (the ρ = max/g ≤ u shells revive as u grows and resum against the
> diagonal). The residual of that partially-disabled cancellation is the
> measured loglog. The exact shell-resummation asymptotic is
> classical-shaped (Graham/Motohashi-class windowed mean values) and is the
> one [CHECK]-import owed at publication; nothing in the verdict depends on
> its constant. A cancellation-free sub-family (windows containing exactly
> one divisor: m = pd, p ∈ (N/q₀(d), N]) already pins V_bd ≥ c > 0
> unconditionally with b_{pd} = λ_d exactly.

## 4. What is hereby refuted, and what is not

> **[REFUTED — Route B as typed.]** The doc 56 chain with the kernel (K-bdd)
> at absolute scale and the fixed-variance premise: the premise is false
> (§§1–3), κ²(N) → ∞, and no consumer tier absorbs an unbounded factor
> (doc 84 §12 E1). All in-class repairs are exhausted:
> smooth cutoff (E2/P-F8), θ-dial (E5), taper dials (P-F6), consumer
> absorption (E1). The kernel question at absolute scale is moot.

NOT refuted: (i) (CR-density) itself — the count is about F_N's zeros, not
about any detector; P1's measured linearity (ε(c) ≈ c/12π) stands; Route A
(GAF universality) and Tier 0/(EPH) are untouched. (ii) The counting layer
(MollifiedDip/ParityCounting/Registration — hypothesis-typed, carrier-free).
(iii) The finite-height instrument: below the loglog crossover the chain
runs with inflated explicit constants (doc 84 §12 E3).

## 5. The in-class seed exhaustion [the "all escapes priced" ledger for the kernel mechanism]

Seven mechanisms attacked the (K-bdd)/(FLOOR) seed inside the class
P = F·M, M supported on [1, y]; each failure is derivation- or
measurement-backed (doc 84 §§5, 7, 9–12): ζ-transfer (line-zero atom wall,
exponent 1); naive Fourier (degree-2 wall, doc 58 §2); √-cascade (retracted
— linear self-reference, coefficient ≥ 1/slice-mass ≈ 10–30); PZ/threshold
cascades (additive, q·loglog diverges); near-deterministic γ-range (P-F6
falsifier — no low-variance range exists, profile grows); fresh-prime
Gaussian floor (vanishes identically at θ = 1/2: the complete zone k ≤ N/p
holds no prime > y, band primes carry c = 0 — derived); taper-prime floor
(contamination R = 0.6–1.2 ≫ 3/16 measured, growing). The one unconditional
seed in the neighborhood — the rough inverse product Π_z, whose
characteristic function factorizes completely (doc 84 §9) — is separated
from the mollified object by an O(1)-L² gap that pointwise density
statements cannot cross (SEED-GAP).

## 6. Part II — the fork (P-F5), appended after the runpod scan lands

Registered discriminator (doc 84 §§9, 11): the NORMALIZED density
saturation ⟹ the re-typed heir (K-bdd-n-log) — meas{|P| ≤ t·rms} ≤
C·t²·log(2/t)·U, N-uniform — is TRUE-shaped and Route B′ (normalized
program) becomes the named heir, inheriting the SEED-GAP as its open core;
loglog growth ⟹ the detector's value law itself degenerates (Harper-class)
and the refutation extends to every re-typing in the class. Standing
quantitative prediction (recorded before the scan finished): saturation at
dens(0.2) ≈ 1.35–1.42 with a log(1/t) profile in t, from the
Gaussian-mixture derivation E[1/u ∧ 1/t²] with the measured w-law 0.70·u.

## 3′. Addendum: the unbounded-growth LOWER bound [PROVED HERE (elementary sketch) — the verdict no longer rests on a fit]

The singleton-window sub-family: for squarefree taper d with least prime
factor q₀ = q₀(d), and prime p ∈ (max(y, N/q₀), N], the element m = p·d has
divisor window EXACTLY {d}: every e ∣ pd with e ≤ y divides d (e < p prime),
and a proper divisor e of d has d ≥ e·q₀, so N·e ≥ p·d forces N ≥ p·q₀ —
excluded (Lean: `RouteBSupport.singleton_window_coeff`). Hence b_{pd} = λ_d
EXACTLY, distinct (p, d) give distinct m (p is m's unique large prime), and

> V_bd ≥ Σ_d λ_d² Σ_{max(y, N/q₀(d)) < p ≤ N} 1/(p·d)
>      ≈ Σ_d λ_d²·(ln q₀(d)/ln N)/d
>      ≥ c·(ln y/ln N)·Σ_{q ≤ √y} 1/q ≥ **c₀·loglog N − O(1)**,

by grouping d = q·d′ (q = q₀, d′ q-rough, taper weight ≥ ½ on d ≤ y^{3/4})
and Mertens. The sub-family alone captures a c₀ ≈ 0.3-grade slope — consistent
with (and below) the measured total 2.27. **V(N) → ∞ is now derivation-backed;
the measured law supplies the constant, not the conclusion.**

## 3″. Addendum: the seed identity of doc 84 §9, corrected and machine-checked [PROVED HERE — Lean-banked]

Typing (SEED-GAP) on the divisor-window + dpoly packet surface (the heir's
entrance exam, item 2) forces a correction to doc 84 §9's sketch:

> **The identity "F_N·M_z = Π_z − D_z with E|D_z|² = τ(z) = O(1) (the n > N
> rough tail)" is FALSE as typed.** The defect D_z has THREE components, not
> one: (i) the rough tail n > N [O(1) by Mertens at z = √N — the part §9 saw];
> (ii) the inner Legendre-truncation error on m ≤ N non-rough (the d ≤ z
> window drops smooth divisors ABOVE z: already at m = pq, p,q ≤ z < pq ≤ N,
> the windowed Möbius sum is −1, not the rough indicator 0); (iii) the
> boundary band N < m ≤ Nz — which is EXACTLY the loglog-critical object of
> §§2–3′. Since ‖Π_z‖²_L² = O(1) and ‖P‖² = V → ∞, the raw L² distance is
> loglog-divergent, not O(1). The heir card's "O(1)-L² distance" asset is
> hereby retracted.

**What is true, exactly (RouteBSeedGap.lean, 8 endpoints, axiom-clean):**

- **Exact match on the rough locus.** For every z-rough n ≤ N the divisor
  window is exactly {1}, so the carrier coefficient is λ₁ = the seed
  coefficient — for ANY weights supported on [1, z]
  (`rough_window_filter_eq_one`, `rough_window_coeff_eq_lam_one`). The
  seed-carrier agreement is an arithmetic IDENTITY on its locus, not an
  approximation. Packet-observable face: over any finite prime support in
  (z, N], interval L² distance ZERO on every vertical window
  (`seedGap_rough_component_secondMoment_zero`, consuming the
  LogIndependenceCompare union-padding surface).
- **The gap coefficient, on the nose.** On singleton-window boundary
  elements p·d the window is exactly {d}: carrier coefficient λ_d, seed
  coefficient 0, gap coefficient λ_d (`singleton_window_filter_eq`,
  `seedGap_boundary_coeff`) — the Lean spine of §3′'s cancellation-free
  sub-family.
- **Cancellation-freeness at the observable level.** The boundary gap packet
  at fixed d has strictly positive L² mass on EVERY nonempty vertical
  interval iff λ_d ≠ 0 (`boundary_gap_packet_secondMoment_pos_iff`): the
  common factor d contributes only the unimodular phase d^{-it}
  (`dpoly_shift_norm`), so the packet inherits the Hurwitz-backed
  prime-packet positivity. No mollifier design cancels the boundary band on
  any window — the criticality is not a large-N artifact; it is visible on
  every finite window.

**Consequence for the heir (entrance exam item 2, re-typed).** The seed
bridge cannot be an L² perturbation — not merely "does not transfer pointwise
density" (§9's own caveat) but quantitatively divergent. The corrected shape:
carrier = [exact seed component on the rough locus ≤ N] ⊕ [windowed-divisor
defect]. A seed transfer must be DENSITY-level on the matched component with
the defect handled by a mechanism that is density-neutral despite unbounded
L² mass (conditioning on the smooth field; the defect's per-prime fields are
the SAME prime packets shifted by d — `dpoly_shift_norm` says their phases
are rigidly coupled to the seed's, which is new structure, not an obstacle
priced before). The seed and the criticality are two faces of one identity:
the windowed Möbius defect. That identification is what this addendum banks.

## 7. Part II — the P-F5 fork, adjudicated [scan complete 2026-07-05]

Runpod single-instrument scan (archive: computations/mwm_kbdd/
probe_pf5b_runpod.out, prereg block in prereg.md): normalized density at
t = 0.2 over N = 4k/16k/40k/100k/200k: **1.292 → 1.441 → 1.489 → 1.52 →
1.587**.

**As registered (t=0.2, P0): SATURATION wins** (rms 0.0136 vs 0.0159;
plateau a ≈ 2.17) — the heir Route B′ SURVIVES its entrance exam part 1;
the falsifier did not fire. Recorded against it, loudly: (i) my registered
saturation band 1.35–1.42 was decisively wrong (plateau fit says ≈ 2.17);
(ii) the full table is mixed — t = 0.3 and t = 0.5 prefer loglog (slopes
0.638/0.406); (iii) the two fits differ by < 0.03 at any reachable N: the
instrument has saturated its resolving power. **The fork is NOT closed
observationally; it is transferred to the analytic gate (SMOOTH-LOW)**
(doc 86 §7(c)) — the low-tail/2D-density of the smooth multiplicative
packet with M_q ≍ c/q row masses, after doc 86's reductions ((SPREAD)
diagonal derived; (CONC-σ) sketch: the rough mixture concentrates).

Verdict status of THIS doc is unchanged: Route B as typed remains refuted
(Part I is derivation-backed and Lean-banked). The heir's claim
(K-bdd-n-log) remains open with a passed-as-registered but weak entrance
exam, one analytic gate, and a machine-checked consumer chain waiting on it.
