# Route B as typed (doc 56): REFUTED — windowed-divisor criticality of the mollified boundary

**Claim (doc 56, doc 60 §4 W5-Route-B).** P = F_N·M_y (BV taper, y = N^θ) is a
fixed-variance detector (V = O_θ(1)) whose kernel (K-bdd) at absolute scale
closes (CR-density) with ε(c) → 0.

**Verdict: REFUTED (docs 84–85, goal #29, 2026-07-05).** The V = O(1) premise
is false: the boundary band m ∈ (N, Ny] carries windowed divisor sums whose
Möbius cancellation is disabled by the truncation geometry (Lean:
`RouteBSupport.window_diagonal_only`), giving
**V_bd ≥ c₀·loglog N** unconditionally via the singleton-window sub-family
(b_{pd} = λ_d exactly; Lean: `RouteBSupport.singleton_window_coeff`);
measured V = −1.58 + 2.27·loglog N across six designs (sharp/BV/taper
dials/smooth cutoff/θ = ¼), retrodicting doc 56 §9's V_BV(400) = 2.48. The
citation gap: Graham's theorem covers only the complete sums (m ≤ N), never
the band. κ²(N) → ∞ and no consumer tier absorbs an unbounded factor.

**Escapes priced (all closed):** smooth inner cutoff (P-F8 — intrinsic);
θ-dial (V_inner ~ 1/θ fights V_bd — total worse at θ = ¼); taper dials
(P-F6); consumer absorption (doc 84 §12 E1); in-class kernel seeds — seven
mechanisms each derivation- or measurement-killed (doc 85 §5): ζ-transfer
(line-zero atom wall), naive Fourier (degree-2 wall), √-cascade (retracted,
linear self-reference ≥ 10–30×), PZ/threshold cascades, low-variance γ-range,
fresh-prime floor (vanishes identically at θ = ½), taper-prime floor
(contamination R ≈ 0.6–1.2 ≫ 3/16).

**Do not re-attempt:** any λ-on-[1,y] mollifier redesign for V = O(1); any
ζ-sublevel transfer for the kernel; any self-referencing density fixed point
at these slice masses.

**Survives:** the counting layer (MollifiedDip/ParityCounting/Registration —
hypothesis-typed, carrier-free); (CR-density)'s truth-shape (ε(c) ≈ c/12π
measured — the count is about F_N, not the detector); Route A (GAF) and
Tier-0/(EPH); the finite-height instrument below the loglog crossover;
RouteBSupport.lean (6 endpoints, axiom-clean). **Heir:** Route B′ — the
normalized program (K-bdd-n-log), entrance exam = P-F5 saturation (runpod
scan) + the (SEED-GAP) crux (doc 84 §9, doc 85 §§5–6).
