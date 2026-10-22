# Route B′ — the normalized-kernel program (heir of the Route B refutation)

**Claim to establish or refute.** (K-bdd-n-log): meas{t : |P(½+it)| ≤ t₀·rms(P)}
≤ C·t₀²·log(2/t₀)·U, C N-uniform — the NORMALIZED, log-corrected kernel. By
the scale-covariance of the doc 56 chain (doc 84 §11 — κ² cancels against
the kernel's normalization), this alone re-closes (CR-density) with
ε(c) = O(c^{1/3}·polylog) despite V(N) → ∞.

**Entrance exam (both required).**
1. P-F5 saturation: the normalized model density saturates in N (runpod scan
   pending at write-time; prediction on record: limit ≈ 1.35–1.42 at t = 0.2
   with log(1/t) profile). Loglog growth of the NORMALIZED density kills the
   whole class (Harper-degeneration of the detector's value law).
2. (SEED-GAP): an unconditional density seed. In-class seeds are exhausted
   (doc 85 §5). Known assets: the rough inverse product Π_z (char function
   factorizes completely — N-uniform density, doc 84 §9) at O(1)-L² distance;
   the full-range conditional linearity (coefficient-vanishing lemma) with
   the measured joint field-exponent 1.25 > 1 (P-F4).

**Banked substrate:** RouteBSupport.lean; slice-Esseen machine (doc 84 §4,
exponent-preserving); counting layer (hypothesis-typed). Do not re-walk the
seven dead seed mechanisms (doc 85 §5) or the retracted √-cascade (doc 84 §9).

## UPDATE (cycle 53) — new banked substrate from the codex RHTower batch

- **Consumer wiring is DONE (machine-checked, axiom-clean).** The heir no
  longer owes any plumbing between a kernel bound and the counting
  conclusions: `midCentral_survivors_le_of_carrierData_average_kernel`
  (+ `_selected_kernel`, `_thick_kernel`) in `DipKillsWiring.lean` and
  `spread_lt_of_upcross_selected_kernel` / `spread_lt_of_upcross_thick_kernel`
  (ParityCounting/ThickDips → RelayLedger) take a kernel-measure budget
  directly to MID-central survivor counts and relay spread. A proven
  (K-bdd-n-log) enters as the single hypothesis `hker`.
- **Covariance instrument for (SEED-GAP).** `LogIndependence.lean` now has
  the exact surface: for any finite prime set s and any nonempty vertical
  interval, ∫‖dpoly a s‖² = 0 ⟺ a ≡ 0 on s, and > 0 ⟺ some a_p ≠ 0
  (`dpoly_prime_finset_secondMoment_*`), with quantitative diagonal-
  dominance lower bounds in `SecondMoment.lean`
  (`secondMoment_lower_bound_sqrt_log`). The rough-product seed Π_z's
  per-prime linear fields live on exactly this packet surface; the O(1)-L²
  gap statement can be typed against it.
- **P-F5 interim (entrance exam, part 1).** Runpod single-instrument set:
  dens(0.2) = 1.292/1.441/1.489/1.52 at N = 4k/16k/40k/100k; N = 2·10⁵
  running. The registered saturation BAND 1.35–1.42 is already exceeded —
  record as a failed level prediction. Shape: falling loglog-slope
  (0.96 → 0.53 → 0.38) leans saturation at a higher plateau (a ≈ 1.9 on
  16k–100k); both fits predict 1.547 at 2·10⁵, so the exam adjudicates on
  full-set rms per prereg (PREREG-4 protocol), not on the last point.

## UPDATE (cycle 54) — (SEED-GAP) typed and Lean-banked; O(1)-L² asset RETRACTED

- **Correction (binding):** the "Π_z at O(1)-L² distance" asset above is
  FALSE as typed (doc 85 §3″). The defect carrier−Π_z also contains the
  inner Legendre-truncation error and the boundary band; raw L² distance is
  loglog-divergent. Doc 84 §9's identity is corrected in doc 85 §3″.
- **What replaces it (RouteBSeedGap.lean, 8 endpoints, axiom-clean, built,
  lint green):** exact seed-carrier IDENTITY on the z-rough locus ≤ N
  (window = {1}, coefficient = λ₁, any admissible weights; zero interval-L²
  distance on prime supports), and the exact gap coefficient λ_d on
  singleton-window boundary elements with observable-level
  cancellation-freeness (positive interval L² iff λ_d ≠ 0, via the
  d^{-it}-phase shift identity `dpoly_shift_norm`).
- **Entrance exam item 2, re-typed:** seed transfer must be density-level on
  the matched rough component; the defect needs a density-neutral mechanism.
  New structure banked for it: the boundary defect's per-prime packets are
  the SEED's prime packets rigidly phase-shifted by d (`dpoly_shift_norm`) —
  the defect is not noise against the seed, it is the seed re-phased. Next
  move: condition the value law on the smooth field and test whether the
  d-phases decouple (Weyl-differencing shape on the dpoly Gram surface).

## UPDATE (cycle 55) — entrance exam part 1 PASSED (as registered); gate = (SMOOTH-LOW)

- P-F5 adjudicated (prereg block + doc 85 §7): SAT at the registered
  (t=0.2, P0) criterion; mixed at other scales; instrument at resolution
  limit. Exam part 1: WEAK PASS.
- Doc 86 (two-field architecture): exact conditional decoupling; (SPREAD)
  diagonal derived (M_q ≈ 0.28/q); (CONC-σ) sketch (rough mixture
  concentrates). The ENTIRE remaining analytic content of (K-bdd-n-log) is
  (SMOOTH-LOW): 2D density/low tail of the smooth multiplicative packet at
  own rms with c/q row masses. Lean substrate: RouteBTwoField.lean.
