# HB producer (row 40): conjecture loop ledger

- **ID:** HB-PROD-LOOP-001
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (loop)
- **Source:** `docs/notes.md` row 40; `1-in-progress/hb-obstacle40-working-log.md`; frontier map HB
- **Statement:** find a source-derived, phase-sensitive, arithmetic (PSL(2,ℤ)) law forcing the physical
  two-rate clock defect to vanish: `K_phys(ρ)/c₀(ρ)² = R(ρ)` with `R` real, for every Xi zero `ρ`.

## Goal
The only RH-bearing open item of the HB lane (all detectors are certified receivers). The corpus's
criterion for a candidate: a second, independent evaluation of the charged coefficient with a forced
sign or vanishing, using arithmeticity beyond Hecke positivity; every local, causal, conservation,
Hermitian-metric, Krein/PT and integrality mechanism is classified as a receiver.

## Gates
- [x] 0 → 1  in-progress: loop ran three cycles, every candidate a receiver; closed 2026-09-18 (NO PRODUCER FOUND)
- [ ] 1 → 2  fully-proven: a candidate survives Phase 4 with a dependency-closed paper proof
- [ ] 2 → 3  formalized
- [ ] 3 → 4  not applicable (no manuscripts)

## Approach
Generate candidates only from corpus objects (readers at `ρ/2`, `F = E*(·,ρ)²`, the certified kernels,
Maass–Selberg, Hecke operators, Rankin–Selberg unfolding); kill by the weight-two covariance, the
σ-blindness of Maass–Selberg positivity, the general-Fuchsian barrier, or by exhibiting the candidate as
an identity in `ρ`.

## Log
- 2026-09-18 — cycle 1: Hecke conjugacy of the two readers, the Hecke–Maass–Selberg commutator identity,
  and Rankin–Selberg reality of the bulk weights — all receivers; survivor = explicit off-line phase law of
  the bulk weights (`2·arg Λ(u_j, 2ρ−½)`) and the spurious locus `Im(ζ'/ζ)(1+2iγ) = −π/4` of the constant-mode
  detector. Details in the working log.
- 2026-09-18 — cycle 2: GL(3) reader class killed before construction (weight-two covariance is
  rank-independent; no GL(3) infrastructure); regularization-scheme class unrelated.
- 2026-09-18 — Phase 2 sweep: 2609.02882, 2609.15329, 2608.24827 all pre-classified (receiver /
  superseded / self-declared non-producer). Cycle 3: Kloosterman/Kuznetsov second-sheet readers —
  REDISCOVERED (Motohashi-type continuation) and pre-classified by ULF-SLC-001 (Class III ledger; zeros
  are poles of `φ`, outside every `L²` Parseval identity). **Loop closed: NO PRODUCER FOUND** after three
  cycles; survivor = cycle 1's phase law (paper). Details in the working log.
- 2026-09-19 — cycle 4: B2 coefficientwise cancellation law — FALSE (Hardy consistency; Lean
  `HBSquareReaderChannelsOnLine`, CANNOT-367); survivor = growth-rate detector (MUST-353 receiver).
  Cycle 5: positive-weight Ward/stationarity identity of the literal action — REDISCOVERED (already
  Lean-classified as "⟺ RH" in the FE–Schwarz Ward dichotomy and covariance-endpoint modules). Loop
  remains closed: NO PRODUCER FOUND after five cycles. Details in the working log.
- 2026-09-19 — Phase 2 (external): a June-2026 claimed proof on this exact mechanism (Aksman, Zenodo 21030636:
  scattering poles on `Γ₀(163)\ℍ` forced onto `Re s = ½` by coercivity + self-adjointness) is killed by the
  general-Fuchsian barrier (CANNOT-366): its inputs are group-independent, and self-adjointness constrains the
  `L²` spectrum, never the second-sheet poles. Confirms the exit verdict; no new producer class.
- 2026-09-19 — cycle 7 (Hecke lane, with the new certified layer MUST-364/365/368/369): conjecture "Hecke
  positivity of truncated resonant states beyond Hecke eigenvalue bounds constrains σ". Exact facts (Lean):
  `⟨T_pΛ^Yu,Λ^Yu⟩ = (p^u+p^{ū})‖Λ^Yu‖²`, `‖T_pΛ^Yu‖² = (2+p^{2u}+p^{2ū})‖Λ^Yu‖²` for all `Y ≥ p`. Kill: the two
  moments are the Breit–Wigner (Cauchy, centre `±γ/2`, width `(1−σ)/2`) expectations of `2cos(r log p)` and
  `2cos(2r log p)+1`; the Eisenstein transform of `Λ^Y E_u` is an explicit `L²(dr)` function for every `Re u < 0`,
  so all Hecke–Gram matrices of resonant states are PSD for every hypothetical σ < 1 — the only exclusion is the
  edge `σ ≥ 1` (variance `2(1−p^{σ−1}) ≥ 0`). Verdict: REDISCOVERED as the Class II ledger in Hecke form;
  receiver. Positive survivor (new, exact): the Hecke moments of truncated resonant states are height-independent
  and equal to the Cauchy characteristic function at `k log p` (certified for `k = 1, 2`). Loop stays closed:
  NO PRODUCER FOUND after seven cycles.
- 2026-09-19 — cycle 8: the two corpus interfaces tagged OPEN PRODUCER were re-read against their definitions.
  `ThetaCuspHawkingCausalHardyNoInnerDefect` is `∀ upper resonance r, causalHardyRange r = ⊤`, and the corpus
  proves `causalHardyRange r ≠ ⊤` for EVERY upper resonance, so the interface says "there is no upper resonance"
  — a literal restatement of RH, not a producer target; the same holds for the finite-Rees partner interface
  (`↔ RiemannHypothesis` by the same mechanism). With MUST-370 (Cauchy wave-packet form of the resonant state)
  the Hardy-space picture is explicit: the packet's Eisenstein transform is meromorphic in the spectral
  parameter with poles at `∓iu'` for every resonance `u'`, so every Hardy/inner–outer statement about it is a
  statement about pole locations, i.e. RH itself. Verdict: CIRCULAR. Loop closed after eight cycles; HB's
  certified arithmetic layer (MUST-364/365/368/369/370) is complete and receiver-side.
- 2026-09-19 — cycle 9: Hermiticity of the Hecke moments vacuous (`⟨T_pΛ^Yu,Λ^Yu⟩ = 2Re(p^u)‖Λ^Yu‖²` is real for every `u`); Bohr-torus Poisson reading REDISCOVERED. Cycle 10: trace-formula reading — the continuous term of the PSL(2,ℤ) trace formula is `½Σ_ρ h(r_ρ)`, so RH ⟺ cuspidal trace inequality `Σ_j h(r_j) ≤ Geom(h) + (1/π)∫h/(1+4r²)` for Weil-class `h`; REDISCOVERED/BRIDGE (Hejhal 1976): the cusp sum's sign bounds the Weil functional from above only, and `Geom` is σ-free. Loop closed after ten cycles; the only remaining HB items are receiver-side transports (frontier map table), which cannot supply the arithmetic sign law.
- 2026-09-19 — cycle 11 (user steer: σ-sensitive non-Parseval statements about resonant states): five conjectures killed (resonant Ramanujan bound CIRCULAR; Hecke reflection law, pointwise partner identity definitional; horocycle/CM/geodesic/RN-triple-product growth exponents receivers; `R_ρ`-weighted trace formula an identity), structural reason recorded (no symmetry of the Eisenstein family fixes `Re s = ¼`). Survivor certified: partner angle law `sin ∠ = |2Re ρ − 1|` (MUST-371, `EisensteinResonantPartnerAngle`). Loop closed after eleven cycles.
- 2026-09-19 — cycle 12 (pivot from HB readers to the corpus's own open conjecture PMR): the wide-bump analysis of cycle 11 turned into a proof for finitely supported perturbations. Lean MUST-372 (`finiteFamily_nonneg_iff`): finite changes of prime weights are positive at all apertures iff RH and no change. SURVIVES; open core = infinite patterns.
- 2026-09-19 — cycle 13: PMR extended to countable summable perturbations (MUST-373, `countableFamily_nonneg_iff`); covers removal of all higher prime powers. Open core: divergent-log-moment patterns.
