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
