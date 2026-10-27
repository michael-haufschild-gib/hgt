# Renormalized arithmetic potential theory of the characteristic circle (RAPT)

- **ID:** rapt
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-2710/obstacles-summary.md §4 (Q2, B3.25, B3.26, W11, W12; Q3 gauge face)
- **Statement:** Regulators, counterterms, anomalies and couplings of the places of the explicit formula; programme folder `formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/` (README there).

## Goal
Answer Q2 of the report (coupled renormalization) and its gauge face with theorems.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  paper proofs of RP1–RP13 (all carried out directly in Lean)
- [x] 2 → 3  Lean: `renormalized_arithmetic_potential_theory_laws` and the module pillars, all
      axiom-clean (`propext`, `Classical.choice`, `Quot.sound`), wired into
      `RenormalizedArithmeticPotentialTheory.lean`
- [ ] open topics (README §9): matched stability law at the atomic spacing; sign of the prime
      finite part on the classes; characters at the horizon; exact torsion constant; matching
      coefficients of natural gauges; several primes

## Results (Lean)
- RP1 coupled survival law; RP2 the archimedean place pays the arithmetic point.
- RP3 covariance ⇒ scalar, `κ_cov(N) = log N + O(1)`; RP4 `κ_tor(N) ≥ (3/2) log N − C`.
- RP5 horizon polarity; RP6 unbounded rank on `p`-adic classes; RP7 tensor law
  `Σ_j δ_j^{−1} ℓ_j²`, `δ_j = φ(p^{J+1−j})/p^{J+1}`; RP9 no anomaly under `[p]`.
- RP10 finite part `−2γ`; RP12 on the classes the finite part is the tower form of `p` with
  `γ_p = γ + log p/(p − 1)`; RP13 matched stability law at widths `δ_N N^{−e^{1/2}}`.
- RP8 spectral ends `±log N`, Liouville flip; RP11 matching law for sign gauges, finite flips
  invisible.

## No-go closure
- **Killing theorem:** condition (i) of the central conjecture (bounded counterterm rank on Hecke
  orbits) fails under the Abel radius (`coupled_torsion_survival`) and at the horizon
  (`horizonCounterterm_rank_unbounded`).
- **Positive survivor:** the tensor law (RP7) with Hecke-covariant finite part (RP9) and computed
  prime finite part (RP10); Lean: `abs_atomicWeilForm_classProfile_sub_le`,
  `finitePart_heckeShift`, `exists_abs_atomicWeilForm_stepProfile_finitePart_le`.
- **New insight:** counterterm rank and anomaly belong to the regulator; at the horizon the degree
  of `[p]` scales orbit densities and cancels.

## Log
- 2026-10-27 — created; README first draft; RP1–RP13 formalized; laws module.
