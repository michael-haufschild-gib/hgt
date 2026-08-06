# Cycle 17: capstone — cancellation ≤ Coulomb potential of the zeros (2026-08-06)

Card: `squarefree-gibbs-parity-vortex.md` (cycle-17).
Lean: `formal/GaloisForLFunctions/RHTower/GibbsPotentialBound.lean`, wired, built, no
sorry, axioms clean.

## THE CAPSTONE
`log_partition_sub_log_current_le` (hypothesis: gibbsDiagC S x (−1) ≠ 0):
  log‖Z_S(x)‖ − log‖J_S(x)‖ ≤ ∑_ζ 2/‖1+ζ‖.
i.e. the LOGARITHMIC cancellation of a Möbius–Laplace sum never exceeds twice the Coulomb
potential of the gas zeros at the parity point. Non-vacuous for ANY size of prime set
(unlike T1/T2 of cycle 13): each zero is weighted by its own proximity, so far-away zeros
contribute ≈ 0.

Combined with cycles 15 (anchor) + 16 (bridge), for the true transform Z(x) ≍ 1/x, an
RH-strength bound |Φ(x)| ≪ x^{−1/2−ε} forces
  ∑_ζ 1/‖1+ζ‖ ≥ (1/4 − o(1))·log(1/x).
**RH requires the gas zeros to accumulate at the parity point with Coulomb potential
growing like log(1/x).** Necessary condition, unconditional and quantitative — the precise
sense in which parity cancellation IS zero condensation.

## Lean notes
- Termwise step: log((2+d)/d) ≤ (2+d)/d − 1 = 2/d via `Real.log_le_sub_one_of_pos`; no
  series expansion of log(1+u) needed.
- Helpers built here (reusable): `multiset_log_prod` (log of a positive multiset product),
  `multiset_sum_map_le` (pointwise), `multiset_sum_map_add` (split).
- `gibbsDiagC_one_ne_zero`: partition function is a positive real via `gibbsDiagC_ofReal`
  + `Finset.sum_pos` with witness ∅.
- After two `multiset_log_prod` rewrites, `Multiset.map_map` puts both sides in
  `Real.log ∘ f` form — match that shape in the termwise lemma.
