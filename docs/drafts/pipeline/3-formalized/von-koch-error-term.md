# Von Koch: RH ⟺ ψ(x) − x = O(√x log²x) ⟺ π(x) − li(x) = O(√x log x)

Stage: 3-formalized (2026-10-03). Loop cycle 229 (MUST-728).

## Lean
- `formal/GaloisForLFunctions/RHTower/VonKochChebyshevBound.lean`: shell counts
  (`card_xiCopiesBelow_le_log`, `sum_xiCopiesBelow_inv_abs_le`), per-zero bounds
  (`norm_lagWindowZeroTerm_le_head`, `_tail`), `tsum_norm_lagWindowZeroTerm_le`,
  `chebyshevPsi_sub_le_of_riemannHypothesis`, `sub_chebyshevPsi_le_of_riemannHypothesis`,
  `abs_chebyshevPsi_sub_le_of_riemannHypothesis`, `re_le_half_add_of_chebyshevError_le_rpow`,
  `riemannHypothesis_of_chebyshevPsi_sub_le_sqrt_log_sq`, `riemannHypothesis_iff_chebyshevPsi_sub_isBigO`.
- `formal/GaloisForLFunctions/RHTower/VonKochPrimeCounting.lean`:
  `exists_abs_primeCounting_sub_logIntegral_le_of_riemannHypothesis`,
  `riemannHypothesis_of_primeCounting_le_logIntegral_add_sqrt_log`,
  `riemannHypothesis_iff_primeCounting_sub_logIntegral_isBigO`.
Axioms `[propext, Classical.choice, Quot.sound]`.

## Proof (paper)
Window squeeze + genus-kernel explicit formula; zero terms bounded by head/tail estimates; shell
counting from the line log-derivative constant; choice `h = S = √x`. Converse through power receivers.

## Reusable survivor
`re_le_half_add_of_chebyshevError_le_rpow`: any one-sided `ψ(t) − t ≤ Ct^{1/2+a}` bound clears
`Re s > ½ + a` — the general one-sided von Koch converse, replacing the logloglog-specific receiver.
