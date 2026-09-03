# Route E Brick 156 — Möbius smooth log power (2026-09-03)

Created `formal/GaloisForLFunctions/RHTower/Sieve/MoebiusSmoothLogPower.lean`.

Public declarations:

- `eventually_mulDistSqPair_moebiusC_ge_logPower`: one absolute constant gives
  `log(log z) - 11*log(log(|t|+e)) - C` as a lower bound for the full Möbius/Archimedean
  pretentious distance, eventually in `z` and uniformly in `t`.
- `exists_norm_sum_moebius_smooth_le_logPower`: the exact complete squarefree `z`-smooth Möbius
  Euler polynomial is bounded by `C*(log(|t|+e))^11`, eventually in `z`, uniformly in `t`.

Verification:

- direct `lake env lean` source check passed;
- targeted `lake build GaloisForLFunctions.RHTower.Sieve.MoebiusSmoothLogPower` passed;
- both declarations have axioms exactly `[propext, Classical.choice, Quot.sound]`;
- import added to `formal/GaloisForLFunctions/RHTower.lean`; umbrella not built.

Research conclusion: complete smooth Euler-product control does not bound its truncation to
`n <= 3X`. Menon's exact final-range proof uses Hildebrand--Tenenbaum smooth-number density for
`P = exp((log X/R) * logloglog X/loglog X)`, obtaining
`Psi(3X,P) <= X*(log X)^(-R+o(1))`. Existing rough-count/Turán layers are too weak, even after
Brun--Titchmarsh fibre control. Next exact brick must formalize a sufficient unconditional
smooth-number upper bound for this literal schedule, then the final-range frequency decomposition.
