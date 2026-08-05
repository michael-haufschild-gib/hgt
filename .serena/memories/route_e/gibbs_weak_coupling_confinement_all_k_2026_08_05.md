# Cycle 6: weak-coupling confinement — the first ALL-k gas theorem (2026-08-05)

Card: `squarefree-gibbs-parity-vortex.md` (cycle-6 section).
Lean: `formal/GaloisForLFunctions/RHTower/GibbsWeakCouplingConfinement.lean`
(RHTower.GibbsGas), wired, built, no sorry, axioms clean.

## Theorems (all k, unconditional, NO Rouché / NO fundamental theorem of algebra)
- W1 `norm_gibbsDiagC_shift_sub_pow_le`: ‖P_S(−1+w,x) − w^k‖ ≤ x·(2+‖w‖)^k·m, m = ∏S.
  Engine: ∑_{T⊆S}(w−1)^{|T|} = w^k exactly, |e^{−u}−1| ≤ u, ∑_T∏_{p∈T}((1+‖w‖)p) =
  ∏_p(1+(1+‖w‖)p) ≤ ∏_p((2+‖w‖)p) using p ≥ 1.
- W2 `gibbsDiagC_ne_zero_of_le_norm`: x·m < (ρ/(2+ρ))^k ⟹ no zero with ‖z+1‖ ≥ ρ.
  (t ↦ t/(2+t) increasing is the whole trick.)
- W3 `gibbs_weak_coupling_stable`: x·m < 3^{−k} ⟹ ‖z+1‖ < 1 ∧ Re z < 0 — Hurwitz
  stability for EVERY k (previously only k ≤ 4).
- W4 `abs_gibbs_current_sub_totient_le`: |J_S(x) − (−1)^{k+1}φ(m)x| ≤ x²∏(1+p²)
  (k ≥ 1, x·m ≤ 1) — quantitative totient law; certifies W2's radius is SHARP:
  (φ(m)x)^{1/k} ≲ cluster radius ≤ 2(mx)^{1/k}, ratio (m/φ(m))^{1/k} = O(1).
- W5 `norm_one_sub_ge_of_norm_one_add_le`: ‖1+ζ‖ ≤ ρ ⟹ ‖1−ζ‖ ≥ 2−ρ ⟹ per-zero
  cancellation factor ≤ ρ/(2−ρ); |J_S|/Z_S ≤ (ρ/(2−ρ))^k matches W4's order φ(m)x/2^k.

## Open frontier now
The INTERMEDIATE WINDOW 3^{−k} ≤ x·m ≲ (Kurtz threshold) is the only remaining gap in
the all-k sector-collapse conjecture (weak end = W3, strong end = Kurtz anchor O3).

## Lean traps
- `Finset.prod_add` cofactor `∏_{S∖T}(1)` normalizes to `1 ^ card`: the simp set needs
  `one_pow`, NOT `Finset.prod_const_one` (which never fires after `Finset.prod_const`).
- `Finset.prod_le_prod_of_subset_of_one_le'` requires multiplicative OrderedCommMonoid —
  does NOT apply to ℝ. Use `Finset.prod_sdiff hT` + `nlinarith [hge1, hTpos]`.
- `Real.abs_exp_sub_one_sub_id_le : |x| ≤ 1 → |exp x − 1 − x| ≤ x^2` (constant 1, not 1/2).
- `Complex.normSq_eq_norm_sq` + `Complex.normSq_apply` to go from ‖z+1‖ < 1 to Re z < 0.
