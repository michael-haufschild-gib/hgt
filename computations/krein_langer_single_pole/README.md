# Krein–Langer inertia of the off-line-zero carrier (numerical pre-certification)

**Theorist, 2026-06-19.** Pre-certification for the Lean theorem
`GaloisForLFunctions.conj_pair_pick_neg_inertia_le_one`.

## Findings
- **Single off-line pole** `m(z)=1/(t-z)`, `Im t>0`: Pick matrix signature `(1, N-1, 0)` — `n₋` GROWS
  with `N`, so κ₋=∞: a lone off-line pole is NOT a generalized Nevanlinna function (not FE-symmetric).
  (`output.txt`)
- **Conjugate pair** `m(z)=1/(t-z)+1/(t̄-z)` (FE-symmetric, real on ℝ): signature `(1, 1, N-2)` —
  **rank exactly 2** for all N ⟹ κ₋ = 1, κ₊ = 1. (`conjpair_output.txt`)
- **Explicit factorization** (machine-verified, max err 2e-14, dps=double): with `a_j=1/(t-z_j)`,
  `e_j=1/(t̄-z_j)`,  `2·Pick = (e+a)(e+a)* − (e−a)(e−a)*`, so `2·Pick + (e−a)(e−a)* = (e+a)(e+a)* ⪰ 0`
  (rank-1 PSD). One rank-1 correction ⟹ κ₋ ≤ 1.

## Lean consequence
`conj_pair_pick_neg_inertia_le_one` (axiom-clean): the closed-form factorization above proves κ₋ ≤ 1;
with `CarrierPickKernel.conj_pair_pick_not_posSemidef` (κ₋ ≥ 1) ⟹ EXACT κ₋ = 1 for one off-line zero.

## Repro
`python3 kl_numeric.py` (single pole), `python3 kl_pair.py` (conjugate pair + factorization).
numpy 2.4.1.
