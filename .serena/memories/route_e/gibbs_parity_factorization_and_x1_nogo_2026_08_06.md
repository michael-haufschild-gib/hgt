# Cycle 10: X1 no-go + the condensation law made rigorous (2026-08-06)

Card: `squarefree-gibbs-parity-vortex.md` (cycle-10 section).
Lean: `formal/GaloisForLFunctions/RHTower/GibbsParityFactorization.lean`, wired, built,
no sorry, axioms clean.

## Y1 — NO-GO: the X1 criterion (cycle 9) is empty beyond k = 4
X1 bounds cos(dθ) ≥ −1 termwise. At x = 0, B_{j,l} = C(k,j)C(k,l) and the true form is the
perfect square |1+z|^{2k}. Check:
  k=4,n=4: 36 ≥ 34 ✓ ; k=5,n=4: 100 < 110 ✗ ; k=6,n=6: 400 < 450 ✗.
Asymptotically Σ_j C(k,j)C(k,n−j) = C(2k,n), so at n=k the off-diagonal mass beats the
diagonal by ≍ √k. **X1 holds exactly for k ≤ 4 — the range already covered — so it buys
nothing.** Any workable criterion MUST keep the phase cancellation among cos(dθ) terms.
DO NOT re-attempt termwise bounding of the two-scale form.

## Y2 — the finite-volume condensation law (THEOREM, all couplings)
gibbsPoly S x : Polynomial ℂ has natDegree = |S| with leadingCoeff = e^{−xm} ≠ 0, so it
splits over ℂ. Evaluating the factorization at z = −1 and z = 1:
  ‖J_S(x)‖ · ∏_ζ ‖1 − ζ‖ = ‖Z_S(x)‖ · ∏_ζ ‖1 + ζ‖   (zeros with multiplicity)
i.e. THE PARITY CURRENT IS THE CROSS-RATIO PRODUCT OF THE GAS ZEROS AGAINST −1.
No Hadamard theory, no smallness. Corollary (completes W5, previously paper-level):
confinement ‖1+ζ‖ ≤ ρ for all zeros ⟹ ‖J_S‖(2−ρ)^{|S|} ≤ ‖Z_S‖ρ^{|S|}.
Key names: `gibbs_parity_cross_ratio`, `norm_gibbs_current_le_of_confinement`,
`gibbsDiagC_eq_prod_roots`, `gibbs_roots_card`, `gibbsPoly_natDegree`.

## Lean traps (mathlib API drift)
- `Polynomial.Splits` is UNARY now: `p.Splits` (no ring hom!). Factorization is
  `Polynomial.Splits.eq_prod_roots : f.Splits → f = C f.leadingCoeff * (f.roots.map (X - C ·)).prod`.
  `IsAlgClosed.splits p : p.Splits`. `IsAlgClosed.card_roots_eq_natDegree`.
- `(Polynomial.mem_roots hp).mp hζ` returns `eval ζ p = 0` DIRECTLY (no `.2`).
- `Polynomial.eval_finset_sum` → `eval_finsetSum`; `finset_sum_coeff` → `finsetSum_coeff`.
- `coeff_X_pow` orients its if as `j = T.card`; `Finset.sum_filter` as `T.card = j` —
  rewrite both: `if_pos h.symm`, `if_neg (fun hh => h hh.symm)`.
- No `norm_multiset_prod` in mathlib: prove by `Multiset.induction_on` (2 lines).
- `Polynomial.ne_zero_of_coeff_ne_zero` does not exist; derive from coeff_zero.
