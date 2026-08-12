# Step 44: the unconditional resolvent mass budget [LEAN-PROVED]

Module `formal/GaloisForLFunctions/RHTower/XiResolventMassBudget.lean` (imports NodalSupply +
XiWardCriticalBudgetProbe), wired in RHTower.lean after XiResolventNodalSupply. Nine theorems,
all [propext, Classical.choice, Quot.sound].

## Corpus assets used (locations)

- `xiSpectral_re_sq_gt_thirtytwo` (XiWardCriticalBudgetProbe:897): 32 < γ² unconditional.
- `xi_divisor_support_centered_re_sq_lt_quarter` (CentralReciprocalMoments:289): open strip.
- `xiBudgetMassAt` (def), `tsum_massAt_half_le : Σ' massAt(1/2) ≤ 3/50`,
  `summable_xiBudgetMassAt xi_probe_half_ne_zero` (XiWardCriticalBudgetProbe).
- `xiResolventMoment_zero_eq_logDeriv` (XiResolventTraceHankelCriterion:168): M₀(x²) =
  logDeriv ξ(1/2+x)/x — the Euler-ray/prime-data identity.
- `xiZeroCopy_two_lt_im_sq` (XiThermalSourceRelativeGapBound:53) — the older height gap 2.

## Theorems

1. `xiSpectralPoint_im_sq_lt_quarter`: b² < 1/4 (im via `simp [xiSpectralPoint]`, neg_sq).
2. `norm_xiResolventPoint_le_re_mul`: ‖u_q(X)‖ ≤ (129/127)·(u_q(X)).re for X ≥ 0 — sector
   bound, TIGHT at γ² = 32. Key algebra: Im(z)² = 4gs ≤ g (s < 1/4) and
   512(g−1/4)² − 16129g = (g−32)(512g−1) ≥ 0; 16641 = 129², 16129 = 127², 512 = 129²−127².
3. `tsum_norm_xiResolventPoint_le_re_moment`: Σ‖u‖ ≤ (129/127)·Re(M₀(X)).
4. `tsum_norm_xiResolventPoint_le_logDeriv`: at X = x², bound by (129/127)·Re(logDeriv
   ξ(1/2+x)/x) — norm mass on prime–Gamma data.
5. `norm_xiResolventPoint_le_budgetMass`: ‖u‖ ≤ (132/127)·massAt(1/2) — via ‖u‖ ≤ 1/(g−1/4),
   massAt ≥ 1/(g+1), and 127(g+1) ≤ 132(g−1/4) ⟺ g ≥ 32 (tight: 127·33 = 132·31.75 = 4191).
6. `tsum_norm_xiResolventPoint_le_budget`: **Σ'‖u_q(X)‖ ≤ 198/3175 ≈ 0.0624, every X ≥ 0,
   unconditional** (actual value ≈ 0.046 — consistent).
7. `polyTuranMinor_supply_of_partial_line_budget`: supply with total mass discharged —
   hypotheses hline + (tail ≤ E) + `8B⁴·E·(198/3175) ≤ 2(r₁r₂)^{2m+1}(evals)(r₁−r₂)²`.
8. `rational_nodal_datum_of_partial_line_budget`: nodal instance (B = 2^j → 2^{4j}).
9. `exists_neg_even_plain_minor_of_offline_top_budget`: numeric top-level window
   `(2(198/3175)²/g + (198/3175)²/(ℓ²−ρ₂²))/Im(u)²`.

## Honest scope

hline = partial RH (the essential arithmetic; not formalizable). Tail ε(δ) at the depth the
actual spectrum needs (height ≈ 3·10¹⁰ at X = 1, from RHS ≈ 1.7e-10 vs S·8) is
numerical-verification knowledge — total mass alone cannot see tail decay (lower-tail of Σ1/γ²
needs counting, not moments). What IS now unconditional: the total-mass factor everywhere, the
trace domination, numeric windows.

## Lean traps

`div_add_div_same` removed → `← add_div`. `ring` fails on (c/d)·(1/B) = c/(d·B) → `rw
[mul_one_div, div_div]`. Re-summability: `(Complex.hasSum_re h.hasSum).summable`;
`Complex.re_tsum h`. `Complex.inv_re : (z⁻¹).re = z.re / normSq z`.

## Next

(i) budget probes at larger c for certified tail decay (family of massAt identities weights
high zeros — could give ε(δ) ≤ E(δ) without N(T)); (ii) certified numeric evaluation of
Re(logDeriv ξ(1/2+x)/x) at rational x via corpus xiSquaredEulerFullResponse monotonicity.
Card: xic-order-one-growth-organ.md step 44.
