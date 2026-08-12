# Step 45: the zero-density surrogate — certified tail decay from ray jets [LEAN-PROVED]

Module `formal/GaloisForLFunctions/RHTower/XiResolventTailSurrogate.lean` (imports
XiResolventMassBudget), wired in RHTower.lean after it. Seven theorems, all
[propext, Classical.choice, Quot.sound].

## The surrogate law

`tsum_norm_xiResolventPoint_tail_le_logDeriv {X c T} (hX : 0 ≤ X) (hc : 1/2 ≤ c)
(hT : 1/2 ≤ T)`:
Σ'_{q : T ≤ γ_q²} ‖u_q(X)‖ ≤ (T + (c+1/2)²)/(2c(T − 1/4)) · 2·Re(logDeriv ξ(1/2 + c)).

Mechanism: budget identity Σ' massAt(c) = 2Re(logDeriv ξ(1/2+c)) holds at EVERY c ≥ 1/2
(`tsum_xiBudgetMassAt_eq` + `XiC_probeAt_ne_zero_of_half_le`); pointwise on the tail
‖u‖ ≤ 1/(g−1/4) and massAt(c) ≥ 2c/(g+(c+1/2)²) (corpus `xiBudgetMassAt_ge`), with the ratio
(g+K)/(g−1/4) decreasing in g (cross-multiplied: (g−T)(K+1/4) ≥ 0). At c ≍ √T the bound decays
like log√T/√T — the true zero-density rate; N(T) never appears.

## Companions

- `norm_xiResolventPoint_le_inv_floor`: ‖u‖ ≤ 1/(γ²−1/4).
- `lt_re_sq_of_norm_xiResolventPoint_lt`: ‖u‖ < δ ⟹ γ² > 1/δ − X − 1/4 (via
  ‖u‖ ≥ 1/(γ²+1/4+X)).
- `tsum_norm_xiResolventPoint_subdelta_le_logDeriv`: the δ-form, hypothesis
  T ≤ 1/δ − X − 1/4 — discharges the supply's ε input by a ray jet.
- `tsum_norm_xiResolventPoint_subdelta_le_numeric`: c = 1/2 instance,
  ε(δ) ≤ (T+1)/(T−1/4)·(3/50) (via logDeriv_xi_one + norm_completedRiemannZeta₀_one_le).
- `rational_nodal_datum_of_partial_line_rayJet`: THE COMPOSED CAPSTONE — every rational-nodal
  criterion entry from: hline (partial line above δ) + one inequality with spectral inputs
  198/3175 (step 44) and 2Re(logDeriv ξ(1/2+c)). No tail hypothesis, no mass tsum, no counting.

## State of the supply program (steps 38, 42, 44, 45)

Arithmetic core of the first rational-nodal data = partial RH above one scale + ξ-jet values
on the real ray (prime–Gamma computable). Everything else is unconditional Lean.

## Lean notes

`Summable.tsum_subtype_le f s (∀ nonneg) (summable)` for subtype ≤ total;
`Summable.tsum_le_tsum_of_inj (Set.inclusion hsub) (Set.inclusion_injective hsub) ...` between
nested subtypes. CHECK CORPUS FIRST: `xiBudgetMassAt_ge`/`_nonneg` already existed
(XiWardCriticalBudgetProbe:148,175) — duplicate declarations are errors.

## Next

(i) certified numeric Re(logDeriv ξ(1/2+c)) at concrete larger c (prime+Gamma with certified
error; corpus xiSquaredEulerFullResponse) → numerically explicit surrogate depth; (ii) sharpen
198/3175 via trace at larger shift; (iii) trig-arc window-optimality family (stretch). Card:
xic-order-one-growth-organ.md step 45.
