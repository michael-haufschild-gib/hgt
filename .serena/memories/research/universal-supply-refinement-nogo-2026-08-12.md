# Step 42: universal supply theorem + refinement-monotonicity no-go [LEAN-PROVED]

Both modules axiom-clean, olean-built, wired (RHTower.lean after XiResolventRationalNodeCriterion;
HTGeometry.lean EOF append).

## (A) RHTower/XiResolventNodalSupply.lean — pricing the countable list

- `polyTuranMinor_supply_of_partial_line {X δ} (hX)(hδ)(hline)(p)(m){B}(hB pointwise disk
  bound)(h1)(h2)(hne)(hmass)`: partial line above δ + `8B⁴εS ≤ 2(r₁r₂)^{2m+1}·
  (eval_{r₁}p)²(eval_{r₂}p)²·(r₁−r₂)²` ⇒ `0 ≤ (0,2,1)-datum of X^m·p`. Proof: index transfer
  via xiPolyMoment_X_pow_mul (0+2m/2+2m/1+2m omega-normalized), pair expansion
  two_mul_polyTuranMinorAt_eq_tsum_pair at n = 2m, two-scale split at F = above-δ finite set;
  above-δ atoms are ofReal norms (hline + eq_ofReal), weights squares of real evals
  (evalRealPolynomial_ofReal), hterm_re closed by `norm_cast`; witness pair via
  Finset.sum_pair; complement ≤ 4B⁴·2εS.
- `rational_nodal_datum_of_partial_line`: nodal instance, B = 2^j (hB from prod of
  norm_sub_node_le), hmass with 2^(4j) and ∏(r_k − c_i) via eval_finNodalPolynomial.
- CHART: cost of list entry (j, m, c) degrades as (r₁r₂)^{2m+1} (shift) and 2^{4j}·node-witness
  distances (nodes). Cheap prefix = small j+m, nodes away from witness moduli.

## (C) HTGeometry/TuranMinorNodeRefinementNonmonotone.lean — no order structure

- `pair_minor_identity (w W wb Wb)`: (wW+wbWb)(w³W+wb³Wb) − (w²W+wb²Wb)² = W·Wb·(w·wb)·(w−wb)²
  — by ring; reusable.
- `pair_minor_re_neg`: at a genuine conjugate pair, datum = −4·normSq W·normSq w·Im(w)² < 0.
- `exists_config_turanMinor_nonneg_nodal_refinement_neg`: explicit config — real atom 1/2
  multiplicity 6, pair (3±4i)/10 — plain (0,2,1) datum = 1/125 ≥ 0, single-node datum at
  rational node 1/2 = −4/625 < 0. Refinement monotonicity FALSE at (j: 0→1); the countable
  family is exhausted by enumeration, not domination.
- Computation pattern: closed-form haves hM/hN per moment (values 18/5, 34/25, 129/250 and
  7/125, 117/1250, 527/12500), each by `rw [ha,hw,hw']; push_cast; linear_combination
  (α·I²+β) * Complex.I_sq` with hand-computed α, β; final `simp only [Fin.sum_univ_three,
  cons_val lemmas, rfl-facts]` then `rw [hM…, ← ofReal_pow, ← ofReal_mul, ← ofReal_sub,
  ofReal_re]; norm_num`.

## (B) scoped

Window optimality: two-pair level family with angle gap θ; conjecture first negative even
minor index ≍ 1/‖V²−1‖ (Cesàro sums of V^{2n+1} stay bounded below until n ≈ 1/‖V²−1‖),
certifying the S²/g window shape optimal. Numeric pre-cert first. Card:
xic-order-one-growth-organ.md step 42.
