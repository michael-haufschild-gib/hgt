# 92 — The RHLadder structural theory (complete, formalized)

`RHLadder k` — *every ξ-zero right of the critical line has vanishing order divisible by `2^k`* — is
the tree's reduction of RH to a decreasing family of divisibility hypotheses
(`rh_iff_forall_ladder : RiemannHypothesis ↔ ∀ k, RHLadder k`). This doc is the ledger of its complete
order-theoretic, arithmetic, and regional structure, all now Lean theorems in
`RHTower/RHLadderTheory.lean` (axiom-clean `[propext, Classical.choice, Quot.sound]`, full RHTower and
MainTheorems green). The proofs are unconditional; the *ladder itself* stays open — this is the exact
scaffolding around the open core, not a claim to have climbed it.

## 1. Order structure (the ladder is a nested family)

- `rhLadder_zero : RHLadder 0` — rung 0 is trivial (`2^0 = 1` divides every order).
- `rhLadder_of_le : m ≤ k → RHLadder k → RHLadder m` — **monotone nesting**: a higher rung implies
  every lower one. The ladder is a decreasing sequence of Props; RH is its intersection.
- `rhLadder_of_succ`, `rhLadder_imp_one` — the successor case and "every rung `≥1` forces rung 1."
- `rh_of_rhLadder_cofinal : (∀ N, ∃ k ≥ N, RHLadder k) → RiemannHypothesis` — **cofinal criterion**:
  the ladder holding at arbitrarily large levels already gives RH. Nesting turns cofinal into all.
- `forall_rhLadder_iff_no_rightHalf_zero : (∀ k, RHLadder k) ↔ ∀ ρ ∈ rightHalf, xi ρ ≠ 0` — the
  intersection of all rungs is exactly "no right-half zeros," i.e. RH.

## 2. The 2-adic valuation is the real invariant (`ladderHeight`)

`ladderHeight ρ := (analyticOrderAt xi ρ).toNat.factorization 2` — the 2-adic valuation of the
vanishing order. This is the correctly-typed successor to the *refuted* mod-2 "parity" of docs 89–90:
not a parity but the full valuation, i.e. how many rungs a zero's order survives.

- `rhLadder_iff_ladderHeight_ge : RHLadder k ↔ ∀ ρ ∈ rightHalf, xi ρ = 0 → k ≤ ladderHeight ρ`.
- `not_rhLadder_of_gt_ladderHeight` / `not_rhLadder_ladderHeight_succ` — **sharp collapse**: a
  right-half zero of height `h` satisfies exactly rungs `0…h` and breaks rung `h+1`. The first failing
  level is `ladderHeight ρ + 1` — an *exact* location, refining `not_rhLadder_of_rightHalf_zero`.
- `rhLadder_one_iff_even_order` (doc 91): rung 1 = every right-half order even = `ladderHeight ≥ 1`.

RH restated through the invariant: **RH ⟺ `ladderHeight = ∞` (order 0, i.e. non-vanishing) at every
right-half point.** A single off-line zero has finite height and so falls off the ladder at a definite
finite rung — the tower's force is that no such finite-height point may exist.

### Symmetry of the invariant

`ladderHeight` is constant on the whole symmetry orbit:
- `ladderHeight_conj : ladderHeight (ρ̄) = ladderHeight ρ` (Schwarz),
- `ladderHeight_one_sub : ladderHeight (1 − ρ) = ladderHeight ρ` (functional equation),
- `ladderHeight_quadruple_eq` — all four of `{ρ, 1−ρ, ρ̄, 1−ρ̄}` share one height.

This is what the doc-89 "weight" *should* have been: a `V₄`-invariant of the quadruple, but the
**2-adic valuation**, not a parity. It carries real information (it is `∞` iff the point is not a zero)
where the parity was constant.

## 3. Regional localization (the open core is a bounded strip box)

Off the strip the ladder is unconditionally satisfied, because ξ has no zeros there:

- `xi_ne_zero_of_one_le_re : 1 ≤ ρ.re → xi ρ ≠ 0` (from mathlib's `riemannZeta_ne_zero_of_one_le_re`,
  boundary `Re = 1` included, plus `xi 1 = 1/2 ≠ 0`).
- `rhLadder_iff_strip : RHLadder k ↔ ∀ ρ, ½ < ρ.re < 1 → xi ρ = 0 → 2^k ∣ ord` — **the quantifier
  collapses to the open critical strip `½ < Re < 1`.**
- `rhLadder_iff_upperHalf` — by conjugation symmetry it further collapses to `Im ≥ 0`.
- `rhLadder_iff_openStrip_upper : RHLadder k ↔ ∀ ρ, ½ < ρ.re < 1 → 0 ≤ ρ.im → xi ρ = 0 → 2^k ∣ ord` —
  **the entire ladder (hence RH) is decided by ξ-zeros in the half-open box `{½ < Re < 1, Im ≥ 0}`.**

## 4. Analytic face (roots)

`rhLadder_iff_root` (tree): rung `k` ⟺ ξ has an analytic `2^k`-th root on `Re > ½`. Complementing
monotone nesting:

- `exists_root_of_exists_root_succ` — **root nesting**: a `2^{k+1}`-th root gives a `2^k`-th root by
  squaring. The analytic shadow of `rhLadder_of_succ`. The full tower of roots is `rh_iff_tower`
  (`CoherentTower`), so the recursion "rung `k+1` = the `2^k`-th root itself has all-even orders" is
  already carried by the coherent-tower layer; this file adds the arithmetic layer beneath it.

## 5. What is exhausted, and the one door left open

Exhausted (all Lean, unconditional): the ladder's order structure (§1), its arithmetic invariant and
sharp per-zero collapse (§2), its symmetry (§2), its localization to `{½<Re<1, Im≥0}` (§3), and its
root face (§4). Rung 0 is a theorem; the base case rung 1 is `√ξ`-existence on the box, and every rung
`≥1` implies it (`rhLadder_imp_one`), so the whole open content sits at **rung 1 = no odd-order ξ-zero
in `{½<Re<1, Im≥0}`** — the exact target, now with the domain minimized and the invariant correctly
typed.

The generative move this opens (doc 91 route 1, now sharpened by §3): build the **boundary functional
on `{Re = ½}`** — the real finite Hardy carrier `H_N` — whose vanishing trivializes the ξ mod-2 deck
cocycle across the *bounded* box `{½<Re<1, Im≥0}`. Localizing the domain to a strip box (not a
half-plane) is what makes a boundary/holography argument viable: a bounded region has a genuine
compact-exhaustion handle (`xi_zeros_finite_ball` gives finitely many zeros per height window), so the
next object is the height-window certificate that forces `ladderHeight ≥ 1` from line data — the
constraint-fixes-bulk step, built one finite box at a time.
