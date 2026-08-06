# Equation (6) proved everywhere, not just on the horizon (2026-08-06)

Card: `stable-coframe-log-calabi-yau-rigidity` (stage 2).  Modules **22 and 23**.
Continues [[research/scheme_eigenvolume_unit_step1_2026_08_06]].

## `EigenvolumeBoundaryDivisor.lean` (22) — abstract, no AG deps

- `boundaryCoeff c x := -(c x)`
- `order_eq_zero_or_neg_one` — the order is `0` or `-1`: **the boundary is reduced**.
- `boundaryCoeff_eq_zero_or_one`
- `order_ne_zero_iff` — total invariance, abstract form (previously only proved ad hoc inside the
  ring capstone and the scheme horizon module).
- **`ramification_eq_pullback_sub`** — `e x − 1 = e x * boundary(F x) − boundary(x)` **at every
  place**.  This is the coefficient form of `R = f*D − D`, i.e. card equation (6).

**The pre-existing `ramificationCoefficient_eq_pullback_sub` was strictly weaker** — it assumed
`c x = −1` and `c (F x) = −1`, i.e. it only covered places already known to be on the horizon.
The off-horizon case is the one that needs `e = 1`
(`ramificationIndex_eq_one_of_order_eq_zero`), and it now follows.

## `SchemeEigenvolumeBoundary.lean` (23)

`schemeEigenvolume_ordAt_eq_zero_or_neg_one`, `schemeEigenvolume_boundaryCoeff_eq_zero_or_one`,
`schemeEigenvolume_ramification_eq_pullback_sub`.

## Card status

Theorem A conclusions (2), (3), (4), (5) **and now (6)** all hold as Lean theorems at scheme
level.  Remaining are inputs, not conclusions:

1. **Different exponent `e − 1`** beyond the Eisenstein presentation — mathlib's
   `pow_sub_one_dvd_differentIdeal` gives only one inequality and the matching non-divisibility
   needs `IsCoprime P Q`, which fails in the totally ramified local case.
2. Tie `Pg`, `J`, `c` to Kähler-differential data (sheaf of differentials on a scheme).
3. Step 4's `e > 1`: needs `N¹` + int-amplification.
4. Corollary B: MMP.

## Repo hazard

`pgrep -f "lean --"` can show a process that is **another agent's session** — check the shell
snapshot path in `ps -o command` before concluding you left one running.  Untracked unwired
module this round: `HTGeometry.DualAnnihilatorRank`.
