# Tate–prime rigidity — the secular weld of motivic and non-motivic blocks (G12)

- **ID:** tate-prime-rigidity
- **Stage:** 0-backlog
- **Type:** CANDIDATE
- **Priority:** FUTURE
- **Source:** ../../door/bucket-new-sibling-conjectures.md (#69 SEED-M), ../../door/bucket-the-seam-archimedean-obstruction.md · 00-status row #101
- **Statement:** Each secular moment splits `P_k = [motivic ζ(k) part, imported MT(ℤ)] + [prime /
  Stieltjes `a_{k−1}` part, NO motivic home]`. **Conjecture:** the secular moment **rigidly welds** a
  known motivic block to an unknown prime block — and that **weld is the new object** no existing
  transcendence theory addresses.

## Goal
Names the field's **genuinely-new (no-motive) content** in period-comparison form: the `P_k` are not
periods of a single motive but a **rigid sum** of a motivic period and a non-period regularization
constant glued at the seam (`ξ = Γ-factor × ζ`). The rigidity — that the two blocks cannot be deformed
independently — is what makes DSS-cross (`g2-dss-lower-bound.md`) hard and what a transcendence theory
spanning the period/non-period divide must capture.

## Door passport
- **Door-3:** the weld (the specific motivic ⊕ non-period decomposition of `P_k`) is a native invariant
  of the secular coordinates — `li_secular_pointwise` ledgers the change of basis it lives in.
- **Door-2:** the *existence* of the decomposition is bookkeeping (BRIDGE); the **rigidity** (the two
  blocks' forced non-conspiracy) is the native-candidate content, = the DSS-cross / seam.

## Gates
- [ ] 0 → 1  in-progress: the `P_k = motivic ⊕ non-period` split pinned (closed forms `ζ(k)/2^k` vs
  `a_{k−1}`); "rigid weld" given an operational meaning (the blocks don't decouple); Door passport sketched
- [ ] 1 → 2  fully-proven: the rigidity proved (the weld is non-trivial — the blocks are
  transcendentally independent yet inseparable)
- [ ] 2 → 3  formalized
- [ ] 3 → 4  publication-ready

## Approach
Use the closed form `P_k = 1 − (−1)^k ζ(k)/2^k − a_{k−1}`, `a_j = [s^j](ζ'/ζ)`, to exhibit the two
blocks; pose the rigidity as: no period relation can mix them (the motivic block is `MT(ℤ)`, the prime
block is fresh — `regularization-freshness.md`). The weld is the local form of the seam at each `k`.

## Cross-references
- `g2-dss-lower-bound.md` — the rigidity is what makes DSS-cross hard.
- `regularization-freshness.md` — the non-period block's transcendental freshness.
- `motivic-period-tower.md` — the motivic block's tower (the live recursion).

## Log
- 2026-06-19 — created in 0-backlog. Tate–prime rigidity (G12, SEED-M): the secular weld of a motivic
  block to a non-motivic prime/Stieltjes block — the field's genuinely-new content.
