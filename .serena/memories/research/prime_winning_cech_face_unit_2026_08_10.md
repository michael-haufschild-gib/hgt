# Prime-winning Čech divisor resolution — face unit banked, Euler product next (2026-08-10)

Card `2-fully-proven/prime-winning-cech-divisor-resolution.md`.  Stage 2; its only Lean gate is
"analytic face Euler product and unit theorem formalized unconditionally".  The **unit half is
now closed**; the Euler-product half is the remaining work.  The card's other open gates
(reflected controlled completion, Xi conormal base change, determinant/RH) are the open research
core — not Lean gates.

## Closed

`RHTower/PrimeWinningFaceUnit.lean` — `faceTransitionUnit` `R_{p,m}`, `faceUnit` `U_{F,m}`,
`faceUnit_ne_zero` + `faceTransitionUnit_ne_zero` (equation `(17)`, for all `m ≥ 1`,
`Re s > 1/2`), `differentiableAt_faceUnit`, and `faceUnit_insert` (the flat transition `(18)`).
Key step: `one_lt_re_succ_mul` — `Re s > 1/2` and `m ≥ 1` give `Re((m+1)s) > 1`, so
`riemannZeta_ne_zero_of_one_lt_re` applies.  Axiom-clean, wired into the RHTower umbrella.

## Remaining: the Euler product `(13)`–`(16)`

Target: `B_{F,m}(s) = ζ(s) · U_{F,m}(s)` where
`b_{F,m}(n) = 1_{M(n)=m ∧ F ⊆ W(n)}`, `M(n) = max_p v_p(n)`, `W(n) = {p : v_p(n) = M(n)}`.

**Plan already worked out (do not re-derive):**

1. For `F` nonempty and `m ≥ 1`, `b_{F,m}(n) = 1` ⟺ `(∀p∈F, v_p n = m) ∧ (∀q prime, v_q n ≤ m)`.
   (⇐ uses `F` nonempty to force `M(n) ≥ m`.)  Prove this as the faithfulness lemma against the
   card's `M`/`W` definition.
2. `b` is **not** a mathlib-multiplicative function: `b(1) = 0`.  Factor out `A = ∏_{p∈F} p^m`.
   Every `n` with `b(n) = 1` is uniquely `A · n'` with
   `c_{F,m}(n') = 1_{(∀p∈F, v_p n' = 0) ∧ (∀q prime, v_q n' ≤ m)}`, and `c(1) = 1`.
   So `B_{F,m}(s) = A^{-s} · C_{F,m}(s)` by reindexing along `n' ↦ A n'`
   (`Function.Injective.tsum_eq` with the support condition).
3. `c` **is** multiplicative — and the coprimality hypothesis is essential: the condition
   `v_q ≤ m` does not factor over general products, but for coprime `m,n` at most one factor has
   `v_q ≠ 0`, so it does.
4. Euler product via `ArithmeticFunction.IsMultiplicative.eulerProduct_tprod` (same template as
   `RHTower/SquarefreeMoebiusNormalization.lean`, which does the squarefree case end to end).
   Local factors: `1` at `p ∈ F`; `∑_{e=0}^m q^{-es}` at `q ∉ F`.
5. Convert with `∑_{e≤m} x^e = (1-x^{m+1})/(1-x)` and the two Euler products for `ζ(s)`,
   `ζ((m+1)s)` to reach `(14)`, then `(16)` with the already-built `faceUnit`.

## Corpus facts

The combinatorial side (`(4)`–`(7)`, the Čech augmentation) is already formalized in
`RHTower/PrimeDilationTropicalBoundaryTomography.lean` over the abstract `BoundedPrimeValuation`
cube (`winningFaceIndicator_mul`, `winnerSetWithin`,
`tropicalShellIndicator_eq_alternating_winningFace_sum`).  The analytic side needs actual `ℕ` and
`Nat.factorization`, so it is a separate development — that is expected, not duplication.
