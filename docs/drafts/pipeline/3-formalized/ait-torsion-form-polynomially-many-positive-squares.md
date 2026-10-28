# The torsion form has polynomially many positive squares

- **ID:** ait-torsion-form-polynomially-many-positive-squares
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** AIT §9 topic 5 ("Indices on boxes"); Pillar XIV (`≤ 2` positive squares per ladder).
- **Statement:** Let `R(x) = −Σ_{m,n ≤ N} x_m x_n P(m,n) − Σ_{n ≤ N} x_n² c(n)` (renormalized torsion
  form). Let `Q₀ = ⌈e^{2c₁+1}⌉` (`c₁` Mertens' constant). For `M ≥ 3` and `N ≥ (Q₀M)⁵`, `R` is positive
  definite on a subspace of `ℝ^{[1,N]}` of dimension `≥ M/log M`. Hence its positive index on
  `[1, N]` is `≥ c N^{1/5}/log N`.

## Proof

Anti-pole `v_q = δ_q − Σ_{p ∈ A} δ_{qp}/(2√p)` at a prime base `q ∈ (M, Q₀M]`, arms `A` = primes in
`(Q₀M, ⌊N/(Q₀M)⌋]`. Only Hecke edges `q → qp` meet its support, so
`R(v_q) = Σ_A log p/p − c(q) − Σ_A c(qp)/(4p) ≥ ½ Σ_A log p/p − log q` (`c(n) ≤ log n`,
`log(qp) ≤ 2 log p`). Distinct anti-poles share no edge: primes of disjoint windows give
`q ∤ q'p'`, `qp ∤ q'p'`; so `R(Σ a_q v_q) = Σ a_q² R(v_q)`. Mertens: `Σ_A log p/p ≥
log⌊N/B⌋ − log B − 2c₁ ≥ 3 log B + 1` for `B = Q₀M`, `N ≥ B⁵`, so `R(v_q) > 0`. Chebyshev
(Mertens localized to a window): `#(M, Q₀M] ∩ primes ≥ (log Q₀ − 2c₁) M/log M ≥ M/log M`.

## Significance

- Answers AIT topic 5 in growth: interaction of ladders of different primes at their common
  bases produces polynomially many positive squares, whereas a single ladder carries at most two.
- No finite-rank counterterm renormalizes the torsion pairing uniformly on boxes (Gårding = finite-rank
  survival, RAPT RP14): the rank needed grows at least like `N^{1/5}/log N`.
- Numerics: index 6, 9, 14, 18, 23 at N = 100, 300, 1000, 2000, 4000 (`≈ N^{0.38}`); the negative
  eigenvectors of `diag(c) + P_N` are localized anti-poles centred at small `m` (1, 2, 3, 4, 6, 5, …),
  with arms on `mt`. Optimal-arm heuristic: bases up to `N^{α*}`, `2α + α log(1/α) = 1`.

## Status

Lean: `formal/GaloisForLFunctions/ArithmeticIntersectionTheory/TheTorsionFormHasPolynomiallyManyPositiveSquares.lean`
(`torsionBilinear`, `torsionBilinear_sum_left`, `armVector`, `sum_armVector_mul`, `Windows`,
`torsionBilinear_armVector_ne`, `torsionBilinear_armVector_self_ge`, `windowRatio`,
`renormalizedTorsionForm_pos_on_span`). Clean exact-file check; axioms
`propext, Classical.choice, Quot.sound`; wired in the AIT umbrella.

Open: the exact exponent; an upper bound `N^{α* + o(1)}` (localization of positive squares near
bases `≤ N^{α*}`).
