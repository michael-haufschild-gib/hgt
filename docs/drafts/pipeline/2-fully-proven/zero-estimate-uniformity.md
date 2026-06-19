# Uniformity-in-S of the multi-q zero estimate (G2 obstruction B / Conjecture 5′) — RESOLVED

- **ID:** zero-estimate-uniformity
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) — **grade BRIDGE** (Door-2 fails: unique factorization + Dirichlet-polynomial
  zero count, both parents)
- **Priority:** FOUNDATIONAL
- **Source:** ../../door/G2-multi-q-siegel-shidlovsky.md (#71 §4 obstruction B, §8 diagonal pullback,
  §15–16) · 00-status rows #13, #14
- **Resolution (2026-06-19, DeWitt):** **Conjecture 5′ is TRUE for the G2-relevant (diagonal) zero
  estimate.** The diagonal/Bohr-lift attack collapses the multi-q multiplicity estimate to a **one-
  variable Dirichlet-polynomial** zero/size estimate, which is uniform in `S` by an **S-free height
  bound** (unique factorization). Obstruction B is **not** a second wall: the
  super-exponential-in-support hazard is **C5★-specific** (it needs a vector-norm/KAM Diophantine bound),
  while B needs only a **height** bound, which is intrinsically S-free. **The G2 lower bound's sole
  remaining wall is obstruction C.**
- **Provenance (validated against the corpus, standing order):** Conjecture 5′ and its framing are
  **pre-named** in `../../support-extraction-log.md` lines 388–392 (obstruction B: finite-S proved via
  multivariate Mahler, "open part = Conjecture 5′ (uniformity in S)"; flatness `F_pq=1` load-bearing;
  "auxiliary = smooth-number Dirichlet polynomials", height-budget `Σ_{p∈S} log p`). **DeWitt's increment is
  the proof:** the diagonal Vandermonde order bound + the S-free elementary height bound that resolves the
  open uniformity (the log lists it as open; this card closes it for the diagonal).

---

## Theorem (uniform-in-S multi-q zero estimate, diagonal form)

Let `S` be a finite set of primes, `ℓ_S = (log p)_{p∈S}`. Let `P` be a nonzero polynomial of degree `≤ d`
in the Bohr coordinates `{x_p}_{p∈S}`; its diagonal pullback is the friable Dirichlet polynomial
`F(s) = Σ_{m∈supp P} λ_m n_m^{-s}`, `n_m = ∏_{p∈S} p^{m_p}`, `K := |supp P|` distinct positive integers,
`λ_m ≠ 0`.

**(a) Order (multiplicity) bound — uniform, constant 1.** `F` vanishes (at any `s_0 ∈ ℂ`) to order
`≤ K − 1`.

**(b) Size bound — S-free per form.** The Vandermonde determinant controlling the order-`K` derivative
system is `∏_{i<j} (⟨m_i,ℓ_S⟩ − ⟨m_j,ℓ_S⟩) = ∏_{i<j} ⟨m_i − m_j, ℓ_S⟩`, and each factor obeys the
**elementary height bound**
> `|⟨m, ℓ_S⟩| ≥ H(m)^{-1}`,  `H(m) = ∏_{p∈S} p^{|m_p|}`,

with constant `1` **independent of `S`**.

**(c) Uniformity.** The only `S`-dependence is `K = C(|S|+d, d)` (monomial count) and `P_S` (largest prime
in `S`), entering **polynomially at fixed degree `d`**: per-form `|⟨m,ℓ_S⟩| ≥ P_S^{-d}` and
`H(m_i−m_j) ≤ P_S^{2d}`. Hence the diagonal multiplicity/size estimate is uniform in `S` with effective
polynomial-in-`|S|` constants. **Conjecture 5′ holds.**

## Proof

**(a)** `F(s) = Σ_j λ_j e^{−s·log n_j}` is an exponential sum with `K` exponents `μ_j = −log n_j`. The
`n_j` are **distinct** (unique factorization: distinct exponent vectors `m` ↦ distinct integers `n_m`), so
the `μ_j` are distinct. If `F` vanished to order `K` at `s_0`, then `F^{(k)}(s_0) = Σ_j λ_j μ_j^{k}
e^{−s_0 log n_j} = 0` for `k = 0,…,K−1`. With `c_j := λ_j e^{−s_0 log n_j} ≠ 0`, this is the Vandermonde
system `Σ_j c_j μ_j^{k} = 0` (`k=0..K−1`) in distinct nodes `μ_j` ⟹ all `c_j = 0`, contradiction. So the
order is `≤ K−1`. (No Diophantine input — only distinctness.) ∎

**(b)** For `m ≠ 0` write `⟨m,ℓ_S⟩ = Σ_p m_p log p = log(a/b)`, `a = ∏_{m_p>0} p^{m_p}`,
`b = ∏_{m_p<0} p^{−m_p}`, coprime positive integers with `a ≠ b` (unique factorization). WLOG `a > b ≥ 1`:
`log(a/b) ≥ (a−b)/a ≥ 1/a ≥ 1/max(a,b) ≥ 1/(ab) = H(m)^{-1}`. The constant is `1`; no reference to `|S|`,
no Baker. The size of the order-`K` Wronskian/Vandermonde determinant `∏_{i<j} ⟨m_i−m_j, ℓ_S⟩` is then
`≥ ∏_{i<j} H(m_i−m_j)^{-1}`, a product of S-free height bounds. ∎

**(c)** At fixed degree `d`, every `m` and every difference `m_i − m_j` has `‖·‖_1 ≤ 2d`, so
`H(·) ≤ P_S^{2d}` and each form is `≥ P_S^{-2d}`; the count is `K = C(|S|+d,d) = O(|S|^{d})`. All quantities
are polynomial in `|S|` (exponent fixed by `d`). The finite-`S` Lemma 5 mechanism and the `|S| → ∞` passage
use the **same** height bound — nothing degrades super-polynomially. ∎

## Door passport / grade — BRIDGE

- **Door-1:** refers to the Bohr coordinates / diagonal flow — but only as carrier.
- **Door-2 (master key): FAILS.** Strip the multi-q vocabulary: the statement is "a Dirichlet polynomial
  with distinct prime-power frequencies has a multiplicity bounded by its term count, with size controlled
  by the trivial height bound `|log(a/b)| ≥ 1/max(a,b)`." That is **analytic number theory + unique
  factorization** — no joint-`σ_p` apparatus is load-bearing. **BRIDGE, not native.**
- **Door-5:** over `F_q(C)` the single-Frobenius collapse (corank 1) makes the analogous estimate
  Papanikolas/ABP; recovers the parent. ✓

## The decisive corollary — B is height-controlled, the hazard is C5★-specific

The controlling Diophantine input for **obstruction B** is the **height** lower bound `|⟨m,ℓ⟩| ≥ H(m)^{-1}`,
which is S-free by unique factorization (Baker-free). The **C5★ / cocycle-reducibility** obstruction
(`../1-in-progress/combination-mode-baker-reducibility.md`) instead requires a **vector-norm** (KAM)
Diophantine bound `|⟨m,ℓ⟩| ≥ c·‖m‖^{-τ}` — which the height bound does **not** supply (it is exp-small in
`‖m‖`), and which fails uniformly in `S` (Baker constant blows up super-exponentially in the support, that
card's Part 1). **Therefore the "super-exponential-in-support hazard" does not apply to B.** The two
obstructions sit on opposite sides of the height/norm divide:

| | controlling bound | uniform in `S`? | engine |
|---|---|---|---|
| **B (zero estimate)** | height `H(m)^{-1}` | **yes** | unique factorization |
| **C5★ (reducibility)** | vector-norm `‖m‖^{-τ}` | **no** | Baker, fails on ∞ support |

**Consequence for G2.** The three-pillar lower-bound architecture (A = Bombieri–Vaaler, supplied; B = this
card; C = arithmetic of values) now has **B resolved**: the infinite base does **not** obstruct the zero
estimate. The entire G2 lower-bound difficulty concentrates on **obstruction C** (the height vacuum / the
`s=1`-Laurent / Stieltjes data) — confirming, from the zero-estimate pillar, the team's "one archimedean
obstruction" picture (seam, `g2-dss-lower-bound.md`, `baker-for-stieltjes.md`).

## Scope (honest boundary)

Proven: the **diagonal** zero estimate (the friable Dirichlet polynomial `F(s)`), which is what the G2
attack uses (§8 diagonal pullback). The fully general off-diagonal multivariate multi-q zero estimate
(Lemma 5, Adamczewski–Faverjon) is the heavier parent statement; this card does not re-prove it, and does
not need it — the diagonal restriction is both sufficient for G2 and elementarily uniform.

## Gates
- [x] 0 → 1  in-progress: Conj 5′ stated precisely; finite-S mechanism + flatness dependence pinned; the
  `|S| → ∞` control scoped (height vs vector-norm divide)
- [x] 1 → 2  fully-proven: the uniform-in-S (diagonal) zero estimate proved (Vandermonde order bound +
  S-free height size bound); grade BRIDGE
- [ ] 2 → 3  formalized — Lean anchors **DONE** for the two finite algebra cores in
  `formal/GaloisForLFunctions/ZeroEstimate.lean`:
  `logPrime_height_bound` proves the S-free height bound
  `H(m)^{-1} ≤ |Σ_p m_p log p|`, and
  `vandermonde_moments_eq_zero_of_injective` /
  `vandermonde_initial_moment_nonzero_of_nonzero_coeff` prove the Vandermonde moment core of the
  order bound. Card remains in `2-fully-proven`: the analytic wrapper translating vanishing order of
  the exponential sum into those moment equations is not yet Lean-formalized.
- [ ] 3 → 4  publication-ready

## Cross-references
- `../0-backlog/g2-dss-lower-bound.md` — the G2 open core; B now removed from its blocking set, only C left.
- `../1-in-progress/combination-mode-baker-reducibility.md` — the C5★ card; the height/vector-norm divide
  cleanly separates B (here) from C5★ (there), correcting the prior "same hazard" cross-reference.
- `../0-backlog/baker-for-stieltjes.md`, `../0-backlog/friable-dirichlet-auxiliary.md` — obstruction C and
  the native auxiliary space (the diagonal pullback `F(s)` of this card).

## Log
- 2026-06-19 — created in 0-backlog (Conj 5′, obstruction B's open uniformity-in-S half).
- 2026-06-19 — DeWitt: pulled to in-progress and **resolved → 2-fully-proven (BRIDGE)**. Diagonal reduction
  to a 1-variable Dirichlet polynomial; Vandermonde order bound `≤ K−1` (distinctness = unique
  factorization); S-free elementary height bound `|⟨m,ℓ⟩| ≥ H(m)^{-1}` for the size estimate; uniformity is
  polynomial-in-`|S|` at fixed degree. Key corollary: **B is height-controlled, C5★ is vector-norm-
  controlled** — the super-exp-in-support hazard is C5★-specific and does not touch B. **G2 lower-bound
  wall = obstruction C alone.** Ledger ticket filed for 00-status #13/#14.
- 2026-06-19 (Leaner) — added Lean anchor `logPrime_height_bound` in
  `formal/GaloisForLFunctions/ZeroEstimate.lean`: for nonzero finite integer prime-exponent vector `m`,
  `H(m)^{-1} ≤ |Σ_p m_p log p|`. Also formalized
  `logPrime_int_sum_eq_log_pos_sub_log_neg`, the `log(a/b)` decomposition. Card remains in
  2-fully-proven; full formalization still needs the Vandermonde/order-bound target.
- 2026-06-19 (Leaner) — added the Vandermonde algebraic core:
  `vandermonde_moments_eq_zero_of_injective` and
  `vandermonde_initial_moment_nonzero_of_nonzero_coeff`. These show that for `n` distinct nodes,
  the first `n` power moments force all coefficients to vanish, equivalently a nonzero coefficient
  vector has a nonzero initial moment. `lake build` and `scripts/check_axioms.sh` pass with 245 theorem
  outputs. The card is not moved to `3-formalized` until the analytic derivative/order-of-zero wrapper
  is also formalized.
