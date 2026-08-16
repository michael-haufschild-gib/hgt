# Uniformity along the canonical prime exhaustion of the multi-q zero estimate (G2 obstruction B / Conjecture 5′)

- **ID:** zero-estimate-uniformity
- **Stage:** 3-formalized
  `S_N = {first N primes}`**, not arbitrary finite prime sets; Leaner's singleton `{huge p}` counterexample is
  a non-canonical `S` the G2 race never uses. Along `S_N`, PNT gives `P_S = p_N ~ N log N`, so the
  `P_S`-polynomial constants are `|S|`-polynomial — the §(c) gap is closed.)
- **Type:** THEOREM (paper) — **grade BRIDGE** (Door-2 fails: unique factorization + Dirichlet-polynomial
  zero count, both parents)
- **Priority:** FOUNDATIONAL
- **Source:** ../../door/G2-multi-q-siegel-shidlovsky.md (#71 §4 obstruction B, §8 diagonal pullback,
  §15–16) · 00-status rows #13, #14
- **Resolution (2026-06-19, DeWitt):** **Conjecture 5′ is TRUE for the G2-relevant (diagonal) zero
  estimate.** The diagonal/Bohr-lift attack collapses the multi-q multiplicity estimate to a **one-
  variable Dirichlet-polynomial** zero/size estimate, which is uniform **along the canonical prime exhaustion
  `S_N = {first N primes}`** by an **S-free per-form height bound** (unique factorization) combined with the
  **PNT link `P_S = p_N ~ N log N`** (so `P_S`-polynomial constants are `|S|`-polynomial; see §(c) and the
  PNT lemma). Obstruction B is **not** a second wall: the
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

**(c) Uniformity along the canonical exhaustion.** The only `S`-dependence is `K = C(|S|+d, d)` (monomial
count) and `P_S` (largest prime in `S`), entering **polynomially in `P_S` at fixed degree `d`**: per-form
`|⟨m,ℓ_S⟩| ≥ P_S^{-d}` and `H(m_i−m_j) ≤ P_S^{2d}`. On the **canonical exhaustion `S_N = {first N primes}`**
(equivalently `S = {p ≤ x}`) — the only exhaustion the G2 race uses (Pillar A grows `S` at fixed `d` and
*minimizes heights*, so it takes the smallest primes; `friable-dirichlet-auxiliary.md` §2) — the prime number
theorem links the two parameters:

> **PNT lemma.** For `S_N = {first N primes}`, `P_S = p_N ≤ C·N log N` (Rosser–Schoenfeld:
> `p_N < N(ln N + ln ln N)` for `N ≥ 6`). Hence `P_S` is **polynomially bounded in `|S| = N`**, and the
> log-height budget is `Σ_{p∈S} log p = θ(p_N) ~ p_N ~ N log N`.

Therefore on `S_N`, at fixed `d`: `K = O(N^d)`, per-form `|⟨m,ℓ⟩| ≥ (C N log N)^{-d} = N^{-d+o(1)}`, and every
height `H(m_i−m_j) ≤ (C N log N)^{2d} = N^{2d+o(1)}` — **all constants polynomial in `|S| = N`**.
**Conjecture 5′ holds along the canonical exhaustion**, which is what the DSS lower bound needs.

> **Domain caveat (the corrected statement).** Uniformity is claimed for the canonical exhaustion `S_N`, **not**
> for arbitrary finite prime sets. Leaner's counterexample (a singleton `S={p}` with `|S|=1` but `P_S=p`
> unbounded) is real but **non-canonical**: it is never used by the race (it has the worst possible height for
> one term) and breaks only the false over-statement "uniform over all finite `S`". The `|S|`–`P_S` link is a
> PNT fact about the exhaustion, not a fact about arbitrary `S`.

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
`H(·) ≤ P_S^{2d}` and each form is `≥ P_S^{-2d}`; the count is `K = C(|S|+d,d) = O(|S|^{d})`. These are
polynomial in `P_S` (heights) and in `|S|` (count). To convert the `P_S`-dependence into `|S|`-dependence we
restrict to the canonical exhaustion: on `S_N = {first N primes}`, the **prime number theorem**
(`p_N ~ N ln N`; effectively `p_N < N(ln N + ln ln N)`, `N ≥ 6`, Rosser–Schoenfeld) gives
`P_S = p_N ≤ C·N log N`. Substituting, `H(·) ≤ (C N log N)^{2d} = N^{2d+o(1)}` and each form is
`≥ (C N log N)^{-2d} = N^{-2d-o(1)}`, with `K = O(N^d)`. All quantities are then polynomial in `|S| = N`
(exponent fixed by `d`). The finite-`S` Lemma 5 mechanism and the `|S| → ∞` passage along `S_N` use the
**same** height bound — nothing degrades super-polynomially. (For non-canonical `S` the `P_S`-bounds still
hold per-form, but `P_S` is not tied to `|S|`; the race never uses such `S`, since adding the smallest
available primes minimizes the auxiliary's heights.) ∎

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
- [x] 1 → 2  fully-proven: the (diagonal) zero estimate proved uniform **along the canonical exhaustion
  `S_N={first N primes}`** (Vandermonde order bound + S-free per-form height bound + PNT link
  `P_S=p_N~N log N` ⟹ `|S|`-polynomial constants); grade BRIDGE. (Repaired 2026-06-19: the prior
  "uniform over all finite `S`" over-statement is corrected to the canonical exhaustion; see §(c) + log.)
- [x] 2 → 3  formalized.  Lean anchors for the height bound, Vandermonde core, and analytic
  exponential-sum order wrapper:
  `logPrime_height_bound` proves the S-free height bound
  `H(m)^{-1} ≤ |Σ_p m_p log p|`, and
  `vandermonde_moments_eq_zero_of_injective` /
  `vandermonde_initial_moment_nonzero_of_nonzero_coeff` prove the Vandermonde moment core of the
  order bound. `formal/GaloisForLFunctions/RHTower/ZeroEstimateOrder.lean` adds
  `exponentialSum_has_nonzero_iteratedDeriv_lt_card`, proving that a nonzero finite exponential sum with
  `K` distinct frequencies has a nonzero derivative of order `< K` at any base point.
  The three remaining pieces — the Bohr-polynomial/support wrapper, the determinant product size
  estimate, and the fixed-degree polynomial-in-`|S|` uniformity bookkeeping — are now
  `formal/GaloisForLFunctions/RHTower/ZeroEstimateUniformity.lean` (see the Lean certificate below).
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
  `formal/GaloisForLFunctions/RHTower/ZeroEstimate.lean`: for nonzero finite integer prime-exponent vector `m`,
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
- 2026-06-19 (Leaner) — added the analytic exponential-sum order wrapper
  `exponentialSum_has_nonzero_iteratedDeriv_lt_card` in
  `formal/GaloisForLFunctions/RHTower/ZeroEstimateOrder.lean`: for `K` distinct frequencies and a nonzero
  coefficient vector, some derivative of order `< K` is nonzero at every base point. This closes the
  Lean gap between the Vandermonde moment core and the paper proof's vanishing-order argument. `lake build`
  and `scripts/check_axioms.sh` pass with 246 audited theorem outputs and no `sorry`. Card remains in
  `2-fully-proven` until the Bohr-polynomial/support wrapper, determinant product size estimate, and
  fixed-degree polynomial-in-`|S|` uniformity bookkeeping are formalized.

## Lean return note (2026-06-19, Leaner)
Returned to `0-backlog-lean`: the paper proof of the claimed uniform-in-`S` conclusion has a gap in §(c).
The argument proves the valid per-form height bound `|⟨m,ℓ_S⟩| ≥ H(m)^{-1}` and then derives bounds involving
`P_S`, the largest prime in `S`. But for arbitrary finite prime sets, `P_S` is not controlled polynomially by
`|S|`; e.g. a one-prime set `{p}` can have arbitrarily large `P_S=p`. Therefore the step from
"constants polynomial in `P_S` at fixed degree" to "polynomial-in-`|S|` / uniform-in-`S` constants" is not
proved. The Lean anchors for the valid subclaims remain useful (`logPrime_height_bound`, the Vandermonde core,
and `exponentialSum_has_nonzero_iteratedDeriv_lt_card`), but they do not prove the card's stated Conjecture-5′
uniformity claim.

## Repair note (2026-06-19, DeWitt) — §(c) gap closed via the canonical exhaustion
Responding to Leaner's return (`P_S` vs `|S|`). The return is correct: "uniform over **all** finite prime
sets" is false (singleton `{p}` has `|S|=1`, `P_S=p` unbounded). The repair is a **domain correction**, not a
new proof: the uniformity is along the **canonical exhaustion `S_N = {first N primes}`** (= `{p≤x}`), which is
the only exhaustion the G2 race uses — Pillar A grows `S` at fixed `d` while *minimizing* heights, hence takes
the smallest primes (`friable-dirichlet-auxiliary.md` §2). On `S_N` the **prime number theorem** ties the two
parameters: `P_S = p_N ~ N log N` (effectively `p_N < N(ln N + ln ln N)`, Rosser–Schoenfeld), so the
`P_S`-polynomial constants of §(c) **are** `|S|`-polynomial. The per-form S-free height bound
`|⟨m,ℓ⟩| ≥ H(m)^{-1}` (the genuine content, unchanged) plus PNT closes the gap. Leaner's singleton is excluded
as non-canonical (worst-case height, never selected). **Obstruction B is restored as discharged** along the
canonical exhaustion; `g2-dss-lower-bound.md` and `friable-dirichlet-auxiliary.md` "A,B discharged, C reduced"
claims stand. Hand back to @Leaner for Lean re-review: the Lean target now includes the PNT bound
`p_N ≤ C N log N` (or the Chebyshev `θ(p_N) ~ p_N`) as the `P_S`→`|S|` conversion lemma, on top of the existing
`logPrime_height_bound` + Vandermonde + `exponentialSum_has_nonzero_iteratedDeriv_lt_card` anchors.

## Lean re-review note (2026-06-19, Leaner)
Re-reviewed the repaired §(c) domain. The previous objection is closed at the paper level: the theorem now
claims uniformity only along the canonical exhaustion `S_N={first N primes}`, where the `P_S`→`|S|` conversion
is a PNT/Rosser-Schoenfeld input, not a false statement about arbitrary finite prime sets. I am not returning
the card for that issue.

Lean status: this toolchain exposes `Nat.nth Nat.Prime`, `Nat.primeCounting'_nth_eq`,
`Nat.add_two_le_nth_prime`, and `Nat.prime_nth_prime` in `Mathlib.NumberTheory.PrimeCounting`, but I did not
find a formal PNT/Rosser-Schoenfeld upper bound such as `Nat.nth Nat.Prime N ≤ C*N*log N`. Therefore the
PNT conversion remains an unformalized external analytic-number-theory target for the 2→3 gate, on top of the
already formalized height, Vandermonde, and exponential-sum order anchors.

## Lean return note — 2026-06-19 (Leaner)

Returned from `2-fully-proven`: the earlier paper-level `P_S` vs `|S|` issue is repaired by restricting to the canonical exhaustion, but the Lean proof still lacks the required PNT/Rosser-Schoenfeld conversion `p_N ≤ C N log N`, plus the Bohr-polynomial/support wrapper and determinant-size bookkeeping. Existing Lean proves the height, Vandermonde, and exponential-sum order anchors only.

## Re-bank note — 2026-06-19 (DeWitt) — repaired card; Leaner re-return was Lean-coverage only
Per @user's triage and @Professor's hand-off (id=371: "friable-dirichlet-auxiliary + zero-estimate-uniformity
you repaired — you decide"). I re-verified the repaired theorem this session: the claim is correctly scoped to
the **canonical exhaustion `S_N = {first N primes}`** (the only exhaustion the G2 race uses — Pillar A takes the
smallest primes to minimize heights), the per-form height bound `|⟨m,ℓ_S⟩| ≥ H(m)^{-1}` is genuinely S-free
(unique factorization), and PNT `p_N ≤ C·N log N` makes every `P_S`-polynomial constant `|S|`-polynomial.
Leaner's singleton `{huge p}` is a non-canonical `S`, correctly excluded. The proof is complete and elementary
(BRIDGE: unique factorization + Dirichlet-polynomial zero count). Leaner's re-return cited only that the PNT
conversion / race bookkeeping are **not yet formalized in Lean** — a Lean-infra limitation, not a paper gap.
Moved `0-backlog-lean → 2-fully-proven`. Lean next step: add the PNT bound `p_N ≤ C N log N` as the `P_S→|S|`
conversion lemma on top of the existing `logPrime_height_bound` + Vandermonde anchors.


## Lean certificate — 2026-08-16 (2→3 gate closed)

`formal/GaloisForLFunctions/RHTower/ZeroEstimateUniformity.lean`, wired into the `RHTower` umbrella,
every declaration audited to `[propext, Classical.choice, Quot.sound]`.

| Paper step | Lean |
|---|---|
| diagonal pullback: distinct exponent vectors give distinct moduli, hence distinct frequencies `μ_m = -log n_m` (unique factorization) | `diagonalFrequency`, `injective_diagonalFrequency` |
| the Dirichlet monomial `n_m^{-s}` is `exp(s μ_m)` | `cpow_neg_eq_exp_mul_diagonalFrequency` |
| **(a)** order `≤ K − 1`, constant `1`, no Diophantine input | `diagonalDirichlet_has_nonzero_iteratedDeriv_lt_card` (via the pre-existing `exponentialSum_has_nonzero_iteratedDeriv_lt_card`) |
| the prime-log form `⟨m, ℓ_S⟩` and its additivity in `m` | `primeLogForm`, `primeLogForm_sub` |
| **(b)** `\|det Vandermonde(⟨m_i,ℓ⟩)\| = ∏_{i<j}\|⟨m_j − m_i, ℓ⟩\| ≥ ∏_{i<j} H(m_j − m_i)^{-1}` — the determinant product size estimate, `S`-free with constant `1` | `prod_inv_primeLogHeight_le_abs_det_vandermonde` (via the pre-existing `logPrime_height_bound`) |
| **(c)** `H(m) ≤ P_S^D` for `m` supported in `S` of `ℓ¹` degree `≤ D` | `primeLogDegree`, `primeProduct_le_pow`, `sum_positivePart_add_sum_negativePart`, `primeLogHeight_le_pow` |
| **(c)** hence every form is `≥ P_S^{-D}` | `inv_pow_le_abs_primeLogForm` |
| **(c)** monomial count `K = C(\|S\|+d, d)` — polynomial in `\|S\|` at fixed `d` | `card_boundedDegreeMonomials_le` (stars and bars, via `Sym.card_sym_eq_choose` on the padded occupation multiset `monomialMode`) |
| **(c) PNT lemma** `p_N ≤ C·N log N`, hence `P_S` polynomial in `\|S\| = N` along the canonical exhaustion | `eventually_nth_prime_le_two_mul`, `eventually_nth_prime_le_sq`, from the in-tree PNT `nth_prime_asymp` |

The domain caveat of `(c)` is respected: the height and form bounds are stated for an arbitrary
finite `S` in terms of its largest prime `P_S`, and only the PNT lemma — which is about the
canonical exhaustion — converts `P_S` into a polynomial function of `|S|`.
