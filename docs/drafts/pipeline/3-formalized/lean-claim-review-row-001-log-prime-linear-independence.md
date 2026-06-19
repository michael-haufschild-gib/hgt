# Lean claim review row #1 — log-prime linear independence

- **ID:** lean-claim-review-row-001-log-prime-linear-independence
- **Stage:** 3-formalized (Lean verification DONE 2026-06-19, Leaner)
- **Type:** THEOREM (Lean) — Door grade **BRIDGE** (the proof is unique factorization; a single parent
  proves it). Foundational floor; the *corank-unification* that rests on it is the `BRIDGE (substrate)` part.
- **Priority:** FOUNDATIONAL
- **Source:** ../../door/00-status.md · 00-status row #1; ../../door/bucket-ledger-footholds.md
- **Claimed ledger status:** `THEOREM (Lean)`; no matching ticket was present in `../3-formalized/` as of
  2026-06-19 — hence this from-scratch audit.

## Statement (restated precisely)
The real numbers `{log p : p prime}` are **ℚ-linearly independent**: for any finite set of distinct primes
`p_1,…,p_n` and rationals `c_1,…,c_n` not all zero, `Σ_{i=1}^n c_i log p_i ≠ 0`. Equivalently, the ℚ-vector
space map `ℚ^{(primes)} → ℝ`, `(c_p) ↦ Σ_p c_p log p`, is injective.

## Paper proof (from scratch — researcher gate 1→2)

Suppose, for contradiction, `Σ_{i=1}^n c_i log p_i = 0` with `c_i ∈ ℚ` not all zero, the `p_i` distinct primes.

1. **Clear denominators.** Let `N` be a common denominator of the `c_i`; set `a_i := N c_i ∈ ℤ`. Then
   `Σ_i a_i log p_i = 0` with `a_i ∈ ℤ` not all zero.
2. **Exponentiate.** Apply `exp` (a homomorphism `(ℝ,+) → (ℝ_{>0},·)`):
   `1 = exp(0) = exp(Σ_i a_i log p_i) = ∏_i exp(a_i log p_i) = ∏_i p_i^{a_i}`.
3. **Separate signs into integers.** Put `P := {i : a_i > 0}`, `M := {i : a_i < 0}`. From `∏_i p_i^{a_i}=1`,
   `∏_{i∈P} p_i^{a_i} = ∏_{i∈M} p_i^{-a_i}` — an equality of two **positive integers** `A = B` (empty product
   `= 1`), with `a_i, -a_i ≥ 1` on `P, M`.
4. **Unique factorization (FTA).** The prime factorization of `A` involves exactly the primes `{p_i : i∈P}`
   (each to a positive power) and of `B` exactly `{p_i : i∈M}`. Since the `p_i` are **distinct**, `P` and `M`
   index **disjoint** prime sets. Two positive integers are equal iff their prime factorizations coincide
   (FTA); a prime in `A`'s factorization (`i∈P`) cannot appear in `B`'s (disjoint), so equality forces both
   factorizations empty: `A = B = 1`, i.e. `a_i = 0` for all `i∈P∪M`. Hence every `a_i = 0`, so every
   `c_i = 0` — contradiction. ∎

**Verdict: the claim is TRUE; the proof is complete and elementary.** The only nontrivial input is the
fundamental theorem of arithmetic (unique factorization), used in step 4. (The `exp`/`log` bijection on the
positives is used in step 2; injectivity of `log` is equivalent to the statement and is *not* assumed — the
argument runs through `exp`.)

## Door / D-axis grade — BRIDGE (foundational floor)
- **Door-2: FAILS → BRIDGE.** Stripped of any multi-`q` vocabulary, this is "distinct primes have
  ℚ-linearly-independent logarithms, by unique factorization" — pure elementary number theory, a single
  parent. It is the *classical floor*, not native.
- **D-axis note.** This linear independence is the **`T=1` / linear level** of the corank invariant
  (`corank(Λ)=∞` at the linear level = this statement; `friable-dirichlet-auxiliary.md` §6). The
  *substrate-load-bearing* content is the **unification** built on it (the corank's linear→algebraic
  filtration, the `F_q↔ℚ` split) — graded `BRIDGE (substrate)` elsewhere — not this floor itself.
- **Door-5.** Over `F_q(C)` the analogue is `{deg v · log q}` with a single `log q`: rank 1, so the analogue
  is "the place-degrees are ℤ-independent multiples of one `log q`" — corank 1 (matches #121).

## Gates
- [x] 0 → 1  in-progress: statement restated precisely; no reliance on the ledger `THEOREM (Lean)` label.
- [x] 1 → 2  fully-proven: complete from-scratch paper proof (clear denominators → exponentiate → FTA);
  verdict **TRUE**, grade BRIDGE. **(Researcher gate met.)**
- [x] 2 → 3  formalized — Lean theorem `linearIndependent_log_primes` in
  `formal/GaloisForLFunctions/Core.lean` proves the stated `ℚ`-linear independence of `{log p : p prime}`;
  `logPrime_linearIndependent_int` proves the cleared-denominator `ℤ` form, and
  `logPrime_no_rat_relation` in `formal/GaloisForLFunctions/OrbitFreeness.lean` gives the finite-relation
  reading. Leaner verified the names by scratch file and `#print axioms`; only the standard
  `[propext, Classical.choice, Quot.sound]` axioms appear. `lake build` green; `scripts/check_axioms.sh` PASS.
- [ ] 3 → 4  publication-ready: standalone note (this proof + the Lean certificate).

## Log
- 2026-06-19 — created in 0-backlog as a claim-review ticket for an un-ticketed `THEOREM (Lean)` row.
- 2026-06-19 (DeWitt) — researcher review DONE → 2-fully-proven: from-scratch paper proof confirmed
  (ℚ-relation → clear denominators → `exp` → `∏ p_i^{a_i}=1` → FTA, disjoint prime supports force all
  exponents 0). Verdict TRUE; grade BRIDGE (unique factorization = single parent); it is the linear-level
  floor under the corank unification (`BRIDGE (substrate)` content sits on top, not here). Lean-name
  verification handed to Leaner (2→3). No runpod (elementary).
- 2026-06-19 (Leaner) — moved to `3-formalized`: verified `linearIndependent_log_primes`,
  `logPrime_linearIndependent_int`, and `logPrime_no_rat_relation` against this toolchain by scratch file.
  `#print axioms` reports only standard axioms; `lake build` and `scripts/check_axioms.sh` pass with no
  `sorry`.
