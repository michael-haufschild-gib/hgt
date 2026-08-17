# The (corank, trdeg) realization locus over Beurling systems is the full sub-diagonal — the two native invariants are independent coordinates

- **ID:** corank-trdeg-realization-locus
- **Stage:** 3-formalized
- **Type:** THEOREM (paper, elementary construction + the certified no-go §1) — a completeness/independence result
- **Owner:** Wheeler
- **Door grade:** **BRIDGE (substrate)** — a completeness theorem for the native invariant pair; imports are
  elementary transcendence-degree field theory + Nesterenko (for the explicit witnesses).
- **Source:** generalizes the single witness `B_dep` (point `(2,1)`) of `corank-arithmeticity-not-cardinality.md`
  and the two-tier split of `frobenius-collapse-linear-vs-algebraic.md` into the full realization locus.
  Continues the (A)/(V) axis-decoupling of `keystone-is-value-relational.md` / `faces-orthogonality.md`.

---

## §0 One line
Over finite Beurling generalized-prime systems, **every** admissible pair `(corank, trdeg) = (c,t)` with
`1 ≤ t ≤ c < ∞` is realized; `trdeg ≤ corank` is the **sole** relation between the two native invariants —
they are otherwise **independent coordinates**.

## §1 Setup and the upper constraint `[PROVED, recalled]`
For a finite generalized-prime system `{g_1,…,g_c}`, `L_i = log g_i`, the continuation block at `s=0` is
`T_0 = ℚ̄(e_1(L),…,e_c(L)) ⊆ ℚ̄(L_1,…,L_c)` (the `e_k` = elementary symmetric functions), with
`corank = dim_ℚ span_ℚ{L_i}` and `trdeg_ℚ̄ T_0 = trdeg_ℚ̄ ℚ̄(L_1,…,L_c)`
(`corank-arithmeticity-not-cardinality.md` §1, numerically certified). The general upper bound there gives
```
        trdeg ≤ corank          (the sole a-priori constraint).
```
So the realization locus is contained in `{(c,t) : 1 ≤ t ≤ c}`.

## §2 Completeness — every sub-diagonal pair is realized `[PROVED HERE]`
Fix `1 ≤ t ≤ c < ∞`. Pick `θ_1,…,θ_t ∈ (1,∞)` **algebraically independent** transcendentals (exist: explicit
for `t≤3` via Nesterenko `{π, Γ(1/4), e^π}`, non-constructive for all `t` via a transcendence basis). Take the
multiplier-logs
```
        L = { θ_1, θ_2, …, θ_t }  ∪  { θ_1^2, θ_1^3, …, θ_1^{\,c-t+1} }        (|L| = t + (c-t) = c).
```
- **corank `= c`.** The elements of `L` are **distinct monomials** in the algebraically independent
  `{θ_1,…,θ_t}`; distinct monomials in algebraically independent elements are **ℚ-linearly independent**.
  Hence `dim_ℚ span_ℚ L = c`. (Verified: `{π, e^π, π²}` → no ℚ-linear relation, PSLQ@80dps height ≤10¹⁴ =
  None, so corank 3; `{π,π²,π³,π⁴}` → None, corank 4.)
- **trdeg `= t`.** `ℚ̄(L) = ℚ̄(θ_1,…,θ_t)` since the extra powers `θ_1^k ∈ ℚ̄(θ_1)` add nothing; so
  `trdeg_ℚ̄ ℚ̄(L) = t`. By §1, `trdeg T_0 = t`.
- **valid Beurling system.** Order `L` increasingly, set `g_i = e^{L_i} > 1` (distinct, finite); a finite
  generalized-prime system.

So `(c,t)` is realized. Combined with §1: **the realization locus is exactly `{(c,t) : 1 ≤ t ≤ c < ∞}`.** ∎

## §3 Consequences `[PROVED HERE]`
- **Independence of the two native invariants.** `corank` (the linear / function-axis invariant, (A)) and
  `trdeg` (the value / transcendence-axis invariant, (V)) are **independent coordinates** on the Beurling
  moduli: knowing one constrains the other only by `trdeg ≤ corank`. This upgrades the abstract O/V split
  (`keystone-is-value-relational`, `faces-orthogonality`) to a **complete, concrete realization**.
- **The collapse defect `δ := corank − trdeg ∈ {0,1,…,c−1}` is freely tunable and structure-blind.** `δ=0` is
  the free/diagonal stratum (all multiplier-logs algebraically independent); `δ=c−1` is maximal collapse
  (`trdeg=1`, all logs in one `ℚ̄(θ)`). Every stratum is populated (§2). By
  `corank-arithmeticity-not-cardinality.md`, no native difference-Galois invariant determines `δ`.
- **DSS as diagonal membership.** For the prime truncation `M_S` (`S` a finite prime set),
  `δ_S = |S| − trdeg_ℚ̄ ℚ̄(\{\log p : p∈S\})`, and
  > **DSS-for-prime-logs ⟺ `δ_S = 0` for all `S` ⟺ `ζ_ℚ` lies on the `δ=0` (free) diagonal of the moduli.**
  The completeness theorem shows the diagonal is just one stratum among all `δ ≥ 0`, every one realized, so
  **no structural argument pins `ζ_ℚ` to the diagonal** — DSS is an arithmetic *position* on a moduli where a
  priori every position is possible. (Sharpens the no-go's "value-arithmetic, not structural.")

## §4 The ∞ fiber and the realization gap `[lattice-level PROVED / continuation OPEN]`
Corank `= ∞` is achievable at the **lattice** level with prescribed log-trdeg: `{θ^k : k ≥ 1}` (one
transcendental `θ`) gives `corank = ∞` (infinitely many ℚ-linearly independent powers) and
`trdeg ℚ̄(\{θ^k\}) = 1` — an **infinite-corank, value-trivial-at-the-log-level** system (the ∞-analogue of
`B_dep`). **But** the `trdeg` of the **continuation block** of an *infinite* system is a genuine limit and may
escape `ℚ̄(θ)` (the realization gap that sank `../5-failed/free-beurling-stieltjes-realization.md`; the
generalized Stieltjes constants carry their own structure constants). So:
- `(∞, t)` is realized at the **lattice/corank** level (rigorous);
- the **continuation-trdeg** of infinite systems — including `ζ_ℚ`'s own `(∞,∞)` — is the **open realization
  gap** (= `bigraded-corank-dss-cross §G`), not settled here.

This is the honest boundary: the finite locus is complete and proven; the infinite continuation-trdeg is the
apex and stays open.

## §5 Door passport
- **BRIDGE (substrate).** Completeness of a native invariant pair; elementary construction + §1.
- **Door-5 ✓:** over `F_q` / a single Frobenius the only realized point is `(1,1)` (the diagonal base); the
  rich locus is the arithmetic-base phenomenon.
- **Content beyond imports:** the **realization locus = full sub-diagonal** (independence of the two
  invariants) and the **DSS = δ=0 diagonal-membership** reframing. A literature search on Beurling systems
  produces neither (the invariant pair is project-native).

## Gates
- [x] 0→1→2: locus characterized (§1 upper, §2 completeness with explicit witnesses); independence + δ-defect +
  DSS-as-diagonal proven/derived (§3); ∞ fiber and the continuation realization gap honestly bounded (§4).
  Fully proven on the finite side; the conjectural `(∞,∞)`/DSS part is explicitly **not** the headline.
- [x] 2→3: formalized — `GaloisForLFunctions.HTGeometry.CorankTrdegRealizationLocus`
  (`corank_trdeg_locus`, `exists_corank_trdeg_realization`, `trdeg_adjoin_le_finrank_span`);
  axioms `[propext, Classical.choice, Quot.sound]`.  No Nesterenko import was needed.
- [ ] 3→4: pairs with the no-go + two-tier-F₁ cards as "the field's two native invariants are independent
  coordinates; DSS = ζ on the free diagonal."

## Notes / risk
- The construction is elementary; the contribution is the **completeness/independence framing** and the
  **DSS = diagonal-membership** corollary, not a transcendence advance. The ℚ apex stays open (§4).
- Honest scope: no claim that `ζ_ℚ` is on the diagonal (that IS DSS); only that nothing structural forces it
  there, with the whole moduli realized as the evidence.

## Log
- 2026-06-20 — Wheeler. Created directly in 2-fully-proven. Generalized `B_dep` to the full realization locus
  `{1≤t≤c<∞}` (completeness, §2, explicit witnesses verified); derived invariant-independence, the freely-tunable
  collapse defect `δ`, and DSS = `δ=0` diagonal-membership (§3). Flagged the ∞ continuation-trdeg as the open
  realization gap (§4). Door BRIDGE (substrate). A provable positive strengthening the no-go.

## Lean formalization — 2026-08-17

`formal/GaloisForLFunctions/HTGeometry/CorankTrdegRealizationLocus.lean`, unconditional
(`#print axioms` = `[propext, Classical.choice, Quot.sound]`).

| Paper step | Lean name |
|---|---|
| §1 upper constraint `trdeg ≤ corank` | `trdeg_adjoin_le_finrank_span` |
| §2 the witness family `θ_1,…,θ_t,θ_1^2,…,θ_1^(c-t+1)` | `locusFamily`, `locusExp` |
| §2 distinct monomials in a free family are ℚ-linearly independent | `locusExp_injective`, `locusExp_degree`, `linearIndependent_locusFamily` |
| §2 `ℚ̄(L) = ℚ̄(θ_1,…,θ_t)`, hence `trdeg = t` | `adjoin_range_locusFamily`, `trdeg_adjoin_range_locusFamily` |
| §2 valid Beurling system (`g_i = e^{L_i} > 1`) | `one_lt_locusFamily` (every member exceeds `1`) |
| §2 the realization statement | `exists_corank_trdeg_realization` |
| §0/§2 the locus (realization + sole relation) | `corank_trdeg_locus` |
| the same degree read on `ℚ̄(L)` | `trdeg_algebraicClosure_adjoin_range_locusFamily` |

Two notes on the formal route.

1. **No Nesterenko import is needed.**  The card proposed importing explicit witnesses
   (`π, Γ(1/4), e^π`) for `t ≤ 3`.  Lean uses instead the corpus theorem
   `HTGeometry.exists_algebraicIndependent_fin_real`, which produces an algebraically independent
   family of every finite size from a transcendence basis of `ℝ/ℚ`, so the theorem is proved for
   *all* `t` with no transcendence import.
2. **Positivity of the multiplier logs.**  The card takes `θ_i ∈ (1,∞)`.  Lean derives this by
   translating a free family by a rational, which preserves algebraic independence
   (`AlgebraicIndependent.add_const`, proved through the translation automorphism `shiftAlgEquiv`
   of the polynomial algebra).

Corank is formalized as `Module.finrank ℚ (Submodule.span ℚ (Set.range L))` and transcendence
degree as mathlib's `Algebra.trdeg ℚ (IntermediateField.adjoin ℚ (Set.range L))`; the corpus lemma
`HTGeometry.trdeg_algebraicClosure_restrictScalars_eq` transports the second to the card's `ℚ̄(L)`.

Not formalized, and explicitly not an obligation of this card: §4's infinite fibre
(the continuation transcendence degree of an infinite system), which the card marks as the open
realization gap, and the §3 DSS reframing, which is commentary on the formalized statements.

## Log

- 2026-08-17 Formalized in Lean 4 and promoted to stage 3.  Both halves of the finite locus — the
  upper constraint and the realization of every pair `1 ≤ t ≤ c` — are unconditional Lean theorems,
  with no transcendence import.
