# Grynkiewicz's Kneser-type extension of Pollard's theorem — Lean programme

- **ID:** `GRYNKIEWICZ-POLLARD-LEAN-001`
- **Stage:** 1-in-progress
- **Type:** FORMALISATION PROGRAMME (single external theorem)
- **Serves:** `matomaki-teravainen-linnik-multiplicative-lean.md`, layer item **L0.3** (the paper's
  Lemma 3.12, "popular Kneser"), which gates its Lemma 3.14 and hence Theorems 1.1 and 1.2.
- **Source:** D. J. Grynkiewicz, *On extending Pollard's theorem for `t`-representable sums*,
  Israel J. Math. 177 (2010) 413–439; arXiv:0803.2601 (LaTeX source fetched and read in full).
- **RH used:** no · **Computation used:** no

## The statement to be formalised

For `A, B` finite nonempty subsets of an abelian group `G`, write
`r_{A,B}(g) = #{(a,b) ∈ A × B : a + b = g}` and `A +_i B = {g : r_{A,B}(g) ≥ i}`.

> **Theorem (Grynkiewicz 1.1).**  Let `t ≥ 1` and `|A|, |B| ≥ t`.  Then either
> ```
> ∑_{i=1}^t |A +_i B| ≥ t|A| + t|B| − 2t² + 1          (P)
> ```
> or there exist `A' ⊆ A`, `B' ⊆ B` with `l := |A \ A'| + |B \ B'| ≤ t − 1`,
> `A' +_t B' = A' + B' = A +_t B`, and
> ```
> ∑_{i=1}^t |A +_i B| ≥ t|A| + t|B| − (t − l)(|H| − ρ) − tl ≥ t|A| + t|B| − t|H|   (S)
> ```
> where `H` is the (nontrivial) stabiliser of `A +_t B` and
> `ρ = |A' + H| − |A'| + |B' + H| − |B'|`.

## What the consumer actually needs

Matomäki–Teräväinen's Lemma 3.12 uses only: **(P)**, or **(`l ≤ t−1` and `A' + B' ⊆ A +_t B`)**.
It does *not* use (S).  But (S) is used *inside* Grynkiewicz's own induction (STEP 2, CASES 4.x),
so the full theorem is the right formalisation target; weakening the conclusion weakens the
induction hypothesis and breaks the proof.

## Prerequisites, and what the corpus already owns

| Input | State |
|---|---|
| Kneser's theorem `|A+B| ≥ |A+H| + |B+H| − |H|` | **owned** — `HTGeometry/AdditiveCombinatorics/Kneser.lean` |
| Coset convolution bound `r(c) ≥ |A|+|B|−|H|` for `A ⊆ aH`, `B ⊆ bH`, `c ∈ abH` | **owned** — `Convolution.lean`, `card_add_card_le_rep_add_card_coset` |
| Ambient convolution bound `r(c) ≥ |A|+|B|−|G|` | **owned** — `Convolution.lean` |
| Prop A(i): `|A+B| ≤ |A|+|B|−k ⟹ r(x) ≥ k` for `x ∈ A+B` | **owned** — `RepresentationCount.lean`, `card_add_card_le_rep_add_card_mul` |
| Prop A(ii): `|A|+|B| ≥ |G|+1 ⟹ A+B = G` | **owned** — `RepresentationCount.lean`, `mul_eq_univ_of_card_lt` |
| `A ·_i B`, `∑_{i=1}^t #(A ·_i B)`, layer-cake identity, total mass | **owned** — `RepresentationCount.lean`: `repSet`, `repSum`, `repSum_eq_sum_min`, `sum_rep`, `repSum_le`, `repSum_le_mul_card` |
| Dyson transform `A(x) = A ∪ (x+B)`, `B(x) = (x+B) ∩ A` | to build |
| Lemma 2.2 (critical pair) | **owned** — `DysonTransform.lean`, `card_mul_lt_of_insert` |
| Dyson transform | **owned** — `DysonTransform.lean`: `dysonLarge`, `dysonSmall`, `card_dysonLarge_add_card_dysonSmall`, `rep_dyson_le`, `repSet_dyson_subset` |
| Lemma 2.1 (additive-energy lower bound for `∑ |A +_i B|`) | **owned** — `AdditiveEnergy.lean`, `repSum_ge_min_of_rep_inv_le`; the paper's heuristic optimisation is replaced by the rigorous argument recorded below |
| The main induction (STEPs 1–3, CASES 3.1, 3.2, 4.1, 4.2 with SUBCASES 4.2.1–3) | the bulk |

### Proof of Prop A(i) from what is already owned

Grynkiewicz cites this as "a simple consequence of Kneser's Theorem" without proof.  Here is a
complete argument in terms of assets the corpus already has.

Let `H = stab(A+B)`, `φ : G → G/H`, `ρ_A = |A+H| − |A|`, `ρ_B = |B+H| − |B|`, `ρ = ρ_A + ρ_B`.
Fix `x ∈ A+B`; then `φ(x) ∈ φ(A) + φ(B)`, so choose `ᾱ ∈ φ(A)`, `β̄ ∈ φ(B)` with `ᾱ + β̄ = φ(x)`.
Put `A_ᾱ = A ∩ φ⁻¹(ᾱ)` and `B_β̄ = B ∩ φ⁻¹(β̄)`; both are nonempty and lie in single `H`-cosets
whose sum-coset contains `x`.  Each nonempty `H`-coset slice of `A` has at least `|H| − ρ_A`
elements, and likewise for `B`, so the coset convolution bound gives

```
r_{A,B}(x) ≥ r_{A_ᾱ, B_β̄}(x) ≥ |A_ᾱ| + |B_β̄| − |H| ≥ |H| − ρ .
```

Kneser gives `|A+B| ≥ |A+H| + |B+H| − |H| = |A| + |B| + ρ − |H|`, i.e. `|H| − ρ ≥ |A|+|B|−|A+B| ≥ k`.
Combining, `r_{A,B}(x) ≥ k`. ∎

## A rigorous replacement for the optimisation step of Lemma 2.1

Grynkiewicz's proof of Lemma 2.1 minimises `∑_{i=1}^t |A +_i B|` over "configurations of points
into cliques", relaxing clique sizes and multiplicities to real numbers and differentiating.  As
written it is a heuristic: the reduction to configurations in which all large cliques have equal
size, and all small cliques have size at most one, is asserted "by a simple extremal argument".
The following linear-programming argument is rigorous, elementary, and reproduces his constants
*exactly*.

**Setup.**  Write `r_g = r_{A,B}(g)`, `M = ∑_g r_g = |A||B|`, `Q = ∑_g r_g²`, and
`S = ∑_{i=1}^t |A +_i B| = ∑_g min(r_g, t)` (the layer-cake identity, already Lean-proved as
`repSum_eq_sum_min`).  Put `s = √(t(t−1))` and `μ = Q/M`.

**Key pointwise inequality.**  Let `a, b` be reals with `b > 0`, `a − b ≤ 1` and `a²/(4b) ≤ t`.
Then for every **integer** `r ≥ 0`,
```
min(r, t) ≥ a·r − b·r² .
```
*Proof.*  If `r ≥ t`, the right side is at most its unconstrained maximum `a²/(4b) ≤ t`.  If
`r ≤ t`, the claim is `r ≥ a r − b r²`, i.e. `b r ≥ a − 1` for `r ≥ 1`, which follows from
`a − 1 ≤ b ≤ b r`; and `r = 0` is trivial.  (Integrality of `r` is what rules out `0 < r < 1`.) ∎

Summing gives `S ≥ aM − bQ` for any such `(a, b)`.

**Two choices of `(a, b)`.**

1. If `μ ≥ t + s`, take `a = 2t/μ`, `b = t/μ²`.  Then `a²/(4b) = t`, and `a − b ≤ 1` is
   `μ² − 2tμ + t ≥ 0`, whose roots are `t ± s`; so it holds.  The bound is
   `aM − bQ = 2tM/μ − tM/μ = tM/μ = t·M²/Q`.
2. If `μ ≤ t + s`, take `a = 2(t − s)`, `b = 2t − 1 − 2s`.  Then `b > 0` (because
   `(2t−1)² > 4t(t−1)`), `a − b = 1`, and `a²/(4b) = t` (because `s² = t(t−1)`).  The bound is
   `M(a − bμ)`, and since `(t + s)(2t − 1 − 2s) = t − s`, the hypothesis `μ ≤ t + s` gives
   `bμ ≤ t − s`, hence `a − bμ ≥ 2(t−s) − (t−s) = t − s = t/(t+s)`.

So in all cases `S ≥ min( t·M/(t+s), t·M²/Q )`, which is exactly Lemma 2.1's inner bound.

**Energy identity.**  `Q = ∑_g r_{A,B}(g)²` counts quadruples `(a,b,a',b') ∈ A×B×A×B` with
`ab = a'b'`, and `∑_g r_{A,B⁻¹}(g)²` counts those with `a b⁻¹ = a' b'⁻¹`.  The involution
`(a,b,a',b') ↦ (a,b',a',b)` is a bijection between the two, so the two sums agree.  (This replaces
the clique-graph edge bijection of the source, and avoids introducing graphs at all.)

**Energy upper bound.**  With `r'_x = r_{A,B⁻¹}(x)`, `r'_x ≤ |B|` always (as `|A| ≥ |B|`) and
`r'_x ≤ k` off `T`:
```
∑_x r'_x(r'_x − 1) ≤ (k−1)·M + (|B|−k)·∑_{x∈T} r'_x ≤ (k−1)M + (|B|−k)|T||B| ,
```
so `Q = ∑_x r'^2_x ≤ kM + |T||B|(|B|−k) = |B|·( k|A| + |T|(|B|−k) )`, and therefore
`t·M²/Q ≥ t·|A|²|B| / ( k|A| + |T|(|B|−k) )`, exactly the second term of Lemma 2.1.

## Layer plan

- **G0 — DONE.** `Rep` layer: `A +_i B` as a `Finset`, `∑_{i=1}^t |A +_i B|`, monotonicity in `i`,
  `∑_{i≥1} |A +_i B| = |A||B|`, translation invariance.
- **G1 — Prop A(i), A(ii) DONE**; Lemma 2.2 (critical pair) still to do.
- **G2 — DONE.** Dyson transform.
- **G3 — DONE.** Additive energy and Lemma 2.1 (`AdditiveEnergy.lean`).
- **G4 — in progress.**  `HTGeometry/AdditiveCombinatorics/PollardGrynkiewicz.lean` fixes the
  statement (`PollardWeak`, `PollardStruct`, `defect`, `holes`), proves the base case
  `pollardWeak_of_card_eq`, the evaluations `repSum_eq_of_rep_le`, `repSum_mono`,
  `card_mul_le_repSum`, `mul_card_repSet_le_repSum`, and the measure facts
  (`card_add_card_le_two_mul_repSum`, `pollardMeasure`).  **STEP 1 is done:**
  `PollardStepOne.lean` (`rep_sdiff_add_rep_sdiff_le`, `repSum_ge_of_repSet_eq`),
  `PollardCoset.lean` (`exists_mul_notMem`, `card_mulStab_le_filter_add_holes'`) and
  `PollardStabiliserBound.lean` (`rep_comm`, the two Fubini lemmas,
  `pollard_step1_smallDoubling`) and `PollardStepOneMain.lean` (`satur`, `satur_mul_satur`,
  `defect_satur_le`, `satur_saturated`, `pollard_step1_largeProduct`, and **`pollard_step1`**).
  `PollardStepTwo.lean` has STEP 2's weak branch (`pollardWeak_of_erase_left/right`) and the
  monotonicity facts that make the induction measure drop.  `PollardDeletion.lean` has
  `rep_smul_mulStab` (representation counts are constant on `S(A)`-cosets), the exact deletion
  costs `repSum_erase_left_add_le`/`repSum_erase_right_add_le`, and the "unstuff" pigeonhole
  `exists_erase_drop`.  `PollardDysonWitness.lean` has `exists_dyson_witness` and
  `exists_max_dyson_witness`.  `PollardStabSmall.lean` has `repSet_eq_or_exists_erase_drop`
  (`#S(A) ≥ t` forces STEP 1 or STEP 2).  `PollardDysonMeasure.lean` has `repSum_dyson_le` and
  `dyson_measure_drop`.  `PollardDysonEnergy.lean` has `dysonFull`, the bridge
  `rep_inv_eq_card_dysonSmall` (`r_{A,B⁻¹}(x) = #((x·B) ∩ A)`) and the instance
  `repSum_ge_min_dyson` of Lemma 2.1 in the Dyson setting.  `PollardFullTranslations.lean` has
  `card_le_card_inter_add_holes` and `card_dysonFull_add_card_le` (`#T + #B + 1 ≤ #A + t` under
  (qubal)).  `PollardStepThreePoly.lean` has the two polynomial inequalities that end STEP 3
  (`case32_poly`, `case31_poly`) — the source's "routine calculation".
  `PollardQubal.lean` has `mulStab_subset_mulStab_mul`, `mem_dysonFull_of_card_ge` (how
  maximality of the Dyson witness is used), `mulStab_dysonFull_eq` (`S(T) = S(T·B)`) and **the
  condition (qubal)**.  `PollardCaseThreeTwo.lean` has the real-arithmetic pieces
  (`half_le_first_term`, `case32_first_branch`, `case32_denominator`, `case32_key`), and
  `PollardStepThreeCase2.lean` assembles **`case32_false`: CASE 3.2 of STEP 3 is closed**.
  Next: the spread condition `#φ_H(B) ≥ 2`; CASE 3.1 (the `t = 2` Sidon argument); STEP 2's
  structural branch; CASE 4; the induction assembly.
  The main triple induction (on `∑_{i=1}^t |A +_i B|`, then `|A|+|B|`, then `min(|A|,|B|)`).

## G4: design of the main induction

The group `G` never changes in the source proof (every appeal to the induction hypothesis is to a
pair of subsets of the same `G`), so no universe-polymorphic quantification is needed; only `A`
and `B` vary, with `t` fixed.

**Well-founded measure.**  Grynkiewicz induces on three quantities in turn.  Writing
`P = repSum A B t`, the lexicographic measure is
```
μ(A, B) = ( P , 2·P − (#A + #B) , min(#A, #B) ) ∈ ℕ ×ₗ ℕ ×ₗ ℕ ,
```
all three components decreasing.  The middle component is a natural number because
`#A + #B ≤ 2·#(A·B) ≤ 2·P` (the first inequality since `#(A·B) ≥ max(#A,#B)`, the second because
`repSet A B 1 = A·B` is one of the summands, for `t ≥ 1`).  Increasing `#A + #B` at fixed `P` —
which is what CASE 4.2 does when it inserts a new element — decreases this component.

**Case structure of the source proof** (all of it must be formalised):

- STEP 1: `(l ≤ t−1) ∧ (A'·_tB' = A'·B' = A·_tB)` ⟹ either the stabiliser bound (S) or the
  weaker `P ≥ t#A + t#B − t²`.  Uses Kneser, Lemma 2.2, and the `H`-hole count.
- STEP 2: if deleting one point of `A` or `B` drops `P` by at least `t`, apply the induction
  hypothesis to the smaller pair and conclude.
- STEP 3: `#((x·B) ∩ A) ≥ t` for the maximising `x`, else contradiction.  Splits:
  - CASE 3.1 (`t = 2`): ends in the polynomial inequality
    `−5|B|⁴ + 26|B|³ − 50|B|² + 40|B| − 15 ≥ 0`, false for `|B| ≥ 3`.  Uses `B` Sidon.
  - CASE 3.2 (`t ≥ 3`): ends in
    `0 ≤ −|B|³ + 4(t−1)|B|² − (6t²−8t+2)|B| + 2t³ − 4t² + 2t`, false for `|B| > 2t`.
  Both use Lemma 2.1 with `k = 1` resp. `k = t−1`, and the bound `#T ≤ #A − #B + t − 1`.
- CASE 4.1 (`l ≥ 1`) and CASE 4.2 (`l = 0`, with SUBCASES 4.2.1–4.2.3) run the Dyson transform.

**Note on `t`.**  `t` is fixed throughout the induction, so the theorem may be proved for
`t ≥ 3` independently of `t ∈ {1,2}`; `t = 1` is Kneser (already owned).  The consumer
(Matomäki–Teräväinen Lemma 3.12, with `t = ⌈εφ(q)/10⌉`) only ever needs large `t`, but the
statement is for all `t ≥ 1`, so CASE 3.1 is still required for a faithful formalisation.

## STEP 1, made rigorous

The source's STEP 1 says the `l` discarded elements "each contribute at least `|H| − ρ` elements to
`∑_{i=1}^t |A +_i B|` not contained in `A' + B'`", and that "the individual contributions are
cumulative".  That is a count of *representations*, not of elements, and the clean form is:

**Counting form.**  Since `A' · B' = A ·_t B`, every `c ∈ A'·B'` has `min(r(c), t) = t`, so
```
repSum A B t = ∑_c min(r(c), t) ≥ t·#(A'·B') + ∑_{c ∉ A'·B'} min(r(c), t) ,
```
and the second sum is at least the number of pairs `(a,b) ∈ A × B` with `a·b ∉ A'·B'` and exactly
one of `a ∉ A'`, `b ∉ B'` — a bound that needs `min(r(c), t) ≥ r'(c)` for the restricted count
`r'`, which holds because `r'(c) ≤ l ≤ t − 1`.  Those pairs split as
```
∑_{a ∈ A \ A'} #{b ∈ B' : a·b ∉ A'·B'} + ∑_{b ∈ B \ B'} #{a ∈ A' : a·b ∉ A'·B'} ,
```
the two families being disjoint.  So it suffices to prove, for each `a ∈ A \ A'`:

**Coset claim.**  If `A ∩ (A'·H) ⊆ A'` (which one may assume, after enlarging `A'` and `B'` by the
elements of `A`, `B` lying in `A'·H`, `B'·H` — this changes neither `A'·B'` nor the hypotheses),
then `#{b ∈ B' : a·b ∉ A'·B'} ≥ |H| − ρ`.

*Proof (shorter than the source's, and quotient-free).*  Suppose `a · B' ⊆ A' · B'`.  Then
`(A' ∪ {a}) · B' = A' · B'`, so Kneser applies to the pair `(A' ∪ {a}, B')` with the same
stabiliser `H`.  Since `a ∉ A' · H`, the coset `a • H` is disjoint from `A' · H`, whence
`#((A' ∪ {a}) · H) = #(A' · H) + #H`; Kneser then gives `#(A'·H) + #(B'·H) ≤ #(A'·B')`, and so
`#A' + #B' ≤ #(A'·B')`, contradicting small doubling.  Therefore some `b' ∈ B'` has
`a·b' ∉ A'·B'`; since `A'·B'` is `H`-stable, no element of `(a b')•H` lies in `A'·B'`, so every
`b` in the `H`-coset slice `B' ∩ b'•H` works, and there are at least `|H| − ρ_B ≥ |H| − ρ` of
them. ∎  (The source instead passes to `G ⧸ H`, establishes
`#(φA'·φB') = #φA' + #φB' − 1`, and invokes the critical-pair lemma there.)

Combining with Kneser (`t·#(A'·B') ≥ t(#A' + #B' + ρ − |H|)`) gives exactly the stabiliser bound
`(S)`; the complementary branch `#(A'·B') ≥ #A' + #B' − 1` gives `repSum ≥ t#A + t#B − t²`.

## Gates
- [ ] 0 → 1  in-progress: statement frozen, prerequisites mapped
- [ ] 1 → 2  fully-proven: every step of the source proof checked and gap-free on paper
- [ ] 2 → 3  formalized: Lean theorem, `lake build` green, axioms ⊆ {propext, Classical.choice, Quot.sound}

## Log
- 2026-08-21 — **CASE 3.2 of STEP 3 is Lean-closed** (`case32_false`), together with the condition
  (qubal) and the periodicity `S(dysonFull A B) = S(dysonFull A B · B)`.  Three more modules,
  axiom-clean and wired.
- 2026-08-21 — the analytic core of STEP 3 is Lean-closed: the bridge from the Dyson transform to
  Lemma 2.1, the bound on `#dysonFull`, and both terminal polynomial inequalities.  Three more
  modules, axiom-clean and wired.
- 2026-08-21 — the scaffolding around STEP 1 is Lean-closed: deletion costs and the unstuff
  pigeonhole, the Dyson witness selection, the smallness of `S(A)`, and the measure-decrease facts
  for the Dyson transform.  Four more modules, all axiom-clean and wired.
- 2026-08-21 — **`pollard_step1` is Lean-proved in full** (both branches, with the saturation
  construction).  STEP 1 is complete.
- 2026-08-21 — **G4 STEP 1 is Lean-closed** across four new modules, with a quotient-free proof of
  the coset claim that is shorter than the source's.  All axiom-clean and wired.
- 2026-08-21 — **G3 Lean-closed** in `HTGeometry/AdditiveCombinatorics/AdditiveEnergy.lean`:
  `energy`, `energy_inv`, `le_min_of_linear_quadratic`, `le_repSum_of_linear_quadratic`,
  `repSum_ge_min`, `energy_le_of_rep_inv_le`, `repSum_ge_min_of_rep_inv_le` (Lemma 2.1).
  All axiom-clean.  **G4 (the main induction) is now the only remaining layer.**
- 2026-08-21 — **the optimisation step of Lemma 2.1 has been replaced by a rigorous
  linear-programming argument** (section above) that reproduces the source's constants exactly;
  the source's own argument is heuristic as written.  G3 is now dependency-closed on paper.
- 2026-08-21 — **G2 and the rest of G1 Lean-closed** in
  `HTGeometry/AdditiveCombinatorics/DysonTransform.lean`.
- 2026-08-21 — **G0 and the two Propositions of G1 are Lean-closed**, in
  `HTGeometry/AdditiveCombinatorics/RepresentationCount.lean`; axioms clean.
- 2026-08-21 — created; source read in full; prerequisite audit done; the missing proof of
  Grynkiewicz's Proposition A(i) reconstructed from Kneser plus the corpus's coset convolution
  bound, so G1 is now dependency-closed on assets already in the tree.
