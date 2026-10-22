# HB all-order triangular QNM-renormalization no-go

- **ID:** HB-ALL-ORDER-QNM-RENORM-NOGO
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` · HB `ORIENT DYN`
- **Statement:** Every history-local perturbative QNM hierarchy with the actual mixed-Casimir-corrected leading Einstein--Teukolsky source and nonzero simple BM Jost derivative has a unique all-order modewise clock renormalization on every Xi fibre; formal solvability is therefore RH-blind, while vanishing of the full correction tower is exactly the critical wall and globally RH.

## Goal

Kill the full perturbative-solvability producer class in the surviving HB chain

`literal corrected spin-two source → arbitrary history-local all-order QNM hierarchy → formal QNM solvability / returned-Jost extinction → FE--Schwarz extinction → RH`.

This is upstream of the RH receiver: the hierarchy is solved without selecting a divisor and the leading forcing is the literal corrected source already present in the corpus. A route kill must prove universal all-order solvability on tilted fibres, not merely restate the existing second-order counterterm.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem `RHTower.d4BMMixedCasimirAllOrderTriangularQNMClockRenormalization_noGo`, targeted `lake build` green, targeted `#print axioms` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach

Use corpus `triangularSolve`: at perturbative order `k`, the new frequency shift has coefficient equal to the normalized simple BM Jost derivative, while every nonlinear remainder depends only on lower shifts. Nonvanishing diagonal gives existence and uniqueness by strong recursion. Require the source-reduced condition that every higher remainder vanishes on the zero history when the literal leading source vanishes. Strong induction should then classify the zero correction tower exactly by the leading source zero locus. Weld to the formalized mixed-Casimir source theorem and the global RH equivalence.

## Proof chain and significance target

1. Fix overtone `n`, Xi copy `q`, and arbitrary history-local nonlinear remainder `L_q(k, δ)`.
2. Seed order zero by the actual mixed-Casimir-corrected reduced chiral source `S(q)`.
3. Prove unique `δ : ℕ → ℂ` satisfying `D_n δ_k + L_q(k,δ)=0` for every order.
4. Prove `δ_0=-S(q)/D_n`, hence tilted fibres are solved with a nonzero leading shift.
5. Under source-reduced darkness preservation, prove `δ_k=0` for all `k` iff `S(q)=0`, iff `Re(q)=1/2`.
6. Quantify over Xi copies to prove global zero standard clock iff RH.

Success kills all finite-order and formal all-order modewise QNM-solvability variants at once. Failure pivots to a non-triangular resonance/collision hierarchy, which must violate the corpus simple-pole derivative or history locality.

## Paper theorem and proof

**Theorem `[PROVED HERE]`.** Write `S(q)` for the actual mixed-Casimir-corrected reduced chiral source and `D_n` for the normalized derivative of the simple BM Jost zero. Let

`L_q : ℕ → (ℕ → ℂ) → ℂ`

be any perturbative remainder hierarchy satisfying:

1. history locality: `L_q(k,v)` depends only on `v_j` for `j<k`;
2. literal seeding: `L_q(0,v)=S(q)` for every history `v`;
3. source-reduced darkness: if `S(q)=0`, then `L_q(k,0)=0` for every `k`.

For every overtone `n` and Xi copy `q`, there is a unique correction tower `δ : ℕ → ℂ` such that

`D_n δ_k + L_q(k,δ)=0`

at every perturbative order. Its leading term is `δ_0=-S(q)/D_n`. Moreover,

`(∀ k, δ_k=0) ↔ S(q)=0 ↔ Re(q)=1/2`,

and, for any family of such hierarchies over all Xi copies,

`(∀ q k, δ_q(k)=0) ↔ RH`.

If `Re(q)≠1/2`, every hierarchy equation still vanishes but `δ_0≠0`; hence solvability is bright and RH-blind. The leading corrected cross source, returned Jost value, and Evans determinant vanish at the Xi QNM because `δ_0` is exactly the already formalized unique BM counterterm.

**Proof.** Fix `n,q,L_q`. The corpus proves `D_n≠0`. Define `δ` by strong recursion:

`δ_k := -L_q(k,δ_{<k})/D_n`,

where `δ_{<k}` agrees with `δ` below `k` and is zero elsewhere. History locality replaces `L_q(k,δ_{<k})` by `L_q(k,δ)`, so multiplication by `D_n` proves every hierarchy equation. If `v` is another solution, strong induction gives `v_j=δ_j` for `j<k`; history locality equates the order-`k` remainders, and cancellation by `D_n≠0` gives `v_k=δ_k`. This proves existence and uniqueness.

At `k=0`, the truncated history is zero and literal seeding gives `δ_0=-S(q)/D_n`, the physical BM counterterm. If the whole tower is zero, its leading term is zero, hence `S(q)=0`. Conversely suppose `S(q)=0`. Strong induction gives `δ_j=0` below `k`, so the truncated history is zero; source-reduced darkness gives `L_q(k,0)=0`, whence the recursion gives `δ_k=0`. Thus the whole tower is zero exactly when `S(q)=0`. The corpus theorem `S(q)=0 ↔ Re(q)=1/2` gives the pointwise classification, and quantification over Xi copies plus the established source-extinction endpoint gives the RH equivalence. Off wall, `S(q)≠0`, so `δ_0≠0` although every hierarchy residual is zero. Finally `δ_0` equals the unique physical single-order counterterm, so the existing exact cross-source, returned-Jost, and Evans-factorization theorems supply leading returned extinction. ∎

## Novelty audit

- Lean-corpus search found only the single-order BM counterterm and generic triangular-system infrastructure; no HB all-order specialization or RH/nonselectivity classification.
- Current primary literature through 2026-08-30 gives all-order QNM frequency-shift formulas and emphasizes non-self-adjoint incompleteness/continuous-spectrum terms, but no Xi/RH classification and no theorem that all-order solvability selects a critical wall.

## No-go closure (mandatory when falsified)

- **Exact killing theorem/mechanism:** A simple Jost pole makes every history-local nonlinear perturbation hierarchy triangular with invertible diagonal; strong recursion uniquely absorbs the literal source on every fibre, including tilted ones.
- **Strongest positive survivor:** Full correction-tower vanishing is exactly the critical wall and globally RH. Any live HB successor must derive that independent standard-clock condition, or exhibit a genuinely non-triangular multiple-pole/resonance obstruction invalidating simple-pole recursion.
- **New insight:** Passing from one frequency counterterm to arbitrary formal order does not strengthen selection. Higher-order solvability contains no new horizontal information; all RH content is concentrated in forbidding the unique leading renormalization.
- **Status:** `[LEAN-PROVED]`. Exact capstone `RHTower.d4BMMixedCasimirAllOrderTriangularQNMClockRenormalization_noGo` in `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMAllOrderTriangularQNMClockRenormalizationNoGo`; strongest survivor and returned-Evans extinction are formalized. `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE]` pending independent proof/priority review.

## Lean certificate

- **Module:** `formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMAllOrderTriangularQNMClockRenormalizationNoGo.lean`
- **Capstone:** `RHTower.d4BMMixedCasimirAllOrderTriangularQNMClockRenormalization_noGo`
- **Positive survivor:** `RHTower.forall_d4BMMixedCasimirAllOrderQNMClockTower_allXi_eq_zero_iff_rh`
- **Physical return:** `RHTower.d4BMMixedCasimirAllOrderClockRenormalizedReturnDeterminant_qnmPlus_eq_zero`
- **Umbrella:** imported by `formal/GaloisForLFunctions/RHTower.lean`
- **Verification:** direct `lake env lean` PASS; targeted `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMAllOrderTriangularQNMClockRenormalizationNoGo` PASS; capstone and global survivor depend only on `propext`, `Classical.choice`, `Quot.sound`.
- **Lint:** new module is umbrella-reachable and contains no forbidden declarations; repository lint remains red only on unrelated pre-existing reachability debt.

## Log

- 2026-08-30 — created directly in 1-in-progress after corpus and current-literature audit; conjecture targets remaining HB source-dynamical chain.
- 2026-08-30 — `[PROVED HERE]`: strong-recursive existence, uniqueness, zero-tower classification, off-wall bright solvability, and global RH survivor closed on paper.
- 2026-08-30 — `[LEAN-PROVED]`: exact all-order class theorem, global zero-tower/RH survivor, and leading returned-Evans extinction formalized; direct and targeted build gates pass.
