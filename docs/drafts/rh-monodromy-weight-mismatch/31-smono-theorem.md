# 31 — (S-mono) on Section Fields: the Assembled Theorem

**Register: SEARCH** (assembly of proved pieces from docs 25–30; the two remaining
constant-chases are marked (χ1), (χ2) — until they are chased and #141 clears, nothing
here crosses to 2-fully-proven). Task #142 write-up, round 4.

## 0. Field class

**(F)** A finite log-field t_1 < … < t_d (t_k = log α_k, α_k the positive zeros of the
section A_d), with, on the outer window i ≥ (d−1)/2:

- **(F1) one-sidedness** — the field is finite with the evaluation range to its right in
  the outer regime (the recentered one-sided-far carrier shape, doc 24 §6);
- **(F2) midpoint-push input** — x-gaps nondecreasing on the span (P-J regime), so that
  the pairing lemma (doc 27 §3, transported by AM–GM per doc 29(a)) gives s_i < δ_i/2
  with outward-deepening margin;
- **(F3) regularity** — |δ_{j+1} − δ_j| ≤ C₀·δ_j² on the window (satisfied by δ_j ~ c/j
  bulk fields; the Airy edge only shrinks the drift sums).

## 1. Theorem

> **Theorem (S-mono, (F)-fields).** For d ≥ d₀ and every outer index i:
> S_{i+1} > S_i, where S_i = d + ¼Σ_k csch²((t*_i − t_k)/2) and t*_i is the equilibrium
> of gap i (Σ_k coth((t−t_k)/2) = −d). Consequently (doc 26 §5, doc 24 §3) the margin
> crosses 1 at most once along the outer equilibria; with doc 25's tracking clearance
> and the counting lemma, T = 1 and Z_c(J^d) = 2 on pair-carriers: **the DISC reader is
> exact on (F)-shaped one-sided-far carriers.**

## 2. Proof assembly (pieces and their status)

1. **s_i < δ_i/2, deepening** — doc 27 §3 + doc 29(a). PROVED (pairing at the midpoint;
   surplus 2i − d grows).
2. **The s-march s_{i+1} < s_i** — doc 30: G_i strictly increasing in s [PROVED];
   ΔG(s_i) > 0 by the exact ledger [PROVED] plus cushion domination:
   drift losses ≤ Σ|Δδ|·csch²/2 ≤ (χ1) < coth((δ_{i+1}+s)/2) − 1 ≈ 2/δ. **(χ1)** is the
   one summation comparison to chase: with (F3), LHS ≤ C₀·Σ_k δ²·csch²(kδ-scale/2)/2 =
   C₀·O(log window)·, RHS ~ 2/δ — clears by ~ 1/(δ log) ≫ 1 for d large. [Constant
   chase remaining; no structural gap.]
3. **dW/ds < 0 on (0, δ/2)** — doc 29(c), the disjoint-interval bound. PROVED for the
   lattice; the general-field version replaces the exact telescoping by the same
   disjoint-interval argument with (F2)-ordered distances — **(χ2)**: verify the
   interval-nesting under nondecreasing x-gaps (the intervals (B_k − s, B_k + s) remain
   disjoint since 2s < δ_i ≤ min-gap on the span). [Constant chase remaining.]
4. **Swap tail** — exponential, doc 29(d). PROVED-shape (explicit bound stated).
5. **Assembly** — ΔS = ∫(−dW/ds) over [s_{i+1}, s_i] + swap ≥ (s_i − s_{i+1})·
   min|dW/ds| − tail > 0, doc 29(e), using 2 and 3. The march increment is bounded
   below via |G′| = 2W: s_i − s_{i+1} ≥ ΔG/(2W̄) with ΔG ~ 2/δ from step 2's cushion.

## 3. Consequence map (conditional on (χ1), (χ2), #141)

(S-mono) ⟹ single crossing ⟹ T = 1 [doc 24 §3 counting + doc 25 tracking legs] ⟹
Z_c = 2 exactly on pair-carriers [Hurwitz visibility] ⟹ the DISC reader reads the true
local square class on one-sided-far windows ⟹ the #136/#140 u-plane instance is a
THEOREM-grade finite window-relation reading ⟹ combined with doc 22's ANNEAL reduction
(modulo #131 seam wiring), the window relation D ≡ L mod 4 on dominated windows reduces
to finite certified readings. The remaining structural inputs of the bridge identity
(#130) are then: the seam-transport lemma (#131) and the exceptional-set bookkeeping
(doc 22) — the reader side is closed.

## 4. Honest ledger of remaining gaps in the whole (SPUR-R) arc

- (χ1), (χ2): constant chases above [this doc].
- Lemma R (m ≥ 4 clusters): #139, proof-shaped, probe-certified.
- Citation gate: #141 (Levin p. 342–343; Craven–Csordas 1983) before any promotion.
- The (F2)/(F3) hypotheses for the ACTUAL u-plane carriers: measured (P-J: 0 violations;
  spacing regularity from the zero-counting function); a paper-register verification per
  carrier accompanies any instance claim.

Next objects: chase (χ1)/(χ2); Lean the doc 30 §1 ledger identity (finite coth algebra);
then the (SPUR-R) capstone statement and the return to the ladder front (#130/#131),
where the exactness of the reader now feeds the bridge identity's finite side.

## 5. (χ1), (χ2) chased [round 5 — both clear with explicit room]

**(χ2).** Pair the k-th behind term with the k-th ahead term. The pairing interval has
length (A_k + s) − (B_k − s) ≤ 2s, so each bracket is ≤ 2s·max|dφ(u/2)/du| ≈ 24s/(B_k)⁴
(φ = csch²coth, |φ| ~ 8/u³, |φ(·/2)′| ~ 24/u⁴). Summing over B_k ≈ kδ:
Σ brackets ≤ 24s·ζ(4)/δ⁴ ≈ 26s/δ⁴, while the near term is φ(s/2) ≥ 8·8/δ³·(δ/2s)³; at
the worst point s = δ/2 the comparison is 13/δ³ against 512/δ³ — **dW/ds < 0 clears by
a factor ≈ 40** for all s ∈ (0, δ/2], needing only B_k ≥ kδ(1 − o(1)) spacing
regularity from (F3). ∎(chased)

**(χ1).** With |Δδ| ≤ C₀δ² per step, the k-th increment is ≤ C₀kδ², the weight
≤ 4/(kδ)², so each term ≤ 2C₀/k and the drift-loss sum is ≤ 2C₀·log d + O(C₀); the
cushion is coth((δ+s)/2) − 1 ≥ 4/(3δ) − 1 ~ O(d/c). **Cushion domination clears by a
factor ~ d/log d** for d ≥ d₀(C₀, c). ∎(chased)

Both chases confirm §2's claims with quantitative margins; the (S-mono) theorem on
(F)-fields is now proved in outline at every step, with the per-carrier verification of
(F2)/(F3) as the remaining application-side input.

## 6. Citation audit: the critical chain is delegate-citation-free [round 5]

The (SPUR-R) chain as assembled — doc 24 counting lemma + doc 25 tracking clearance +
docs 26–31 outer monotonicity — uses ONLY in-lane proofs and classical Hermite facts
that are now machine-checked (SpurHermite.lean). The delegate-sourced citations (Levin
p. 342–343, Craven–Csordas 1983) support (HBJ) in doc 23 §2e, which the assembled chain
does NOT use (the winding/counting route superseded it). **#141 therefore gates only
doc 23's context bricks, not the (SPUR-R) theorem** — promotion of the (S-mono) arc is
blocked only by the (χ)-constants' final write-out and per-carrier (F)-checks.

Also noted: the #136/#140 truncation instance has verified SIMPLE zeros in its window,
so the instance-level theorem needs only doc 25's m ≤ 3 case — Lemma R (#139) is needed
for multiplicity-uniform generality (Ξ₁-grade statements), not for the finite instance.

---
**STATUS 2026-07-05 (task #138 verdict — doc 79):** (S-mono) is isolated as a **standalone**
open conjecture (proved in outline here; corroborated numerically, doc 79 §3), NOT a blocker
of #130. Its consumer, the DISC/SPUR-R reader, is retired: the live #130 counting is the
Rouché+EM spine (domination-only, unconditional). Promotion of this arc is not pursued — it
would discharge a hypothesis (`AMPReaderInput`) that no live object consumes.
