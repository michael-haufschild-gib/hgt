# 37 — The Ledger Corrected: Far-Field Extras, (ADB) Reopened and Re-Closed

**Register: SEARCH** (a correction found by the 1→2 gate, plus the repaired closing
argument). Tasks #138/#142/#145. **This document supersedes doc 30 §5 (ADB-crude),
doc 35 Lemma C, and doc 35 Theorem B′/(M) as stated.** Doc 36's Lemmas A′/D/E′ and the
regime structure survive unchanged; Theorem S′'s numbers are revised in §4.

## 1. The correction: ΔG's extras are BOTH far-field [PROVED HERE]

Expanding ΔG(s) = G_{i+1}(s) − G_i(s) from doc 30 §1's own definition, with
matched-index pairing (behind k ↔ k for k ≤ i, ahead j ↔ j for j ≤ d−i−2, pole terms
cancelling by the matched-distance design):

> **ΔG(s) = coth((t_{i+2} − t_1 − s)/2)      [new far-BEHIND extra]
>   + coth((t_d − t_{i+1} + s)/2)            [old far-AHEAD extra]
>   + Σ_{k=1}^{i} [coth((B_k − Σ_k − s)/2) − coth((B_k − s)/2)]    [gains, Σ_k = δ_{i+1−k} − δ_{i+1} ≥ 0]
>   + Σ_{j=1}^{d−i−2} [coth((A_j + s)/2) − coth((A_j − Λ_j + s)/2)]  [losses, Λ_j = δ_{i+1} − δ_{i+1+j} ≥ 0]**

*Proof.* Count: G_i has i behind terms, one pole term, d−i−1 ahead terms; G_{i+1} has
i+1, one, d−i−2. Same-k behind pairing leaves the NEW k = i+1 term (distance
t_{i+2} − t_1); same-j ahead pairing leaves the OLD j = d−i−1 term (distance
t_d − t_{i+1}), entering ΔG with + sign since the old ahead sum carries − in G_i. The
old j = 1 near-ahead term coth((δ_{i+1}+s)/2) is PAIRED (against the new j = 1 term,
increment δ_{i+2} − δ_{i+1}) — it is a drift term, not an extra. ∎

**Doc 30's display listed "coth((δ_{i+1}+s)/2) [near swap extra]" — a bookkeeping
error.** Doc 29(b)'s lattice computation was correct all along: its two extras
coth(((N+1)δ−s)/2) and coth((s+(M−1)δ)/2) are exactly the far-behind and far-ahead
terms above. Cross-check on the lattice: drifts vanish, ΔG = two far extras > 2 ✓.

**Fallout.** The far extras exceed 1 by exponentially (behind) resp. polynomially
(ahead, ≈ 0.63/(t_d − t_{i+1})) small excesses in the bulk — there is NO O(1/δ)
cushion there. Doc 30 §5's (ADB-crude) — losses < cushion — is invalidated; with it
fall doc 35's Lemma C and Theorem B′'s criterion (M) (they bound a term the ledger
does not contain). The far-ahead excess DOES grow at the tip (few poles ahead:
excess ≈ 0.63/(Mδ̂)) — the cushion is a TIP phenomenon, consistent with every
measured deepening. The bulk march must be closed by the gains — doc 30 §3's original
(ADB) — which the next section does.

## 2. The repaired closing: convexity pairing with explicit remainder

Add the hypothesis (satisfied by c/j-model fields, and per-carrier checkable):

- **(F5) convexity:** the log-gap increments are ordered,
  δ_{j−1} − δ_j ≥ δ_j − δ_{j+1} ≥ 0 on the window (δ nonincreasing convex).

**Lemma G (termwise gain–loss domination, near range).** Pair gain_k with loss_k.
(F5) gives the increment ordering Σ_k ≥ Λ_k (both are k-fold sums of ordered
one-step drops). The weights: gain weight w^B_k = csch²((B_k−Σ_k−s)/2)/2, loss weight
w^A_k = csch²((A_k−Λ_k+s)/2)/2 — wherever B_k − Σ_k − s ≤ A_k − Λ_k + s (the behind
pole at matched index is nearer), w^B_k ≥ w^A_k and
gain_k − loss_k ≥ (Σ_k − Λ_k)·w^A_k ≥ 0. The nearness condition holds for
k ≤ k*(s) := ⌊√(2s/(C₀δ²))⌋, since B_k − A_k ≤ k²C₀δ² (cumulative second
differences) while the ±s shift contributes 2s. ∎

**Lemma H (remainder beyond k*).** For k > k*(s) the pairing can reverse; the total
reversal is second-order in C₀:
Σ_{k>k*} (loss_k − gain_k)⁺ ≤ Σ_k Λ_k·(w^A_k − w^B_k)⁺
≤ Σ_{k ≤ 4/δ} [kC₀δ²]·[k²C₀δ²]·(43/(kδ)³) + (exp tail)
≤ 172·C₀² + tail ≤ **200·C₀²**
(the reversed weight difference is driven by the same k²C₀δ² second-difference that
bounds Σ_k, so increment × weight-difference is O(C₀²) per term; constants folded as
in doc 36 §2(iii)). ∎

**Theorem B″ (the march, corrected).** Assume (F1)–(F5), δ ≤ 1. Then
ΔG(s_i) ≥ 2 + [far-ahead excess ≥ 0] − 200·C₀², so the march s_{i+1} < s_i holds
whenever **(M″): 200·C₀² < 2, i.e. C₀ ≤ 1/10** — uniformly in i, no per-index
criterion needed — and, at the tip, with the additional cushion 0.63/(t_d − t_{i+1}).

*Proof.* ΔG = extras + Σ(gain−loss) ≥ 2 + Σ_{k≤k*}(≥0) − Σ_{k>k*}(reversal) by
Lemmas G, H. ∎

**Honest range.** (M″) covers C₀ ≤ 1/10 (model fields c ≥ 10). For the actual
carriers (c ≈ 2, C₀ ≈ 1/2) the crude constant 200 does not clear; the folded
constants have known fat (the (4/3)/v³ bound for φ, integer-sum vs integral counting)
but a ~50× tightening is not plausible by polish alone. For c < 10 the march
inequality ΔG(s_i) > 0 is a FINITE PER-INDEX EVALUATION — the per-carrier protocol
checks it directly on the window (it is one number per index: d + G-sum at s_i). The
theorem's role is the tail: for every field class with C₀ ≤ 1/10 the march is
unconditional; below that, per-window certification.

## 3. What survives unchanged

- Doc 35: hypotheses (F1)–(F4), toolbox (T1)–(T6), Lemma A, Lemma B (the loss bound
  is exactly Lemma H's near-range input), the march-increment mechanism
  s_i − s_{i+1} ≥ ΔG/(2W̄).
- Doc 36: Lemma A′ (exact AM–GM margin), (T7), Lemma D (response — never used the
  near extra), Lemma E′ (swap sign — ditto), the three-regime architecture.

## 4. Theorem S′ renumbered with the corrected increment

With ΔG ≥ 1 (from Theorem B″ at C₀ ≤ 1/15, or per-carrier value γᵢ), increment
≥ 1/(2W̄) ≥ δ²/80:

1. Deep band s_i ≤ δ/3: ΔS ≥ (δ²/80)·(1.4·27/δ³) − 16/(M²δ²) = 0.47/δ − 16/(M²δ²)
   > 0 for **M ≥ 6/√δ** (δ ≤ 1).
2. Endpoint band s_i ∈ (δ/3, δ/2 − δ²/9]: ΔS ≥ (δ²/80)·(5/(12δ²)) − 16/(M²δ²)
   = 5.2·10⁻³ − 16/(M²δ²) > 0 for **M ≥ 56/δ**.
3. (E-band) is now M < 56/δ WHERE s_i is still in the endpoint band. Mitigation: the
   march is monotone, so s_i decreases along i — the endpoint band is an INITIAL
   segment of the march; once s_i < δ/3 the deep band's M ≥ 6/√δ takes over. The
   per-carrier protocol therefore records where s drops below δ/3 and applies the
   matching regime; only tip indices with BOTH s ≥ δ/3 and M < 56/δ remain for direct
   evaluation.

## 5. What this cycle establishes about the method

The 1→2 gate has now caught: (χ2)'s constants (doc 31), the unbanded response claim
(doc 29(c)), the swap-magnitude framing (doc 36 §3), and the near-extra mislabel with
its phantom cushion (doc 30 §1/§5 → doc 35 Lemma C). Each repair used exact structure
(shifted pairing, AM–GM gap, sign ledger, convexity pairing). The corrected
architecture is: **extras = 2 + tip cushion; gains beat losses by convexity up to an
O(C₀²) remainder; response and swap are sign-controlled; assembly closes per regime.**
Next objects: (i) formalize the §1 regrouping identity in Lean (finite-sum algebra —
it would have caught the doc 30 error mechanically; task #143); (ii) fold Lemma H's
constant honestly (the 200 has fat only to ~50×; state c ≥ 10 as the theorem range);
(iii) the per-carrier protocol now carries the c < 10 bulk march — pre-register it
with the (E-band) tip evaluation (#145).
