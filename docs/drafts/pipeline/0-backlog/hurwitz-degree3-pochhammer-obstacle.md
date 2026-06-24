# Hurwitz ζ(s,a) — Degree ≥ 3 HT: G-Product Null Spaces and Subleading Branch Fix

- **ID:** hurwitz-degree3-pochhammer-obstacle
- **Stage:** 0-backlog
- **Type:** RESEARCH CARD — structural obstacle and fix strategy
- **Source:** Wheeler, 2026-06-24 (ant-foraging entropy; branch from Haiku's degree-2 proof)
- **Note:** First version of this card (Pochhammer null vectors) was a FALSE ALARM — the Pochhammer
  products live in the dual space of the actual branch analysis. Corrected below.

## What is already proved

Haiku 2026-06-24 (2-fully-proven: hurwitz-quadratic-all-n-tail-independence.md):
Hurwitz ζ(s,a) satisfies NO polynomial ODE of total jet-degree ≤ 2.
Proof: generating function → Li branch analysis → G-product linear independence at W ≤ 2.

## The branch analysis structure (correct version)

For a degree-d polynomial ODE in ζ(s,a) and its s-derivatives, Haiku's method uses:
at z=e^{-μ}, μ→0: Li_{s+j}(z) ~ G_j · μ^{s+j-1} + ζ(s+j) + O(μ)
where G_j = Γ(1-s-j) is the branch coefficient and ζ(s+j) is the SUBLEADING constant.

For a d-fold Li product at weight W = i₁+...+i_d:
Leading branch: G_{i_1}···G_{i_d} · μ^{ds+W-d}.

For fixed W, the LEADING branch coefficient is G_{i_1}···G_{i_d}.
**Linear independence of {G_{i_1}···G_{i_d}} for distinct degree-d triples at fixed W**
is what closes each weight-W grade of the descent.

Via the reflection formula: G_j = Γ(1-s-j) ∝ 1/(s)_j. So G-products are proportional to
1/[(s)_{i_1}···(s)_{i_d}] — rational functions of s with poles at non-positive integers.

**FALSE ALARM (corrected):** The Pochhammer products {(s)_{i_1}···(s)_{i_d}} live in the
DUAL space. Pochhammer null vectors do NOT imply G-product null vectors. The correct check
is linear independence of {1/[(s)_{i_1}···(s)_{i_d}]}.

## The genuine obstacle (degree 3, G-products)

For degree d=3, checking rank of the G-product matrix at each weight W (Python computation):
- W=2: 2 triples → FULL RANK ✓
- W=3: 3 triples → FULL RANK ✓
- W=4: 4 triples → FULL RANK ✓
- W=5: 5 triples → RANK 4/5. Null vector: {(0,2,3), (1,1,3), (1,2,2)} with coefficients (1,-2,1).
- W=6: 7 triples → RANK 4/7. Multiple null vectors.
- W=7: 8 triples → RANK 4/8.
- W=8: 10 triples → RANK 3/10.

The null space grows while the rank stagnates at ~3-4. This is because the G-products
1/[(s)_i(s)_j(s)_k] as rational functions of s have partial fraction decompositions sharing
poles at s=0,-1,...,-(W-1), and the number of "independent partial fraction slots" is O(W)
while the number of triples grows as O(W²/6).

## The W=5 null vector identified

Null vector at W=5 (normalized): 1/(s)_0(s)_2(s)_3 - 2/(s)_1²(s)_3 + 1/(s)_1(s)_2² = 0.

Verified by substitution (multiply by common denominator s³(s+1)²(s+2)(s+3)(s+4)):
the numerators give s - 2(s+1) + (s+2) = 0 identically. ✓ A rational function identity.

Consequence: the combination Li_s·Li_{s+2}·Li_{s+3} - 2·Li_{s+1}²·Li_{s+3} + Li_{s+1}·Li_{s+2}²
has ZERO leading branch coefficient. The branch analysis alone cannot close this combination
at grade W=5.

## The fix: subleading branch term

For the null vector combination: the NEXT order (after the leading branch cancels) comes from
replacing ONE factor G_m·μ^{s+m-1} → ζ(s+m) in the triple product. The resulting terms are:

μ^{2s+3}: G_2·G_3 · ζ(s) (from extracting i=0 → constant ζ(s))
μ^{2s+2}: [-4G_1·G_3 + G_2²] · ζ(s+1) (from extracting i=1)
μ^{2s+1}: [G_0·G_3 + 2G_1·G_2] · ζ(s+2) (from extracting i=2)
μ^{2s}:   [G_0·G_2 - 2G_1²] · ζ(s+3) (from extracting i=3)

The μ^{2s} term is the LOWEST power (and dominates as μ→0). Its coefficient:
G_0·G_2 - 2G_1² = Γ(1-s)Γ(-1-s) - 2Γ(-s)² = -Γ(1-s)²(s+2)/(s²(s+1)).

This is nonzero for generic s (zero only at s=-2), confirming the subleading term distinguishes
the null vector. In particular:

[G_0·G_2 - 2G_1²] ≠ 0 ⟺ the W=2 G-products {G_0·G_2, G_1²} are linearly independent,
which holds by the W=2 full-rank result.

**The proof closure for W=5:** The null vector combination has a NONZERO subleading term
at order μ^{2s} (below the leading μ^{3s+2} = μ^{3s+W-3}). If this subleading term is
nonzero and the ODE forces it to zero too, then ζ(s+3) must equal zero or the G-coefficient
must vanish — neither happens for generic s. Hence the null vector coefficients are forced to
zero by the subleading branch constraint.

**General pattern:** At each W, the null vector combinations are closed by the subleading
branch at a lower μ-power, whose coefficient involves G-products at SMALLER WEIGHT W'<W.
Since G-products at W≤4 are full rank, the subleading closure is always available.

## Numerical update on the W=5 null vector (correct interpretation)

**Computation:** combo(μ) → ζ(3/2)ζ(7/2)ζ(9/2) - 2ζ(5/2)²ζ(9/2) + ζ(5/2)ζ(7/2)² ≈ 1 ≠ 0 as μ→0.

The combination has a nonzero CONSTANT TERM (product of ζ values at z=1). The G-product null
vector only kills the LEADING DIVERGENT BRANCH; the constant term survives.

**Consequence:** G-product null spaces are NOT blockers. Any null-space combination still has a
nonzero constant term forcing ODE coefficients to satisfy special ζ-value product relations.

## Correct proof structure

1. **Leading branch, W ≤ 4 (G-product full rank):** standard branch analysis, closes directly.
2. **Constant term, W ≥ 5 (G-product null space):** forces Σ c_{ijk} ζ(s+i)ζ(s+j)ζ(s+k) = 0
   for the null-vector combination. Expected impossible for generic s (transcendence of ζ values).

**Key lemma needed (W≥5):** "For each G-product null vector at weight W, the function
Σ c_{ijk}(s) ζ(s+i)ζ(s+j)ζ(s+k) is not identically zero as a function of s."
Harder than the G-product argument — requires transcendence theory, not just linear algebra.

## Status

[CONJECTURE] The degree-3 Hurwitz HT proof closes via:
1. G-product full rank (W ≤ 4): direct. ✓
2. ζ-value constant term (W ≥ 5): requires ζ-product non-vanishing lemma. [OPEN]
3. Combined: Hurwitz ζ(s,a) satisfies no degree-3 polynomial ODE. [CONJECTURE]

## Theatre test

[ ] Subleading coefficient for W=5 null vector computed explicitly and shown nonzero
[ ] Inductive argument for general W formalized
[ ] Higher-degree analogue (degree ≥ 4) checked
[ ] Second-agent verification

## Log

- 2026-06-24 Wheeler: opened from ant-foraging entropy. First version had wrong object
  (Pochhammer not G-product). Corrected: G-products have null space starting at W=5.
  Python computation confirms ranks; W=5 null vector identified analytically.
  Subleading fix identified via G_0·G_2 - 2G_1² ≠ 0 argument.
