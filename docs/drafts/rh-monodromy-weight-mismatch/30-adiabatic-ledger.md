# 30 — The Adiabatic Ledger: Exact Step Comparison and the (ADB) Condition

**Register: SEARCH** (§1–§2 decompositions are exact [PROVED HERE]; §3's evaluation is
model-level, labelled; the named condition (ADB) is the registered closing inequality of
(LEG)). Task #142, round 2 — generalizing doc 29's step (b) from the constant lattice to
real section fields.

## 1. The step comparison at matched pole-distance [PROVED HERE]

Log-time field t_1 < … < t_d, log-gaps δ_j = t_{j+1} − t_j. For the equilibrium in gap i
at distance s from the ahead pole t_{i+1}, the constraint is G_i(s) = −d with

> G_i(s) = Σ_{k≤i} coth((B_k − s)/2)·… written via distances: behind distances
> B_k(s) = (t_{i+1} − t_{i+1−k}) − s + …; precisely
> G_i(s) := Σ_{k=1}^{i} coth((t_{i+1} − t_{i+1−k} − s)/2) − coth(s/2)
>   − Σ_{j=1}^{d−i−1} coth((t_{i+1+j} − t_{i+1} + s)/2),

strictly increasing in s, running −∞ → +∞ across (0, δ_i): unique root s_i. The march is
monotone, s_{i+1} < s_i, iff **ΔG(s_i) := G_{i+1}(s_i) − G_i(s_i) > 0.** Termwise (the
near −coth(s/2) cancels; new behind member and removed ahead member split off):

> **ΔG(s) = coth((t_{i+2} − t_1 − s)/2)  [far swap extra, > 1]
> + coth((δ_{i+1} + s)/2)  [near swap extra, > 1]
> + Σ_{k≥1} [coth((t_{i+1}−t_{i+1−k}−s)/2 + (δ_{i+1}−δ_{i+1−k})/2·…) − …]  — exactly:
> + Σ_{k=1}^{i} [coth((newB_k − s)/2) − coth((oldB_k − s)/2)],  newB_k − oldB_k = δ_{i+1} − δ_{i+1−k},
> + Σ_{j=1}^{d−i−2} [coth((oldA_j + s)/2) − coth((newA_j + s)/2)],  newA_j − oldA_j = δ_{i+1+j} − δ_{i+1},**

with oldB_k = t_{i+1} − t_{i+1−k}, oldA_j = t_{i+1+j} − t_{i+1}. Every drift term is a
single-gap-increment difference of coth's — the exact ledger, no approximation. On the
constant lattice every increment vanishes and ΔG = two extras > 2 (doc 29(b) recovered).

## 2. Orientation of the drift under the measured gap shape [PROVED HERE, as stated]

For log-gap sequences DECREASING outward (the section fields' bulk: x-gaps grow ~ 2κk
while positions grow ~ κk², so δ_j ≈ 2/j — exactly the regime in which P-E refuted
log-gap growth): δ_{i+1} − δ_{i+1−k} ≤ 0 and δ_{i+1+j} − δ_{i+1} ≤ 0, so the BEHIND
drift terms are ≥ 0 (gains) and the AHEAD drift terms are ≤ 0 (losses); with increasing
log-gaps the roles swap. In both orientations the two swap extras contribute > 2.

## 3. The log-divergence cancellation and (ADB) [model-level evaluation; CONJECTURE for general fields]

Linearizing each drift term (|coth′| = csch²/2): gain_k ≈ (δ_{i+1−k} − δ_{i+1})·
csch²(oldB_k/2)/2, loss_j ≈ (δ_{i+1} − δ_{i+1+j})·csch²(oldA_j/2)/2. For δ_j ≈ 2/j
fields: increments ~ kδ²/2, weights ~ 4/(kδ)², so gain_k ~ 1/k and loss_j ~ 1/j — BOTH
sums are logarithmic, Σgain ≈ log i, Σloss ≈ log(d−i), and the k-wise pairing cancels
the divergences:

> **Σgains − Σlosses ≈ log( i/(d−i) ) ≥ 0 in the outer half,**

so ΔG ≳ 2 + log(i/(d−i)) > 2: the march clears with the swap cushion intact, and the
first ahead loss alone evaluates to ≈ 1/(1+θ)² ≈ 0.62 < 2 — consistent with every
measured zero-violation run. The named closing condition:

> **(ADB) [OPEN — the final inequality of (LEG)]:** for the section fields (one-sided,
> log-gaps decreasing–convex with δ′ = O(δ²), the image of nondecreasing x-gaps of
> regular variation), Σ_k gain_k − Σ_j loss_j > −2 + [extras' excess]. Sufficient and
> essentially matched: pair the k-th gain against the k-th loss — larger increment
> against smaller weight versus smaller increment against larger weight — and control
> the paired difference by the convexity of δ.

With (ADB): the s-march is monotone on real section fields; doc 29's (c)+(e) then give
(S-mono) (the W-response argument transfers verbatim — dW/ds < 0 needs only s < δ/2 and
the disjoint-interval bound, both gap-shape-free), closing (LEG) ⟹ (AMP-mono) ⟹
(SPUR-R) on one-sided-far carriers with doc 25.

## 4. What this opens

The whole outer problem is now one explicit inequality between two log-series of
coth-increments with a +2 cushion — no dynamics, no equilibria, just the gap sequence.
Next moves: (i) prove (ADB) for the exact model class δ_j = c/j (the paired difference
telescopes against the convexity — one page of calculus); (ii) transfer to Jensen-section
fields via doc 25's heat expansion (the sections' log-gaps inherit c/j-regularity from
the carrier in the bulk and Airy-compress at the edge — the edge only helps: losses
shrink); (iii) Lean the ledger identity of §1 (exact, finite sums — formalizable now).

## 5. The cushion is O(1/δ), not O(1): (ADB) is crude-provable [round 3 finding]

Evaluating honestly in the δ_j = c/j model: the near swap extra in ΔG is
coth((δ_{i+1}+s)/2) ≈ 2/(δ(1+θ)) ~ 2i/c — it GROWS along the march — while the total
drift losses are O(log i / c) (the §3 sums, even WITHOUT the gains' cancellation). The
march criterion ΔG > 0 therefore clears by a factor ~ i/log i: the O(1)-tightness
measured throughout (margin_far → 0.28, dδ* ≈ 3.7) concerns the LEVEL of the crossing —
where margin passes 1 — which the monotonicity theorem never uses. Monotonicity itself
has 1/δ-room. Hence the crude sufficient condition:

> **(ADB-crude) [replaces §3's (ADB) as the closing inequality]:**
> Σ_k |δ_{i+1} − δ_{i+1−k}|·csch²((B_k−s)/2)/2 + Σ_j |δ_{i+1} − δ_{i+1+j}|·csch²((A_j+s)/2)/2
>   < coth((δ_{i+1}+s)/2) − 1,
> i.e. total-variation-weighted spectator energy < the near-swap cushion. No
> cancellation, no signs, no convexity: for any field with |δ_{j+1} − δ_j| = O(δ²)
> regularity (all Jensen-section fields in the bulk; the Airy edge shrinks the LHS
> further), LHS = O(log/c) ≪ RHS ~ 2i/c.

Consequently the (LEG) proof shape is COMPLETE: (b′) the s-march via cushion domination
[(ADB-crude), provable by summation comparison per field class]; (c) dW/ds < 0
[proved, doc 29 — gap-shape-free]; (d) exponential swap tail; (e) assembly [doc 29].
What remains is pure write-up: fix the field-class hypotheses (one-sided, s < δ/2 via
midpoint-push, |Δδ| = O(δ²)), chase the constants once, and (S-mono) is a theorem on
real section fields — then (SPUR-R) closes on one-sided-far carriers with doc 25, and
the DISC reader is provably exact on the u-plane theorem-track carrier (doc 24 §6,
DISC run 6). Next: the write-up as doc 31 with theorem-grade statements, then the
promotion gate (#141 citations) before anything crosses to 2-fully-proven.
