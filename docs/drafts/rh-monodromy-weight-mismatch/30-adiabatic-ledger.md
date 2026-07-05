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

## 6. The ledger and its march, formalized [PROVED HERE — Lean]

`formal/GaloisForLFunctions/RHTower/LegAdiabatic.lean` states the §1 identity and the §5
closing over arbitrary gaps, axiom-clean `[propext, Classical.choice, Quot.sound]`.

Model. A charge between two poles at ahead-distance `s`, with behind spectator distances
`c₀,…,c_{L−1}`, ahead spectator distances `e₀,…,e_{R−1}`, the nearest ahead pole at `s`, the
about-to-be-swapped pole at `δ+s`:

* `legFieldOld = Σ_m coth(c_m/2) − coth(s/2) − coth((δ+s)/2) − Σ_r coth(e_r/2)`.
* `legFieldNew` is the same charge advanced by exactly the swapped gap `δ`: behind distances
  become `c_m+δ`, the old nearest-ahead pole becomes the nearest behind pole at `δ−s`, the
  swapped pole becomes the nearest ahead pole at `s`, ahead distances become `e_r−δ`:
  `legFieldNew = Σ_m coth((c_m+δ)/2) + coth((δ−s)/2) − coth(s/2) − Σ_r coth((e_r−δ)/2)`.

The advance-by-`δ` keeps the ahead-distance `s` invariant and crosses exactly one pole; the
two `coth(s/2)` cancel.

* `adiabatic_ledger`: **exactly**
  `ΔG = coth((δ−s)/2) + coth((δ+s)/2) + Σ_m [coth((c_m+δ)/2) − coth(c_m/2)]
        + Σ_r [coth(e_r/2) − coth((e_r−δ)/2)]` — the §1 identity, finite sums.
* `swap_cushion_gt_two`: `0 < s < δ ⟹ coth((δ−s)/2) + coth((δ+s)/2) > 2`.
* `behind_drift_abs_le` / `ahead_drift_abs_le`: each spectator increment has magnitude
  `≤ (δ/2)·csch²(nearer/2)` — the mean value theorem for `coth`, `coth′ = −csch²`.
* `adiabatic_march_pos`: **the closing** — if
  `Σ_m (δ/2)csch²(c_m/2) + Σ_r (δ/2)csch²((e_r−δ)/2) < coth((δ−s)/2) + coth((δ+s)/2)`
  (the (ADB-crude) hypothesis), then `ΔG > 0`. Every spectator is charged at full magnitude
  against the cushion; no sign cancellation, no convexity.

What remains is the field-class instantiation: verifying the (ADB-crude) hypothesis for the
concrete section-field gap sequences (`|δ_{j+1}−δ_j| = O(δ²)`, one-sided, `s < δ/2`), where
the LHS is `O(log/δ)` against a cushion `~ 2i/δ`. That is the general-gap join — a bounded
comparison of the two explicit `csch²`-series against the near-swap `coth`.

## 7. The crude no-signs bound is TIGHT; the clearing form is the rank pairing [PROVED HERE — Lean, correction to §5]

§5 claimed (ADB-crude) — the total-variation spectator energy against the near cushion — clears
with `1/δ` room. It does not. In the pole pairing (`legFieldOld/New`, `adiabatic_march_pos`)
each behind spectator's distance grows by the FULL swapped gap `δ`, so the nearest weight
`(δ/2)csch²(c₀/2)` alone is the same order as the near cushion `coth((δ±s)/2)`. Direct check on
the constant lattice: with `c_m = mδ − s` the LHS `Σ_m (δ/2)csch²(c_m/2)` exceeds the cushion
for every `s ≳ δ/4` (e.g. `δ = 0.1`, `s = δ/2`: LHS `≈ 94`, cushion `≈ 53`). The pole crude
bound is a correct sufficient condition but its hypothesis is UNMEETABLE on the physical fields.

The reason: the pole pairing hides the telescoping cancellation. Pairing by RANK instead — the
`k`-th nearest behind pole of one gap against the `k`-th of the next — makes each increment a
gap DIFFERENCE and exposes the two FAR poles as the cushion. Formalized in the same module:

* `legRankOld`, `legRankNew` — the rank fields (behind rank distances, shared nearest-ahead at
  `s`, ahead rank distances, and the single far pole each gap carries that the other has swapped).
* `adiabatic_ledger_rank` — **the exact rank identity**
  `ΔG = coth(fB/2) + coth(fA/2) + Σ_k [coth(newB_k/2) − coth(oldB_k/2)]
        + Σ_k [coth(oldA_k/2) − coth(newA_k/2)]`, with `newB_k − oldB_k = δ_{i+1} − δ_{i+1−k}`,
  `newA_k − oldA_k = δ_{i+1+k} − δ_{i+1}` — gap DIFFERENCES, zero on the constant lattice.
* `far_cushion_gt_two` — `coth(fB/2) + coth(fA/2) > 2` for `fA, fB > 0` (the two far poles):
  the ONLY unconditional input.
* `behind_gain_nonneg` / `ahead_loss_nonpos` — under gaps decreasing outward, behind increments
  are gains (`≥ 0`), ahead increments are losses (`≤ 0`).
* `rank_march_pos` — **the clearing closing**: if the net spectator drift is nonnegative (behind
  gains at least offset ahead losses), then `ΔG > 2`. The constant lattice is immediate (all
  increments zero, `ΔG =` far cushion `> 2`); a smooth field perturbs it by `O(δ²)`-weighted
  drifts.

So the genuine (ADB) is the SIGNED inequality `Σ behind gains ≥ Σ ahead losses` (§3), not the
no-signs total-variation bound (§5). The residual (#170) is exactly this: prove the net-drift
nonnegativity for the concrete section gap sequences — the `k`-wise pairing of the `k`-th
outward behind gain against the `k`-th ahead loss under `δ` convexity (`|Δδ| = O(δ²)`,
decreasing outward), so the outer half has gains dominating and `rank_march_pos` fires.
