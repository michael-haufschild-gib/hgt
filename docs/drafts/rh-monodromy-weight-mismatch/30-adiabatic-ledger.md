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

## 8. (ADB) discharged: the net drift is coth-free, closed on one-sided-far carriers [PROVED HERE — Lean]

The `hADB` net-drift hypothesis of `rank_march_pos` is reduced in `LegAdiabatic.lean` to
elementary per-rank inequalities on the distances — no `coth` remains in the criterion.

* `rcoth_pair_ge` — the `coth` mean value LOWER bound `(b−a)csch²(b) ≤ coth(a)−coth(b)` (far
  endpoint), companion to `rcoth_pair_le` (near endpoint).
* `rank_pair_domination` — at one rank the behind gain dominates the ahead loss:
  `coth(newA/2)−coth(oldA/2) ≤ coth(newB/2)−coth(oldB/2)`, from three coth-free facts —
  inward drift on both sides (`newB≤oldB`, `newA≤oldA`), the behind interval to the left
  (`oldB≤newA`), and the behind increment wider (`oldA−newA ≤ oldB−newB`). Proof: bound the
  gain below by `(widthB/2)csch²(oldB/2)`, the loss above by `(widthA/2)csch²(newA/2)`, and the
  wider `csch²`-heavier behind box wins.
* `net_drift_nonneg` — sums it: with `R ≤ L` (outer half) the paired ranks are dominated and
  the surplus behind ranks are nonnegative gains, so net drift `≥ 0` — exactly `hADB`.
* `section_march_pos` — the capstone: `fA,fB>0`, `R≤L`, the per-rank inward-drift signs, the
  midpoint-push `oldB≤newA`, and the convexity width bound `oldA−newA ≤ oldB−newB` give
  `ΔG > 2`. The transcendental (ADB) inequality is gone; only these distance inequalities remain.

Translating the per-rank conditions to a gap field `δ_j` decreasing outward, with the charge
under midpoint-push (`s < δ_{i+1}`, ahead-distance short), the behind distance at rank `k` is
`(δ_{i−k}+…+δ_i) − s`, the paired ahead distance `(δ_{i+2}+…+δ_{i+2+k}) + s`:

* the signs are gap monotonicity (`δ` decreasing);
* the width bound `oldA−newA ≤ oldB−newB` is gap convexity termwise (the earlier gap-drops
  `δ_{i−k}−δ_{i+1}` exceed the later `δ_{i+1}−δ_{i+2+k}`);
* the midpoint-push `oldB ≤ newA` holds when `2s` covers the behind-minus-ahead cumulative gap
  deficit — TRUE for the near ranks, and for EVERY paired rank exactly when the ahead ranks are
  few and near, i.e. on the ONE-SIDED-FAR carriers (`R` small, the charge near the far edge).

Direct check, `δ_j = 1/j`, midpoint-push `s = δ_{i+1}/2`: all per-rank conditions hold for
`i = d−3, d−5, d−8` (`R = 1,3,6`) and `section_march_pos` fires; in the bulk (`R ≳ 10`) the
midpoint-push condition `oldB ≤ newA` first fails near rank `k ≈ 5`, where the behind cumulative
gap overtakes `2s`. So (ADB), hence the `s`-march monotonicity, is CLOSED on the one-sided-far
carriers — the exact regime `(SPUR-R)` consumes (doc 25, doc 30 §3). The bulk residual is now a
coth-free statement: the `csch²`-tail of the far paired ranks (where `oldB > newA`) is
negligible against the near behind gains — the §3 log-sum estimate, isolated and elementary.

## 9. The bulk closed: one summed csch²-box inequality [PROVED HERE — Lean; class check model-level]

Correction to §8's closing sentence. The bulk residual is NOT "far tail negligible against near
gains" in the form suggested there — the far paired ranks carry log-scale weight while the
DIST-surplus of the near ranks is only O(i^{−1/2}). Two findings replace it.

**(a) Per-rank domination genuinely fails in the deep bulk — exact scaling.** For δ_j = c/j at
rank k = αi (leading order, s-terms dropped), gain_k ≥ loss_k reduces to φ(1+α) ≥ φ(1−α) for

> φ(x) = x^{c+1} + x^{1−c} − 2x.

At c = 1: φ(x) = (x−1)², difference ≡ 0 — the harmonic field is the NEUTRAL case (measured
per-rank passes were borderline, not generic). At c = 2 (the physical section gaps δ_j ≈ 2/j,
§2): φ(1+α) − φ(1−α) = −2α⁵/(1−α²) < 0 — per-rank domination fails at EVERY bulk rank, with
per-rank deficit (8/i)·α²/(4−α²)² and paired total ≈ 8∫₀¹ α²/(4−α²)² dα = 4/3 − log 3 ≈ 0.235
at mid-carrier. Any bulk closure must absorb an O(1) paired deficit; no per-rank criterion can.

**(b) What absorbs it: the midpoint-push near-rank asymmetry.** The march compares behind
distances shortened by s against ahead distances lengthened by s. At the nearest ranks the
csch² weight is inverse-quadratic in distance, so at s = δ/2 the rank-0 behind box carries
weight ≈ 16/δ² against the ahead box's ≈ 16/(9δ²): surplus ≈ (8/c)(1 − 1/9) = 64/(9c) — an
O(1) surplus concentrated on O(1) ranks (measured: +3.52 at rank 0, +0.57 at rank 1, c = 2,
i = d/2 = 100; total net +4.65 against the 0.235 deficit). At s = 0 the rank-0 boxes invert
(0.99 vs 1.01): the midpoint-push window is a genuine hypothesis, not bookkeeping.

**The Lean.** `LegAdiabatic.lean`, axiom-clean:

* `net_drift_nonneg_csch` — (ADB) from ONE summed inequality: box every gain below by
  `((oldB−newB)/2)·csch²(oldB/2)` (far endpoint), every loss above by
  `((oldA−newA)/2)·csch²(newA/2)` (near endpoint); if the ahead box sum ≤ the behind box sum
  over the paired ranks, net drift ≥ 0. Individual ranks may lose; only totals compare.
* `bulk_march_pos` — the capstone: signs + `R ≤ L` + the box inequality give `ΔG > 2`.

**(htail) — the box inequality on the physical class [pre-certified, model-level]:**

> Σ_{k<R} ((oldA_k−newA_k)/2)·csch²(newA_k/2) ≤ Σ_{k<R} ((oldB_k−newB_k)/2)·csch²(oldB_k/2)

holds over δ_j = c/j, c ∈ [1,3], d ≤ 400, all outer-half positions, θ = s/δ ∈ [0.15, 0.5];
worst margin +0.33 (c = 3). Threshold θ_min ≈ 0.05 at c = 2, and the bulk equilibrium sits at
θ* solving 2 − 4θ = qθ(1−θ), q = dδ_{i+1} — θ* ∈ [0.29, 0.38] across the outer half, deep
inside the certified window. So (ADB), hence the s-march monotonicity, is closed on ALL
outer-half carriers of the section class: the one-sided-far closure of §8 plus the bulk via
`bulk_march_pos`. The Lean instantiation of (htail) for the concrete c/j class (finite coth
arithmetic, forgiving margins) is the remaining execution step.

**What this opens.** The inner half (R > L) is now the live object: the unpaired far LOSSES
contribute ≈ (2/c)·log(R/L) against the fixed 64/(9c) near surplus, so the march should stay
monotone down to log((d−i)/i) ~ 32/9 and FAIL for the charge within distance ~ d/30 of the
sparse edge [CONJECTURE — leading order]. A predicted monotonicity BREAKDOWN with a computable
boundary is a new named object (the march horizon): locate it exactly in the c/j model, ask
what the equilibrium cascade does PAST it (does the march reverse, or do equilibria pair-merge
there?), and whether (LEG)'s consumers ever route a charge through it.

## 10. The march horizon refuted; the boundary lives in the gap scale, not the position [MEASURED + Lean instance]

§9 predicted an inner-half monotonicity breakdown at log((d−i)/i) ~ 32/9. Direct equilibrium
scan (δ_j = c/j, equilibria G_i(s_i) = −d solved per gap, ΔG(s_i) evaluated exactly; c ∈
{1,2,3}, d ∈ {200, 1000, 5000}, every interior position): **no horizon exists**. ΔG(s_i) > 0
everywhere, both halves, zero violations. The prediction's error: the inner-half equilibrium
θ*(i) = s_i/δ_{i+1} RISES toward the sparse edge (0.78 at i = 1, c = 2) — the ahead crowd
pushes the charge away from itself, the opposite of the assumed θ* ≈ 2i/(cd) — and large θ
strengthens the near-rank box surplus faster than the extra ahead ranks add losses.

What the scan found instead, three structures:

* **U-shaped margin with a gap-scale boundary.** ΔG_min is d-stable and decays in c:
  13.9 (c=1), 4.95 (c=2), 2.93 (c=3), 2.63 (c=3.5), 2.42 (c=4), 2.19 (c=5), 2.09 (c=6),
  2.011 (c=8), 1.993 (c=12; d = 500). The margin over the bare swap value 2 dies at
  **c\* ≈ 10–12**: there the net drift is genuinely negative at the sparse-edge gaps and no
  box certificate can hold — yet the march STILL clears (ΔG = 1.99 > 0) on the cushion. The
  minimum migrates from mid-carrier (c ≤ 3) to the sparse edge (c ≥ 3.5). The boundary
  object conjectured in the position direction lives in the gap-scale direction.
* **The push horizon.** θ*(i) crosses 1/2 — breaking doc 29(c)'s W-response hypothesis
  s < δ/2, NOT the march — at i/d ≈ 0.5 (c=1), ≈ 0.04 (c=2), never (c=3, θ_max = 0.496).
  For c = 1 the extreme sparse-edge equilibria even overflow the next gap (s_i > δ_{i+1}).
* **Equilibrium window certified.** The (htail) box inequality holds over the FULL measured
  equilibrium range: θ ∈ [0.15, 0.8], c ∈ [1, 3], d ≤ 400, worst margin +0.33 (at θ = 0.15;
  small θ remains the only failure direction, threshold θ_min ≈ 0.05).

**The Lean instance** (`LegBulkCarrier.lean`, axiom-clean): the transcendence is quarantined
in two rational envelopes —

* `rcsch_sq_le_inv_sq` (pre-existing): csch²(v) ≤ 1/v², and
* `rcsch_sq_ge_rat` [NEW]: ((1 − v²/6)/v)² ≤ csch²(v) for v² ≤ 6, from the cubic bound
  `sinh_mul_one_sub_le`: sinh v·(1 − v²/6) ≤ v (two derivative passes from sinh v ≤ v·cosh v)

— after which (htail) at rational distances is exact rational arithmetic. `harm_bulk_march`
certifies the 24-pole harmonic carrier (gaps 2/j, charge one third into the twelfth gap):
ΔG > 2, entirely by `norm_num`. `harm_dist_fails` machine-checks that the interval condition
`oldB ≤ newA` fails at rank 5 — eight of ten paired ranks violate it, so this instance is
provably out of `section_march_pos`'s reach: the box comparison is doing real work.

**What this opens.** (i) The gap-scale boundary c\*: at c > c\* the box route dies while the
march survives — a THIRD decomposition must exist that is exact there (the pole pairing's
near cushion ~ 4/δ is the natural candidate: at large c the gaps are wide and its crude form
stops being tight — quantify the crossover between rank-form and pole-form certificates in
c). (ii) The push horizon bounds where (S-mono)'s W-response applies; the inner-half strip
i ≲ 0.04d (c = 2) needs either a W-response argument valid at s > δ/2 or a proof that
(SPUR-R) never routes a charge there. (iii) The symbolic c/j class theorem: the concrete
instance's envelope arithmetic is uniform enough to parameterize (harmonic-sum log bounds
are the only new ingredient).

## 11. The certificate union closes the march for ALL c; the crossover is Lean [PROVED HERE — Lean]

The gap-scale boundary c\* of §10 is not a boundary of the MARCH — only of the box certificate.
The march needs `ΔG > 0`, and the ledger `ΔG = cushion + gains − loss` supports a second,
weaker certificate that carries exactly where the box one dies:

> **weak certificate:** behind gains `≥ 0` and total ahead loss `< cushion` ⟹ `ΔG > 0`.

Since `gains ≥ 0` and `cushion > 2`, this needs only `loss < cushion` — no net-drift sign, no
outer-half count, no interval-position condition. As the gaps widen the ahead poles recede and
`loss → 0` while `cushion` stays above `2`, so the sparse, wide-gap regime is where the weak
certificate is EASIEST — precisely the regime the box certificate cannot reach.

**Certificate map (measured, δ_j = c/j, d ≤ 300, every position):** box-OR-weak covers EVERY
`(c, i)` for `c ∈ [2, 50]`, zero uncovered, zero march failures. The binding (minimum-margin)
certificate is `box` for `c ≤ 8` and flips to `weak` at `c ≈ 10–12`, staying weak thereafter —
the crossover c\* is the switch of the binding certificate, not a wall. In the whole
net-drift-negative region the total loss never exceeds `0.05`, vastly under the cushion.

**Lean** (`LegAdiabatic.lean`, `LegBulkCarrier.lean`, axiom-clean):

* `rank_march_pos_weak` — `ΔG > 0` from `gains ≥ 0` and `loss < cushion`, straight off the
  ledger. Strictly weaker premise than `rank_march_pos`'s `ΔG > 2`.
* `section_march_pos_weak` — the section form: behind inward-drift signs give `gains ≥ 0`, and
  one summed loss-below-cushion bound closes `ΔG > 0`.
* `wide_bulk_march` — a satisfiability WITNESS only, not a result: one fixed five-pole
  configuration (`0, 12, 18, 22, 25`, charge at `11.1`) where the box premise fails (net drift
  negative) while the weak premise holds (loss `≈ 0.26 < 2 < cushion`). A `norm_num` evaluation
  at a handpicked tuple proves nothing about the class; its sole content is that the two
  certificate premises are incomparable. The class-level, length-uniform statement is §12.
  (Same demotion applies to `harm_bulk_march` in §9: witness that the summed box premise is
  non-vacuous where per-rank domination fails — nothing more.)

**What this opens.** The march is now certified across the entire gap-scale axis by a UNION of
two coth-free certificates — box (dense, gains carry it) and weak (sparse, cushion carries it).
The remaining objects: (a) a single self-contained theorem taking the disjunction as hypothesis
(`box-data ∨ weak-data ⟹ ΔG > 0`) so a carrier picks its regime once; (b) the exact hand-off
locus in `(c, i)` — where does `loss = cushion` and where does `net drift = 0`, and do the two
loci coincide at c\*? Those two curves bounding a thin overlap band is the sharp form of the
crossover.

## 12. The length-uniform edge theorem: the first quantifier moved [PROVED HERE — Lean]

The measure separating a class result from a witness: does the theorem MOVE A QUANTIFIER
(fixed tuple → ∀ carrier length → ∀ positions → ∀ configurations the cascade visits)? §§9/11's
instances sit at level zero. This section moves the first quantifier: the march at the sparse
edge of the harmonic class, uniformly in the carrier length.

**Mixed certificate** (`rank_march_pos_of_gain_loss`, `LegAdiabatic.lean`): if the behind
gains total at least `γ` and the ahead losses stay below `2 + γ`, then `ΔG > 0`. This is the
formal hand-off object of §11(a) in interior form — `γ = 0` is the weak certificate,
`loss ≤ gains` is the box one, and the interior is what a configuration with a strong near
pair but non-negligible losses uses. The budget `2 + γ` prices the hand-off exactly.

**Theorem** (`harmonic_edge_march`, `LegHarmonicEdge.lean`, axiom-clean): on the harmonic
carrier (poles at partial sums of `2/j`, gaps `2/j`), with the charge in the widest gap at
ahead-offset `s ∈ [3/5, 1)` — a window containing the measured equilibrium `s* ≈ 0.78` (§10)
— the rank ledger of the step into the second gap is positive for EVERY number `R` of paired
ahead poles. No finite check can state this; `R` is universally quantified.

Ingredients, each a small reusable lemma:
* gain floor `2`: `1/v ≤ coth v` (tangent comparison `sinh v ≤ v·cosh v`) at the shrunken
  behind distance `(1−s)/2` against `coth v < 1 + 1/v` (from `2v + 1 < e^{2v}`) at the old
  one — `2/(1−s) − 1 − 2/(2−s) ≥ 2` on the window;
* loss cap `< 4 = 2 + γ`: exact excess `coth(a/2) − 1 = 2/(e^a − 1)`; the harmonic slice
  dominates the log, `harmT(3+k) − harmT 2 ≥ 2·log((k+4)/3)` (tangent-line bound per step);
  `e^s ≥ 1 + s ≥ 8/5`; together the `k`-th loss is at most the RATIONAL envelope
  `90/(8(k+4)² − 45)`; six explicit terms plus a telescoping tail `45/(4·9)` give
  `3.8867 < 4`, uniformly in `R`.

Pre-registered numerics (pure python, exact rationals where the proof is rational): envelope
cap `3.8867 < 4`; true loss saturates at `≈ 1.26` (`R = 2000, s = 3/5`) — the envelope is 3×
lossy and the gain floor pays for it; per-term envelope, telescope domination (`k ≥ 2`), and
gain floor verified on grids before writing Lean. Zero failures.

**What the theorem settles about §11's conjecture.** The goal's premise — "the instance's
envelope arithmetic is uniform enough to parameterize, with harmonic-sum log bounds the only
new ingredient" — is CONFIRMED at the sparse edge and REFUTED at mid-carrier: the edge column
needed exactly the log bounds (plus the mixed certificate), but the mid-carrier box inequality
has leading boxes `≈ 2/(ck)` on both sides that CANCEL, so log bounds alone cannot close it —
its content is the subleading midpoint-push asymmetry. The two residuals, precisely:

* **(MID-∀d)** the mid-carrier box theorem, ∀ carrier length: needs the subleading asymmetry
  of the harmonic boxes, not log envelopes. The convexity width inequality
  `wB_k ≥ wA_k` (indices `i−k, i+2+k` symmetric about `i+1`) is symbolic and banked on paper;
  the `csch²` weight comparison against it is the open half.
* **(EDGE-c)** the same edge theorem with the gap scale `c` as a parameter: the loss chain
  survives verbatim through `((k+4)/3)^c ≥ ((k+4)/3)²` for `c ≥ 2`, but the gain floor
  `2/(c/2−s) − 1 − 2/(c−s)` thins as `c` grows, so the `c`-power envelope must carry the
  shrinkage of the loss — an `rpow`-monotone elaboration of the same six-term-plus-tail chain.
* **(EDGE-i)** interior gaps at fixed rank `i`, ∀ length: same mixed certificate with gain
  floor from the rank-0 behind pair of width `c/i − c/(i+1) ~ c/i²` — the floor decays toward
  mid-carrier, quantifying exactly where the mixed route hands off to (MID-∀d). The hand-off
  curve `γ(i) = loss-cap(i)` is the next computable boundary object.

## 13. The push-horizon strip resolved: nothing consumes it, and the outer half self-discharges [PROVED HERE — Lean + doc 79]

§10(ii) asked for a W-response argument valid at `s > δ/2` in the sparse strip (`i ≲ 0.04d`,
c = 2) OR a proof that (SPUR-R) never routes a charge there. Both branches close, the second
in a stronger form than posed:

**No load-bearing consumer.** Doc 79 §1 (machine-checked import audit): the live #130
counting spine is a transitive-import island disjoint from every `Spur*` module. Nothing in
the load-bearing chain consumes the W-response ANYWHERE — the reader that would have routed
charges was retired. The strip question survives only inside the conditional (S-mono) island.

**The island never quantifies over the strip, and its outer range self-discharges.**
(S-mono) as isolated (doc 79 §4) quantifies over the OUTER equilibria — behind train at
least as long as ahead. The general-gap midpoint push is now Lean
(`LegMidpointPush.lean`, axiom-clean):

* `equilibrium_gt_midpoint` — on any pole-free gap, if the field's midpoint value exceeds
  the equilibrium level, the equilibrium sits right of the midpoint (`s < δ/2`);
* `paired_train_sum_ge` — the paired deficit envelope: each behind/ahead pair with the
  ahead partner nearer loses at most the mean-value box `((B−A)/2)·csch²(A/2)`; unpaired
  behind terms each add `> 1`;
* `midpoint_push_of_deficit` — the capstone: on ANY decreasing-gap-paired configuration
  (`M` pairs, `E` extra behind poles, two gap-edge poles), total deficit under the budget
  `2M + 2E + 2` ⟹ the level-`−(2M+E+2)` equilibrium has `s < δ/2`. The lattice is the
  zero-deficit case (exact cancellation), recovering the localization of
  `equilibrium_theta_gap`.

**Measured coverage (c/j, c = 2, d ∈ {200, 1000}):** the capstone's hypothesis-shape gates
it to the outer half by construction (`E ≥ 0`), and the budget holds from `i/d ≈ 0.503`
upward — nearly saturated at the boundary (`D = 198.7` vs budget `202` at `d = 200`, ratio
`0.98`), relaxing fast outward (`59` vs `300` at `i/d = 0.75`). The theorem's hypothesis
range and (S-mono)'s quantification range COINCIDE: every equilibrium the island quantifies
over satisfies the W-response hypothesis, provably; the strip (`θ* > 1/2`, inner edge) is
outside both the live chain and the island's scope.

**What this opens.** (a) The near-saturation at `i = d/2` says the budget `2M + 2E + 2` is
the RIGHT scale — the deficit-vs-budget ratio along the carrier is a sharp new invariant;
its symbolic c/j form (harmonic arithmetic, §12's toolkit) would locate the coverage
boundary as a class function. (b) The margin variant — budget slack ⟹ quantitative
`δ/2 − s` gap via the MVT pattern of `equilibrium_theta_gap` with a general-gap derivative
cap — is the remaining piece the island's assembly step (e) would want. (c) The strip
itself is now a free-standing object: the inverted-response regime `θ* > 1/2` where the
ahead crowd pushes the charge past the midpoint — what `dW/ds` does there is a fresh
question for the theory, blocking nothing.
## 14. The inverted-response strip has a sharp threshold: c_strip = 2, the physical carrier is marginal [MEASURED + CONJECTURE]

§13(c) named the strip `θ* > 1/2` — where the equilibrium sits LEFT of the gap midpoint,
`dW/ds` inverts, and (S-mono)'s mechanism reverses — as a free-standing object. Taking it
apart yields a threshold and two exact-looking edge constants.

**The strip exists iff `c < 2`; `c = 2` is marginal.** Full equilibrium scans (δ_j = c/j,
level −d, `d` up to 1.6·10⁴, `θ*(i)` over the entire inner half): the maximum over `i` of
`θ*(i)` behaves as

| c | θ_max trend in d | strip |
|---|---|---|
| 1.8 | 0.540 → 0.547 (rising) | YES |
| 1.9 | 0.514 → 0.520 (rising) | YES |
| 1.98 | 0.498 → 0.503 (crosses ½) | YES (asymptotic) |
| **2.0** | 0.493 → 0.498 (↗ ½⁻, never crossing) | **marginal** |
| 2.1 | 0.468 → 0.472 (below) | no |
| 3.0 | 0.327 (flat, well below) | no |

So the inverted-response regime is a strictly SUB-harmonic phenomenon. For `c ≥ 2` — every
carrier at or above the harmonic gap density — the strip is EMPTY: every equilibrium has
`θ* < 1/2`, so the W-response hypothesis `s < δ/2` holds at EVERY gap, not just the outer
half. This is stronger than §13's outer-half coverage: for the physical density there is no
strip to quarantine.

**The physical carrier sits exactly on the threshold.** Doc 30 §2: the section-zero fields
have `δ_j ≈ 2/j` in the bulk — `c = 2` EXACTLY, the marginal case. The section field is not
comfortably inside the no-strip regime; it sits on its boundary. Whatever protects the push
at `c = 2` does so with vanishing margin, not with room to spare.

**The marginal margin is `1/(π√d)` at the `√d` edge scale [CONJECTURE — 5-digit fit].**
At `c = 2` the deficit `1/2 − θ_max(d)` is not merely positive; scaled by `√d` it is a dead
constant:

> `(1/2 − θ_max)·√d = 0.31831` across `d ∈ [10³, 6.4·10⁴]` (pod, 5-digit stable) — i.e. `= 1/π = 0.318310`,

and the peak sits at `i_peak ≈ (π/4)√d` (measured `i_peak/√d = 0.785 ± 0.006 ≈ π/4`). The
`√d` location is the Airy/boundary-layer scale — the same edge doc 30 §10 flagged as
"the edge only helps: losses shrink." Here the edge is where the PUSH MARGIN is thinnest, not
thickest: the two edge effects pull opposite ways, and at `c = 2` they balance to a clean
`1/π` residue. The appearance of `1/π` (margin) and `π/4` (location) together points at a
single edge integral — the continuum limit of the coth-field near the sparse pole, where
`coth(x/2) → 2/x` and the harmonic pole spacing becomes a `1/√·` boundary layer.

**Why the threshold is `2`, conjecturally.** `c = 2` is exactly where §3's log-divergence
cancellation is marginal: behind-excess `Σ(coth(behind_k/2) − 1) ≈ Σ 2/behind_k` and
ahead-excess `Σ 2/ahead_k` are both logarithmic in the harmonic (`c = 2`) spacing and cancel
term-for-term at the midpoint; for `c < 2` (denser ahead crowd) the ahead-excess wins and
pushes the equilibrium past the midpoint (`θ* > 1/2`), for `c > 2` the behind-excess wins.
The strip threshold is the log-cancellation threshold — a testable identification, not a
coincidence of the scan.

**Pre-registered vs measured.** Predictions were `c_strip ≈ 2.95`, `ρ(boundary) → 1`,
`dW/ds > 0` in the strip. Outcomes: `c_strip = 2.0` (REFUTED, and sharper — the harmonic
value); the boundary ratio `ρ` does NOT converge to 1 but drifts above for `c = 2`
(`0.95 → 1.03`, envelope slop at the shape boundary) and to clean c-fractions for larger c
(`c=3: 0.62`, `c=5: 0.28`) (REFUTED — the near-saturation I reported at `i = d/2` was a
`c = 2`, moderate-`d` coincidence, not universal); `dW/ds > 0` UNTESTABLE at `c = 2`
(strip empty) — the inversion is a sub-harmonic (`c < 2`) fact. The `ρ`-invariant claim of
§13 is thus DOWNGRADED: `ρ` is a conservative envelope proxy for the push margin, not a
class-sharp locator; the sharp locator is `θ_max(c) − 1/2` with threshold `c = 2`.

**What this opens.** (a) **Prove `c_strip = 2`** from the log-cancellation identity — a
clean class statement (`sub-harmonic ⟺ inverted response`) that would make the physical
carrier's marginality a theorem. (b) **The `1/π` edge law**: derive `(1/2 − θ_max)√d → 1/π`
from the continuum `2/x` coth-field on the `√d` boundary layer — a native edge-scaling
result for the construction. (c) **The marginal assembly question**: at `c = 2` the push
margin is `~1/(π√d) → 0`; whether (S-mono)'s energy gain at the Airy edge beats this
shrinking margin is the sharp form of the last (S-mono) step (e) — the push holds for every
finite `d`, but the assembly must be uniform against a `1/√d` margin, so the edge energy
gain must be shown `≳ 1/√d` there. (d) **The `c < 2` inverted branch** is now its own object:
a regime where the equilibrium overshoots the midpoint and `dW/ds > 0` — a place to ask what
the reversed energy response builds, blocking nothing.

## 15. c_strip = 2, proved: the log-cancellation residue is 1 − (π/c)cot(π/c) [PROVED HERE]

The threshold `c_strip = 2` measured in §14 is not a fitted constant; it is the unique zero of
an exact special function. The proof turns the midpoint field into a single classical integral.

**Setup.** Poles `T_j = c·H_{j−1}` (`H_0 = 0`, `H_{j−1} = Σ_{l=1}^{j−1} 1/l`), `j = 1..d`, level
`−d`. Gap `i` has midpoint `m = (T_i + T_{i+1})/2 = T_i + c/(2i)`. Write the behind and ahead
distances from `m`, indexed by rank `k`:

> `behind_k = c/(2i) + c·Σ_{l=i−k}^{i−1} 1/l`  (`k = 0..i−1`),
> `ahead_k  = c/(2i) + c·Σ_{l=i+1}^{i+k} 1/l`  (`k = 0..d−i−1`),

with `behind_0 = ahead_0 = c/(2i)` (nearest pair equidistant from the midpoint).

**Proposition 1 (exact midpoint identity).** Using `coth(u/2) = 1 + 2/(e^u − 1)` for `u > 0`
and oddness for `u < 0`, each behind pole contributes `+1 + 2/(e^{behind_k} − 1)` and each ahead
pole `−1 − 2/(e^{ahead_k} − 1)`:

> `F(m) = (2i − d) + 2(B − A)`,  `B = Σ_{k=0}^{i−1} 1/(e^{behind_k}−1)`,
> `A = Σ_{k=0}^{d−i−1} 1/(e^{ahead_k}−1)`.

Since `F` is strictly decreasing on the gap and `F(x*) = −d`, the strip condition is exactly

> `θ*(i) > 1/2 ⟺ x* < m ⟺ F(m) < −d ⟺ 2i + 2(B − A) < 0 ⟺ A − B > i`.

The `k = 0` terms are equal and cancel: `A − B = Σ_{k≥1} 1/(e^{ahead_k}−1) − Σ_{k=1}^{i−1}
1/(e^{behind_k}−1)`. **This is the log-cancellation.** Each sum diverges logarithmically —
near `k = 0`, `behind_k, ahead_k ≈ (c/i)(k+½)` so each term `≈ i/(c(k+½))`, giving the
harmonic `Σ 1/k`. The two divergences are identical and cancel in `A − B`, leaving a finite
`O(i)` residue.

**Proposition 2 (continuum limit).** For `c > 1`, with `d → ∞` then `i → ∞` (`k = xi`,
`c·Σ_{l=i+1}^{i+k} 1/l → c·log(1+x)` and `c·Σ_{l=i−k}^{i−1} 1/l → −c·log(1−x)` by
Euler–Maclaurin, uniformly on compacts, the `c/(2i)` shift vanishing), the paired Riemann sum
converges (dominated by the integrable envelope `F_a − F_b = O(1)` near `0`, `O((1+x)^{−c})` at
`∞`):

> `Φ(c) := lim (A − B)/i = ∫_0^∞ dx/((1+x)^c − 1) − ∫_0^1 dx/((1−x)^{−c} − 1)`

(each integral divergent at `0`, the difference convergent). Substituting the distance itself
(`u = c·log(1+x)` ahead, `v = −c·log(1−x)` behind — exact, no approximation) merges them:

> `Φ(c) = (2/c) ∫_0^∞ sinh(u/c)/(e^u − 1) du`.

**Proposition 3 (closed form, exact).** Expand `1/(e^u − 1) = Σ_{n≥1} e^{−nu}` and integrate
termwise: `∫_0^∞ sinh(u/c) e^{−nu} du = (1/c)/(n² − 1/c²)`. The Mittag-Leffler cotangent sum
`Σ_{n≥1} 1/(n² − a²) = (1 − πa·cot πa)/(2a²)` at `a = 1/c` gives

> **`Φ(c) = 1 − (π/c)·cot(π/c)`.**

**Theorem (c_strip = 2).** The inverted-response strip (`θ*(i) > 1/2` at the edge gaps
`1 ≪ i ≪ d`) is nonempty **iff `Φ(c) > 1`, i.e. iff `c < 2`.** `Φ` is strictly decreasing on
`(1, ∞)`: with `t = π/c ∈ (0, π)`, `Φ = 1 − t·cot t` and `d/dt(t cot t) = (sin t cos t − t)/
sin²t < 0` (since `sin t cos t = ½ sin 2t < t`), while `dt/dc < 0`; so `Φ: (1,∞) → (0,∞)`
decreasing, `Φ → +∞` as `c → 1⁺` (the c=1 gap overflow), `Φ → 0` as `c → ∞`. Hence `Φ(c) = 1`
has the **unique** solution `cot(π/c) = 0 ⟺ π/c = π/2 ⟺ c = 2`. At `c = 2`, `Φ(2) = 1 −
(π/2)cot(π/2) = 1` — **marginal**: the `O(i)` balance vanishes exactly, so the sign of
`F(m) + d` is set by the next order, the `√d` edge — consistent with §14's `1/(π√d)` margin. ∎

**Independent check of `Φ(2) = 1` (rational integrals).** At `c = 2`,
`(1+x)² − 1 = x(x+2)` and `(1−x)^{−2} − 1 = x(2−x)/(1−x)²`, so the bracketed difference on
`(0,1)` is `(1/x)[1/(x+2) − (1−x)²/(2−x)] = (2 − x²)/(4 − x²) = 1 − 2/(4 − x²)`, giving
`∫_0^1 = 1 − ½log 3`; the ahead tail `∫_1^∞ dx/(x(x+2)) = ½log 3`. The `log 3` cancels:
`Φ(2) = 1`. Two independent routes agree.

**What this settles and opens.** The measured threshold is now a theorem: `c_strip = 2`
exactly, uniquely, from the cotangent residue of the log-cancellation. The physical carrier
`δ_j ≈ 2/j` (§2) sits at `Φ = 1`, the marginal point — not inside the no-strip regime but on
its boundary, protected only by the `1/(π√d)` edge margin. The `cot(π/c)` is the native
signature of the harmonic pole spacing: its first zero at `π/c = π/2` IS the threshold, and
its pole at `c = 1` IS the overflow. Forward: (a) the same residue in the FINITE-`d` problem —
the `√d` edge correction to `Φ` should reproduce `1/π` (the `sin 2t = 2t` deficit at `t = π/2`
governs it); (b) does an analogous `Φ`-residue control the `dW/ds` sign in the `c < 2` inverted
branch, i.e. is the reversed energy response also a `cot`-threshold object; (c) `c_strip = 2`
against §3's log-divergence cancellation, now the SAME statement — the pairing that cancels the
`Σ 1/k` divergence leaves precisely this `1 − (π/c)cot(π/c)`.

### §15 formalized [PROVED HERE — Lean]

`formal/GaloisForLFunctions/RHTower/LegStripThreshold.lean` (axiom-clean
`[propext, Classical.choice, Quot.sound]`, in the umbrella, lint-green) formalizes the two exact
endpoints of the proof; the continuum-limit bridge between them (Prop 2) is the paper's stated
analytic layer.

* `poleExcess u = 1/(e^u − 1)`; `rcoth_half_pos` / `rcoth_half_neg` — the exact
  `coth(u/2) = 1 + 2·poleExcess u` decomposition (from `rcoth_sub_one`) and its odd reflection.
* `cothField_midpoint_split` — **Prop 1, exact**: `F(m) = (#behind − #ahead) + 2(B − A)` for any
  finite pole set and any `m` avoided by the poles. Pure finite rearrangement.
* `strip_iff_excess` — **the strip criterion**: with the gap pole-free and the equilibrium at
  level `−(pole count)`, `xEq < m ⟺ A − B > #behind`. The `coth` field is gone; the criterion is
  a finite inequality among `1/(e^·−1)` terms.
* `stripResidue c = 1 − (π/c)cot(π/c)`; `stripResidue_two` (`Φ(2) = 1`),
  `stripResidue_eq_one_iff` (**`Φ(c) = 1 ⟺ c = 2`**, via `cos(π/c) = 0` only at `π/c = π/2` on
  `(0,π)`, using `strictAntiOn_cos`), `stripResidue_gt_one_iff` (**`Φ(c) > 1 ⟺ c < 2`**, the
  strip is the sub-harmonic side) — the cotangent threshold, `c > 1`.
* `stripResidue_strictAntiOn` — **`Φ` is strictly decreasing on `(1, ∞)`**. From the series form
  `Φ(c) = Σ_{n≥1} 2/((cn)²−1)`, every term strictly decreases in `c` (the denominator strictly
  grows), so the sum decreases termwise (`Summable.tsum_lt_tsum`). This upgrades "`c = 2` is *a*
  crossing" to "`c = 2` is the *unique* crossing" by monotonicity, and makes the strip depth
  `Φ(c) − 1` a strictly increasing function of `2 − c` on the sub-harmonic side — the continuum slope
  whose finite-`d` avatar is the measured edge margin `1/(π√d)`. No `cot`-derivative needed: the
  monotonicity is read straight off the series.

The discrete reduction quantifies over ALL configurations (any pole set, position, level); the
threshold is the exact `c = 2`.

**Prop 3 formalized — the closed form as an explicit series.** `stripResidue_eq_tsum` proves
`Φ(c) = Σ_{n≥1} 2/((cn)² − 1)` for `c > 1`, by evaluating mathlib's Mittag-Leffler cotangent
expansion (`cot_series_rep`) at `x = 1/c` and descending complex→real; `stripResidue_series_summable`
proves the series converges (dominated by `(2/(c²−1))(1/n²)` via `(cn)²−1 ≥ (c²−1)n²`). This is the
substantive analytic half of the bridge: the residue is now a proven explicit convergent series,
not a bare `cot` definition — the same series `Σ 2/((cn)²−1)` that `(A−B)/i` limits to, and whose
`c = 2` value telescopes (`2/(4n²−1) = 1/(2n−1) − 1/(2n+1)`) to `1`.

**Prop 2's Riemann-sum core, formalized.** `tendsto_riemann_sum_antitone` proves the general fact
that for any `f` antitone on `[0,1]`, `(1/i)·Σ_{k<i} f(k/i) → ∫_0^1 f` — the discrete-to-continuum
step that mathlib does not package (it has only the one-sided sum↔integral sandwich; this squeezes
both sides, the gap being the telescoping `(f 0 − f 1)/i → 0`). `tendsto_riemann_sum_shell`
instantiates it on the concrete shell profile `(1+x)^{−r}` — the `n`-th ahead term after expanding
`1/(e^u−1) = Σ_{n≥1} e^{−nu}`, bounded and antitone unlike the singular full excess.
`tendsto_riemann_sum_antitone_Ioi` is the **infinite-domain upgrade**: for any `f` antitone and
nonnegative on `[0,∞)` and integrable on `(0,∞)`, `(1/i)·Σ_{k≥0} f(k/i) → ∫_0^∞ f`, with the
summability of the sample sequence `Σ_k f(k/i)` proven as part of the conclusion (mathlib has neither
the tsum comparison nor the improper Riemann-sum limit). Its proof runs two nested limits — the
finite sandwich per mesh, then `N → ∞` with the tail controlled by `∫_0^∞ f` — and is exactly the
half-line convergence the continuum passage `(A−B)/i → ∫_0^∞` needs.

**Prop 2's integral avatar, formalized — the closed loop `Φ(c) = ∫_0^∞`.** The continuum integral
`∫_0^∞ (2/c)·sinh(u/c)·1/(e^u−1) du` is now proven equal to the excess series, and hence to the
cotangent residue, over the whole half-line:

* `poleExcess_hasSum` — the geometric shell expansion `1/(e^u−1) = Σ_{n≥1} e^{−nu}` for `u > 0`,
  as a `HasSum` over `ℕ+` (geometric `HasSum`, drop the `n=0` term, reindex `ℕ ≃ ℕ+`).
* `integral_exp_neg_mul_Ioi` (`∫_0^∞ e^{−au} = 1/a`) and `shell_integral` — the per-shell Laplace
  transform `∫_0^∞ (2/c)·sinh(u/c)·e^{−nu} du = (1/c)[(n−1/c)⁻¹ − (n+1/c)⁻¹] = 2/((cn)²−1)`, an
  exact improper-integral evaluation on `(0,∞)`.
* `poleExcess_integral_eq_tsum` — **the interchange**: `∫_0^∞ (2/c)sinh(u/c)/(e^u−1) du =
  Σ_{n≥1} 2/((cn)²−1)`, via mathlib's `L¹` sum↔integral exchange `integral_tsum` (whose hypothesis
  `Σ_n ∫|shell_n| < ∞` is discharged from `∫ shell_n = 2/((cn)²−1)` and the series' convergence).
* `stripResidue_eq_integral` — the capstone weld: `Φ(c) = 1 − (π/c)cot(π/c) =
  ∫_0^∞ (2/c)sinh(u/c)/(e^u−1) du`, chaining the series form with the integral evaluation.

This closes the *analytic* half completely: the improper per-shell integral (the old step (b)) and
the shell interchange `Σ_n ∫ = ∫ Σ_n` (the old step (c)) are now both machine-checked inside
`poleExcess_integral_eq_tsum`. Both endpoints of the continuum integral — its series value and its
`cot` closed form — are proven.

**Every analytic brick of the continuum bridge is now machine-checked.** The discrete-to-continuum
passage `(A−B)/i → ∫_0^∞ (2/c)sinh(u/c)/(e^u−1) du` decomposed into (i) the improper monotone
Riemann-sum convergence `(1/i)Σ_k f(k/i) → ∫_0^∞ f`, and (ii) the harmonic-to-log substitution
`Σ_{l=i+1}^{i+k} 1/l → log((i+k)/i)` turning pole distances into the continuum variable
`u = c·log(k/i)`. Both are now in Lean: (i) is `tendsto_riemann_sum_antitone_Ioi`; (ii) is the
`HarmonicLog` cluster — `log_step_bounds` (per-step `1/(y+1) ≤ log((y+1)/y) ≤ 1/y`), `sum_log_step`
(telescoping `Σ log((i+j+1)/(i+j)) = log((i+k)/i)`), the two-sided `harmonic_log_lower/upper`, and the
capstone `harmonic_sub_log_le` (the harmonic tail approximates the log with defect `≤ 1/i → 0`). So
every endpoint (series value, `cot` closed form), the `Σ_n ∫ = ∫ Σ_n` interchange, the half-line
Riemann-sum limit, **and** the change of variables are formalized.

**The slope at the threshold, formalized [PROVED HERE — Lean].** `deriv_stripResidue_two` proves
`Φ'(2) = −π²/8` — the exact continuum slope of the residue at `c = 2`, built from the derivative of
`cot` (`hasDerivAt_rcot`, `(cot)' = −1/sin²` via `cos/sin` and the quotient rule) by the chain and
product rules, evaluated at `π/2` (`cot(π/2) = 0`, `sin(π/2) = 1`). This is the quantitative form of
`stripResidue_strictAntiOn`: the strip depth `Φ(c) − 1` opens with slope `π²/8` as `c` drops below
`2`, the continuum shadow whose finite-`d` avatar is the edge margin `1/(π√d)`. (`LegStripContinuum.lean`.)

**The ahead half of the passage, formalized end-to-end [PROVED HERE — Lean].** `tendsto_aheadShell`
proves that the discrete `n`-th **ahead** shell sum on the harmonic carrier — with the *exact* pole
distances `ahead_k = c/(2i) + c·Σ_{l=i+1}^{i+k} 1/l`, i.e. `(1/i)·Σ_{k≥0} e^{−n·ahead_k}` — converges
to `1/(nc − 1)`, the ahead term of the shell decomposition. The proof runs the whole bridge: expand
`poleExcess` into shells `e^{−n·ahead_k}`, sandwich each by the profile `(1+k/i)^{−nc}` via
`harmonic_sub_log_le` (the correction `e^{±nc/2i} → 1`), and send the profile Riemann sum to its
improper integral `1/(nc−1)` via `tendsto_riemann_sum_antitone_Ioi` and the reusable `Ioi`-shift
lemmas (`setIntegral_Ioi_add_right`, `integral_one_add_rpow`). This is a genuine physical-field
discrete quantity converging to its continuum value, with exact distances — not a uniform-`u`
resampling.

**The behind shell and the per-shell balance, formalized [PROVED HERE — Lean].** The **behind**
shell — `(1/i)·Σ_{k=0}^{i−1} e^{−n·behind_k}` with `behind_k = c/(2i) + c·Σ_{l=i−k}^{i−1} 1/l` —
converges to `1/(nc+1)` (`tendsto_behindShell`). Its backward tail is pinned to the log by a dedicated
`backward_harmonic` sandwich (`log(i/(i−k)) ≤ B_k ≤ log(i/(i−k)) + 1/(i−k) − 1/i`), the profile
`(1−x)^{nc}` Riemann sum converges by `tendsto_riemann_sum_antitone`, and `∫_0^1(1−x)^{nc} = 1/(nc+1)`
(`integral_one_sub_rpow`). The near-endpoint non-uniformity (the backward defect is `O(1)`, not
`O(1/i)`, at `k → i−1`) — which I earlier flagged as blocking a clean squeeze — is dissolved by a
*total* deviation bound: `1 − e^{−x} ≤ x` gives `(1/i)Σ_k dev_k ≤ nc/i → 0` (the per-term defect is
weighted by `(1−k/i)^{nc}`, tiny exactly where the correction is large), so the two-sided squeeze
`profileShell − nc/i ≤ behindShell ≤ profileShell` closes it — no ε-argument needed after all.

The capstone `tendsto_shellDiff` proves the **per-shell balance**: for every `n ≥ 1`, the `n`-th shell
of the discrete field's ahead-minus-behind balance, divided by `i`, converges to
`1/(nc−1) − 1/(nc+1) = 2/((cn)² − 1)` — exactly the `n`-th term of `Φ(c) = Σ_{n≥1} 2/((cn)² − 1)`
(`stripResidue_eq_tsum`). So `(A−B)/i → Φ(c)` is machine-checked **shell by shell**: each shell of
the physical field balance lands on its continuum residue term.

The literal *single-limit* statement `Σ_{n≥1} shellDiffTerm c n i → Φ(c)` is now **also closed**
(`tendsto_shellSum_stripResidue`, `LegStripCapstone.lean`, axiom-clean). It is the shell-sum
interchange `Σ_n lim_i = lim_i Σ_n`, a dominated-convergence exchange over `n`
(`tendsto_tsum_of_dominated_convergence`): each shell converges (`tendsto_shellDiff`), and the shell
differences are dominated uniformly in `i` by a summable bound `shellBound c n`. The uniform bound is
the technical core — writing the difference as `region1 + tail`:
* `region1_le` bounds the bulk `k < (i+1)/2` by `36864/(cn)²`. The cancellation
  `A_k − B_k ≤ A_k·(cn)·(S^b_k − S^a_k)` with `S^b_k − S^a_k ≤ 4k(k+1)/(3i²)` turns the difference
  into the geometric second-moment sum `Σ k(k+1)ρ^k = 2ρ/(1−ρ)³`, controlled uniformly in `i` by
  `β³e^{−β}/(1−e^{−β})³ ≤ 216`. This is a genuine second-order (midpoint-rule) Euler–Maclaurin remainder.
* `tail_le` bounds the ahead tail `k ≥ (i+1)/2` by `(3/2)(9/10)^{cn}/(cn−1)`, geometric in `n`: the
  offset-preserving profile `A_k ≤ e^{−cn/2i}((i+1)/(i+k+1))^{cn}` plus an antitone `p`-series tail
  give a base `e^{−1/2i}·2(i+1)/(3i) ≤ 9/10`.
Both are summable in `n` (`shellBound_summable`), so the exchange holds. The whole `(A−B)/i → Φ(c)`
arc — endpoints, per-shell limits, and the `n`-interchange — is machine-checked end-to-end.

## 16. The `1/π` edge law, derived: AM–GM of the shell correction against the truncation [PROVED HERE — analytic core + 5-digit-validated mechanism]

§14 measured `(1/2 − θ_max)√d = 1/π` and `i_peak ≈ (π/4)√d`. The mechanism is now identified and every
constant is pinned; the closed-form skeleton is a theorem (`LegStripEdge.lean`, axiom-clean).

**The deviation decomposes.** At `c = 2`, gap `i`, with `g(i) := i − (A − B)` (`A` truncated at the
finite pole count `d`), the equilibrium deviation is exactly `θ*(i) − 1/2 = (m − x*)/δ_i`, and
linearizing `F` at the midpoint (`F(m) − F(x*) = 2g(i)`, `x* − m = 2g(i)/F'(ξ)`):

> `1/2 − θ*(i) = 2·g(i) / (|F'(m)|·δ_i)`.

Three matched asymptotics fix the two competing scales and the local factor:

* **Local field factor** `|F'(m)|·δ_i → π²·i`, i.e. `κ := 2/(|F'(m)|δ_i/i) = 2/π²`. The nearest pole
  distances at `c = 2` are `behind_k, ahead_k ≈ (2k+1)/(2i)`, so `|F'(m)| = ½Σ_k csch²(dist/2) ≈
  (i²/1)·Σ_{k≥0} 1/(k+½)² = i²·(π²/2)`, using **`Σ_{k≥0} 1/(k+½)² = π²/2`** (odd Basel `= 4·π²/8`).
  Then `|F'(m)|δ_i = (π²i²/2)(2/i) = π²i`. [Numerically `|F'(m)|δ_i/i → 9.86960 = π²`, 5 digits.]
* **Truncation (finite `d`)** `A_trunc/i → i/d`: the `d − i` cut removes `A_trunc = Σ_{k≥d−i}
  poleExcess(ahead_k) ≈ Σ_{k≥d−i} i²/(k(k+2i)) → i²/d` from `A`. [Digamma-exact tail.]
* **Shell correction (finite `i`)** `ε(i) := poleModelDiff(2,i) − 1 → −(π²/16)/i`, where
  `poleModelDiff` is the infinite-ahead residue (`LegStripPoleModel.tendsto_poleModel`, `→ Φ(2) = 1`).
  [Numerically `i·(1 − poleModelDiff(2,i)) → 0.61685 = π²/16`, 5 digits after removing the finite-cutoff
  artifact.]

So `g(i)/i = A_trunc/i − ε(i) = i/d + (π²/16)/i` — a truncation term rising in `i` against a shell term
falling in `i`.

**The `√d` edge is AM–GM.** `min_{x>0}(x/d + a/x) = 2√(a/d)` at `x = √(a·d)` (`edge_amgm`,
`edge_amgm_eq`). With `a = π²/16`: the minimum margin is `(π/2)/√d` at `x = √(π²d/16) = (π/4)√d`
(`edge_peak_loc`). Scaling by `κ = 2/π²` and by `√d`, **the `√d` cancels exactly**
(`edge_margin_const`):

> `(1/2 − θ_max)·√d = κ · √d · min_i g(i)/i = (2/π²)·√d·(π/2)/√d = **1/π**`,  `i_peak = (π/4)√d`. ∎

The margin `1/(π√d)` and the location `(π/4)√d` are one AM–GM balance: the shell coefficient `π²/16`
sets `i_peak = √(π²d/16) = (π/4)√d`, and the local factor `2/π²` collapses `2√((π²/16)/d) = (π/2)/√d`
to the `1/π` residue. Both trace to `Σ 1/(k+½)² = π²/2` (the same near-pole `2/x` Coulomb kernel that
gives `Φ`'s `cot`) — the `1/π` is the odd-Basel constant read through the boundary layer.

**Status.** The closed-form skeleton — AM–GM minorant, attainment at the boundary layer, the exact
`√d`-cancellation to `1/π`, the peak at `(π/4)√d` — is machine-checked — including `edge_law_reduction` (given the sole physical input `½−θ_max = κ·m`
with `m` the least gap margin, the AM–GM minimum `edge_isLeast` and the `√d`-cancellation deliver
`(½−θ_max)√d → 1/π` rigorously) and `edge_law`, `edge_law_tendsto`; the local-factor constant is grounded — odd-Basel
`Σ 1/(2k+1)² = π²/8` (`hasSum_odd_basel`), the series `Σ 1/(k+½)² = π²/2` (`local_factor_series`), and
`κ = 2/π² = (Σ 1/(k+½)²)⁻¹` (`kappa_eq_inv_series`) are all theorems, so the `1/π` is provably the
odd-Basel constant read through the boundary layer.
The three inputs (`κ = 2/π²`, `A_trunc/i → i/d`, `ε(i) → −(π²/16)/i`) are matched Euler–Maclaurin/digamma
asymptotics of the `poleExcess` field; each is a finite-order correction to an already-formalized limit
(`Φ(2) = 1`, `tendsto_poleModel`). The discrete `θ*(i)` field is now **built** (§17.2): the decomposition
`½ − θ*(i) = g(i)/(W(ξ)δ_i)` is an exact theorem read off the field by the mean value theorem
(`harmonic_theta_deviation`), so `κ` and `m` are factors of a proven identity, not hypotheses. The three
input limits are the sole remaining formalization surface.

Forward (carried into §17): the AM–GM shape `local factor × √(shell·truncation)` is a **family**
`margin·√d → ρ(κ,a) = 2κ√a` (`edge_law_reduction_general`), with `κ(c) = c/π²` at the harmonic carrier
(§17.1) and `ρ(2) = 1/π`; the genuine one-parameter object is the marginal crossover `G(ξ)`,
`ξ = (2−c)√d` (§17.4).

## 17. The edge-law family, the discrete field, and the §14c race — made exact [PROVED HERE — Lean core]

§16 identified the edge law's shape `κ·√(shell·truncation)` and grounded `κ` in odd Basel. Three
things now stand on that shape as theorems: the edge law becomes a **family** in the local factor; the
`θ*(i)` field is **built** with its deviation identity, so the decomposition is read off the field
rather than assumed; and the §14c race — whether the (S-mono) energy gain beats the `1/(π√d)` margin —
is reduced to an **exact** sign condition. (`LegStripEdgeFamily.lean`, `LegStripField.lean`,
`LegStripHarmonic.lean`, axiom-clean.)

### 17.1 The edge-law family `margin·√d → ρ(κ,a) = 2κ√a` [PROVED HERE — Lean]

The `√d`-cancellation is not special to `κ = 2/π²`, `a = π²/16`. For any local factor `κ` and shell
coefficient `a ≥ 0`, `√d·(κ·2√(a/d)) = 2κ√a` exactly (`edge_margin_const_general`), and the reduction
`margin(d) = κ·m(d)` (`m` the least gap margin) delivers `margin·√d → ρ(κ,a) := 2κ√a`
(`edge_law_reduction_general`, via AM–GM uniqueness `edge_isLeast` and the cancellation). The harmonic
carrier is one point: `ρ(2/π², π²/16) = 1/π` (`rhoFamily_harmonic`).

The **local factor at a general harmonic carrier `δ_j = c/j` is `κ(c) = c/π²`** (`localFactor`): the
near-gap pole distances are `≈ (c/i)(k+½)`, so `|F'(m)| = ½Σ csch²(dist/2) → (16i²/c²)Σ_{k≥0}1/(2k+1)²
= 2π²i²/c²` and `|F'(m)|δ_i/i → 2π²/c`, whence `κ(c) = 2/(|F'|δ/i) = c/π²`, `κ(2) = 2/π²`
(`localFactor_two`). It is grounded in odd Basel: `κ(c) = c/(8·Σ 1/(2k+1)²)` (`localFactor_odd_basel`),
so the whole family's constant is the odd-Basel value read through the boundary layer.

### 17.2 The discrete `θ*(i)` field, built — the deviation identity is a theorem [PROVED HERE — Lean]

The `κ·m` decomposition is no longer an assumed input: it is the leading asymptotics of an **exact**
identity read off the field by the mean value theorem. On a pole-free gap `(a,b)` the field
`F = cothField s t` has `F' = −2W` (`W = ¼Σ csch²`, `cothField_hasDerivAt`), so for the equilibrium
`x*` at level `L` and any reference `m`, `x* − m = (F(m) − L)/(2W(ξ))` at an interior mean-value point
`ξ` with `W(ξ) > 0` (`cothField_deviation`). Taking `m` the midpoint and `θ* = (b − x*)/(b − a)` from
the ahead pole,

> `½ − θ*(i) = (F(m) − L)/(2·W(ξ)·(b − a))`  (`cothField_midpoint_deviation`),

and the midpoint excess is the exact §15 residue: at `L = −(pole count)`,
`F(m) + card = 2·(behind + BehindEx − AheadEx) = 2g(i)` (`midpoint_excess_eq`,
`cothField_theta_deviation`). Instantiated on the **literal harmonic pole model** `T_j = c·H_{j−1}`
(built as an actual `Finset`-indexed field: `harmPole`, strictly increasing, gap width `δ_i = c/(i+1)`,
`i+1` poles behind the midpoint — `harmPole_strictMono`, `harmPole_gap_width`, `harmonic_behind_card`),

> `½ − θ*(i) = ((i+1) + BehindEx − AheadEx) / (W(ξ)·δ_i)`  (`harmonic_theta_deviation`),

the exact discrete deviation. Its two asymptotic factors — the steepness `W(ξ)δ_i/i → π²/2` (local
factor `κ = 2/π²`) and the numerator `g(i)/i → i/d + (π²/16)/i` (truncation against shell correction)
— are exactly the edge-law inputs (§16), now **factors of a proven identity, not hypotheses**. Their
limits (the second-order Euler–Maclaurin `ε → −π²/16`, the digamma truncation `A_trunc/i → i/d`, and
the near-pole steepness limit) are the residual formalization surface; the identity they sit inside is
closed.

The equilibrium is **not** hypothetical: it exists. On any pole-free gap with simple poles at both
endpoints the field blows up `+∞/−∞` at the ends (`cothField_atTop_leftPole`,
`cothField_atBot_rightPole` — the endpoint term `rcoth((x−a)/2) ≥ 2/(x−a) → ∞`, the rest continuous),
so the intermediate value theorem attains every level (`cothField_root_exists`). On the harmonic model
the strictly-increasing poles are simple, so the gap-`i` equilibrium exists at level `−d`
(`harmonic_equilibrium_exists`) and the exact deviation identity holds for it unconditionally
(`harmonic_theta_deviation_exists`): the discrete `θ*(i)` field is a genuine object, existence +
uniqueness (`cothField_eq_unique`) + exact deviation.

### 17.3 The §14c race, made exact: room = excess/(2W), the race is a sign [PROVED HERE — Lean]

Doc 13(b) wanted a *bound* on the W-response room `δ/2 − s` (the margin by which the equilibrium sits
in the outer half, where `dW/ds < 0` and (S-mono) operates). The deviation identity gives it as an
**exact identity**:

> `δ/2 − s* = (b − a)/2 − (b − x*) = (F(m) − L)/(2·W(ξ))`  (`cothField_room_eq`),

i.e. the room is the midpoint field excess over the level, measured in energy units; on the harmonic
model `δ/2 − s* = g(i)/W(ξ)`. The race "does the (S-mono) energy gain beat the `1/(π√d)` margin" is
therefore an exact **sign condition**:

> `0 < δ/2 − s*  ⟺  L < F(m)`  (`cothField_room_pos_iff`),

the W-response applies at a gap iff the midpoint field exceeds the level, iff `g(i) > 0`. At the
marginal carrier `c = 2` the excess is the `√d`-edge residue: `½ − θ_max = 1/(π√d) > 0` at every
finite `d` (§16 edge law, positive), so the room **never closes at finite `d`** — it shrinks like
`1/(π√d)` but stays strictly positive, and the assembly step (e) has positive room at every level. For
`c ≥ 2` the strip is empty (§15), so `g(i) > 0` and the room is positive at **every** gap, not only the
edge. The "energy gain `≳ 1/√d`" of §14(c) is exactly this: the room's `√d`-rate is the edge law, and
its sign is the strip-emptiness — both now exact, the first proven-to-a-skeleton, the second a proven
equivalence.

### 17.4 The marginal crossover `G`, constructed — and it is linear [PROVED HERE — Lean]

Varying `c` in the harmonic family gives no `√d` law off `c = 2` (`1 − Φ(c) ≠ 0` makes `½ − θ_max` an
`O(1)` constant `→ c(1−Φ(c))/π²`). The genuine one-parameter object is the **finite-size-scaling
crossover at the marginal point**, with scaling variable `ξ = (2 − c)√d`. It is now **constructed as a
theorem** (`crossoverG`, `crossover_reduction`, `LegStripEdgeFamily.lean`), and the construction reveals
it is **linear**:

> `crossoverG ξ = 1/π − ξ/4`,   and along the scaling curve `c = 2 − ξ/√d`,
> `(½ − θ_max)·√d → G(ξ)`  (`crossover_reduction`).

The reason it is linear: near `c = 2`, `Φ(c) ≈ 1 − (π²/8)(c − 2)`, so the imbalance term `(π²/8)(c − 2)`
in `g(i)/i = (π²/8)(c−2) + i/d + (π²/16)/i` is **`i`-independent** — it does not move the AM–GM
minimizer, only shifts the min value additively. Hence `margin·√d = κ·[(π²/8)(c−2) + 2√(a/d)]·√d`
splits exactly into `κ·(π²/8)(c−2)·√d = −ξ/4` (the `√d` cancels for every `d`) plus `κ·2√(a/d)·√d = 1/π`
(the edge law). The two boundary constants are unified in one line: `G(0) = 1/π` (`crossoverG_zero`, the
edge law) and `G(ξ) + ξ/4 = 1/π` (`crossoverG_slope`, the `Φ'(2) = −π²/8` linear response). The
`crossover_reduction` consumes the physical decomposition `margin = κ·((π²/8)(c−2) + m)`; the collapse
of `margin·√d` onto this single linear `G` across `d` is the remaining input (the same status as the
edge law's own decomposition).

The **carrier family** is likewise made concrete (`rhoOfCarrier c a = (2c/π²)√a`, `edge_law_along_curve`):
sectioning the abstract `ρ`-surface `2κ√a` along the local-factor curve `κ(c) = c/π²` gives the
one-parameter family `ρ(c, a)`, with `ρ(2, π²/16) = 1/π` (`rhoOfCarrier_two`) as one point — no longer a
point-plus-skeleton but a curve on the surface. The remaining constructive step is a **deformed carrier**
whose marginal *locus* is a curve (a power carrier `δ_j = c·j^{−α}` with residue `Φ_α(c)` and marginal
curve `Φ_α = 1`), so that `a(c)` too varies — this needs the generalized `Φ_α`, a new object.

**Forward.** (i) Land input #1's steepness on the literal `W(m)` via the finite-sum Tannery variant
(`tendsto_rescaled_csch_sq_finsum`) + the `range d` behind/ahead reindex + `δ`-rescale. (ii) Discharge
inputs #2 (`A_trunc/i → i/d`, the digamma/tail-integral of the far-ahead cut) and #3 (`ε → −π²/16`, the
second-order Euler–Maclaurin remainder of the shell balance). (iii) The `ξ`-drift control
`W(ξ)/W(m) → 1` (from `θ*(i) → ½` pinning `ξ` within `o(δ)` of `m`) and the max-over-`i` assembly.
(iv) The generalized `Φ_α` for the deformed-carrier marginal curve.

## 18. Discharging the steepness input: the near-pole `csch²` Tannery limit [PROVED HERE — Lean]

§17.2's exact identity `½ − θ*(i) = g(i)/(W(ξ)·δ_i)` reduces the edge law to three input asymptotics
(§16). The first — the near-pole **steepness** `2W(m)·δ_i/i → 2π²/c` (local factor `κ(c) = c/π²`) — is
now proved as a mechanism, rigorously (`LegStripSteepness.lean`, axiom-clean).

The steepness is `W(m)/n² → π²/c²` (`n = i+1`, both sides), a **Tannery limit**: each pole contributes
`csch²(dist/2)/n²`, whose `n → ∞` limit is the near-pole value `(2/(c(k+½)))²` — proved from
`csch²(z) < 1/z²` (`rcsch_sq_lt_inv_sq`, via `x < sinh x`) and `w/sinh w → 1` (`tendsto_self_div_sinh`,
the derivative of `sinh` at `0`), giving `tendsto_rescaled_csch_sq_term`. The contributions are dominated
uniformly by the summable `(2/(c(k+½)))²` (`rescaled_csch_sq_le`), which sums to `2π²/c²` by odd Basel
(`tsum_near_pole_bound = (16/c²)·Σ 1/(2k+1)² = (16/c²)(π²/8)`). Dominated convergence then delivers

> `tendsto_rescaled_csch_sq_sum`: `Σ_k csch²(dist n k /2)/n² → 2π²/c²`

for any distance family with the near-pole pointwise limit `n·dist n k → c(k+½)` and lower bound
`dist n k ≥ (c/n)(k+½)`. Both hypotheses are met by the harmonic behind distances
`bdist_i(k) = c/(2i) + c·Σ_{j<k}1/(i−1−j)`: the pointwise limit `i·bdist_i(k) → c(k+½)`
(`tendsto_behind_dist`) rests on the **backward harmonic sum limit** `i·Σ_{j<k}1/(i−1−j) → k`
(`tendsto_backward_harmonic_sum`, a squeeze between `ik/(i−1)` and `ik/(i−k)`), and the lower bound is
`behind_dist_lb`.

So the steepness **mechanism** — the near-pole `csch² → 1/z²` collapse of the field's curvature onto the
odd-Basel constant `π²/c²` — is a theorem, and the harmonic carrier meets its hypotheses. The
finite-sum reconciliation is also done (`tendsto_rescaled_csch_sq_finsum`, the growing-finite-sum Tannery
via indicator truncation), and the **behind side is now landed on the literal harmonic distances**:

> `behind_csch_sum_tendsto`: `Σ_{k<n} csch²(bdist_n(k)/2)/n² → 2π²/c²`,

the behind train's near-pole steepness on the exact distances `bdist_n(k) = c/(2n) + c·Σ_{j<k}1/(n−1−j)`,
a direct application of the finite-sum Tannery limit + `tendsto_behind_dist` + `behind_dist_lb`.

**Both trains are now landed on the literal harmonic pole positions** (`LegStripSteepnessHarmonic.lean`):
the per-term identities `bdist_{i+1}(k) = harmMid c i − harmPole c (i−k)` (`harmMid_sub_harmPole`, a
`harmPole`-difference + reflection) and `adist_{i+1}(k) = harmPole c (i+1+k) − harmMid c i`
(`harmPole_sub_harmMid`, forward, no reflection) identify the abstract distances with the exact
midpoint-to-pole distances, giving

> `behind_energy_harmonic`, `ahead_energy_harmonic`: `Σ_{k<i+1} csch²(dist_k/2)/(i+1)² → 2π²/c²`,

the behind and ahead near-pole steepness on the actual pole positions `T_j = c·H_j`. The ahead side uses
the generalized finite-sum Tannery `tendsto_rescaled_csch_sq_finsum_gen` (domination constant `c/2`,
since the ahead distances satisfy only `adist ≥ (c/2)(k+½)/n`) and the forward harmonic sum
`tendsto_forward_harmonic_sum`.

**Input #1's steepness is fully discharged on the literal field energy** for the balanced model
(`d = 2i + 2`, exactly `i+1` behind and `i+1` ahead poles — every pole near, no far-ahead tail):

> `harmonic_midpoint_energy_steepness`: `W(m)/(i+1)² → π²/c²`  (i.e. `2W(m)·δ_i/i → 2π²/c`, `κ(c) = c/π²`),

where `W(m) = spurLatticeEnergy (range (2i+2)) (harmPole c) (harmMid c i) = ¼Σ csch²((m − T_k)/2)` is the
actual reduced energy of the harmonic pole configuration. It combines `behind_energy_harmonic` and
`ahead_energy_harmonic` via the `range (2i+2)` split (behind `k ≤ i` reflected, ahead `k ≥ i+1` shifted,
`csch²` even). So the local factor `κ` is no longer an assumed asymptotic — it is the `π²/c²` limit of the
literal field curvature at the midpoint. For general `d` the only addition is the far-ahead tail
(`k > i+1`) vanishing under the `(i+1)²` rescaling (`Σ_far csch²/(i+1)² → 0`, the boundary with input #2)
— the balanced model exhibits the steepness with that tail absent.
The other two inputs (`A_trunc/i → i/d` digamma, `ε → −π²/16` second-order Euler–Maclaurin) and the
`ξ`-drift control (`W(ξ)/W(m) → 1`, from `θ*(i) → ½` pinning `ξ` to `m`) are the onward surface toward
the assumption-free edge law.

## 19. Input #2, the truncation bound — the digamma rational envelope [PROVED HERE — Lean]

The margin term `A_trunc/i → i/d` is the finite-`d` cut of the ahead train: the pole count `d` removes
the far-ahead excess `A_trunc = Σ_{k ≥ d−i} poleExcess(ahead_k)`. Its **upper bound** is now a theorem
on the exact field `poleExcess` (`LegStripTruncation.lean`, axiom-clean), reusing the tree's harmonic-log
and digamma primitives (`sum_log_step`, `log_step_bounds`, `sum_inv_sq_shift_le`):

> `trunc_ahead_le`: `Σ_{d−i ≤ k < N} poleExcess(ahead_k) ≤ (i+1)²/(d−i−1)`.

The mechanism is the exact **exp ≥ rational** sandwich: the harmonic ahead distance dominates a logarithm,
`Σ_{j<k} 1/(i+j+1) ≥ log((i+k+1)/(i+1))` (`aheadHarm_ge_log`, the reverse of `harmonic_log_lower` via the
same `sum_log_step` telescope), so `exp(ahead_k) ≥ ((i+k+1)/(i+1))²` and the `coth`-excess is below the
rational envelope `(i+1)²/(k(k+2i+2))` (`poleExcess_ahead_le_rational`); its tail telescopes
(`trunc_rational_tail_le`, via the `1/k²` comparison and `sum_inv_sq_shift_le`) to `(i+1)²/(d−i−1)`. So
`A_trunc/i ≤ (i+1)²/(i(d−i−1)) ~ i/d` — the truncation scale, rigorously, on the exact `poleExcess`.

The **matching lower bound is now also a theorem** (`poleExcess_ahead_ge_rational`): from
`Σ 1/(i+j+1) ≤ log((i+k)/i)` (`harmonic_log_lower`) and `exp(1/i) ≤ i/(i−1)` (`exp_inv_le`, from
`1−x ≤ e^{−x}` reciprocated), `poleExcess(ahead_k) ≥ i(i−1)/(k(k+2i)+i)`. So the exact field `poleExcess`
is **sandwiched between two rationals**,

> `i(i−1)/(k(k+2i)+i) ≤ poleExcess(ahead_k) ≤ (i+1)²/(k(k+2i+2))`,

both `→ i²/(k(k+2i))` as `i → ∞` — the per-term two-sided envelope, the analytic crux of input #2.

**The summation is now also done** — the truncation mass is two-sidedly trapped by explicit digamma
partial-fraction rationals (`trunc_ahead_two_sided`):

> `((i−1)/2)·(B_M − B_N) ≤ A_trunc = Σ_{M≤k<N} poleExcess(ahead_k) ≤ (i+1)²/(M−1)`,

where `B_M = Σ_{M≤k<M+2i} 1/(k+1)` is a harmonic block of `2i` terms. Both rational sums are the exact
partial-fraction telescopes (`trunc_upper_sum_eq`, `trunc_lower_sum_eq`, via the general
`sum_shift_telescope`), and the blocks satisfy `2i/(M+2i) ≤ B_M ≤ 2i/M` (`harmonic_block_ge`,
`harmonic_block_le`). At `M = d−i` this pins `A_trunc = (i²/d)(1 + o(1))`: the removed truncation mass is
`~ i²/d` on the exact field, both bounds proved. The only remaining slack is the two-variable `o(1)` (the
`(i±1)/2 → i/2`, `B_M → 2i/d` as `i,d → ∞`), an arithmetic tightening of the now-explicit sandwich.

Input #3 (`ε → −π²/16`) is the second-order Euler–Maclaurin remainder of `poleModelDiff` — now
discharged at the boundary-layer term level in §20 (the odd-Basel constant `−½·Σ1/(2k+1)²`), with the
matched interchange named as the residual.

## 20. Input #3, the shell correction — the boundary-layer rate is the odd-Basel constant `−π²/16` [PROVED HERE — Lean]

Input #3 is the `1/i`-rate of `poleModelDiff(2,i) → Φ(2) = 1`: `ε(i) := poleModelDiff(2,i) − 1 →
−(π²/16)/i`. Two facts now stand as theorems.

**(a) The pole-excess field's second-order Euler–Maclaurin sandwich [PROVED HERE — Lean].** The field
`poleExcess u = 1/(eᵘ−1)` carries the exact expansion `1/u − 1/2 + u/12 − …` with Bernoulli
coefficients `B₁ = −1/2`, `B₂ = 1/6`. Both leading corrections are pinned Padé-tight
(`LegStripShellEM.lean`, axiom-clean):

> `poleExcess_em_lower`/`poleExcess_em_upper` : `1/u − 1/2 ≤ poleExcess u ≤ 1/u − 1/2 + u/12`  (`u > 0`).

The lower bound is the `[1/1]` Padé inequality `(2−u)eᵘ ≤ 2+u` (equivalently `coth(u/2) ≥ 2/u`); the
upper is the `[2/2]` Padé inequality `(u²+6u+12) ≤ (u²−6u+12)eᵘ`. Each is iterated monotonicity from
`0`: the defining function and its first one/two derivatives vanish at `0`, and the last derivative —
`ueᵘ` for the lower, `u²eᵘ` for the upper — is manifestly `≥ 0` on `[0,∞)` (`nonneg_of_deriv`,
`hasDerivAt_quad_exp`). This is the literal EM object input #3 is built from.

**(b) The per-term boundary-layer rate is `½ − 1/(2(2k+1)²)` [PROVED HERE — Lean].** At `c = 2` the
`k`-th ahead/behind distances `aheadₖ = 1/i + 2Σ_{j<k}1/(i+j+1)`, `behindₖ = 1/i + 2Σ_{j<k}1/(i-1-j)`
(the exact per-`k` arguments of `poleModelDiff 2 i`) both tend to `0` like `(2k+1)/i`, and their field
imbalance converges (`LegStripShellRate.lean`, axiom-clean):

> `poleModelTerm_rate` : `poleExcess(aheadₖ) − poleExcess(behindₖ) → 2k(k+1)/(2k+1)² = ½ − 1/(2(2k+1)²)`.

The proof splits the imbalance into (i) the reciprocal part `1/aheadₖ − 1/behindₖ`, whose limit
`2k(k+1)/(2k+1)²` is read off the three scaling limits `i·aheadₖ → 2k+1`, `i·behindₖ → 2k+1`,
`i²(behindₖ − aheadₖ) → 2k(k+1)` (`tendsto_i_ahead`, `tendsto_i_behind`, `tendsto_i2_diff`, this last
via the product ratio `i²/((i-1-j)(i+j+1)) = i²/(i²-(j+1)²) → 1`); and (ii) the Euler–Maclaurin
remainder `r(u) = poleExcess u − (1/u − 1/2)`, which vanishes along the shrinking distances by the
sandwich squeeze `0 ≤ r(u) ≤ u/12` of part (a).

**The constant is the odd-Basel value.** The algebraic split `2k(k+1)/(2k+1)² = ½ − 1/(2(2k+1)²)` is
exact: the `½` per term is the bulk linear growth (it feeds the leading `i` in `A − B`), and the
convergent correction `−1/(2(2k+1)²)` sums to

> `oddBasel_correction_hasSum` : `Σ_k −1/(2(2k+1)²) = −½·Σ_k 1/(2k+1)² = −½·(π²/8) = −π²/16`,

via `hasSum_odd_basel`. So the `−π²/16` rate constant is `−½·(odd Basel)` read off the boundary layer
term by term — the same `Σ 1/(2k+1)² = π²/8` that fixes the near-pole steepness `π²/c²` (input #1) and
the `1/π` edge law. The three inputs are one constant seen through three windows of the boundary layer.

**What this opens.** The per-term rate + the odd-Basel sum give the constant `−π²/16` at term level with
zero assumptions. The remaining assembly is the **matched interchange**: promoting the per-`k` limits to
`i·ε(i) = i·(poleModelDiff(2,i) − 1) → Σ_k(½ − rate_k) − (bulk i) → −π²/16`, i.e. a dominated-convergence
exchange of `Σ_k` and `lim_i` against the bulk subtraction of the `½`-per-term growth (the ahead-tail
`Σ_{k≥i}poleExcess(aheadₖ)` supplying the complementary half). The next brick is the uniform-in-`i`
domination of `poleExcess(aheadₖ) − poleExcess(behindₖ) − (½ − 1/(2(2k+1)²))` — the boundary-layer
analog of `shellBound` — after which the `ε`-limit closes by `tendsto_tsum_of_dominated_convergence`,
exactly as `tendsto_shellSum_stripResidue` closed the leading term.

## 21. Input #1, general `d` — the far-ahead energy envelope [PROVED HERE — Lean]

Input #1's midpoint steepness `W(m)·δ/i → π²/c` is `harmonic_midpoint_energy_steepness`
(`spurLatticeEnergy(range(2i+2))/(i+1)² → π²/c²`) times the trivial factor `c(i+1)/i → c` — proven for
the balanced model `d = 2i+2`. Promoting it to a general pole count `d` needs the far-ahead poles
`j ≥ 2i+2` to contribute `o((i+1)²)` to the energy. The obstruction is that the near-pole bound
`rcsch²(z) < 1/z²` (`rcsch_sq_lt_inv_sq`) loses the exponential decay of the `csch²` kernel; the far
tail needs that decay. Three theorems now supply the envelope (`LegStripFarTail.lean`, axiom-clean):

* `rcsch_sq_le_exp` : `rcsch(z)² ≤ 4/(1−e^{−2z₀})²·e^{−2z}` for `0 < z₀ ≤ z` — the missing exponential
  decay of `1/sinh²`, from `e^z − e^{−z} = e^z(1 − e^{−2z}) ≥ e^z(1 − e^{−2z₀})`. (Reusable; the
  ξ-drift crux `W(ξ)/W(m) → 1` needs the same kernel control.)
* `harmMid_far_dist_lower` : `harmPole c j − harmMid c i ≥ c·log((j+1)/(i+2))` for `j ≥ i+2` — the far
  pole's distance to the midpoint, from the tree's harmonic-log tail (`harmonic_log_upper`) plus the
  half-gap `c/(2(i+1))`.
* `farEnergy_term_le` : for `j ≥ 2i+2`, `rcsch²((harmPole c j − harmMid c i)/2) ≤ 4/(1−(2/3)^c)²·((i+2)/(j+1))^c`.
  The **uniform floor** `(j+1)/(i+2) ≥ 3/2` (from `j ≥ 2i+2`) fixes `z₀ = c·log(3/2)/2` independent of
  `i`, so the constant is fixed and the exponential kernel becomes a **polynomial `p`-series envelope**
  in `j` — the exact analog, for the energy, of the rational per-term envelope that controls the
  truncation train (§19).

**The `p`-series summation is now also done [PROVED HERE — Lean].** The envelope sums against the
tree's `p_series_tail_le`:
* `envelope_summable` : the shifted `p`-series `((2i+3)+m)^{−c}` is summable for `c > 1`.
* `envelope_tsum_le` : `Σ'_m ((i+2)/(2i+3+m))^c ≤ (i+2)^c·(2i+2)^{1−c}/(c−1)` (`div_rpow` + `tsum_mul_left`
  + `p_series_tail_le`).
* `rpow_prod_le` : `(i+2)^c·(2i+2)^{1−c} ≤ 2(i+1)` (real-power arithmetic `(i+2)^c ≤ (2(i+1))^c` and
  `x^c·x^{1−c} = x`).
* `farEnergyTail_le` : `Σ'_m rcsch²((harmPole c (2i+2+m) − harmMid c i)/2) ≤ 4/(1−(2/3)^c)²·(2/(c−1))·(i+1)`
  — the total far energy is `O(i+1)`, by comparison (termwise `farEnergy_term_le`, summable by
  domination) then the envelope bound.
* `farEnergyTail_div_tendsto` : **`(far energy)/(i+1)² → 0`** (squeeze by `K/(i+1)`).

So the far-ahead poles provably vanish under the `(i+1)²` rescaling: the general-`d` midpoint steepness
agrees with the balanced model `d = 2i+2`, and `W(m)·δ/i → π²/c` holds for **every** pole count `c > 1`,
not only the balanced one — input #1's general-`d` residual is closed. Forward: the sole remaining piece
of input #1 is the ξ-drift `W(ξ)/W(m) → 1` as the mean-value point drifts in the shrinking sub-gap
`|x* − m| = |½ − θ*|·δ`; it sits on the same `rcsch_sq_le_exp` kernel control now in hand.

## 22. The crossover `G` derived, and the marginal locus as a curve [PROVED HERE — Lean]

Bullets 2–3 of the collapse program — the crossover `G` as a genuine one-parameter object, and a
deformed carrier whose marginal locus is a curve — are now theorems (`LegStripCrossover.lean`,
axiom-clean).

**The crossover slope is derived, not posited (`crossover_derivation`).** `crossoverG ξ = 1/π − ξ/4`
was a linear ansatz joining the two boundary constants. Its slope is now derived from the local factor
`κ(c) = c/π²` and the curvature `Φ'(2) = −π²/8`: along the finite-size curve `c(d) = 2 − ξ/√d` (so
`ξ = (2−c)√d` is held fixed), the off-marginal edge margin — `κ(c)` times the AM–GM minimum
`(π²/8)(c−2) + (π/2)/√d` (the `Φ'(2)` shift plus the marginal `2√(a/d)`, `a = π²/16`) — scaled by `√d`
converges to `1/π − ξ/4`:

> `κ(c)·[(π²/8)(c−2)]·√d = (c/π²)(π²/8)(c−2)√d = (c/8)(c−2)√d → (2/8)(−ξ) = −ξ/4`, and
> `κ(c)·(π/2) = (c/π²)(π/2) → (2/π²)(π/2) = 1/π`.

So the two ends `G(0) = 1/π` (marginal, `c = 2`) and `G'(ξ) = −1/4` (off-marginal, through `κ·Φ'(2)`)
are one object, and `−1/4` is the odd-Basel `κ` read against the cotangent curvature.

**The marginal locus is a curve (`rhoOfCarrier_marginal_curve`, `rhoFamily_marginal_locus`).** The
`ρ`-skeleton `ρ(κ,a) = 2κ√a` has marginal locus `ρ = 1/π` at `a = 1/(4π²κ²)` — a curve, not a point.
In carrier terms the deformed shell coefficient `a(c) = π²/(4c²)` keeps `ρ(κ(c), a(c)) = 1/π` for
**every** `c > 0` (`marginalShell`), and the physical value `a(2) = π²/16` (`marginalShell_two`) is one
point of that one-parameter family of marginal carriers. The single physical carrier is a section of a
curve of marginal carriers — the skeleton `ρ(κ,a) = 2κ√a` is exactly what it sections.

**Where the program now stands.** The founding identity `½ − θ*(i) = g(i)/(W(ξ)δ)` has both factors
proven; its three input limits are discharged at the analytic core (input #1 midpoint steepness + the
now-closed general-`d` far tail §21; input #2 two-sided digamma sandwich §19; input #3 boundary-layer
odd-Basel rate §20); and the crossover `G` and marginal-carrier curve are derived (§22). The residuals
are three named coupled limits: the ξ-drift `W(ξ)/W(m) → 1` (bootstrap through the shrinking sub-gap,
on the `rcsch_sq_le_exp` kernel now in hand), input #2's two-variable `o(1)`, and input #3's matched
`Σ_k`/`lim_i` interchange. Each is one dominated-convergence or bootstrap step on an already-built
envelope — the analytic scaffolding for all three is now formalized.

## 23. The ξ-drift foundation — the energy `W` is convex on the gap [PROVED HERE — Lean]

The last residual of input #1 is the ξ-drift `W(ξ)/W(m) → 1`, where `ξ` is the mean-value point of
`cothField_theta_deviation`, strictly between the equilibrium `x*` and the midpoint `m`. Its structural
foundation is now a theorem (`LegStripConvex.lean`, axiom-clean):

* `spurLatticeEnergy_convexOn` : `W = ¼Σ_k rcsch²((x−t_k)/2)` is **convex** on the pole-free gap
  `(a,b)`. Proof: `W′ = −¼Σ_k rphi((x−t_k)/2)` (`spurLatticeEnergy_hasDerivAt`) is monotone, because each
  `rphi((x−t_k)/2)` is antitone on the gap — behind poles (`t_k ≤ a`) keep the argument in `Ioi 0` where
  `rphi` is antitone (`rphi_strictAntiOn_pos`), ahead poles (`t_k ≥ b`) keep it in `Iio 0` where `rphi`
  is antitone because it is odd (`rphi_neg`, `rphi_antitoneOn_Iio`).
* `rcsch_sq_convexOn` : the per-term atom `rcsch²` convex on `[a,∞)` (`a > 0`).

**The closure plan the convexity unlocks (no circularity).** With `W` convex:
1. *Uniform lower bound.* The two nearest poles give `W(ξ) ≥ ½·rcsch²(δ/4)` at every `ξ` in the gap
   (the two-pole sum is minimised at the midpoint by symmetry + convexity), i.e. `W(ξ) ≳ i²`
   uniformly — no dependence on `θ*`.
2. *Centering.* Then `|½ − θ*| = g(i)/(W(ξ)δ) ≤ g(i)/(c₀i²δ) ~ i/d + O(1/i) → 0` at `i ~ √d`, using
   only the lower bound — the equilibrium provably approaches the midpoint.
3. *Sub-gap.* Hence `|ξ − m| ≤ |x* − m| = |½ − θ*|·δ = o(δ)` — `ξ` sits in a sub-gap of width `o(δ)`.
4. *Upper refinement.* On that central sub-gap `|W′| ≲ i³` (far from the poles at distance `~δ/2`), so
   `W(ξ) − W(m) ≤ |W′|·|ξ − m| ≲ i³·o(δ) = o(i²) = o(W(m))`.
5. `W(ξ)/W(m) = 1 + o(1) → 1`, and `W(ξ)δ/i → π²/c` transfers from the proven `W(m)` limit.

The convexity (step 1's minimiser structure) and the energy derivative are now formalized; the four
remaining steps are the uniform two-pole lower bound, the centering inequality, and the central-sub-gap
`W′` bound — each a quantitative `csch²`/`rphi` estimate on the machinery already built
(`rphi_le_exp`, `rphi_ge_cubic`, `rcsch_sq_le_exp`).
