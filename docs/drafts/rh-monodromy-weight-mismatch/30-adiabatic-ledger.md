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

**What still remains outside Lean** has shrunk to a *single substitution*. The discrete-to-continuum
passage `(A−B)/i → ∫_0^∞ (2/c)sinh(u/c)/(e^u−1) du` had two components: the improper monotone
Riemann-sum convergence `(1/i)Σ_k f(k/i) → ∫_0^∞ f`, and (a) the harmonic-to-log substitution
`Σ_{l=i+1}^{i+k} 1/l → log((i+k)/i)` turning pole distances into the continuum variable
`u = c·log(k/i)`. The Riemann-sum convergence is now machine-checked
(`tendsto_riemann_sum_antitone_Ioi`); what remains is only (a) — the telescoping-`log` identification
of the harmonic pole distances with the sample points `k/i`, plus the routine algebra recasting the
excess balance as `Σ_k g(k/i)` for the profile `g`. Every endpoint (series value, `cot` closed form),
the `Σ_n ∫ = ∫ Σ_n` interchange, and the half-line Riemann-sum limit are all in Lean; the lone open
step is the change of variables — named exactly, not scoped out for effort.
