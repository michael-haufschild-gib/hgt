# JAS square-shell finite power window

- **ID:** JAS-SQUARE-SHELL-FINITE-POWER-WINDOW-2026-10-18
- **Stage:** 3-formalized; paper proof and component Lean certification complete
- **Type:** Quantitative source-criterion compression; not an RH proof
- **Source:** JAS; rotation after RW → TH → MSC → RB → SZ → BVI and an HCF source audit.
- **Verdict:** SURVIVES PRELIMINARY ATTACK against the inspected Lean corpus. External novelty audit excluded by user instruction; no external novelty claim.

## Exact target

Write D(N,k)=jasShellRieszSum N k, with the literal prime-product/Riesz definition in JointAncestryDampedShellArithmetic. Then

RH iff, for every ε>0, infinitely many natural m satisfy

    |D(m²,k)| ≤ m^(ε k)

for every natural k with m<k and k≤m+m/log(m+1).

The stronger negative certificate is: if RH fails, some ε>0 has, for every sufficiently large m, a natural k in this same window with |D(m²,k)|>m^(ε k). Thus the all-power condition is compressed to a finite window on square-indexed shells. No maximal off-line zero, zeros-approach-line assumption, or independent tail estimate remains.

## Prior corpus and attack

The deep JAS source search completed with partial=false, no errors or unfinished stages, inventory 73961/73961. Compiler metadata is mostly pending/source-only, so applicability must be checked in Lean. Raw result: /tmp/hgt-jas-source-search.json. All 20 candidate lemmas and 20 source arguments were inspected. Both suggested positivity mechanisms assumed RH and were rejected as new inputs.

Exhaustive source search of jasShellDampedSum and jasShellDampedPowerSum found the existing all-k criterion, arithmetic Riesz identity, damping bounds and positivity receivers. JointAncestryDoubleExpWindowsDyadicShells compresses prime windows under quasi-RH, not the power quantifier. The finite weighted Turán theorem already controls k in [M+1,M+n], but the existing infinite loud-set argument chooses M after n and discards its upper bound.

Potential failures: an unbounded number of large modes; a cone angle degenerating as the selected finite set changes; circular finite-tail control; Turán's denominator overwhelming amplification. The estimates below address each separately. This result does not supply the arithmetic upper bound and must not be advertised as doing so. It is a nontrivial quantitative interface reduction, not a new positivity producer.

Exact-mechanism follow-up: `summable sector weights growing rank finite power window Turan`, 90-second deep budget, excluding the new WeightedPowerWindow modules. This search was partial: Qdrant semantic retrieval timed out; finite-power and Turán-window subqueries were unfinished. Inventory was complete at 73980/73980; compiler metadata remained mostly pending/source-only. All 20 candidate lemmas, 20 source arguments and the proposed ingredient set were inspected; none supplied the missing window theorem. Cached lexical `weightedPowerSum` returned all three matches in the two existing weighted Turán modules, whose exact statements/proofs were checked. The adjacent PositiveExponentialSumPowerSums results require positivity of an exponential sum on a circle and do not supply the new finite-window certificate. This is a limited corpus audit, not an external novelty assertion.

## Dependency-closed paper proof

### 1. Arithmetic mass and matched damping

Let P_m={prime p:m²<p≤2m²}, U_m(s)=Σ_{p∈P_m}p^(s−3/2), and B_m(s)=U_m(s)/(s+1)². For m≥1, #P_m≤m² and every p∈P_m has p^(−1/2)≤1/m. Hence H_m=Σ_{p∈P_m}p^(−1/2)≤m. This uses interval counting only.

For 0<σ=Re(s)<1, |U_m(s)|≤H_m. The norm-square differences |s+1|²−|s|²=2σ+1 and |s+1|²−|1−s|²=4σ are nonnegative. Consequently |s(1−s)|≤|s+1|² and

    |B_m(s)| ≤ m |1/(s(1−s))|.

All denominators are nonzero in the open strip. The same domination at arbitrary N has H_N in place of m.

### 2. An unconditional uniform cone

For each Xi multiplicity copy q put s=ρ_q, w_q=1/(s(1−s)). Existing source theorems give 0<σ<1 and |γ|>1 (XiEndpointSourceHeightGap.xiZeroCopy_one_lt_abs_im). Set A=σ(1−σ)+γ² and T=γ(1−2σ). Then A>γ²>1 and |T|<|γ|<γ²<A. Thus |s(1−s)|≤2A. Since Re(w)=A/|s(1−s)|² and |w|=1/|s(1−s)|, Re(w)≥|w|/2. This cone is uniform over all copies; it does not depend on any selected finite set.

The established summable_inv_mul_one_sub gives W=Σ_q|w_q|<∞. W>0 whenever a nonzero-amplitude witness is present; under RH the upper-bound proof also handles W=0.

### 3. General growing-rank estimate

Consider any summable complex weights w_i satisfying Re(w_i)≥|w_i|/2, and amplitudes b_m(i) satisfying |b_m(i)|≤m|w_i|. Fix δ>0. Suppose that eventually there is an i with |b_m(i)|>2m^δ. Put L=m^δ and G={i:|b_m(i)|>L}. Domination and summability imply G is finite, and

    n L ≤ Σ_{i∈G}|b_m(i)| ≤ mW,
    n=#G≤mW/L.

In particular n≥1, eventually n≤m, and n≤m/log(m+1): the last assertion is equivalent to W log(m+1)/m^δ≤1, which tends to zero. Every power sum Σ_i w_i b_m(i)^k converges absolutely because |b_m(i)|≤mW uniformly.

Set Z=2L. For m≥1, L≥1, and the witness above Z has |w_i|≥1/m. Every radial subset {i∈G:tZ≤|b_m(i)|} with t≤1 contains that witness. Its weight sum has real part at least half its total absolute weight, so its norm is at least β=1/(2m). No maximum-modulus selection is needed.

Apply HTGeometry.exists_norm_weightedPowerSum_ge_scaled with M=m, Z, β, and G. It supplies m+1≤k≤m+n and

    |Σ_{i∈G}w_i b_m(i)^k| ≥ β Z^k / T(m,n),
    T(m,n)=2 e n [6(n+1)(m+2n+2)]^n.

The complement has norm at most W L^k, by absolute summation. No auxiliary finite truncation and no independently assumed tail modulus are needed.

### 4. Uniform absorption of the Turán loss

For m≥1 and 1≤n≤m, 6(n+1)(m+2n+2)≤60m². Therefore

    T(m,n) ≤ 2 e m (60m²)^n.

The logarithm of 8WmT(m,n)/2^(m+1), divided by m, is bounded above by

    [log(16eW)+2log m]/m
      + W[log 60+2log m]/m^δ − (1+1/m)log 2.

This tends to −log 2<0, since log m/m^a→0 for every a>0. Hence uniformly for every n≤mW/m^δ, eventually

    8WmT(m,n) ≤ 2^(m+1).

For the selected k≥m+1, β Z^k/T(m,n)≥4W L^k. Subtracting the complement bound gives the full power sum norm at least 3W L^k, in particular at least 2W m^(δk). Its index satisfies k≤m+m/log(m+1).

### 5. Actual off-line source supplies the witness

If RH fails, the existing Xi reflection/support theorem supplies q with δ=Re(ρ_q)−1/2>0. The unconditional PNT shell theorem eventually_lt_norm_jasShellUniformSum, used with exponent 3δ/4, gives |U_ρ(N)|>N^(3δ/4) on every sufficiently large N. Along N=m²,

    |B_m(ρ_q)| > m^(3δ/2)/|ρ_q+1|² > 2m^δ

eventually, since m^(δ/2)→∞. Apply Sections 3–4. With ε=δ/2, eventually 2W m^(δk)>m^(εk) uniformly for k≥1: it suffices that 2Wm^(δ/2)>1. The exact arithmetic identity jasShellDampedPowerSum_eq_rieszSum applies because k≥m+1≥1. This proves the negative certificate and, by contradiction with infinitely many good m, the reverse implication of the criterion.

### 6. Forward implication

Under RH, norm_jasShellDampedSum_le_one_of_riemannHypothesis bounds every amplitude by one. Absolute summation yields |D(m²,k)|≤W for every k≥1. Given ε>0, eventually m≥1 and m^ε≥W. For every k≥1, m^(εk)≥m^ε, so every requested finite window obeys the bound. Eventually implies frequently atTop on naturals.

All analytic inputs above are existing unconditional source/PNT/summability theorems or elementary real limits. The sole RH premise occurs in the forward direction of an equivalence; the reverse direction establishes RH from the exact stated arithmetic criterion. No unconditional RH proof is claimed.

## Lean plan and checks

1. Reusable weighted finite-window and growing-rank absorption in HTGeometry.
2. Prime-shell Mellin mass/damping budget and finite loud-dimension estimate in BiScaleUncertainty; use the actual prime window, not a substitute source.
3. Uniform actual Xi cone, off-line certificate and Riesz criterion in RHTower.
4. Probe mathlib names in /tmp; canonical foreground lake --old env lean audits, one owned process; audit every public declaration's axioms; wire finished leaves; index/lint; clean owned temporary artifacts.

## Status

- Paper: complete; constants and quantifiers checked above.
- Lean: all four canonical leaves pass `lake --old env lean` with empty output and are wired into their appropriate umbrellas. The capstone is `RHTower.riemannHypothesis_iff_squareShellRiesz_finitePowerWindow`; the stronger negative certificate is `RHTower.exists_eventually_large_squareShellRiesz_of_not_riemannHypothesis`.
- Arithmetic positivity/subexponential upper bound: OPEN.
- RH: OPEN.

## Verification

- Canonical leaves: `HTGeometry/WeightedPowerWindowCompression.lean`, `HTGeometry/WeightedPowerWindowAsymptotics.lean`, `BiScaleUncertainty/PrimeShellMellinMassBudget.lean`, `RHTower/JointAncestrySquareShellFinitePowerCriterion.lean`.
- All four canonical checks exit 0 without warnings. Five main theorem types were inspected in a separate scratch audit.
- Every public declaration was audited: 17 declarations, each depending only on `propext`, `Classical.choice`, `Quot.sound`. Scratch audit `/tmp/hgt-jas-window-axioms.lean`, output `/tmp/hgt-jas-window-axioms.log`, exit 0.
- Source and compiled-artifact hashes, exact declaration list and check records: `/tmp/hgt-jas-window-audit-manifest.json`. Source hashes were checked again after the canonical and axiom audits.
- `scripts/formal_tools.py index` exits 0. `git diff --check` exits 0.
- Global `scripts/formal_tools.py lint` exits 1: unrelated untracked leaves `BiScaleUncertainty/EulerPoissonChiralDriftAndPrimeShiftRigidity.lean` and `BezoutValuationIncidence/GcdOrbitProjectionAndExactTranslationPeriods.lean` are unreachable from their umbrellas. None of this component's modules is reported. Existing large-file warnings also remain. These other workers' leaves were not changed or wired.
- No full/umbrella build, added axiom, heartbeat increase, commit or push.

## Significance and rotation audit

The removed obstruction is the unbounded power quantifier and its uncontrolled Turán starting index. The actual prime mass pays for the growing loud rank; the actual source height gap supplies a uniform cone; the complementary infinite tail is discharged directly. The result retains the literal Riesz observable and permits non-attained off-line frontiers.

This is a quantitative interface improvement, not the missing arithmetic upper-bound producer and not an RH proof. External novelty was not checked under the user's instruction; no claim beyond the inspected corpus is made. The preceding HCF investigation found an already-closed source-identification bridge and produced no new theorem; that dead end prompted this rotation rather than another receiver restatement there.

Next research cycle: rotate to another live family or candidate before extending JAS again. Prefer an independent source estimate; do not count a restatement of the new finite-window upper bound as its proof. Recent own sequence: RW → TH → MSC → RB → SZ → BVI → HCF audit → JAS.
