# Proportion Hierarchy of Near-Line Clustering and Window Occupancy

- **ID:** proportion-hierarchy-near-line-questions
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-0511/obstacles-summary.md` §2.5.1 (B20), §2.5.3 (B21)
- **Lean Module:** `GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.ProportionHierarchyOfNearLineQuestions`
- **Lean Declarations:**
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.criticalClustering_of_tendsto_xiCriticalRatio_one`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.logMean_tendsto_zero_of_tendsto_xiCriticalRatio_one`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.UnitWindowStripZeroModel.windowOccupancy_of_logFreeZeroDensity`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.rootModel`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.exists_proportionOne_allRates_model_not_windowOccupancy`
- **Statement:**
  1. Unconditionally for $\xi$, if the critical-line zero proportion $N_0(V)/N(V) \to 1$ as $V \to +\infty$, then $100\%$ critical-scale clustering holds (`offLineCountBeyond (\kappa / \log V) V = o(V \log V)` for every $\kappa > 0$), and hence $T^{-1}\int_T^{2T} \log\|\zeta(\tfrac{1}{2} + it)\|\,dt \to 0$ together with all eight equivalent forms in `criticalClustering_logMean_mollifier_hecke_tfae`.
  2. In every `UnitWindowStripZeroModel`, `LogFreeZeroDensity` implies `WindowOccupancy`.
  3. There exists a reflection-symmetric `UnitWindowStripZeroModel` (`rootModel`, with one off-line pair per window at depth $\sqrt{\log\log m}/\log m$ and all remaining zeros simple on $\operatorname{Re} s = 1/2$) satisfying local Riemann–von Mangoldt asymptotics, per-window simple critical-line proportion $\to 1$, exponential near-line depth-moment tails $\ll_r e^{-r a} V$ for **every** rate $r > 0$, `(L)`, and `CriticalClustering`, while violating `WindowOccupancy` and `LogFreeZeroDensity`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized (`lake --old env lean` exit 0; `#print axioms` `[propext, Classical.choice, Quot.sound]`)

## Proof `[PROVED HERE]`
1. For any $a > 0$, every zero counted by `offLineCountBeyond a V` lies strictly off $\operatorname{Re} s = 1/2$, so $\operatorname{offLineCountBeyond}(a, V) \le N(V) - N_0(V) = N(V)(1 - N_0(V)/N(V))$. Combining $N(V) \le 2 V \log V$ eventually (`xiZeroCount_asymptotic`) with $N_0(V)/N(V) \to 1$ gives $\operatorname{offLineCountBeyond}(\kappa/\log V, V)/(V\log V) \to 0$, and `criticalClustering_logMean_mollifier_hecke_tfae` yields $T^{-1}\int_T^{2T}\log\|\zeta(\tfrac{1}{2}+it)\|\,dt \to 0$.
2. In any `UnitWindowStripZeroModel`, every bad window $m \in [\lceil V\rceil, \lfloor 2V\rfloor]$ contributes multiplicity $\ge 1$ to the deep window sum, so `#Bad \le \sum_m N_m(A, V) \le \eta(A) V$.
3. On window $m \ge 256$, place $2 b_m - 2$ simple critical zeros ($b_m = \lfloor \log m / (4\pi)\rfloor + 1$) and one symmetric pair at depth $d_m = \sqrt{\log\log m}/\log m$. Put $u = \sqrt{\log\log V}$; for $m \in [V, 2V]$, $u/(2\log V) \le d_m \le 2u/\log V$. Thus the per-window simple critical ratio $(2b_m - 2)/(2b_m) \to 1$. For any rate $r > 0$, when $1 \le a \le 2u$ the shell depth moment is at most $8\pi (u/\log V) V$ and $u e^{ra} \le e^{(2r+1)u} \le e^{u^2} = \log V$ once $u \ge 2r + 1$, while for $a > 2u$ the shell sum vanishes. Finally, $V^{-1}\sum_m d_m \le 4u/\log V \to 0$ gives `(L)` and $\le 2$ off-line zeros per window gives `CriticalClustering`, whereas for any fixed $A > 0$, $d_m \ge A/\log V$ on every window once $u \ge 2A$, violating `WindowOccupancy`.
