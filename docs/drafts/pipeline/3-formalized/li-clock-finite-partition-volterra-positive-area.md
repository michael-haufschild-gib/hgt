# Actual finite partition: symmetrized Volterra law and unbounded positive area

- **ID:** LI-CLOCK-FINITE-PARTITION-VOLTERRA-POSITIVE-AREA
- **Stage:** 3-formalized
- **Type:** THEOREM (40 public declarations; full paper/source/proof audits and exact certificates PASS)
- **Source:** [completion/arithmetic boundary](../3-formalized/li-clock-completion-arithmetic-cancellation-boundary.md); actual finite interval-union Laplace measure
- **Statement:** For every actual N>0 and a valid regular central contour, the partition clock P_N satisfies2(P_N*B_N)(t)=tB_N'(t), where B_N is the full symmetrized tilted-measure Borel series; its positive-part area is unbounded and P_N is positive cofinally.

## Goal

Retain strongest nontrivial generic positive-measure survivor. This does not imply pointwise compensation against completion/pole, give its required exponential rate, or prove RH.

## Gates

- [x] Exact literal partition/tilt normalization and full moment series well posed.
- [x] Complete dependency-closed paper proof and independent factor/series audit; existing theta Volterra overlap inspected.
- [x] Actual finite-source moment positivity, exact Volterra law, positive-area growth and cofinal positive clocks formalized; named/direct/all-public foundational checks.
- [ ] Standalone publication/novelty audit.

## Dependency-closed paper certificate

Full producer note `/tmp/hgt-li-actual-partition-compensation-paper.md` section5, read completely by root and independent pole. For A_N(s)=actual interval-union Laplace transform, Z_N=A_N(1/2)>0 and mu_N=exp(-u/2)nu_N/Z_N, independentU,V give X=U-V. Every even momentd_(2j)>0 forj>=1 because the first interval is diffuse and nondegenerate; |X|<=log(2N). Full B_N(t)=sum_j d_(2j)t^(2j)/[(2j)!]^2 is entire, positive and increasing fort>=0. Selected partition connection odd jets are even cumulants κ_(2j+2), and P_N has the complete two-factorial clock series on every regular closed source disk. Symmetrized difference cumulants are2κ_even and vanishodd. Exact beta integral and complete compact absolute series exchange yield2 integral_0^t P_N(u)B_N(t-u)du=tB_N'(t). Then integral_0^t max(P_N(u),0)du>=tB_N'(t)/(2B_N(t)). Positive B_N coefficients at every even degree imply weighted degree tB_N'/B_N→infinity: each finite prefix is negligible against a positive higher-degree term. Thus positive-part area→infinity and positive clocks occur cofinally. The factor TWO and tilted Z_N^2 normalization are essential.

Existing actual-theta `LiEvenCrossActualClockVolterra.lean` and `LiEvenCrossActualClockBorelGrowth.lean` overlap substantially. This is an actual finite-partition adaptation, not a new general mechanism or a corpus/public novelty claim. Formal source must retain all intervals, both independent variables, every moment and factorial; formal implementation may use source derivatives instead of selecting principal logarithms.

## Formal scope

Pole completed `LiClockPairedEtaFinitePartitionVolterra.lean`; root independently audited every proof and wired the exact leaf. Inputs: finite Laplace partition, finite log-measure/Gaussian Gram, all-order finite complexMGF derivatives, generic/actual Volterra and Borel weighted-degree growth. No unrelated edits or proof debt.

## Formal certificate

FINAL leaf: 1139 lines; 40 public declarations (11 definitions, 29 theorems); SHA256 `3696ea69fcad853192b48f4343e9b8523ac7490007796365ffc15c92c92da919`. Exact named build and final direct Lean PASS, direct output empty. Every public declaration depends only on `propext`, `Classical.choice`, `Quot.sound`. Logs `/tmp/li_pole_finite_partition_named_build.log`, `/tmp/li_pole_finite_partition_final_direct.log`, `/tmp/li_pole_finite_partition_axioms.log`; complete ledger `/tmp/li_pole_finite_partition_public.tsv`. Root read the full core, every added wrapper, all final header/whitespace changes, and all40 axiom reports.

The exact source is the full normalized double half-tilt, with normalizer `Z_N^2`; its entire MGF is `A_N(1/2-z)*A_N(1/2+z)/A_N(1/2)^2`. Every even moment is positive for `N>0` and bounded by `log(2N)^(2j)`. Full factorial series and compact absolute convolution yield the factor-two Volterra law. The positive-part area tends infinity on every regular closed disk; clocks occur positively on every tail. The explicit phase radius `π/(2*(log(2N)+1))` supplies such a disk for every `N>0`, giving the unconditional existence capstone. No pointwise completion-compensation estimate follows.

Index refresh PASS (3 changed, 0 removed), `/tmp/hgt-li-moving-volterra-index.log`. Authoritative global lint FAILED on12 unrelated unreachable modules, `/tmp/hgt-li-moving-volterra-lint.log`; no errors or forbidden proof declarations in this leaf or the moving helper. New-leaf whitespace check empty. This is a scoped formal certificate, not a globally clean-tree claim.

## Log

- 2026-09-30 05:02 UTC — CreatedStage2 after complete author/independent/root paper audits and prior-source overlap check, before new Lean. Formalization pending; no route retirement.
- 2026-09-30 06:35 UTC — All40 public declarations FINAL, full root audit PASS, wired, index/lint result recorded. MovedStage3; actual growing-window sign and RH remain open.
