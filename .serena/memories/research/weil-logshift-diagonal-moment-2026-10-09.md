# One moving log-shift probe exposes the summable majorant boundary

User restriction: Lean corpus ONLY. No web or external papers. Active endless corpus research goal remains ACTIVE; this increment is verified progress, not goal completion. Read the active objective attachment at each new automatic goal turn. Use hgtl7 with external phases overridden by user source restriction; do not claim external novelty.

New verified source: formal/GaloisForLFunctions/RHTower/WeilLogShiftDiagonalMoment.lean. Imports WeilTailPanelPositiveCompletion and WeilFullConeSummableExcessRigidity. Namespace RHTower, opens WeilExcess. Six public declarations:

1. weilLogShiftDiagonalProbe (lam : Nat -> Real) (k : Nat) : Real = Re weilFullFunctional lam (EF.weilTest f f), f=logShiftRiemannDifference k (log(k+2)). This is a valid member of the original finite panel for k>=1 because k+2 <= exp(2k).

2. tendsto_weilLogShiftDiagonalProbe: if Summable (fun n => |weilDeviation lam n|), then Q_k(lam) -> -4 * tsum_n weilDeviation lam n * riemannAutocorr(log n). Exact signed-moment limit, NO positivity, RH or full-cone assumption. weilDeviation is the existing guarded (lam-Lambda)/sqrt n on n>=2 and zero below.

3. weilLogShiftDiagonal_moment_nonpos: absolute summable deviation plus EVENTUAL nonnegative Q_k implies signed kernel moment <=0.

4. eq_vonMangoldt_of_eventually_diagonal_nonneg_of_summable_excess: lam>=Lambda on n>=2, Summable raw excess max(lam n-Lambda n,0)/sqrt n, and eventual nonnegative Q_k imply lam=Lambda on n>=2. Only ONE moving probe per integer window, eventual nonnegativity sufficient. Full positivity removed in this sector.

5. weilLogShiftSummableMajorants_subset_exact: set inclusion version, replacing eventual Q positivity by original WeilLogShiftTestsPositive. Includes majorant and raw summable-excess domain.

6. exists_weilLogShift_majorant_infinite_excess(t : Real): exists lam with WeilLogShiftTestsPositive, lam>=Lambda everywhere, lam2=Lambda2+exp(t)*sqrt2, and NOT Summable raw excess. Unconditional existential sharpness family; no analytic premise. Apply old prescribed-head completion to Lambda plus positive spike at2, then (5) gives non-summability.

Paper proof: paired real arithmetic kernel B_k(y)=4K_k(y)-2K_k(y+log(k+2))-2K_k(y-log(k+2)). K_k(y)->K(y), shifted terms tend0 by K_k<=K and exponential decay, so B_k(y)->4K(y). Uniform |B_k(y)|<=4K(0). Dominated convergence against absolute summable deviation yields arithmetic sum limit. Zero-side norm <=4exp(2k)*nearRadicalEnergy(k)->0 from existing energy theorem. Exact functional decomposition gives Q limit. For majorants, deviation>=0 and K(log n)>0; nonpositive sum forces every deviation zero.

Existing APIs used: WeilExcess.tendsto_truncatedRiemannAutocorr, exists_riemannAutocorr_le, riemannAutocorr_pos/nonneg/le_zero, summable_deviationExcess; RHTower.norm_logShiftRiemannPair_le, logShiftRiemannPair_eq, exists_exp_mul_nearRadicalEnergy_le, norm_W_logShiftRiemannDifference_le, weilFullFunctional_eq_sub, zeta_W_eq_weilFullFunctional. Scratch-verified mathlib dominated tsum, squeeze_zero_norm', ge_of_tendsto, Summable.of_norm_bounded, Summable.le_tsum. Complex.norm_re_le_norm DOES NOT EXIST; use Real.norm_eq_abs and Complex.abs_re_le_norm. Summable.tsum_eq_zero_iff_of_nonneg DOES NOT EXIST; bound individual nonnegative term by tsum with Summable.le_tsum. Explicit Function.comp_def required in simp only for Tendsto.comp expressions. For Complex.re_tsum after functional rewrite, first change raw guarded deviation expression to weilDeviation so rewriting matches. Calc by-body indentation must exceed calc-step indentation.

Card: docs/drafts/pipeline/3-formalized/weil-logshift-diagonal-moment-limit.md, full dependency-closed paper proof and significance audit. Exact logShift-majorant and logShift-moment-limit lexical searches zero hits; exhaustive source names/statement search had no matching result. No external novelty assessment.

Audits 2026-10-09: final leaf session9239 exit0, no diagnostics, emitted olean, no heartbeat override. Separate import/signature/#print axioms session14300 exit0; all six declarations exactly [propext, Classical.choice, Quot.sound]. Umbrella import exactly once observedline6925. Index54181exit0, six API rows. Scoped whitespace no diagnostics. Authoritative lint72818exit1 only six unrelated unreachable modules: RHTower.StretchedBoseDefect; HTGeometry.ApertureConeCalculus, ApertureConeWinding, ApertureLogTranslation, ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra. All owned jobs terminal; all11 inventoried /tmp/hgt-weil-excess* files removed and absence verified. No full or umbrella builds, numerical experiments, commits, pushes or unrelated fixes.

Next: unrestricted MIXED-SIGN summable-excess replacement remains OPEN; do not claim this theorem settles it. Earlier finite-deficit counterfamily does not have proved summable excess. Signed moment <=0 is compatible with mixed signs and highlights a real gap. Competing conjecture worth attacking: finitely supported deviations (negative at2, positive nearby) could keep signed moment negative while all log-shift tests positive, but NO proof or exact numerical/kernel inequalities established. Do not assume this from training data or run numerical experiments. Investigate exact corpus mechanisms or further countable observables; don't silently add majorant as a replacement goal. Existing majorant result is a genuine partial premise reduction explicitly allowed by objective.

Predecessor: `mem:research/weil-logshift-finite-deficit-separation-2026-10-09`; earlier chain sharp-prefix, simultaneous tail completion, finite-block excess budgets all verified.
