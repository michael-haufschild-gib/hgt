# CCM-FU: quantitative parity-defect transport and initial-subset diagnostic

Goal remains ACTIVE. RH, SD1, PE4/G/C and the all-cutoff two-prime ceiling remain open. Previous turn was progress (oriented initial block); this turn adds all-state gain control after signs change, arithmetic creation cost, and a second-prime estimate. No RH premise or numerical proof input.

## New formal leaf
`formal/GaloisForLFunctions/RHTower/MobiusDivisorParityDefectTransport.lean` (233 lines), imports only previously built OrientedPrimeExtension. Three definitions and ELEVEN public theorems, fourteen public declarations total.
Definitions: A=mobiusDivisorOrientedFibre=(-1)^card(R)F_P(R); D=mobiusDivisorParityDefectEnergy=sum max(-A,0)^2; G=mobiusDivisorParityGoodEnergy=sum max(A,0)^2.
- `mobiusDivisorOrientedFibre_sq`: A²=F².
- `mobiusDivisorOrientedFibre_insert`: oriented prime update A'=A_R-A_insertqR for q not in R.
- `mobiusDivisorParityGoodEnergy_add_defect`: G+D=E exact.
- `mobiusDivisorParityDefectEnergy_nonneg`, `mobiusDivisorParityGoodEnergy_nonneg`.
- `mobiusDivisorParityDefectEnergy_empty`: D(empty)=0 all M.
- `mobiusDivisorSelectionEnergy_insert_le_parity_geometric`: at ANY retained state P, every available prime q<M has E(insert q P)-E(P)<=2 sqrt(G(P)) sqrt(D(P)). No sign-preservation hypothesis. Proof expands paired overlap, bounds constructive part by positive-negative cross terms, Cauchy on paired labels × Bool.
- `mobiusDivisorParityDefectEnergy_insert_le_packet`: from an input with all A_R>=0, new D after q is at most removed q-containing packet energy. Uses max(b-a,0)^2<=b² for a,b>=0.
- `mobiusDivisorParityDefectEnergy_insert_le_adjacent`: same input condition, new D<=q*((1-w)E(floor(M/q),P)+w E(floor(M/q)+1,P)), exact existing copied-packet interpolation. Common processed state retained.
- `mobiusDivisorParityDefectEnergy_singleton_le_quadratic`: UNCONDITIONAL actual first-prime D({q})<=722 q*((1-w)N²+w(N+1)²), N=floor(M/q), q prime<M. Source original parity and existing quadratic diagonals discharge all orientation/energy inputs.
- `mobiusDivisorSelectionEnergy_second_prime_le_defect`: UNCONDITIONAL distinct primes p,q<M: E({p,q})<=E({p})+2 sqrt(E(empty))*sqrt(D({p})). First-prime contraction bounds G({p}) by original E.

Important boundary: geometric gain bound is sufficient, NOT an identity or necessary condition on actual gain. Paying that potential cost from released energy would give a continuation, but failure of this comparison does not refute PE4. Repeated smaller-prime defect accumulation and a growing bounded schedule remain open. Do not automatically iterate zero parity; previous formal F21({2},{3})>0.04 refutes that invariant.

## New frozen diagnostic, no channel regeneration
Card `docs/drafts/pipeline/1-in-progress/ccm-fu-initial-small-subset-ceiling.md` remains OPEN. Question: do all original subsets of <=2 primes stay within initial diagonal; what smallest cardinality fails in stored range?
Files in existing computations dir `docs/drafts/pipeline/2-fully-proven/computations/ccm-fu-adaptive-prime-energy-2026-09-06/`: `cardinality_reanalysis.py` and `cardinality-reanalysis.json`; README updated. Reads ALL subset-states.csv, original tolerance1e-12*max(1,E0), groups counts/failures/max ratios by cardinality, stores source hash. No channels or greedy path regenerated.
Results through32: 627 two-prime states, all pass. ALL states cardinality<=4 pass (counts 0:32,1:192,2:627,3:1321,4:1930). First failure M17 P={3,5,7,11,13}, E≈0.373051588208>E0≈0.362178444601. Smallest failing stored cardinality5. Remaining failure counts cardinality5:6,6:41,7:53,8:25,9:7,10:1;11none. These are numerical only; no Lean certificate of cutoff17 claimed. No route retirement or no-go based on these values. Python here lacks int.bit_count; initial inline probe failed on it; persisted script uses bin(mask).count('1') and ran successfully. Do NOT rerun without a new question.

## Completed verification — do not repeat
New names scratch passed; full proof scratch passed after local parser/multiplication-order fixes. Exact leaf compiled via lake env lean -o own olean. Wired once immediately after OrientedPrimeExtension in RHTower.lean. No umbrella/full/dependency build. ALL FOURTEEN NEW public declarations axiom-audited ONCE; only propext/Classical.choice/Quot.sound. Checked leaf matches scratch bytes; scoped diff check passed; promoted card/new links/import count/provenance verified. Index refreshed once (see tool output in turn); no old declarations re-audited.
Global formal lint failed solely on TWELVE unrelated concurrent unwired modules: RHTower.ThetaCuspSecondAtomAllMoments,ThetaCuspTwoAtomExponentialAdmission,ThetaCuspTwoAtomOddProfiles,ThetaCuspTwoAtomOddReserves; HTGeometry.LogarithmicLaplaceMiddleAbsoluteBounds,MiddleHankelPerturbation,TwoAtomMiddleEntryBounds,TwoAtomMiddleHighEntries,TwoAtomMiddleLowEntries,TwoAtomOddAlgebra,TwoAtomOddHighReserve,TwoAtomOddLowerReserve. Do not claim passing global lint and do not change their scope.

Card promoted to `docs/drafts/pipeline/3-formalized/ccm-fu-parity-defect-transport.md`. PE4, SD1, current frontier updated with proved bounds and explicit open comparisons. Universal STATUS has route-independent MUST-BUDGET-SIGN-DEFECT-COUPLING. All owned handles completed; process snapshot found none. Six exact owned scratch/audit files removed. No commit/push/subagents. Preserve unrelated concurrent changes.

Next turn: state full CCM-FU proof chain, classify this turn progress, inspect current source, pursue arithmetic comparison between first/repeated sign-defect costs and released energy. The all-cutoff two-prime ceiling is supported only by stored finite diagnostics; it still needs a genuine source comparison, not generic positive-cube arguments.
