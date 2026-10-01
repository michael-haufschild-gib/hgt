# BAG exclusive recurrence producer — latest checkpoint
Use with mem:rh/bag-full-gaussian-cofactor-mean-closed-packets-next-2026-10-01 for F108–F114 and base route. This is newer.
User focus remains only independent recurrence producer. No receiver extensions or unrelated work. Goal ACTIVE, not achieved. Need quantitative return count exceeding zero-density, NOT merely infinitely many returns. Full random/source work does not close deterministic recurrence.

## Runtime NOW
- Sole owned Lean: F119 FINAL session28138 RUNNING:
 lake --old env lean GaloisForLFunctions/RHTower/SteinhausFullGaussianModeCells.lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/SteinhausFullGaussianModeCells.olean
 log /tmp/bag-full-gaussian-mode-cells-final.log
- F119 lint session84656 pending /tmp/bag-full-gaussian-mode-cells-lint.log
- F119 exact lexical index terminal0 /tmp/bag-full-gaussian-mode-cells-index.json UNINSPECTED
- After explicit terminal final0, run F120 scratch /tmp/BagFullGaussianNormalizedChannel.lean, carries BOTH F119 public audits.
- F120,F121,F122 drafts complete, UNCOMPILED, no repo leaves.
- No other owned Lean or search jobs live. Exactly one foreground owned Lean; don't launch successor before explicit terminal write_stdin. No heartbeat increases, full builds, numerics, devserver, commit/push or agents.

## Durable docs
Card docs/drafts/pipeline/1-in-progress/bagchi-quantitative-sparse-recurrence.md
matching -working-log.md
frontier docs/reports/rh-current-frontier-map.md BAG row~309.
Card/frontier FINAL through F118. Working log through F119 scratch success/final launch.
C22 initial overview updated to actual full mean/mode separation already PROVED; simultaneous packets marked provedF116.
Original BAG mission from card: coefficient-faithful quantitative boundary self-return around hypothetical off-line zero -> distinct translated zeros -> exceed strict-right-strip zero count. Sparse rates allowed. RecurrenceZeroDensity receiver assumes return/count inputs. ZetaStrongRecurrenceReceiver positive upper-density disc predicate is one stronger receiver. No edits receivers.
Square-height option (paper only): smoothing/height=n², truncation=n³ gives cofactor cutoff>=n forp<=n², seam n³<(n²/D)² eventually. Cofinal square windows allowed only IF full quantitative window return count retained; one return per square scale is insufficient. Check quantifiers before implement.

## FINAL new leaves (all formal/GaloisForLFunctions/RHTower/, wired append-only, uncommitted)
F115 SteinhausFullGaussianCofactorModes:
 defs fullGaussianCofactorNodeVector s R omega=fullcofactor_j*R^-s_j
 relativeFullGaussianCofactorMode=A^-1 • R^-it • nodevector
 3 public convergence, normalized prefix stability, one large-energy late block.
 final97341 exit0 warning-free; all3 audits F116scratch9927 standard-only; index99; lint65370 11unrelated.
F116 SteinhausFullGaussianModePackets:
 exists_prescribed_fullGaussianCofactor_mode_blocks
 Anyfinite twists t:Fin k→Real, one extendingphase, separated Mi (2Mi<Mj), Mi>=B,Mi>=1,Ai!=0,Mi*normAi²>=K, allrealR∈[Mi,2Mi] modeerror<ε.
 Inductk generalizingε, IHε/2, prefixstabilityε/2 eacholdblock, unionrangesCi+1, newblockpastalloldendpoints, triangle.
 final64207 exit0 warning-free; public auditF117scratch3952 standard-only; index10; lint4328 11unrelated.
F117 SmoothAFEGaussianCofactorModeCoercivity:
 exists_gaussianCofactorMode_robust_row_lower hJ s hs hinj:
 ∃t:FinJ→Real, ε,c>0 ∀u∃i∀v, norm(v-kernelmode_i)<=ε ->c*normu<=normΣv_j u_j.
 Private matrix inverse-norm + finite dot estimate copied from audited old SteinhausCofactorModeCoercivity; uses F106 Gaussian full-rank packet.
 final82716 exit0 warning-free even after temporaryF116import stripped; publicauditF118scratch9534standard-only; index50; lint28046 11unrelated.
F118 SteinhausFullGaussianCharacterStability:
 exists_fullGaussianCofactor_character_tolerance s U hε:
 ∃B>=1,δ>0∀0<R<=U∀omega eta,
 (∀n∈Icc1B norm(Xn eta-Xn omega)<δ) -> norm(fullcofactor eta-fullcofactor omega)<ε.
 Private gaussianCofactorHead and exists_uniform_fullGaussian_tail.
 Two uniform tails<ε/4; finitehead error<=δ Σnormn^(s-1), δ=ε/(4*(1+sum)). NormV<=1.
 scratch1failed only add_le_add_right orientation; explicit add_le_add(norm_add_le..)(le_refl..) fixed.
 final18069 exit0 warning-free; publicauditF119scratch44644standard-only; index42; lint23486 12unrelated.
Allpublic axioms standard-only [propext,Classical.choice,Quot.sound]. Lint failures only unrelated unreachable modules; no own proof debt.

## F119 FINAL RUNNING, scratch44644 exit0 warning-free
Repo written/wired SteinhausFullGaussianModeCells.lean; no final result yet.
2public:
1 exists_relativeFullGaussianCofactorMode_character_tolerance:
 hJ>0, nodeRe>=0,t,A!=0,U,ε>0 ->∃Bδ>0 uniform1<=R<=U relativefullmode difference<ε fromcharactercloseness throughB.
 ChoosesF118 node tolerances with rawerrorε*normA, commonB=univ.supB_j, positiveδ=minδ_j usingexists_min_image; unitnormtwist, normR^-s<=1.
2 exists_fullGaussianCofactor_mode_cell_blocks:
 hJ>0, nodesRe∈(0,1), finiteS/omega,B0,K,ε>0, hk>0,twistsFin k;
 ∃extendingomega', Mi,Ai,B,δ>0, B0<=B, separatedblocks, eachMi>=B0,Mi>=1,Ai!=0,budgetMi*normAi²>=K,2Mi<=B;
 forall eta character-close throughBδ, forallrealR∈[Mi,2Mi], relativemodeerror<ε.
 F116ε/2 + normalizedchartoleranceε/2 perblock; commonδmin, B=B0+sum(2Mi+B_i).
 Public audits queued F120scratch.

## F120 draft UNCOMPILED
/tmp/BagFullGaussianNormalizedChannel.lean
Imports F115,SteinhausCofactorPrimeBlocks, TEMP F119 + bothF119audits.
Planned final SteinhausFullGaussianNormalizedChannel.lean.
def normalizedFullGaussianCofactorChannel s R omega := R*fullGaussianCofactorNodeVector s R omega.
4public:
 normalizedFullGaussianCofactorChannel_eq_mode (hA!=0,hR>0):
 channel=R*A*R^it*relativeFullmode.
 norm_normalizedFullGaussianCofactorChannel_dot_eq:
 norm dotchannel=R*normA*norm dotrelative.
 cofactorPrimeBlock_real_scale_bounds hM hp:
 M<=N/p(real)<2M, usingexisting Nat.div bounds andcasts.
 fullGaussian_prime_channel_factor (N p:Real>0):
 p^(s_j-1)*fullcofactor(s_j,N/p)=N^(s_j-1)*normalizedfullchannel(s,N/p)_j.
 Proof R=N/p,N=pR; cpow_mul positive bases; R^(s-1)*R*R^-s=1.
 Potential proof issue: conv_rhs rw[hNR] might also rewrite N inside R (let R is opaque to rw normally); compile and inspect. Allotheralgebrafromverifiedsource.
No repo leaf.

## F121 draft UNCOMPILED
/tmp/BagFullGaussianChannelEnergy.lean
Imports planned F119,F120,F117 + SteinhausFiniteCharacterCells.
Planned final SteinhausFullGaussianChannelEnergy.lean.
Public exists_normalizedFullGaussianCofactorChannel_energy_cell_lower.
 ∃extendingphase,K>0,Bδ>0 eventuallyN: original seamN<(N/(2K))² AND
 ∀eta∈characterCell B centreδ∀u,
 H*N/logN*normu²<=Σ_(p∈largePrimesN(N/(2K))) norm(dot fullNormalizedChannel s (N/p) eta,u)².
 Source energy ONLY. Literal finite conditional channel transfer remains unproved.
Adapted old SmoothAFENormalizedChannelEnergy proof:
 F117twists εc; F119 modecell budget4H/c² andε/2; K=1+sumMi; existingprimecounts N/(4Mi logN). selected robustrowi lower perprimeMi² normAi²c² normu². Sumoneblock +nonnegativeothers. UsesF120real-scale bounds andnormdot. Might needtype casts at hMi (1<=Mi versus0<Mi), inspectcompiler.
All98-ishlines fullywritten but not re-read after scripted adaptation exceptconstruction known.

## F122 draft UNCOMPILED
/tmp/BagFullGaussianTruncation.lean
ImportsF115,Pow.Asymptotics.
Plannedfinal SteinhausFullGaussianTruncation.lean.
defs truncatedFullGaussianCofactor (rangeL of X(n+1)*n^(s-1)*V(n/R))
 relativeTruncatedFullGaussianCofactorMode (sameA^-1R^-itR^-s normalization).
3public:
 truncatedFullGaussianCofactor_eq_Icc (reindex verifiedFinsetIco/range)
 eventually_truncatedFullGaussianCofactor_uniform_error s U hε:
 eventuallyL, all0<R<=U, allomega, norm(trunc-full)<ε.
 FromF113tail, A=absRes+2, real rpow negative limit, boundR^A<=U^A.
 eventually_relativeTruncatedFullGaussianCofactorMode_uniform_error:
 nodesRe>=0,A!=0,U,ε>0 -> eventuallyL all1<=R<=U allomega vectornormdiff<ε.
 Filter.eventually_all scalarerrorsε*normA, unitnormtwist andnormR^-s<=1.
No audits addedyet. No repo leaf.

## Mathematical next steps after drafts
1 F120/F121 fullsourceenergy cell.
2 F122 uniformtruncatedrelative approximation totransferselectedcofactorrows atcarrierlengthL≈N^1.5 (or n³ heightn²).
 Arithmetic seamL<Y²,Y≈N/D makes each exteriorprime occur exactly once; cofactorcutoffL/p<Y so actual frozen-channel factors coincide. Fullcofactor response approximation uniform sinceL/p→∞ onselectedp≈N/M.
3 Literal conductor/common-height transport: originalτ absorbed by phase rotation and common unit primephase, asalreadyF34source, nowexpandedcarrier andfullGaussian x=N (r=1).
4 Actual all-channel max/uppertrace musthold forpup toL, notmerelyp<=N. AbsoluteGaussian bound givesC*N^-1/2*decay(p/N); need weightedprimecount to gettraceO(1/logN), trivialallintegerbound onlyO(1).
5 FullGaussian randomfirstmean/boundedbackground: F77 weightedprefixmean=o(R^d), Gaussian averaging andFubini/DCT shouldgivefullseriesmean=o(N^d), projected smoothbackground viaJensen. ExistingfiniteN Gaussianmean onlyo(N^d) atcutoffN cannotnaivelysubstituteL=N^1.5 (losespower). No suchfullrandommean proved yet.
6 Full conditionaltargetlaw/boundaryAFE/deterministicgrowing-primecommonheightreturnCOUNT stillopen. No fixed-supportKronecker shortcut.

## Source reads / API checks
- Existing SteinhausCofactorPrimeBlocks fullyread:
 cofactorPrimeBlock M N=primesInIoc(N/(2M))(N/M).
 mem_bounds ->prime,M<=NatN/p,N/p<2M.
 eventuallycard≥N/(4MlogN).
 subset_largePrimes ifM<=K; eventualoriginalseamN<(N/(2K))² &2K<N/(2K).
 RealR bounds followexactN≥M*p,N<2M*p; no newPNT needed.
- SmoothAFENormalizedChannelEnergy fullyread, includingsourceenergyproof andpointwisecorollary. Noedits.
- SmoothAFECofactorCellStability fullyread:
 norm_smoothAFECutoff_le_one hr publicline180;
 existing finite corrected chartolerance86;
 existingcellblocks133 minδ via Finset.exists_min_image univδ univ_nonempty.
- SteinhausFiniteCharacterCells:88 celldefinition ∀n∈Icc1B normXdifference<δ; positiveSteinhausmassδ>0, anyrealcentre.
- Matrixprivatehelper sourcefullyread/copied toF117,noedits.
- Mathlib: Finset.le_sup(mem_univ j), pi_norm_lt_iff hε,
 Real.rpow_le_one_of_one_le_of_nonpos hR hz,
 root tendsto_rpow_neg_atTop positive exponent, root tendsto_natCast_atTop_atTop,
 Finset.Ico_add_one_right_eq_Icc NOT Nat.*, sum_Ico_eq_sum_range,
 measurable_from_nat implicitf, Measurable.nat_floor,
 Complex.norm_cpow_eq_rpow_re_of_pos hR.
- add_le_add_right resolved with opposite additiveorientation inF118 context; use add_le_add h (le_refl _) toavoidshadow ambiguity.

## Research searches all terminal/reviewed
/tmp/bag-full-gaussian-character-stability-source.json: lexical cofactor character tolerance, exactly1hit oldfinitecorrectedchartolerance, sourceused.
/tmp/bag-full-gaussian-normalized-channel-source.json search92889:14total,10displayedreviewed; existingnormalizedchannel defs,reflectedcofactorfactorization, normalizedpowerfactors. Actualoldnormalizedsource fullyread.
Perleafindex searches allinspected throughF118; F119uninspectedcurrently.
Lint failures10–12unrelated unreachablemodules; don'tfixconcurrentlanes. No fullbuildclaim.
Keepgoalactive; do notfinalize/markcomplete independentrecurrence.
