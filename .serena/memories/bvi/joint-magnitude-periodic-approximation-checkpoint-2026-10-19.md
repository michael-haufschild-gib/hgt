# BVI joint magnitude checkpoint — 2026-10-19

Active goal remains 100 significant novel native BVI contributions, accepted 0/100. Do not complete/block. User reminder: use actual corpus research search, avoid missing existing work. No hgtl7, no agents, no experiments/certificates, no commits, field README read-only. One owned Lean/build process at a time; targeted commands only. Original attachment and session-init instructions were fully read earlier; do not restart.

## Completed owned leaf
`formal/GaloisForLFunctions/BezoutValuationIncidence/MobiusMagnitudePeriodicApproximation.lean` (279 lines), wired in BVI umbrella after CofinalMobiusSourceClockSupport. Original-source `lake env lean -o ... -i ... <canonical source>` exited 0, no diagnostics. Separate /tmp axiom audit exited 0, all seven public declarations depend only on propext, Classical.choice, Quot.sound. Search index readback inspected all 8 names/docstrings, including all 7 public declarations. Logs `/tmp/bvi100-magnitude-periodic-{canonical,axioms,index-readback,formal-lint}.*`. Completed scratch/API/axiom .lean files removed. No repeat checks needed without edits.

Public declarations:
- moebiusBandMagnitude(j n): abs(sum q in Icc 1 j, if q|n then moebiusReal(n/q) else 0).
- moebiusLocalBandMagnitude(j R n): same, replacing mu(n/q) by mu(gcd(n/q,primorial(R)^2)).
- moebiusLocalBandPeriod(j R): j! * primorial(R)^2.
- moebiusBandMagnitude_eq_rough_mul_local(R:Nat)(j:Fin(R+1))(n:PNat): b_j(n)=abs(mu(roughPart R n))*local_jR(n).
- moebiusLocalBandMagnitude_periodic(j R): Function.Periodic local (period j R).
- abs_sieveSeq_moebius_eq_bandMagnitude(N n:PNat): abs(source_N(n))=if n=1 then 1 else b_((n-1)/N)(n).
- moebiusBandMagnitude_disagreement_count_le(R:PNat)(j:Fin(R+1))(m X:Nat)(h:Fin m->Nat): number of n in Icc 1 X with ANY shifted b_j/local mismatch <= sum_i (X+h_i)/R.
Private helpers prove smooth/rough factor, gcd truncation, agreement outside large prime squares, anchored shifted-square union bound. Imports existing RHTower.Sieve.SmoothRough, AveragedSquarefreeTailSharp, BVI.CofinalMobiusQuadraticQuotientProfile, Primorial. All capstones have data parameters only.

Latest plain lint exits 1 ONLY nine other-owner BiScaleUncertainty leaves unreachable: SieveParityAmplitudeScaling, SieveParityAnchorEstimate, SieveParityCutoffRecovery, SieveParityFourierBounds, SieveParityNeighborhoodClassification, SieveParityNeighborhoodSharpness, SieveParityNeighborhoodStability, SieveParityResonanceCounts, SieveParitySharpWitnesses. Earlier THIM gaps are now repaired by their owners. Do not modify unrelated files.

## Current owned running command
Session **64239**: `lake env lean /tmp/bvi100-magnitude-pattern-density.lean`, from formal/. Logs `/tmp/bvi100-magnitude-pattern-density.log`, status `.status`. Do NOT launch another Lean/build before collecting completion. Draft currently ~130 lines, not canonical and not claimed verified. Defines band/local pattern counts, local period density, private periodic count error and pattern count difference, public finite unnormalized pattern error. Need inspect errors and finish, then add density convergence. No other owned commands pending.

## Paper theorem and route
Card `docs/drafts/pipeline/1-in-progress/bvi-joint-magnitude-law-2026-10-19.md` now contains dependency-closed paper construction. Programme row updated. Full joint law still unfinished in Lean and uncounted.

Avoid unnecessary affine-form producer. Fixed band b_j has periodic approximation above for R>=max(1,j). Exact common rough factor shows mismatch only where p>R has p^2|n. Shifted tail count <=(X+h)/R: inject into anchored [1,X+h], use floor((X+h)/d^2) <= (X+h)/d^2 and existing sum_Icc_inv_sq_le. No +1 or sqrt error.
For finite h_i, max H, target vector a, local full-period probability c_R satisfies |E_X-c_R|<=m*(1+H/X)/R+T_R/X. Then |c_R-c_S|<=m/R+m/S after X->infinity, hence Cauchy and limit c_j(h,a); |c_R-c_j|<=m/R, E_X->c_j. Finite support/nonnegativity/normalization follow from finite distributions. Can strengthen to TV<=m/R using natural mismatch coupling (same candidate, no extra credit).
Literal source vectors differ from common-band vectors at <=1+(K+1)*sum_i h_i samples through (K+t)N, t in [0,1], K>=2. Thus raw mass limit is sum_{j<K} c_j+t*c_K, divide by K+t. No claim positive density iff cofinal attainability; bounded boundary positions are discarded.
Native consumer: reverse triangle inequality yields magnitude-gradient mean <=liminf signed source-gradient energy. First band b_1=mu^2 gives 2(D-C); classical CRT products C/D=prod_p(p^2-2)/(p^2-1)<=7/12 using 2,3, so 2(D-C)>=5D/6>2D/3. Optional product identification still to formalize, not needed to build full joint law.

## Next Lean steps
1. Collect session64239; fix draft finite pattern approximation.
2. Normalize error, prove local probabilities Cauchy along R=j+K+1, define density using Filter.limUnder, prove local approximation and literal band count limit. Then finite support/normalization as needed.
3. Real-horizon band transport and native gradient consumer. Canonical/audit/wire/index/lint for completed leaves only; no umbrella build.
Verified /tmp APIs (axiom audit also checked examples): Function.Periodic.map_mod_nat hf n: f(n%a)=f n; Nat.filter_Ico_card_eq_of_periodic; cauchySeq_of_le_tendsto_0' b h h0 where h n m (n<=m):dist(s n)(s m)<=b n; CauchySeq.tendsto_limUnder: Tendsto u atTop (nhds(atTop.limUnder u)); Filter.limUnder; le_of_tendsto_of_tendsto; tendsto_const_div_atTop_nhds_zero_nat(C:Real).
Lean lessons: avoid global reverse rewrite n=smooth*rough (rewrites inner n arguments); use calc congrArg. For gcd with addition in FIRST argument use Nat.gcd_add_mul_right_left. PNat.pos 0<N may need omega to give 1<=N. Unbounded exists inside theorem filter needs open scoped Classical. card_le_card_of_injOn lambda goals need explicit `change n+h ...` before omega. push_cast changes numerator X+h too; reconcile with simpa only[Nat.cast_add].

## Research audits completed this continuation
Actual documented search commands, no help/source reads of research tool. All 137 squarefree-affine lexical names/docs reviewed offsets0,20,...120. All20 candidate+20 source records inspected in new deep searches:
- /tmp/bvi100-joint-local-state-research.json
- /tmp/bvi100-periodic-squarefree-research.json
- /tmp/bvi100-magnitude-rough-thim-research.json
- /tmp/bvi100-truncated-mobius-factor-research.json (one unrelated source signature truncated at let t, not used)
- /tmp/bvi100-periodic-pattern-count-research.json
All partial=false, semantic coverage unmeasured; latter snapshots older, mainly source-only compiler evidence. No absence/novelty claims.
Read full AffinePairSieve (prime-pair upper bounds, not squarefree limit), SmoothRough, ResiduePartitionCount, AveragedSquarefreeTailSharp, ShiftedCongruenceCount; first156 lines HorizonRadicalStateAndDefectNormalForm. Prior TruncatedPairCount/JointCongruence/Class/Tail/MR sources already read. MRInterface result has open MRBilinear premise AND different balanced-pair observable; reject as producer.
Primary classical baseline Cellarosi-Sinai JEMS2013 https://ems.press/content/serial-article-files/31903 sections1-3 through eq17 inspected: classical Mirsky tuple product, Kronecker model, pure-point spectrum. Generic squarefree pattern or periodic-process result earns no novelty credit. AMS Mirsky1949 PDF403, do not claim read. Zhang-Liu2014 HTML displayed equations missing, no exact constants used.
Additional primary sources inspected: Coppola-Laporta2016 https://hrj.episciences.org/2635/pdf introduction, Thm1.1, Cor1.7+proof (shift averages, Q^2 error unsuitable at proportional cutoff); Green-Tao Linear equations in primes AppendixD ThmD.3 https://annals.math.princeton.edu/wp-content/uploads/annals-v171-n3-p08-p.pdf (smooth cutoff small power of ambient scale, different regime). Murty PDF URL redirected to homepage, not read. Neither regime distinction proves novelty.

Earlier eight completed one-point source-law leaves remain verified, wired, indexed and uncounted; see prior memory real-source-law-complete-and-joint-magnitude-frontier-2026-10-19. No edits to them this continuation.