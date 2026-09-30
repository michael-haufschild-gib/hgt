# Short finite eta prefix: exact pole-dominated clock boundary

- **ID:** LI-CLOCK-SHORT-PREFIX-POLE-ASYMPTOTIC
- **Stage:** 3-formalized; three leaves/37 public declarations final; author and independent complete proof audits PASS
- **Type:** exact source classification and positive deflated survivor
- **Parent:** [finite eta orientation window](../1-in-progress/li-clock-finite-eta-orientation-window.md)

## Exact target

For N>0 with L=log(2N)<2pi and every0<r<1/2, the literal finite completed source clock has

`exp(-2t)*F_N(r,t) -> -1` as real t->+infinity,

hence its real response tends to minus infinity. Prefer the complex normalized theorem, then derive the real statement. This falsifies an all-clock positivity argument based only on positive finite Laplace partition plus the same completion. It does not falsify the eventual-N growing-logarithmic-window candidate.

For the first prefix, the source-defined deflated response has the nontrivial positive survivor

`exp(-(2/5)t)*Fdef_1(r,t) -> 1/5`,

so it is eventually positive and unbounded while remaining too small to compensate 2sinh(2t). Exact two-term decomposition has remainder bounded by M*sinh(t/3).

## Dependency-closed author paper proof

Let L_N(s)=pairedEtaFiniteLaplacePartition N s. Installed E_N=sL_N identity, entire finite tilted-measure complex MGF and centered half-turn positivity imply L_N(s)!=0 for every complex s satisfying |Im(s)|log(2N)<=pi. The sharp rotated half-turn theorem is PREEXISTING, not a new survivor or novelty claim. Installed finite-core zero corollary restricts Re(s)>0; the all-real sigma Laplace bridge must be retained for the larger filled disk.

Exact d(s)=1-2exp(-s log2)=E_1(s-1)=(s-1)L_1(s-1). The literal completion C=s(1-s)Gamma_R(s)/d(s) agrees on the regular strip with the filled deflated factor

`K_N(s)=-2pi Gamma_R(s+2)*L_N(s)/L_1(s-1)`.

Gamma recurrence has factor2pi. At s=1 the literal C is zero (totalized0/0); the filled quotient is nonzero. Do not identify those point values. Only equality of regular central germs is needed.

Choose1/2<rho<min(5/2,pi/L). Gamma_R(s+2), L_N(s), and L_1(s-1) are analytic and nonzero on the closed central disk |s-1/2|<=rho. Its logarithmic trace R_N(z)=i K_N'(1/2+iz)/K_N(1/2+iz) is analytic. Original regular-circle source equals i/s+R_N. The installed Cauchy-sine coefficient identity gives radius independence between the actual r<1/2 circle and rho circle; generic contour envelope gives normFdef_N(t)<=M_N*sinh(t/rho). Exact source split F_N=-2sinh(2t)+Fdef_N and1/rho<2 prove the normalized -1 limit. No global divisor expansion or fixed-prefix/growing-prefix interchange.

For N=1, define

`K_2(s)=-4pi^2 Gamma_R(s+4)*L_1(s)/L_1(s-1)`.

It is analytic/nonzero on closed central radius3, using log2<1 and pi>3. Double Gamma recurrence gives T_1=i/s-i/(s+2)+iK_2'/K_2. The two exact pole clocks are -2sinh(2t) and(2/5)sinh(2t/5); remainder norm<=M*sinh(t/3). Since1/3<2/5, normalized deflated limit is1/5.

## Prior research and scope

Direct documented query `python3 scripts/formal_tools.py research 'positive compact Laplace partition rotated phase zero free strip gamma completion fixed finite clock pole growth' --mode deep --budget-seconds 300 --explore 0` completed; log `/tmp/hgt-li-finite-laplace-phase-pole-research.log`. Full63160 inventory, generation1147455 current1147455, semantic coverage unmeasured; candidates/source_arguments source-only with broad mismatches. Producer's independent positive-Laplace-clock query completed full63157 inventory, partialfalse, with source-only unchecked candidates. Expanded rg found exact preexisting `RiemannXiSuzukiPositiveCriticalStripEtaFiniteLaplaceHalfTurn.lean`, correcting the initial missed source collision. No corpus-wide or public novelty claim.

Relevant sources: HalfTurn135 (all-sigma centered positive moment), Partition98 (E_N=sL_N), RiemannXiSuzukiPositiveCriticalStripEtaLeadingLogMomentFiniteCompletedResidual63/78/88 (entire finite tilted complex MGF), GammaRealHalfPlane17, Deligne66, ArchimedeanGamma29, LiClockCentralTraceSineReflection131 (same germ/radius), LiClockCentralSineContourStability36, FiniteDeflation218. Verify every exact name in this toolchain before new Lean.

## Status

Author exact normalization, removable-point, nonzero disk, source-germ and contour audits PASS. Independent current-source audit PASS every filled endpoint, entire/nonzero disk, source germ, contour and complex-limit premise. All three formal leaves passed named, final exact source and every public foundational axiom audit. No numerical jobs were used. Main growing pointwise candidate remains OPEN; no route retired. If the generic finite-Laplace all-clock mechanism is retired, formalize BOTH normalized negative boundary and first-prefix positive deflated survivor first.

- 2026-09-30 02:37 UTC — Card recorded before new Lean; strongest two source asymptotics sent to independent audit. Exact filled quotient avoids denominator-lattice classification and preserves literal regular-clock source.

## Reserved formal scopes

- Producer: `LiClockPairedEtaFiniteFilledDeflation.lean`; entire/nonzero finite partitions, exact filled factors, analytic/nonzero disks, equality with literal regular source and one/two-pole splits.
- Current-source agent: `LiClockCentralTraceSineGrowth.lean`; radius-independent contour growth envelope and normalized exponential decay from larger analytic disk.
- Root: `LiClockPairedEtaShortPrefixAsymptotic.lean`; exact literal short-prefix normalized limit/negative escape and N1 positive deflated survivor.

No concurrent tree writes overlap. Every actual mathlib API requires this-toolchain scratch verification; final named/direct/all-public axiom audits required. No principal-log branch or fictitious totalized endpoint identity.

- 2026-09-30 02:42 UTC — Independent audit PASS all source and contour hypotheses; strongest complex normalized limits and both real escape laws recorded before formalization. Root read full author proof and spotchecked exact completion, centered phase, Laplace bridge and contour series/stability sources. Deep query completed80.47s; narrowed lexical centeredMoment query terminalexit0 found4 exact declarations, no compiler/coverage metadata. Card promotedStage2.

## Separate stronger survivor sent back to paper audit

2026-09-30 03:25 UTC — The first eight literal asymptotic/decomposition targets passed root scratch Lean and independent full proof review. During closure, a stronger N1 candidate was exposed: `logDeriv L_1(s)-logDeriv L_1(s-1)` may be even under `s -> 1-s`, making its entire clock contribution zero. If correct, the actual first deflated clock is exactly the shifted Gamma hyperbolic series `sum_{n>=1} sinh(t/(2n+1/2))/(2n+1/2)`, hence positive for every t>0, while the completed first clock is negative for every t>0. This stronger statement is a CONJECTURE pending a complete author/source/overlap and independent paper audit; the already-proved asymptotic statements do not establish it. No new Lean for this strengthening before the audit. Parent growing-window candidate remains OPEN.

The stronger conjecture has its own [formalized card](../3-formalized/li-clock-first-prefix-gamma-exact-sign.md); it does not change the scope of the eight formal asymptotic targets above.

## Final formal certificate

Three leaves/37 public declarations are complete and wired: `LiClockCentralTraceSineGrowth.lean` (5), `LiClockPairedEtaFiniteFilledDeflation.lean` (24), `LiClockPairedEtaShortPrefixAsymptotic.lean` (8). The capstone proves the full-complex short-prefix remainder envelope and normalized negative limit, real negative escape, exact first-prefix second-pole decomposition, complete complex radius-three remainder envelope, normalized positive deflated limit, real positive escape, and common-tail strict sign/pole separation. Every stated prefix/radius/circle hypothesis is literal; no source endpoint is replaced by a totalized filled value.

- Growth logs: `/tmp/li_current_trace_growth_{named,direct,axioms}.log`.
- Filled factor logs: `/tmp/hgt-li-filled-deflation-{build,direct,axioms}.log`.
- Capstone logs: `/tmp/hgt-li-short-prefix-{build,direct,axioms}.log`; all8 capstone axioms are exactly `propext`, `Classical.choice`, `Quot.sound`; final direct diagnostics empty. Named capstone build passed12980jobs, own92s.
- Exact public ledger: `/tmp/hgt-li-short-prefix-public.txt`.
- Independent final review inspected every public target and private proof, including contour pole sign, larger-radius restriction to the filled remainder, full complex estimates, casts, and exponential unscale. Root spotchecked the N1 positive normalized limit and radius-three error bound against source.

2026-09-30 03:28 UTC — Formal asymptotic classification closed. Generic all-clock finite-Laplace sign mechanism has an exact literal-source obstruction and a nontrivial positive deflated survivor. Main eventual-prefix growing-window pointwise sign remains OPEN; no RH proof, falsification, or route retirement. Separate stronger all-clock first-prefix Gamma identity is still in paper audit on its own card. Index/global lint update follows wiring.

2026-09-30 03:33 UTC: short-prefix closure index PASS (1 changed,0 removed). Scoped diff check PASS; all three new leaves reachable. Global formal lint currently has17 unrelated umbrella-reachability errors and no proof-debt errors; concurrent external lanes changed the earlier23-error inventory. Logs `/tmp/hgt-li-short-prefix-index.log`, `/tmp/hgt-li-short-prefix-lint.log`. No unrelated files repaired.
