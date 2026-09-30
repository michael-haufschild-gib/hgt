# Contiguous comparison clock: exact lattice and positive growing window

- **ID:** LI-CLOCK-CONTIGUOUS-COMPARISON-WINDOW
- **Stage:** 3-formalized
- **Type:** THEOREM (two leaves/64 public declarations; all paper/source/proof and exact formal certificates PASS)
- **Source:** [completion/arithmetic cancellation](../3-formalized/li-clock-completion-arithmetic-cancellation-boundary.md)
- **Statement:** U_L(s)=integral_0^L exp(-su)du has partition clock2sinh(2t)-K_L(t), K_L=sum_k beta_k sinh(t beta_k) includingk0; for every0<c<1/16 the completed contiguous MODEL C-K_L is eventually positive on0<t<=cL, with uniform K_L/t→0.

## Goal

Extract exact positive survivor of the rejected contiguous replacement. Actual finite eta source retains nontrivial log gaps; model window positivity does not imply its sign or RH.

## Gates

- [x] Well-posed literal filled interval source and complete lattice normalization.
- [x] Complete dependency-closed paper and independent audits; prior-source overlap checked.
- [x] Exact all-complex model/lattice identity, compact summability, uniform envelope, positive model window and fixed-clock decay formalized; named/direct/all-public foundational checks.
- [x] Full real clock positivity `K_L(t)>0` for `L,t>0` and the paper's stronger comparison `norm(O(z))<=Re(O(norm(z)))` formalized and independently checked.
- [ ] Standalone publication/novelty audit.

## Paper certificate

Full `/tmp/li_current_large_prefix_lattice-paper.md` sections1–5 and independently derived `/tmp/hgt-li-actual-partition-compensation-paper.md` sections1–3 were read completely by root and pole. U_L is entire with filledU_L(0)=L, nonzero on Re(s)>0. Q_L=L/(exp(Ls)-1), q_U=Q_L-1/s; cotangent identity fixes the constant -L/2, and complete upper-half-plane derivative expansion fixes every β_k=(1/2+2pi*i*k/L)^(-1), includingβ0=2. Full atom/order series is absolutely and locally uniformly convergent. Alternative exact K_L=L sum_{m>=1} exp(-mL/2) O(mLt), O(x)=sum_j x^(2j+1)/[(2j+1)!]^2. Bound O(|x|)<=|x|exp(2sqrt|x|) closes every exchange. Forκ=1/2-2sqrt(c)>0, normK_L(t)<=normt*L²exp(-κL)/(1-exp(-κL))² whenevernormt<=cL. This gives uniform normalized decay and positive model window using C(t)/t>=181/1600. The sufficient1/16 is not claimed optimal. Fixed-clock K_L→0 follows the same bound. Constant/exponential shifts are clock-invisible; actual gaps are retained separately. No new Lean before these completed audits.

## No-go closure

- **Killing mechanism:** Actual partition is a union of log intervals, not contiguous U_L or its shifted transform; exactN2,s1 witness7/12 versus3/4 or3/2.
- **Strongest positive survivor:** Exact complete model clock, its entire positive resolvent packet, quantitative positive growing model window, and fixed-clock decay.
- **New insight:** Contiguous model admits compensation, whereas arithmetic gap clock must cancel nearly all actual completion. The source-pure remaining estimate keeps gap residual.
- **Status:** Paper and exact Lean survivor FINAL; actual orientation route remains open. This card classifies the comparison model and the rejected contiguous-source replacement.

## Formal scope

Current completed `LiClockPairedEtaContiguousSource.lean` and `LiClockPairedEtaContiguousComparison.lean`; both frozen and wired. Root and producer independently read every private/public comparison proof and the exact positivity delta; root also checked all final public axiom reports, source normalization, snapshot equality and generated API entries.

## Formal certificate

Source: 297 lines/20 public declarations; SHA256 `240cd433421897e3e21bfb5d0f180b568d93d585f776491de8346a185ebfccf3`. Comparison: 1018 lines/44 public declarations (35 theorems, 9 definitions); SHA256 `81c0459089c13433b84a11d1c92cae819feea97dcf66450ba9a9f00859eeb521`. The first939 comparison lines stayed byte-identical; the independently audited80-line positivity/radial delta was appended with its standalone self-import removed. Exact named builds, final direct checks (empty output) and all64 public axiom checks PASS; only `propext`, `Classical.choice`, `Quot.sound`.

Final comparison logs `/tmp/li_current_contiguous_comparison_final_named.log`, `/tmp/li_current_contiguous_comparison_final_direct.log`, `/tmp/li_current_contiguous_comparison_final_axioms.log`; named12986jobs, own85s, no own-leaf warnings. Complete64-API ledger `/tmp/li_current_contiguous_api_ledger.md`; full independent reviews and terminal evidence `/tmp/li_current_contiguous_proof_audits.md`. Source logs below remain final.

Index refresh PASS (0 changed, 0 removed after managed research refresh), `/tmp/hgt-li-comparison-final-index.log`; all five added target entries verified. Authoritative global lint FAILED on10 unrelated unreachable modules, no proof-debt or own-leaf errors, `/tmp/hgt-li-comparison-final-lint.log`. New-leaf whitespace check empty; scoped tracked diff check PASS. No global clean-tree claim.

## Log

- 2026-09-30 04:57 UTC — CreatedStage2 after all complete paper/dependency/overlap audits, before new formal work.

- 2026-09-30 06:07 UTC — Support `LiClockPairedEtaContiguousSource.lean` FINAL/FROZEN,297lines20public declarations. Root read every private/public proof; final derivative-conversion-only delta spot-checked. Named build2756jobs6.8s, final direct EMPTY, all20 axioms only `[propext, Classical.choice, Quot.sound]`. Logs `/tmp/li_current_contiguous_source_{named,direct,axioms}.log`; SHA256 `240cd433421897e3e21bfb5d0f180b568d93d585f776491de8346a185ebfccf3`. Wired umbrella. Literal filled source, all-complex regular-radius contour identity/reality and full fixed-clock decay closed; full model series/lattice/window targets remain required, so this card staysStage2.

- Direct quarter-contour alternative independently audited before use: onnormt<=cL, normK_L(t)<=normt*4L exp(-(1/4-4c)L)/(1-exp(-L/4)); for0<c<1/16 the envelope tends zero. This proves the same sufficient model-window threshold with a weaker rate than the complete O/lattice envelope. All sharper complete-packet targets remain required. Moving odd-endpoint windows and actual finite joint cancellation are tracked in [joint cancellation](../3-formalized/li-clock-joint-arithmetic-cancellation-window.md).
- 2026-09-30 06:44 UTC — Full939-line comparison and all39 initial public declarations independently audited by root/producer; named/final-direct/all-public axioms PASS. Final scope audit caught the explicit paper209–229 positivity and stronger O-series norm comparison missing from exported targets. Existing complete absolute summability supplies both proofs; original paper and termwise positivity audits PASS before additional Lean. Card remainsStage2 until these exact survivor claims and final changed-leaf checks close.
- 2026-09-30 07:03 UTC — All original paper targets closed, including strict positive full clock and exact radial O bound. Final all64 certificates and every proof audit PASS; wired, closure results recorded, movedStage3. Actual arithmetic residual and RH remain OPEN.
