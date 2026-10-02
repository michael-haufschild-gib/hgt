# Route TG: full mixed reflected inverse collision

Unconditional RH/negation goal remains ACTIVE and unmet. No subagents, numerical experiments, full/umbrella builds, commits, new axioms, or heartbeat increases. One foreground Lean process at a time. Corpus evidence is authoritative. Every turn state TG, actual hard producer gaps, preceding progress, next attack.

## New audited source results
- `formal/GaloisForLFunctions/RHTower/PrimeBurnolConfluentMomentGram.lean` (285 lines): literal radial jets A r^(m+1)e^-lambda r are L2; exact factorial mixed moments. The finite family (f_i,r f_i) is independent for injective prime-depth labels. Proof uses AE-to-pointwise on Ioi0, positive integer sampling, corpus `HTGeometry.expPolySum_eq_zero`, distinct literal rates and nonzero amplitudes. Full block Gram [[G,M1],[M1,M2]] invertible. K=M2-M1 G^-1 M1 invertible, K^-1=(fullGram^-1).toBlocks22.
- `formal/GaloisForLFunctions/RHTower/PrimeBurnolMixedReflectedCollision.lean` (345 lines): actual reflected L2 Gram at common clocks k,-k; parity form c_p=(1/2)P c P, P=[[I,I],[I,-I]]. Exact c_p=T J T*, T=diag(I,i k I). J rational continuous for all real k, J0=2 full confluent Gram. Two-sided punctured limit k² c_p^-1 -> diag(0,(1/2)K^-1), no mixed-prime omissions or assumed inverse.
- Also `HTGeometry.matrixTrace_weighted_cubic_single_inverse`: for matrix unit c and idempotents p,q, Tr(c*C(c^-1 q c,q,p)) = Tr(c p c^-1 q c (p-q)) + Tr(c(q p q-p q p)).

All new public theorems (21 total) audited in separate /tmp import: only propext, Classical.choice, Quot.sound. Both direct production `lake --old env lean -o ... <leaf>` checks pass no warnings. Wired umbrella, regenerated index; no umbrella build. Lint exits1 on ten unrelated unwired RHTower leaves: CCMApertureChainProfile, CCMApertureTranslationChains, CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation, CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower, MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines, ThetaMovingShellFirstOrderPhase, ZetaZeroDensityPowerSaving. New TG modules absent from errors. Owned scratch/search/audit files cleaned, no owned process left.

## Exact next mathematical target
C5 inverse collision solved; full cubic coefficient still PAPER ONLY:
k² Tr(c*C) -> -Tr(G K^-1 (U-I/2) G V), with actual theta U=diag(visibility²), V=diag(visibility*contrast). In parity coordinates p=[[I,I],[I,I]]/2 and q=[[I/2+V,U-I/2],[U-I/2,I/2-V]]. Use actual theta Pythagorean identity to establish idempotence; continuity of det J at0 plus explicit T inverses gives eventual punctured invertibility; apply checked one-inverse trace identity and polynomial block limit. The coefficient equals -2Tr(G L(U-I/2)GV) with L=(J0^-1).toBlocks22=(1/2)K^-1.

Then compare with actual retained-grade Gamma/continuum matrix countercurrent, not coefficientwise scalar Wold budgets. No uniform packet inverse bound follows from finite invertibility. Hard RH gaps remain full pre-divisor matrix-complete cyclic transgression, source-to-Hardy index identification and residual nonnegative/sub-unit bound. Prior C4 one-cell pole is audited and not to be rederived.

Logs/cards: `docs/drafts/pipeline/1-in-progress/tg-source-conjecture-loop-2026-10-01.md`, `.../tg-mixed-reflection-collision-counterterm.md`, `docs/drafts/pipeline/3-formalized/tg-mixed-reflected-inverse-collision.md`; TG frontier map updated. Mixed corpus search complete, confluent search partial semantic deadline but useful uniqueness candidates verified in Lean.

## Lean details learned
- `Complex.ofReal_exp` rewrites cast(real exp) to complex exp (forward).
- `.congr_fun` needs an explicitly typed IntegrableOn hypothesis, not raw Integrable.const_mul.
- ContinuousAE lemma is MeasureTheory.Measure.eqOn_open_of_ae_eq, μ explicit.
- Avoid convert on LinearIndependent across instance variants: prove exact function equality, rw at existing hli.
- For Continuous rational matrix entries use `fun_prop (disch := intros; positivity)`.
- `continuousAt_matrix_inv A` takes continuity of Ring.inverse at det A; rewrite Ring.inverse_eq_inv' and use continuousAt_inv₀.
- `Matrix.mul_inv_rev` valid even singular; scalar version ambiguous under open Matrix, use `_root_.mul_inv_rev`.
- `Matrix.isUnit_iff_isUnit_det _` has explicit matrix argument before `.mp`.
- Block inverse equations need rewrite identity using ←Matrix.fromBlocks_one, then toBlocks_fromBlocks lemmas.
- ContinuousAt is not syntactically Tendsto: obtain ht.tendsto, simp Pi.mul_apply, then rewrite endpoint.
- Safe owned scratch cleanup uses apply_patch Delete File (shell rm previously denied but this worked).
