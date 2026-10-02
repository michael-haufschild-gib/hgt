# Route TG: actual full mixed-prime cubic principal coefficient

Goal ACTIVE/unmet. Prior goal turn is PROGRESS: exact actual-source principal coefficient now fully formalized. User requires corpus-grounded conjecture loops, no subagents/numerical computations/new axioms/heartbeat increases/full or umbrella builds/commits. One owned foreground Lean process at once. Every turn state TG, hard gaps, preceding progress, next attack. Main goal only met by unconditional RH or negation.

## New audited production module
`formal/GaloisForLFunctions/RHTower/PrimeBurnolMixedCubicPrincipal.lean` (298 lines), imports only `PrimeBurnolMixedReflectedCollision`.
- `primeBurnolMixedReflectedThetaCubicTrace` is trace of actual literal reflected Gram c(k) times C(c^-1 q c,q,p), with original-sector p=diag(I,0), q=[[U,V],[V,I-U]], U=diag(thetaVisibility²), V=diag(thetaVisibility*thetaContrast).
- `primeBurnolMixedCubicPrincipalCoefficient` is -Tr(G K^-1 (U-I/2) G V), G=M0, K=M2-M1 G^-1 M1.
- Final `primeBurnolMixedReflectedThetaCubicTrace_principal` line290: for EVERY finite injective prime-depth packet (embedding) and every real theta grade a, k² actual raw cubic -> that coefficient on two-sided punctured nhds0. No extra invertibility/projection/analytic premises. Retains every cross-prime term.
- Auxiliary public: continuous_primeBurnolReflectedParityGram, primeBurnolReflectedParityGram_zero, eventually_primeBurnolReflectedParityGram_isUnit, primeBurnolParityThetaProjection_idempotent, primeBurnolParityThetaCubicTrace_principal, primeBurnolParityThetaCubicTrace_eq_source.
- Actual theta Pythagorean identity gives idempotence; J determinant continuity gives punctured invertibility. Checked single-inverse cubic formula + exact inverse residue gives block coefficient. Explicit Hadamard unit and generic cubic trace conjugation (valid even singular c) identify original source and parity coordinates.
- ONLY second-order coefficient: not first-order pole, bounded finite part, cofinal control, Gamma cancellation, Hardy index or RH.

Production `lake --old env lean -o ... <leaf>` exit0 no warnings. Separate `/tmp` import #print axioms all7 public theorems: propext, Classical.choice, Quot.sound only. Umbrella wired, index regenerated. No umbrella build. Lint exit1, eleven unrelated unwired RHTower leaves: CCMApertureChainProfile, CCMApertureTranslationChains, CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation, CCMExponentialRampTerminalEntropy, CCMPrimeDeficitEulerPositiveRigidity, CCMRetainedChainKernelLower, MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines, ThetaMovingShellFirstOrderPhase, ZetaZeroDensityPowerSaving. New TG leaf absent. Scoped diff whitespace passes. All9 owned scratch/search/lint files removed. No owned jobs remain.

## New hard frontier evidence and next conjecture C6
Read current direct-subunit-anchor card sections12–14 (around1250–1365): central Gamma ghosts, exact co-shift absorption, bounded-clock anomalies, positive source order and existing scalar-continuable Krein landing are closed. Actual remaining target is noncentral signed/relative polar–Gamma colligation that survives as an operator across balanced wall, carrying integral charge without scalar normalization. Do not mistake finite cancellation for a global budget.

Read `PrimeBurnolDepthCompletion.lean` directly. `dense_primeBurnolLiteralDepthSpan (p)` says actual unsquared one-prime depth columns f_n=primeBurnolWindowFeatureLp(p,n)0 already span dense physical L2. The targeted corpus search was partial but returned these useful exact declarations. Broad Gamma search completed but no matching mixed inverse countercurrent; semantic top hits mostly irrelevant. New C6 argument uses direct source evidence, not literature assumptions.

Conjecture C6 (paper only; not Lean/no-go yet): use depths0..N, h_j=r f_j, P_N projection onto original f-span, w_j=(I-P_N)h_j, Gram(w)=K_N. Let b=G_N e0 and z_N=sum_j(K_N^-1 b)_j w_j. Then <f_j,z_N>=0, <h_j,z_N>=b_j; norm² z_N=(G_N K_N^-1 G_N)00. For any fixed original-column combination y and all sufficiently large N, <y,z_N>=0 but <h0,z_N>=||f0||²>0. Density lets y approximate h0; Cauchy-Schwarz forces ||z_N||->infinity. Positive trace Tr(G_N K_N^-1 G_N) consequently diverges. On one prime U=uI,V=vI, actual principal coefficient simplifies to -v(u-1/2)Tr(G_N K_N^-1 G_N), hence no uniform bound when scalar nonzero. This would not exclude cancellation in a new jointly renormalized Gamma carrier.

Required positive survivor BEFORE retiring candidate: normalized dual e_N=z_N/||z_N|| are unit vectors orthogonal to each fixed original packet eventually; density gives weak0; rank-one orthogonal projections then strong0 while rank1 (trace1 in appropriate interface). Need exact finite residual/dual norm proof, divergence and positive survivor formalized. This targets source operator survival rather than adding another scalar budget lemma.

Card `docs/drafts/pipeline/1-in-progress/tg-confluent-cofinal-counterterm.md` contains full argument/gates. Current log `.../tg-source-conjecture-loop-2026-10-01.md`; C5 parent `.../tg-mixed-reflection-collision-counterterm.md`; formalized card `docs/drafts/pipeline/3-formalized/tg-mixed-reflected-cubic-principal.md`. TG frontier map updated. Prior inverse module/card remain valid; card now points to checked cubic coefficient.

## Lean notes
- Matrix.diagonal_add rewrites SUM of diagonals to diagonal sum (forward); diagonal_sub same. To prove theta block idempotence, rewrite scalar I as diagonal, diagonal_smul backwards, then diagonal products and apply scalar theta identity.
- `.congr'` eventual function equality may require `simp only [...]` to beta-reduce, raw rw may miss lambda application.
- For sourceModularAutomorphism RingHom coercion, explicit `change` handles application before Matrix.coe_units_inv; simp only unfolding RingHom structure alone leaves coercion redex.
- In Tendsto product chain specify constant `(x:=p)`; specify continuous scalar map basepoint `(h.tendsto (0:ℝ)).mono_left (nhdsWithin_le_nhds (s:={0}ᶜ))`.
- Generic Matrix.mul_inv_rev + coe_units_inv proves inverse respects inner conjugation even singular; then RingHom map_mul/sub/pow and trace_units_conj' prove cubic trace invariance.
- Finish block coefficient by norm_num then simp [sub_eq_add_neg], not module tactic (trace arguments are nonlinear opaque atoms).
