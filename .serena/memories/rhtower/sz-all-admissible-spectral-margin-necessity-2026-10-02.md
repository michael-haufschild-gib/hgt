Route SZ active; unconditional RH proof/falsification remains unachieved. User: no subagents, numerical experiments, added axioms/sorry, heartbeat increases, commits, full/umbrella builds; corpus-first conjecture/proof loop and foreground serial leaf audits.

New milestone completed:
- SuzukiSpectralMarginSource.lean (196 lines): actual covariance C, prescribed c, true ground energy E=1/||C||-c. Positive m, shift d=c+(m-1)/||C|| exhausts d>-E; exact (E+d)/(E+c)=m. Transfer T=I+(m-1)C/||C|| has coercivity q=min(1,m)>0. Construct actual inverse, response C T^-1 p, prove (A+d)x=p and q||d x-p||<=||c C p-p||. 9 public theorems.
- SuzukiSpectralMarginLimit.lean (200 lines): physical defect via actual isometry and raw exp(x) source, both complex weighted normalized mixed errors->0 on full joint filter a->infinity, all m>0. With P=d exp(-(1+s)a)<p_s,x>, M=d exp(-(1+s)a)<p_-s,x>, get q(P-g)->0, qM->0 where g=1/(1+s) for .5<s<1. 3 public theorems.
- SuzukiSpectralMarginNecessity.lean (109 lines): literal Fourier carrier imaginary quotient. Nonzero carrier limit at one segment point implies qP=Cayley*qM/B->0 (unscaled denominator eventually nonzero). Thus qg->0, q->0, eventually m=q, m->0. Root suzukiSpectralMargin_xi_limit_forces_relative_floor (line89) forces (E+d)/(E+c)->0 for any cofinal locally uniform Xi-identifying fixed-source schedule. General nonzero-limit theorem at line31. 3 public theorems.
- This is a genuine necessary source law, NOT existence/identification, absolute gap->0, parity/simplicity/ground overlap, or RH. Covers all admissible metric shifts at fixed source exp(x), NOT moving source anchors.
- Existing SuzukiRaisedMetricShiftCarrier.lean nonzero Xi segment witness made public: exists_xi_target_imaginary_ne_zero. Only declaration visibility/comment changed; proof reused.

Audits:
Source scratch56723/final17124; Limit scratch40762/final44729; Necessity scratch15326/final15580; reused witness leaf final2368. All final commands from formal/: lake --old env lean GaloisForLFunctions/RHTower/<leaf>.lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/<leaf>.olean. All exit0 warning-free.
Axiom39186 checked all15 new public theorems + witness: ONLY propext, Classical.choice, Quot.sound.
3 new imports once in RHTower.lean lines18181-18183 at check. No umbrella build.
Lint63539 exit1 on10 unrelated unreachable modules: CCMApertureChainProfile, CCMApertureTranslationChains, CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation, CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower, MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines, ThetaMovingShellFirstOrderPhase, ZetaZeroDensityPowerSaving. None current leaves. Global lint NOT green.
Brief process lapse: replacement77328 accidentally overlapped scratch13394; terminated ONLY owned PIDs21877/21740, exit143; original then exited1. All subsequent checks strictly serial; all processes now terminal.

Docs:
- P3 docs/drafts/pipeline/3-formalized/sz-spectral-edge-shift-necessity.md has complete paper proof, commands, audit/cleanup ledger. Old P1 path removed.
- Frontier map adds all-admissible necessary-margin paragraph, updates old raised-shift P1 reference to P3.
- Existing P5 sz-prescribed-shift-direct-xi-identification extended with positive survivor.
- Working log docs/drafts/pipeline/1-in-progress/sz-source-wronskian-conjecture-loop-2026-10-01.md records closure/process issue.
- NEXT card P1 sz-actual-source-defect-quasimode.md, precise source-derived conjecture with paper mechanism, Lean pending.

NEXT exact conjecture:
For same actual source p, shifted response x, y=d*x-p, nonzero carrier limit should force y eventually nonzero and ||(I-C/||C||)y||/||y|| ->0. Let r=exp(-(1+s)a), G+ =r<p_s,p> ->g>0, G- ->0. Errors P-G+,M-G- have norms<=exp(-a)||y||. B P=k M implies ||B G+-kG-|| <=(||B||+||k||)exp(-a)||y||. LHS has positive limit, so normalized y is bounded below. Base source residual ||c C p-p|| <=K exp(a)*profile_error, error->0. Hence residual/||y||->0. Exact (I-C/mu)y=T y-m(C/mu)y and m->0 give quasimode law. It is ONLY relative covariance-scale concentration, NOT distance to a ground eigenspace or absolute gap. No constant optimization needed. Actual signed parity/residue and canonical-head Gamma-prime-polar positivity remain hardest arithmetic problems. Do not replace them with generic receivers.

Corpus reads/searches:
Search1190824 partial/pending source-only, no proofideas/ingredientsets; actual covariance source APIs verified Lean. Residue search1190984 older snapshot1190971/semantic timeout, proposed ingredient set irrelevant moving-wall alignment. Lexical quasimode search gave no applicable result; no novelty claim from misses. Actual modulus search1191029 partial/older1191028, decomposition-only ingredientset, not actual sign proof.
Read SuzukiGroundProjectionReflectionCone first205: conditional projected equal-norm cone, does not establish actual projection. Read SuzukiLimitingLogGroundSimplicity intro +1690-1748: unconditional simplicity is for limiting logarithmic operator on aperture1, NOT actual interval Weil operator. Read CCMRestrictedWeilFriedrichsOperator1-165: actual Gamma + polar mixed term - prime. Cannot import logarithmic modulus/sign argument across polar term without proof. SuzukiParityResolventTransportBudget has conditional finite cross-gap budget and bi-unbounded parity ordering no-go (465-540,610-680 read).

Lean lessons:
- inner_self_eq_norm_sq_to_K creates RCLike casts; norm_cast solved coercivity; rw [←Complex.ofReal_pow] did not.
- q NNReal subtype in isUnit coercivity: explicitly change goal to ||v||²*q <= norm(inner...). 
- Cauchy-Schwarz with underscore vectors produced stuck InnerProductSpace or Complex norm-instance mismatch. Explicit vectors norm_inner_le_norm (v b.1) ((d:ℂ)•f-p) solved.
- Quotient field_simp with denominator-ne-zero in context closed goal entirely; extra ring caused No goals to be solved.
- Avoid dividing by shifted normalization d, which may be zero/negative.
- Final q->m equality uses eventual q<1 and le_total 1 m.

Cleanup complete: exact10 /tmp files removed (sz_floor_margin_search.json, sz_spectral_margin_source.lean, sz_spectral_margin_extra.txt, sz_spectral_margin_limit.lean, sz_spectral_margin_necessity.lean, sz_floor_residue_search.json, sz_floor_quasimode_search.json, sz_actual_modulus_search.json, sz_spectral_margin_axioms.lean, sz_spectral_margin_lint.txt). Verified remaining=[]; all3 audited oleans retained. Targeted git diff --check and new-file whitespace/import checks passed. Preserve unrelated huge dirty tree. Do not redo passed checks absent changes.

Previous context memory: mem:rhtower/sz-raised-metric-shift-collapse-2026-10-02. Goal stays ACTIVE; no goal status mutation.