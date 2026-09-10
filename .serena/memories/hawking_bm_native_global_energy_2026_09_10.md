CURRENT SUCCESSOR: `mem:hawking_bm_native_radial_endpoint_2026_09_10`. The actual angular energy family and Dirichlet endpoint value/radial-derivative convergence are now installed and audited. NativeJointEnergy is now 1223 lines; new NativeRadialEndpoint is 261 lines. Next: radial convolution and the original four-slot closed-graph admission. Full native domain admission and RH remain unproved. Do not repeat the completed global energy/family/endpoint audits.

# HB native global gradient energy — 2026-09-10

Goal ACTIVE: unconditional RH proof/falsification through literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH. RH, complete current cancellation, complete inverse identification and native form-domain admission remain UNPROVED. Global native gradient energy and its exact source-response identity are now CLOSED, not an open target.

Authoritative report: docs/drafts/pipeline/3-formalized/hb-native-global-energy.md.
Active card: docs/drafts/pipeline/1-in-progress/hb-native-cusp-inverse-identification.md, Native elliptic energy construction (end of file). Earlier cutoff report docs/drafts/pipeline/3-formalized/hb-native-joint-energy.md updated to point to the global closure. Frontier map READ ONLY. Universal ledger unchanged: this new result is route-local.

## Installed, audited public theorems
Extended formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMNativeJointEnergy.lean (935 lines):
- nativeTimePrimitive_forcing_pairing_limit, line 656: actual complex source pairing integrable and actual eta_n² localizations converge.
- nativeTimePrimitive_cutoff_energy_limit, line 701: exact total cutoff energy tends to full source pairing, before global derivative admission.
- nativeJointGradientEnergy, definition line 748: actual radial derivative norm plus original global native hyperbolic frame derivative norms with sech² radial weight.
- nativeTimePrimitive_gradient_energy_integrable, line 795: global original gradient energy integrable and bounded by Re integral conj(G) W.
- nativeTimePrimitive_global_energy, line 871: exact global equality integral E = Re integral conj(G) W.
All q,s,amplitude,t universally quantified; no additional analytic hypotheses. Complete G includes all three principal cutoff commutators. All four new public theorems use only propext, Classical.choice, Quot.sound. Do NOT reaudit old theorems.

## Actual positive proof mechanism
W,G are already admitted to original joint L² by NativeResidualAdmission. M=||G||²+||W||² is L¹, dominates all complex cutoff pairings, and cutoff norm≤1. Full cutoff germ eventually1 gives pairing convergence by DCT. Exact old cutoff identity plus audited error limit gives integral F_n→L before global energy admission.
E is original actual derivative density; raw chart jets give continuous representative a.e. Full cutoff germ preserves derivatives, hence F_n=E eventually at each original cell point.
First Fatou gives finite integral E≤L. Product rule gives F_n≤2E+2e_n where e_n is actual weighted cutoff error with integral→0. Second Fatou on 2E+2e_n−F_n gives integral E≤2 integral E−L, hence exact equality. This avoids a separate uniform gradient majorant and excludes escaping energy. No new uniform derivative estimate needed.
Private helpers in same extended module: nonnegative_integral_limit (extended-integral Fatou with finite convergent integrals), gradient_energy_chart, gradient_energy_measurable, cutoff_energy_pointwise, square_cutoff_product_bound, cutoff_energy_complement_nonnegative. Earlier private jointJets_continuous, native_cutoff_frame, frame_germ_eq remain available within module.

## Next direct attack: native first-derivative graph admission
The hardest ultimate target remains 2 Ω(B(p,p)/2,B(m,m)/2)=0 with independent SS/SV/VV amplitudes and all onset/horizon/AdS/temporal/cusp currents. Immediate obligation is native domain admission for complete inverse identification.
1. Prove actual cutoff graph convergence: integrable E controls (eta_n−1) grad W by DCT; existing error integral controls W grad eta_n.
2. Each fixed cutoff/radius is ALREADY an angular CoreField: nativeTimePrimitiveCutoff in NativeAngularGreen. Do not build unnecessary angular charts/partitions/mollification. Joint value/frame continuity and compact angular support should establish continuity of x↦that field in angular energyDomain.
3. Its actual x=0 trace vanishes, including angular derivative slots because boundary value is identically zero angularly. Zero-extend this angular-energy-valued family, translate into negative x, mollify radially at a smaller scale. This yields smooth compact RadialEnergyFamily.
4. Prove derivative after original angular value embedding equals mollification of zero-extended actual W_x by integration by parts and zero trace. Do NOT demand W_x in angular energyDomain or mixed spatial derivatives. Radial mollification gives smoothness in AngularEnergy; derivative convergence only needed after original value embedding.
5. RadialEnergyFamily.graph_mem in ThetaCuspHawkingBMJointRadialFamilyAdmission.lean:63 admits resulting families. Structure in ThetaCuspHawkingBMJointRadialFamilyData.lean: field ℝ→energyDomain, smooth∞, compact, tsupport⊆Iio0.
6. Extend weak elliptic identity through graph convergence; get W_graph=J.adjoint(W+G), W=J J.adjoint(W+G), actual Friedrichs (I+A)W=W+G. Then bounded-resolvent comparison B u+(I−B)W=0 and conserved bounded energy can kill native/physical difference. Do not assume operator-domain admission of W'.

Search found radialDirichlet_zeroExtension_derivative in ThetaCuspHawkingBMRadialDirichletZeroExtension.lean:56, but it presupposes existing radialDirichletDomain membership. It cannot discharge native admission. Angular family construction is the positive replacement.
MollifierUniformApproximation / MollifierPositionCommutator found scalar real mollification bounds; they do not themselves supply Hilbert derivative-graph approximation.

## Search and outside literature
Own broad terms: Scheffe, cutoff gradient, zero extension, mollification; deep mechanism queries for Fatou, complementary integral limits, and graph approximation. Inspected candidate_lemmas, source_arguments/methods, proof_ideas, ingredient_sets and coverage/compiler freshness. Results partial, mostly source_only, some deadline failures. Method ingredients unverified until Lean. Source Fatou mechanisms from DiskSmirnovRadialL1 and HeatEnergyBridge used without their domain-specific hypotheses.
Own arXiv terms tightness and recovery (newest first). Read Ding–Liu–Lo arxiv.org/html/2609.10222v1, Sep9 2026, sections3.3–3.4: subtract adjacent evolution equations, retain compatibility defects and derivative jumps. Suggestion only for later onset-current comparison. Delayed parabolic hypotheses and nonzero mismatch are not native premises.

## Validation and cleanup complete
Full final scratch lake env lean passed warning-free.
Final exact leaf lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeJointEnergy passed (12s reported build, 2 jobs), isolated audit, 4134 cached local modules, 11 cached dependency packages. No dependency/full/umbrella rebuild.
Only four new theorem axiom checks passed. Source equality guard before install; source and five emitted .olean/.ilean/.trace/.olean.hash/.ilean.hash artifacts byte-identical to audit. Existing RHTower.lean import at17090 already wired module; no umbrella edit/build.
Formal lint passed existing large-file warnings; this leaf935lines.
Owned /tmp/hb-native-global-energy.sODOap3w (including audit) and eight search JSON files REMOVED. Every owned process handle observed terminal; no owned Lean/Lake process remained. No computations, Git or launch.sh.

## Lean practical points
Keep explicit types for constants in Tendsto.add/sub, especially 2*integral E. Explicit lambda Integrable hypothesis before integral_sub avoids Pi.add rewrite mismatch. add_le_add (le_refl a) h is robust; add_le_add_left used unexpected orientation in this toolchain. Eventually pointwise equality may not expose .symm field: filter_upwards then hn.symm. For constant full-germ frame derivative, change fderiv of composed constant to explicit fun _ : ℂ =>1 before simp.
Only one foreground owned Lean/Lake process; poll actual live session until exit_code before next. No stale process cleanup affecting others. No computations or full builds. Cache audit uses exactly11 package stubs excluding Cli, ClassFieldTheory cache .lake/build/default/lib/lean, roots/globs empty for dependencies; exact changed leaf only.
