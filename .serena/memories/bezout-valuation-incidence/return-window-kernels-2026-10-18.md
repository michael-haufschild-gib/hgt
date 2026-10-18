Contribution 007 completed, root goal total 7 / 250; goal still active.
Source: formal/GaloisForLFunctions/BezoutValuationIncidence/ReturnWindowTwoMomentKernelsAndSharpZeroBlocks.lean (409 lines; 25 declarations: 9 public theorems, 4 public definitions, 12 private helpers).
Card: docs/drafts/pipeline/3-formalized/bvi-translated-prefix-observability-and-maximal-zero-runs-2026-10-18.md.
Write L(M)=sievePrefixDiscrepancy N M c, H=finiteHarmonicSum N c, D=H-sum[1,N] c(d).
Generic private helpers prove common-period translation and reflection L(P-(t+1))=D-L(t) for t<P; uses the existing residueCombination bridge and core Nat.mul_sub_mod.
Public unconditional statements use P=(k+a+1)*N!, ensuring divisibility and P>=a for all natural parameters.
Exact all-radii kernel: zero on [P-a,P+b] iff initial zero on [1,max(b,a-1)] AND (a=0 OR D=0), including N=0,1 and zero radii.
With a,b>0, s=min(max(b,a-1),N), kernel iff c(2..s)=0, sum[s+1,N]c(d)/d=0, and sum[s+1,N]c(d)=0. Reflection supplies a second tail moment; c(1) remains unrestricted.
At N=n+3, centered radius n+1 window (2N-3 samples) vanishes iff variance zero.
At N=n+4, window [P-(N-2),P+(N-3)] (2N-4 samples) has unique tail direction c(N-2)=v(N-2), c(N-1)=-2v(N-1), c(N)=vN, others 2..N-3 zero. Normalized second difference v*(1,-2,1).
Canonical triple has adjacent values -v(N-2), v(N-2); variance zero iff v=0.
Arbitrary-phase horizon remains OPEN, not falsified/retired. Backlog: docs/drafts/pipeline/0-backlog/bvi-arbitrary-phase-observation-horizon-2026-10-18.md. A matching arbitrary-phase upper bound is an uncounted refinement; do not double-count this lower-bound/classification package.
Named original-source lake --old env lean -j 1 audit passed without diagnostics. All 13 public declarations axiom-audited; all 9 theorem closures exactly propext, Classical.choice, Quot.sound.
Raw audit logs/bvi-root-2026-10-18-return-window-axioms.txt.
Source SHA256 ea7fd45d595e76066f25db9326c03e372f359781b4e89780b4087dabb1567670.
Olean SHA256 a0f1e40cc354839ca8177bb365a5db796ff68094ea0609a5511db533ad7df6c5.
Artifact installed atomically, newer than unchanged source. Wired once. Index: all 25 declarations match lexical DB names/kinds/lines/module/path; public cache/LEAN_API deliberately contain only 13 public declarations.
Global lint exit1 only 5 foreign umbrella omissions: BiScaleUncertainty.AffineFourierCorrelation, BiScaleUncertainty.DivisorSieveAffineSpectrum, BezoutValuationIncidence.DilatedCellScalingAndSecondOctaveFermiJumpBridge, BezoutValuationIncidence.EndpointHaarCellDecompositionAndWitnessPronicTransfer, BezoutValuationIncidence.PowerDampedPronicMultiplicativityAndRoutePMBridge. 381 unrelated large-file warnings; no owned-module/proof-debt finding. At inventory 14/17 field leaves wired. Preserve concurrent work.
Local corpus only, partial coverage disclosed; inspected all candidate/source-argument sections for deep searches and all new field declaration statements. No experiments, external sources, hgtl7, full/umbrella builds, or dev server.
All 18 /tmp/bvi7-* paths cleaned via guarded script, all owned jobs terminal. Source/artifact hashes preserved. Serena symbol tools reject this field as ignored; patch fallback without ignore changes.
