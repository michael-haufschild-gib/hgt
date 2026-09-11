HB current progress: new FullAngularGoursat module is installed and audited. RH remains UNPROVED; complete pulse/current pairing, physical QNM pairing and extinction remain OPEN. Goal remains ACTIVE. No subagents used.

Constraints: no Git, no launch.sh, no numerical experiments. Frontier map READ ONLY. Universal STATUS only genuinely route-independent new facts (not edited). Use own broad corpus queries plus deep method retrieval directly, no help/implementation preparation. One owned foreground Lean/Lake process at a time; lake env lean scratch; lake build exact new module final audit only; no umbrella/full/dependency rebuilds. Audit only new public theorem axioms. Keep updates <=60s. Every goal turn opens full chain, hard obstacle, prior progress, next attack.

New source: formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMFullAngularGoursat.lean (601 lines). Namespace RHTower.D4BMFullAngularGoursat. Imports existing ThetaCuspHawkingBMFullAngularCircleAction only. SHA256 2be351569394318dc60e450411b036911aca521616852c7a2c39aabac6594d99. Uses existing fullAngularRiemannKernel from Action and existing angularDirichletKernel/onsetDirichletKernel from Reconstruction; does not define replacement physical kernels.

Five new public theorems:
- fullAngularKernel_right_derivative line176: HasDerivWithinAt of actual angularMean(arcosh z) at z=1 within Ici1, value alpha*(H+Q)/2.
- onsetAngularKernel_right_derivative192: original pulse contact CH*alpha*(H+Q)/2 + CQ*DeltaQ/2.
- fullAngularRiemannKernel_goursat527: existing KH at any CausalPoint equals H(vertex) + double null integral of literal alpha*(KH+KQ)/(4*cosh(source+(a-b)/2)^2).
- fullAngularDirichletKernel_volterra558: existing H kernel retains original gated datum difference/2 plus direct-minus-image correction/2.
- onsetDirichletKernel_volterra580: existing pulse kernel retains actual fullSourceOnsetPulse vertex with both gates/2 + CH times H correction difference/2 + CQ times original native correction difference/2.
One new public def fullAngularCorrection539: literal integrated forcing within original direct gate, zero outside.
All five axiom reports EXACTLY propext, Classical.choice, Quot.sound. Do NOT re-audit old modules.

Proof: private regular-singular origin lemmas derived from existing NativeSpinTwoPrimitive: smooth h plus continuous g=alpha(h+m) gives h'(0)=0, h''(0)=g(0)/2. Slope/sinh limit and arcosh right filter give actual characteristic derivative. Existing native Goursat scalar null geometry copied/adapted: Z_y(u,v)=1+2*sinh(u/2)*sinh(v/2)/(cosh(y+(u-v)/2)*cosh y). Continuous clamped radius arcosh(max1z) extension, removed on whole physical cone. Finite angular first derivative times zero null-invariant axis derivative -> zero characteristic first derivative limit. Two actual FTC identities recover full closed cone including axes. Literal forcing avoids replacing H by Q. Original pulse vertex is derived from fullSourceOnsetPulse_transition and unchanged coefficients. No new hypotheses/axioms or unevaluated extinction premise.

Validation: scratch first contact part205lines passed; full proof had two interface conversion errors, fixed by rfl after unfolding old kernel aliases and simpa ... using! for existing KH vs angularMean. Full scratch then passed. Exact module build in isolated cache-only workspace passed: 2jobs, 323s, only new module built. 3994 cached project modules, 19937 hardlinked artifacts, 12 installed dependency cache stubs. Source+5 build artifacts installed byte-identical. One umbrella import in RHTower.lean. Index ran once: 4changed0removed, all six new API rows verified. Global lint FAILED only for unrelated unwired RHTower.ChronologicalTailTransform, plus existing large-file warnings. Last observed it remained unwired; do not silently report lint passed. No own-module gap.

All owned processes terminal. /tmp/hb-full-angular-goursat-0911 REMOVED. Four search JSONs hb-transversal-0911c, hb-origin-method-0911c, hb-darboux-goursat-0911c, hb-backstepping-0911c and lint capture REMOVED. No live handles. Do not reuse audit path or old sessions.

Docs:
- docs/drafts/pipeline/3-formalized/hb-full-angular-goursat.md full paper mechanism+validation.
- docs/drafts/pipeline/1-in-progress/hb-onset-pulse-green-action.md current attack, endpoint trace and preferred next constructive Green proof. Read its final ~45 lines first.

Next hard attack:
Existing timeOriginalForcing_full_onset_decomposition (FullSourceOnsetReduction352) gives F=wave(lift)-wave(seedH)/alpha+P/alpha. Define W=lift-seedH/alpha, P original full onset pulse. Need actual retarded R_F=W+R_P/alpha, then all four physical current terms (incoming/incoming, incoming/pulse, pulse/incoming, pulse/pulse with branch-specific factors), all physical faces and QNM pairing.

Preferred constructive Green mechanism (paper candidate, NOT Lean closed):
invariant(h,x,y) is symmetric x/y by explicit formula. Derive source-radius wave equations for KH and KQ from existing target-radius equations. For coefficient beta, circular image of wave(beta H) equals (beta_tt-beta_yy)*KH - beta*sech(y)^2*K_DeltaH. Source-radius kernel equation makes this a 2D Green divergence. Integrate on original backward causal half-domain; retain characteristic vertex and past/AdS faces. Actual W has zero past value/time derivative from fixed onset for tau+y<=0; seed and lift both vanish at scalar AdS boundary.
Crucial use of NEW PUBLIC GOURSAT: apply reciprocity first so original target x becomes FIXED source/center in Goursat formula. Backward source null coordinates then occur only as upper integration limits. FTC gives continuous single-integral first derivatives and mixed derivative directly from literal forcing. Avoid re-proving private arcosh derivative limits or importing a supplied global inverse. Moving-domain Green integration, characteristic corner admission, vector reconstruction, complete current pairing remain to prove.

Endpoint source admission insight (paper-only, not new Lean theorem):
From exact profiles radialUnit0=0; sourceAmplitude(s,0,a,1,0)=a²; sourceSeedFieldFirst(s,0,a,1,alpha,0)=a²alpha; radialLiftFirst(s,0,a,1,0)=0. Hence P(tau,0,z)=-2*a²*alpha*H(z)*chi'(tau)*exp(2s*tau). Do NOT blindly reuse a globally continuous odd-source lemma at AdS: split at zero or integrate original negative-tortoise half-domain with direct/image kernels. Gate/characteristic corner intersections still need AE integral justification.
Profiles definitions inspected: JointSourceAmplitude13, JointSourceLiftJets10-24, JointSourceRadialUnit14, FullSourceOnsetReduction29-72.

Search evidence:
Own broad transversal; deep radial regular singular/Volterra mechanism; OR Darboux Goursat; backstepping. All partial source+semantic coverage, source_only candidates with some stale entries. Inspected declarations/candidates/source_arguments/ingredient_sets. NativeGoursat and NativeCharacteristicContact actual source proofs supplied valid mechanism. Generic ClockGoursat existence does not identify physical kernel. Backstepping search had no direct lexical hit, unrelated semigroup/implicit-step suggestions; no proof adopted. FullNativeWave source1914lines read inventory and selected sections: it handles native Q response with original oddSource, not original CH H + CQ Q pulse. Can adapt finite triangle/Fubini machinery once pulse source admission fixed.

External own broad words: memory/transmutation/viscoelastic/backstepping/observability; recent preferred. Useful methodological lead https://arxiv.org/html/2605.25217v1 section3.2: triangular transform to transport, explicit boundary kernel equation, bounded transit time. NOT physical identification or proof dependency; controller free there, HB pulse fixed. June https://arxiv.org/html/2606.27722v1 is designed optimization feedback, no identified applicable lemma. Previous Aug port matching paper remains optional lead recorded in card. Do not repeat search as progress.
