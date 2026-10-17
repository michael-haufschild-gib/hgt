# Exact EWU Lévy/Krein package and interpolation obstruction

Date: 2026-10-17. User attachment f6f19c37-5edd-4cc0-b363-d81c8374fb0e/pasted-text-1.txt. Corpus-only, no web/novelty, no old research Markdown, no numerical experiments, no heartbeat changes, one own foreground Lean process; direct lake --old env lean audits; no full/umbrella builds or commits. Substantial concurrent work in shared tree, preserve it.

## Completed source

1. formal/GaloisForLFunctions/RHTower/EvenSectorLevyKreinRigidity.lean: real L² autocorrelation integral and translation identities, nonnegative deficit, Krein increment inequality, subadditivity bound D(x+y)≤2D(x)+2D(y), dyadic D(L)≤4^m D(L/2^m), literal EF.weilTest wrappers on real Lp sources, prime-two dyadic bound. In EvenSector, RealEvenPolarTestFn and RealSmoothEvenPolarTestFn subtypes, exact pole elimination, integrability of Lévy integrand, weilArchRe_eq_levy and pointwise nonnegativity. Positive survivor: D(x)+D(L-x)≥D(L)/2. Also continuous cosine positive-definite blind-interior-return witness, explicitly not an L² source.
2. formal/GaloisForLFunctions/RHTower/AutocorrelationBlindInterpolationObstruction.lean: rectangular pulse train, spacing a=4log2/5, width d=log2/10, exact k0=(N+1)d, k(a)=Nd, k(log2)=0. Actual real L² sources with arbitrarily small normalized deficit at fixed interior a. Endpoint exists_blind_small_interior_deficit.
3. formal/GaloisForLFunctions/RHTower/EvenSectorSmoothBlindInterpolationObstruction.lean: NEW exact smooth real EWU counterexample. Namespace RHTower.EvenSector.SmoothBlindInterpolation. packet=evenPolarProfile20, M=packetMass>0. packet support diameter <d by exact log2≥1/2. Centered train of N+1 packets at (i-N/2)a is smooth, compact, real, even (reflect i↦N-i), polar (each translated packet Fourier moment at i/2 remains zero). Reuses rectangle separation to obtain exact same counts with M: train_autocorr_zero=(N+1)M; train_autocorr_spacing=NM; train_autocorr_blind=0. test N : RealSmoothEvenPolarTestFn packages domain properties. exists_smooth_polar_blind_small_interior_deficit takes ε:Set.Ioi0 and gives positive mass, k(log2)=0, D(a)<εk0. not_exists_positive_uniform_smooth_polar_interior_bound has NO hypotheses and disproves any positive universal constant at a inside smooth real EWU.

All three imports added beside WeilArchimedeanExactForm in formal/GaloisForLFunctions/RHTower.lean (~27709). No umbrella build.

## Verified

All three modules passed direct lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/<module>.olean GaloisForLFunctions/RHTower/<module>.lean. New module final session87331 exit0 no diagnostics. New final scratch API+axiom audit session72963 exit0: test, three train autocorr endpoints, epsilon family, no-go all use only propext/Classical.choice/Quot.sound. Previous nine package endpoint axiom audits also passed with only those three. Mathlib names checked via scratch have:=@Name with pinned universes. Owned scratch files cleaned after recording results.

Latest formal lint session19945 exit1: 15 unrelated HTGeometry modules unreachable from umbrella plus root BiScaleUncertainty.lean location (16 errors total). No task-module errors. Earlier concurrent SymbolicRuellePollicott sorries disappeared from this latest lint. Never claim global lint passed; do not change concurrent work.

## Paper/progress cards

- docs/drafts/pipeline/3-formalized/ewu-exact-levy-krein-autocorrelation-2026-10-17.md
- docs/drafts/pipeline/3-formalized/ewu-smooth-polar-interpolation-obstruction-2026-10-17.md (moved from in-progress after audit)
- docs/drafts/pipeline/5-failed/ewu-continuous-interpolation-from-prime-two-blindness-2026-10-17.md
These task-owned cards have closed paper proofs, positive survivors, exact endpoints, audit results, and original goal disposition.

## Active goal blocker

Original attachment also claims continuous interpolation gives a universal positive pointwise lower bound on all [0,log2]. FALSE, now disproved even in exact real smooth EWU domain. No extra structure in requested domain rescues it. Do not mark original goal achieved by silently dropping this requirement. User was asked async in previous goal turn whether accept valid package+counterexample or investigate EWU structure; no answer yet. This continuation resolved latter option negatively with stronger exact-domain proof. The blocker persisted for three consecutive goal turns. Third-turn audit reread the attachment and current Lean no-go source and umbrella imports: objective unchanged, exact-domain contradiction still present, no remaining aligned work can make the false theorem true. Previous turn classified as progress (new smooth EWU proof and audits). update_goal(status="blocked") succeeded on the third turn. Current goal status BLOCKED, not complete. Resume requires a corrected objective; a user resumption starts a fresh blocked-turn audit.

## Lean elaboration lessons

HasCompactSupport.comp_left can exhaust default heartbeats inferring the composed function for train; solved with explicit (f:=train N) (g:=Complex.ofReal). Qualified SeparatedBump.hasCompactSupport_of_abs_gt avoids shadowing. ContDiff∞ to C2 uses WithTop.coe_le_coe.mpr (show (2:ℕ∞)≤⊤ from le_top). Keep explicit helper lemmas for nested RealSmoothEvenPolarTestFn construction. No heartbeat hacks.
