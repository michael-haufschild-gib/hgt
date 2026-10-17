# The interpolation obstruction inside smooth real EWU

Status: paper proof closed; Lean formalization verified. Continues the original exact EWU Lévy/Krein objective, without claiming the false interval-wide requirement achieved.

Previous goal turn: progress (two verified Lean modules, exact L² counterexample family, axiom audit). This continuation proves the obstruction in the narrower real smooth EWU domain itself. Original mathematical blocker persists for a second consecutive goal turn; no further domain restriction in the original request remains to test.

## Statement

For every ε>0, there exists a real SmoothEvenPolarTestFn with positive autocorrelation mass, k(log 2)=0, and k(0)-k(4log 2/5)<ε k(0). No assumption on spectral second moments or unproved analytic premises.

## Corpus proof

Use q=evenPolarProfile 20. Existing corpus proves smoothness, evenness, compact support, Fourier value zero at i/2, and strictly positive square integral M. Its support radius is 3/(4(2·20+3)); twice this radius is less than log 2/10, using log 2≥1/2.

Set a=4log 2/5. For N≥0, define g_N(u)=Σ_{j=0}^N q(u-(j-N/2)a). This is real, smooth, compactly supported, and even by reversing j↦N-j. Every translate retains the vanishing polar Fourier value, so g_N is an actual smooth EWU source.

The separation inequalities were proved for the earlier rectangular pulse family. They imply that overlap integrals of two q-translates vanish except at identical centers (shift zero) or adjacent centers (shift a); at shift log 2, every overlap vanishes. Consequently k_N(0)=(N+1)M, k_N(a)=NM, k_N(log 2)=0. Choose N+1>1/ε. This disproves the all-interior positive bound within the precise real smooth EWU domain.

Positive survivors remain the exact Lévy identity, general L² Krein inequality, dyadic lower bound and complementary-shift bound, already formalized in EvenSectorLevyKreinRigidity.lean. No external or novelty search.

## Gates

All scoped gates completed:

- `lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/EvenSectorSmoothBlindInterpolationObstruction.olean GaloisForLFunctions/RHTower/EvenSectorSmoothBlindInterpolationObstruction.lean`: exit 0, no diagnostics.
- `lake --old env lean /tmp/ewu-smooth-final-audit.lean`: exit 0. Mathlib API checks use `have := @Name`. Six axiom audits (the packaged test, three exact autocorrelation values, the small-deficit family, and the hypothesis-free no-go theorem) report only `propext`, `Classical.choice`, `Quot.sound`.
- New module imported in `RHTower.lean` beside the two earlier task modules. No umbrella or full build run.
- Final `scripts/formal_tools.py lint`: exit 1 on 16 unrelated errors: 15 HTGeometry umbrella omissions and the package-root `BiScaleUncertainty.lean` location. No task-module errors or task proof debt. Earlier concurrent `sorry` errors are absent from this final lint output.
- One owned foreground Lean process at a time. No numerical experiments, external searches, added axioms, heartbeat changes, commits, or pushes. Owned scratch files removed after recording results.

## Exact Lean endpoints

Namespace `RHTower.EvenSector.SmoothBlindInterpolation` in `formal/GaloisForLFunctions/RHTower/EvenSectorSmoothBlindInterpolationObstruction.lean`:

- `test N : RealSmoothEvenPolarTestFn` packages the actual smooth, real, even, compactly supported polar source.
- `train_autocorr_zero`, `train_autocorr_spacing`, `train_autocorr_blind` give the exact three values in the paper proof.
- `exists_smooth_polar_blind_small_interior_deficit` supplies arbitrarily small normalized deficit at the fixed interior point `pulseSpacing`.
- `not_exists_positive_uniform_smooth_polar_interior_bound` has no hypotheses and refutes a positive universal constant at that point.

## Positive survivor and disposition

The exact pole-eliminated Lévy identity, nonnegative integrand, real L² Krein inequality, dyadic bound, and complementary-shift bound remain fully proved and formalized in `EvenSectorLevyKreinRigidity.lean`. This new obstruction strengthens the failed-route audit without weakening those results. See the companion formalized EWU card and failed interpolation card for their closed proofs.

The original interval-wide positive lower bound is false even in the exact real smooth EWU domain. Original goal remains unachieved as written; no user direction accepting a corrected objective has arrived. The narrower-domain investigation proposed in the earlier question is now resolved negatively.

Third-turn blocked audit: reread the original attachment and current exact-domain no-go theorem, and confirmed all three umbrella imports. Same mathematical contradiction persists for three consecutive goal turns. Previous turn was progress (new smooth EWU proof and completed audits); no remaining aligned action can establish the false claim. `update_goal(status="blocked")` succeeded. Goal is blocked pending correction of the interval requirement, not complete.
