# Positive interior deficit from prime-2 blindness alone

Verdict: FALSE. Negative statement and positive survivors formalized.

## Exact rejected claim

A positive universal lower bound for k(0)-k(x) at every fixed x in (0,log 2), relative to k(0), follows solely from real L² autocorrelation and k(log 2)=0. The dyadic reciprocal points are not dense; continuity does not extend their bounds to the full interval.

## Exact obstruction

`formal/GaloisForLFunctions/RHTower/AutocorrelationBlindInterpolationObstruction.lean` proves `exists_blind_small_interior_deficit`: for every ε>0 there is a real L² source with positive mass, k(log 2)=0, and

    k(0)-k(4log 2/5) < ε k(0).

The source is a finite train of N+1 equal rectangular pulses, width d=log 2/10 and spacing a=4log 2/5. Exact overlap identities are k(0)=(N+1)d, k(a)=Nd, k(log 2)=0. These identities and the quantified family all passed direct `lake --old env lean` verification. No numerical experiment is involved.

A separate continuous positive-definite cosine witness in `EvenSectorLevyKreinRigidity.lean` has exact interior return to its maximum. Unlike that finite spectral witness, the rectangular pulse family consists of actual L² sources. The continuation `EvenSectorSmoothBlindInterpolationObstruction.lean` now proves the stronger obstruction inside `RealSmoothEvenPolarTestFn` itself: replace rectangles by `evenPolarProfile 20` and center the train. Smoothness, evenness, compact support, and the zero polar Fourier moment all hold exactly, while the same three autocorrelation values and arbitrarily small normalized interior deficit survive. Its hypothesis-free theorem `not_exists_positive_uniform_smooth_polar_interior_bound` rules out a universal positive constant at `4 log 2 / 5` even in this narrower domain.

## Positive survivor audit

The exact pole-eliminated EWU Lévy–sinh formula survives, including a proof of Bochner integrability and pointwise nonnegativity of its integrand. Krein's increment bound survives for every real L² source. The dyadic lower bound D(log 2/2^m)≥4^(-m)k(0) survives without any spectral moment assumption.

The valid interval-wide replacement couples complementary shifts:

    D(x)+D(log 2-x) ≥ k(0)/2.

It follows from D(x+y)≤2D(x)+2D(y). The full proof uses translation invariance and the square triangle inequality; no frequency moment enters. All these exact positive statements are formalized in `EvenSectorLevyKreinRigidity.lean`, and its direct Lean audit passed. Their dependency-closed paper proofs are on the companion EWU exact Lévy/Krein card.

## Scope

Corpus-only work. No external search or novelty audit. Original request's stronger interval claim cannot be proved as stated; goal disposition awaits user direction. All three modules are wired into `RHTower.lean`; no umbrella build was run. The smooth continuation passed its direct `lake --old env lean` audit and six scratch axiom checks, all using only `propext`, `Classical.choice`, `Quot.sound`. Final global lint reports 16 unrelated layout/umbrella errors and no task-module errors. The companion smooth-obstruction card records the full proof and commands.
