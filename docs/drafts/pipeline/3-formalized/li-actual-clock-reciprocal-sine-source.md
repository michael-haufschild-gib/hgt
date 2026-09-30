# Literal reciprocal-frequency sine response

- **ID:** LI-CLOCK-RECIPROCAL-SINE-SOURCE
- **Stage:** 3-formalized
- **Type:** THEOREM; unconditional complete-source identity
- **Parent:** [sine growth boundary](../2-fully-proven/li-actual-clock-sine-growth-boundary.md)

For every real `t`, with `F(t)=tS(t²/16)` and `α_q=xiSpectralPoint q`,

`(F(t):ℂ)=Σ_(q:XiZeroCopy) α_q⁻¹ sin(tα_q⁻¹)`.

The complex sum is real. Every analytic multiplicity copy contributes once; no square-root branch or zero-location hypothesis occurs.

## Exact proof

The sine Taylor coefficient is `(-1)^j t^(2j+1) λ_q^(j+1)/(2j+1)!`, where `λ_q=α_q⁻²`. Its norm is at most `|λ_q||t|(t²/150)^j/(2j+1)!`. Summable absolute source mass and the complete factorial envelope give absolute convergence on `XiZeroCopy×ℕ`. Thus both complete sums commute. Literal central moment equality identifies each coefficient with the already formalized response coefficient; entire sine expansion identifies each zero-copy sum with its branch-free atom.

## Lean and verification

`LiEvenCrossActualClockSineSource.lean` has 12 public declarations: two definitions, complete Taylor/atom summability, complex source equality, real-part equality and zero imaginary part. Named `lake build --old` passed, 9522 jobs (own leaf 4.7s). Final exact source check passed with empty log. All 12 public axiom audits use only `propext`, `Classical.choice`, `Quot.sound`. Root read the complete proof and logs; import is wired into `RHTower.lean`.

Evidence: `/tmp/li_pole_audit_sine_named_build.log`, `/tmp/li_pole_audit_sine_axioms.log`, `/tmp/li_pole_audit_sine_final_direct.log`.

## Open burden

RH-conditional decay is additionally formalized in `LiEvenCrossActualClockSineDecay.lean`: `F(t)/t→0` and literal `S(w)→0`, by complete squared-weight dominated convergence and exact `t=4√w` substitution. Named build (9523 jobs, own leaf 3s), final exact direct check and all four public axiom audits passed. Evidence: `/tmp/hgt-clock-sine-decay-{build,direct,axioms}.log`. RH is an explicit premise.

Finite top-frequency isolation is additionally formalized in `LiEvenCrossActualClockTopFrequency.lean`: from `¬RiemannHypothesis`, a positive maximal reciprocal imaginary rate is attained by a finite nonempty complete multiplicity packet, and every remaining copy has a strict smaller upper rate. Named build (8837 jobs, own leaf 37s), final exact direct check and all nine public axiom audits passed. Evidence: `/tmp/li_pole_audit_top_frequency_{named_build,axioms,final_direct}.log`. Oscillatory amplitudes and RVM mean transfer remain paper-only.

Unconditional [cofinal response height](li-clock-unbounded-support-response-growth.md) is additionally formalized by unbounded spatial support and literal Volterra law: every tail contains `F(t)>M` for every M. This does not assert unbounded positive S, all-clock positivity, a negative literal witness or RH. Global lint remains red on unrelated unreachable modules.
