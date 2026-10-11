# Additive local modulus for logarithmic nodal distortion

Status: formalized, including canonical raw-weight identification and grid modulus; native builds and complete axiom/API audit passed.
Date: 2026-10-10. Local corpus only.

Use the now-formalized positive distortions a_i for r+2 positive distinct nodes x_i. For x_i<=x_j, the proved local bound is a_i<=a_j and (x_i/x_j)^r a_j<=a_i.

Paper proof:
1. Put delta=x_j-x_i>=0. Bernoulli, already verified in the preceding corpus increments, gives (x_i/x_j)^r=(1-delta/x_j)^r>=1-r*delta/x_j. Its hypothesis holds since 0<=delta/x_j<1.
2. Multiply by positive a_j and x_j. Obtain the unconditional cross bound (x_j-r*delta)a_j<=x_j*a_i. Equivalently (x_j-r*delta)(a_j-a_i)<=r*delta*a_i.
3. If 2r*delta<=x_j, then x_j-r*delta>=x_j/2, so x_j*(a_j-a_i)<=2r*delta*a_i. This retains index separation, unlike the earlier global endpoint-power comparison.
4. More symmetrically, let A>0, A<=x_i,x_j, and 2r*abs(x_i-x_j)<=A. Then A*abs(a_i/a_j-1)<=2r*abs(x_i-x_j). If x_i>=x_j, use step3 with the indices swapped and divide by positive a_j. If x_i<=x_j, step1 gives 1-a_i/a_j<=r*(x_j-x_i)/x_j; clearing denominators and A<=x_j gives the stronger factor-one bound. The equal-index case follows from positivity and a_i/a_i=1.

Completed: unconditional Bernoulli cross receiver plus the quantified structural-width local modulus. Lean exposes a stronger statement: the cross-multiplied local modulus needs no separate positivity assumption on A. All analytic input comes from the proved logarithmic-mean distortion and already-audited Bernoulli inequality. No new analytic estimate is admitted as a premise.

Grid specialization: x_i=A+i and A>=2(r+1)² makes the modulus valid for every pair of indices. Relative distortion near a central index is therefore controlled by its distance from that index divided by order. This is the missing finite estimate needed before attempting binomial concentration and maximum-coefficient control for the still-unproved quadratic-start mass limit.

Completed in `WeilLogShiftLocalDistortionModulus.lean`: Bernoulli cross bound (line9), ordered additive error (line41), and general relative modulus (line54). Completed in `WeilLogShiftCanonicalDistortionModulus.lean`: positive physical nodes, their positivity/injectivity/gaps, canonical raw distortion, exact identification with the ratio of logarithmic and arithmetic raw weights (line36), quadratic scaled modulus (line67), and root `finiteWeilCanonicalRawDistortion_index_modulus` (line110), giving abs(a_i/a_j-1)<=abs(i-j)/(r+1) whenever k+2>=2(r+1)².

Focused local `local distortion error` search had no hits; broader `distortion` search returned seven declarations from the already-read global comparison, Bernoulli width, and local distortion producers. No separate additive local modulus was found.

Verification: both native leaf builds exited0 with empty final logs; `/tmp/hgt-modulus-final-audit.lean` checked all 11 public declarations and 8 explicit API terms. Axioms are contained in `propext`, `Classical.choice`, `Quot.sound`. Metadata audit reports no source/direct-dependency freshness, complete axiom coverage, or exact umbrella-count issues; the direct Mathlib Bernoulli dependency is fresh. Exhaustive incoming imports are the umbrella and internal generic-to-canonical chain. No numerical experiments, heartbeat change, full/umbrella build, or external source lookup.

Lean lessons: `field_simp` did not use positivity stated on the unfolded distortion after introducing a local abbreviation; `change 0 < aj at hj` made the nonzero fact available. A `by_cases` negated equality needed an explicit `hne : i != j` before `.symm`. After those fixes, remove two redundant `ring` calls already closed by `field_simp`. No mathematical weakening; the positivity premise on A was eliminated.

Formal lint `/tmp/hgt-modulus-lint.log` exits1 on eight unrelated missing imports: `RHTower.JointAncestryClusterPhase`, `RHTower.JointAncestryLogWeightBernoulli`, `RHTower.JointAncestryLogWeightExpansion`, `RHTower.JointAncestryLogWeightPrimeSum`, `RHTower.LiSignAlongSquares`, `RHTower.XiCosineShiftExceptionalOnset`, `HTGeometry.QKrawtchoukCompanionTriangular`, `HTGeometry.TaylorFiniteOrderPositiveAxisBound`. No errors in these leaves; foreign work untouched.

Next: centered binomial second moments, then simultaneous total-mass and maximum-coefficient control. The quadratic-start asymptotic is not yet formalized.

Local index refresh exited0. Exact post-index lookup found `finiteWeilCanonicalRawDistortion_index_modulus` at source line110. All owned build, audit, lint, index, and search sessions are terminal. The next dependency-closed paper argument is `../2-fully-proven/finite-weil-quadratic-mass-concentration.md`; its concentration and asymptotic Lean bridges remain pending.
