# CHMD: local reflected-jump absorption fails

Status: local positivity conjecture disproved; dependency-closed paper proof and exact positive survivor formalized and kernel-audited.

Scope: the literal reflected off-diagonal jump kernel of the original von Mangoldt Doob source on odd half-line tests. The CHMD route and unconditional RH goal remain active.

## Rejected conjecture

After odd folding, a positive scalar reweighting together with archimedean density and diagonal killing corrections might make the entire reflected jump kernel nonnegative.

This is false. It does not imply negativity of the Weil quadratic form and does not exclude nonlocal Hilbert or Hodge factorizations.

## Exact obstruction and positive survivor

Write Theta for `riemannKernelReal`, a_n=Lambda(n)/sqrt(n) with the original cutoff n>=2, and L_n=log n. On ordered positive pairs x<y, the normalized positive jump measure consists of

- the density `[archLevyDensity(y-x)-archLevyDensity(y+x)] Theta(x) Theta(y) dx dy`;
- the pushforwards of `a_n Theta(x) Theta(x+L_n) dx`, x>0, along `(x,x+L_n)`.

The normalized negative jump measure is the sum of the pushforwards of `a_n Theta(x) Theta(L_n-x) dx`, 0<x<L_n/2, along `(x,L_n-x)`.

These two complete measures are mutually singular. Let S be the union of the ordered reflected lines x+y=L_n. Every such line has planar measure zero. Each forward line meets each reflected line in at most one point; weighted one-dimensional Lebesgue measure gives these countable intersections zero mass. Every reflected measure is supported on its own line. This proves the global separation without truncating any prime power.

On B={(x,log 2-x):0<x<log 2/2}, the negative measure restricts exactly to the reflected n=2 measure. Its mass is strictly positive and finite: the original coefficient a_2 and both theta factors are positive, and the density is continuous on the compact interval closure. All positive jump contributions vanish on B, as do every other reflected prime and every diagonal measure. A strictly positive measurable reweighting preserves this contrast. Any additional absolutely continuous measure has zero mass on B. Thus the negative singular component cannot be absorbed into a locally positive jump measure by these operations.

The positive survivor is the exact original compensation, not just the negative statement. For every continuous compactly supported odd real v,

`primeCrossing(v,n) = a_n * integral(collarKillingDensity(v,L_n)) - 2 * reflectedDifference(v,n)`.

The complete sum of these compensated terms equals the absolutely convergent positive divisor-cut expansion from `CHMDPrimeDivisorCuts.lean`. It is strictly positive for every nonzero v in that class. The original per-prime energy carries `2 * sameSideEnergy + compensation`; the full Doob source retains the original archimedean energy and negative cosh mass. No source weight or theta index is changed.

## Lean artifact

`formal/GaloisForLFunctions/RHTower/CHMDReflectedPrimeSingularPart.lean`, namespace `RHTower.CHMDReflectedPrime`.

- `negativeJumpMeasure_restrict_slice`: exact first-prime singular restriction.
- `negativeJumpMeasure_slice_pos`, `negativeJumpMeasure_slice_lt_top`: nonzero finite negative-component mass.
- `negative_component_survives_positive_gauge`: persistence under positive reweighting, absolutely continuous measure additions, and diagonal measures.
- `positive_negative_mutuallySingular`: full global sign separation.
- `reflectedDifference_as_measure`, `integral_primeJump_eq_reflected_difference`: link to the original prime energy.
- `compensated_source_hasSum_cuts`, `compensated_source_pos`: exact positive survivor with every prime retained.
- `doob_source_eq_reflected_compensation`: full original source identity, cosh subtraction explicit.

## Frontier consequence

A local positive-jump comparison cannot erase the reflected prime sector. The negative coefficient must remain coupled to its exact positive collar diagonal, which forms a reflection sum-square interaction. The remaining problem is global positivity with the original cosh subtraction. No new RH equivalence, receiver, improved bound, numerical experiment, or novelty claim is supplied.

## Validation

The new leaf has 415 lines and 50 declarations. Scratch proof and separate mathlib-name probe passed. `lake --old build GaloisForLFunctions.RHTower.CHMDReflectedPrimeSingularPart` exited 0; final plain `lake env lean GaloisForLFunctions/RHTower/CHMDReflectedPrimeSingularPart.lean` exited 0 with empty output. All 50 declarations audited with `#print axioms` in `/tmp`: only `propext`, `Classical.choice`, `Quot.sound`. Leaf wired once in `formal/GaloisForLFunctions/RHTower.lean`. Source SHA-256: `e397128936fcad6ccc9c3c89584a80355aab740404d86f973851c23539c3fef8`.

Index refresh exited 0 (7 changed sources, including concurrent work). Formal lint exited 1 solely because concurrent, unrelated `DeningerMeyerInvisibleTorsionFree` and `DeningerMeyerSourceShiftTopology` were unreachable from the RHTower umbrella. This leaf was reachable and had no lint error. Scoped whitespace check passed. No heartbeat override, full build, numerical experiment, web lookup, subagent, commit, or push.
