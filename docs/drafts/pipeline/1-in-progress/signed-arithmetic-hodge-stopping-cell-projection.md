# Whole-orbit cutoffs as actual stopping-cell averages

## Objective

Identify the existing all-level generator projection P_A on the literal
logarithmic-cell source. Retain root generators and Haar labels a<A at
every dyadic level. The expected physical range consists of constants on
the stopping cells

- [log n, log(n+1)) for 1<=n<A;
- [j log2+log a, j log2+log(a+1)) for j>=0 and A<=a<2A.

These intervals partition the half-line. Their positive widths are the
original logCellWidth a; tail widths are comparable, independently of
the translation level. The projection should be weighted averaging on
each cell, preserve the actual integral, and map finite real cell sources
to finite real compact BV sources.

## Exact algebra to formalize

The inverse weighted Haar rotation gives
P_A e_(2a)=alpha_a W_2 P_A e_a and
P_A e_(2a+1)=beta_a W_2 P_A e_a when A<=a.
For n<2A, P_A e_n=e_n. Recursion therefore stops at a label in [A,2A),
or immediately at an initial cell n<A. Its coefficient telescopes to
sqrt(logCellWidth n/logCellWidth a). Orthogonality identifies the result
with the average over the actual translated stopping interval.

The exact mean and L2 identities should remove the mean-pole and constant
multiplier corrections in the centered square mixed source at every level.
No projected-source Gamma estimate is available as an assumption.

## Analytic transfer question

Seek a uniform bound for Gamma(P_A f)+Gamma(f-P_A f) in terms of the
original Gamma(f). Repeating the one-level bound is insufficient because
its constant can grow with depth. The stopping partition suggests a direct
comparison of averaged Levy kernels, or an all-level weighted Haar upper
estimate. These are research targets, not proved inputs. A more specific synthesis target
is Gamma(h)<=C sum_(j,a)(1+log a)|d_(j,a)|^2 for finite root-free dyadic
expansions. The existing original-source weighted estimate would then pay the
tail; the quadratic triangle bound would pay the head. Root-free details have
zero mean on each log2 shell. Disjoint-shell synthesis is available, while
nested Haar cross terms still need a proof. These intermediate targets are not
claimed to be globally unsolved mathematical problems.

If uniform Gamma stability is proved, combine it with the existing
centered-square epsilon-Gamma-plus-tail-mass estimate and the all-level
L2 tail bound to transfer signed square compensation. First-prime payment,
the remaining polar comparison and retained-orbit positivity are distinct.

## Evidence and status

Corpus inputs inspected: FiniteGeneratorOrbitsApproximateThePhysicalCellSource,
GeneratorOrbitCutoffsReduceTheDyadicClock, EveryFiniteCellSourceHasFiniteDyadicCoordinates,
CompleteCellAveragesAreBoundedInGammaEnergy, TheCenteredSquareSourceHasAGammaMassBound,
TheMixedSquareSourceHasUniformSmallTails.

`EveryGeneratorCutoffStopsAtAnActualDyadicCell.lean` passes its individual
Lean check and dependency audit. It proves the terminal-label bounds and exact
orthogonal projection of every original cell onto its normalized stopping cell.

`GeneratorCutoffsAreLogarithmicBlockAverages.lean` passes its individual Lean
check and standard transitive-axiom audit: exact square-root
block matrix, common stopping ancestor across each block, positive averaging
weights summing to one, and support below twice the original label.
`ActualGeneratorHeadsPreserveTheSourceMean.lean` is drafted: explicit finite real
compact BV head, equality with the existing physical projection, original
wholeCellProfile interface, mean preservation, head-tail orthogonality, exact
centered-square correction cancellation, and original-Gamma tail-mass payment.
`TheSquareSourceHeadErrorHasOnlyAGammaStabilityCost.lean` is drafted: exact
quadratic homogeneity supplies the centered diagonal estimate, and the zero-mean
tail supplies a bound for the complete even-power source head error by

 epsilon*(Gamma(head)+Gamma(tail))
 + C_epsilon*32 Gamma(original)/(1+log A).

One constant precedes every finite source family, horizon and cutoff. These
two physical-source drafts are not accepted proofs until their individual Lean checks pass.

Uniform all-level Gamma stability remains unproved. Research findings and
continuation state are recorded in logs/signed-arithmetic-hodge-research.log.
