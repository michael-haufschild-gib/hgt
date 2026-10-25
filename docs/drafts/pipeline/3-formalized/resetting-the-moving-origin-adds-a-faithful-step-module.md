# Resetting the moving origin adds a faithful step module

- **ID:** resetting-the-moving-origin-adds-a-faithful-step-module
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [Q-III](../1-in-progress/q-iii-escape-state-classification.md)

## Exact source convention

Write `A(n)` for the actual damped Möbius centered prefix, `A(0)=0`.
Three translations are distinct:

- Fully recentered: `A(n+k)-A(k)`.
- Reset only at zero: `B_k(0)=0`, `B_k(n)=A(n+k)` for `n>=1`.
- Unreset: `C_k(n)=A(n+k)` for all `n>=0`.

The normalized integer cofactor Gram sees this distinction because floor
dilation reads the value at zero. The relevant fixed step row is
`u(0)=0`, `u(n)=1` for positive `n`.

## Exact limit statement

Take any actual escaping common Gram subsequence, with source energy `E`
and limit `K`. Along moving integer shifts suppose
`k^(1-epsilon)/E` stays bounded and `A(k)^2/E` tends to a finite `c>=0`.
No convergence of the sign of `A(k)` is needed. The separate record-horizon
card constructs such shifted limits for every `c>0` on escape; this card
classifies the resulting limit from these observables.

At the original energy scale, the reset-only-origin Gram tends to

`K(j,l) + c/max(j,l)`.

Its own energy divided by `E` tends to `1+c`, so its own normalized Gram is

`[K(j,l) + c/max(j,l)]/(1+c)`.

If `c>0`, this mixed cyclic module has zero Wiener annihilator and the full
Bohr hull. The closure of its diagonal cyclic orbit need not equal the whole
orthogonal direct sum; the proof uses its projection onto the step module.

For the unreset row the corresponding formulas replace `1/max(j,l)` by `1`.
If `c>0`, that normalized kernel violates the zero-origin critical dilation
bound. It therefore does not define an actual cofactor limit in the original
zero-origin compactification.

## Dependency-closed paper proof

Let `r_k(n)=A(n+k)-A(n)-A(k)`. The already formalized source-power result
makes its pronic energy `o(k^(1-epsilon))`, uniformly in the horizon. Thus
its normalized norm vanishes under the stated bounded scale condition.
The reset row has the exact decomposition

`B_k = A + r_k + A(k)*u`.

Floor dilation of `u` is `u_j(n)=1_(n>=j)`. Telescoping the pronic weights
`1/[n(n+1)]` gives their infinite Gram
`sum_(n>=max(j,l)) 1/[n(n+1)] = 1/max(j,l)`.

The subcritical source envelope bounds `|A(n)|` by `C n^(1-epsilon)`
for positive `n`. Hence every cofactor has uniformly bounded absolute pronic
mass, since `sum n^(-1-epsilon)` converges. Pairing a cofactor with any fixed
bounded row is therefore uniformly bounded. Moreover,
`(A(k)/E)^2=(A(k)^2/E)/E` tends to zero. Thus every mixed source-step term
vanishes after division by `E`, without choosing a sign subsequence.
The disappearing `r_k` terms are controlled by Cauchy–Schwarz. Expansion
gives the stated Gram and energy limits.

The step orbit spans the weighted sequence space: `u_j-u_(j+1)` is the
single-coordinate vector at `j`. A Wiener kernel sends `u_1` to the row
whose `n`-th coordinate is `sum_(j=1)^n k_j`. If this row is zero, subtract
successive coordinates to obtain every `k_j=0`. Hence its action is faithful.
The mixed Gram realization embeds in the orthogonal sum via
`v_j -> (v_j,sqrt(c)*u_j)`. Its projection onto the step summand intertwines the
Wiener action. Any kernel annihilating the mixed module annihilates the step
cyclic vector, so it is zero. The nonzero scalar normalization changes none
of these annihilators.

The unreset decomposition is `C_k=A+r_k+A(k)*1`. The constant row is fixed by
every floor dilation, giving the additional constant Gram `c`. Since
`K(j,j)>=0`, the normalized diagonal is at least `c/(1+c)`, whereas every
zero-origin actual cofactor diagonal is at most `1/j`. Arbitrarily large
`j` contradict this bound unless `c=0`.

## Audit and Lean status

The exact source-power disappearance theorem, uniform bounded-row pairing,
moving-Gram perturbation, reset and raw source Gram convergence, every
positive-mass realization, complete step and mixture faithfulness, full
Bohr hulls, and exclusion of constant boundary mass passed final canonical
Lean checks with standard axioms. The dimension/index corollaries below also
passed their final canonical check. These shifted-source results do not
identify the unshifted actual escape spectrum.

## Consequence for moving-source repair transport

Every positive step mixture has injective cyclic Wiener map. Consequently
any nonzero kernel acts nontrivially on that shifted limiting cyclic vector,
even if it was a paid repairing kernel for the original source. No existence
of a nonzero paid kernel on an escaping branch is asserted. This pinpoints
an extra requirement for transporting paid-ideal annihilation through moving
translations: the retained origin boundary must be controlled. Recentered
translation invisibility alone does not control the uncentered boundary.
For finite kernels the shifted source pairing conclusion follows directly
from the finite Gram limits. Extension to full source Wiener pairings needs
the uniform summation argument, rather than a bare interchange of limits.

## Formalization coverage

All thirteen reset-origin boundary leaves passed final canonical source
checks. `RawMovingOriginsAddConstantGramMass` also passed final check `46880`
with standard axioms for `admits_or_unreset_own_gram_tendsto` and
`admits_or_every_positive_unreset_boundary_is_realized`. These include the
receiver-scale formula, own-scale formula, realization of every positive
mass on escape and exclusion from every actual zero-origin kernel, at every
subcritical damping. The canonical sources and imports are installed.

`PositiveOriginBoundariesHaveContinuumIndex` proves the step module and every
positive origin mixture are infinite-dimensional and their annihilator
quotients have continuum Hamel rank. In each namespace `OriginStepModule`
and `MixedOriginModule`, the exact declarations are `not_finiteDimensional`
and `annihilator_quotient_rank`. They apply the existing Hilbert-image rank
theorem to the injective continuous cyclic Wiener map. Final canonical
check `86587` passed all four transitive axiom audits with only `propext`,
`Classical.choice`, `Quot.sound`. All leaves are umbrella-wired.

The complete canonical checks are tracked in
[the completion ledger](q-iii-existing-findings-lean-completion.md).
