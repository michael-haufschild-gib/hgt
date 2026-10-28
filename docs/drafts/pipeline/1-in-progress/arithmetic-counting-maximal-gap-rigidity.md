# Does the maximal prime gap select the untwisted multiplicative source?

- **ID:** ACP-MAXIMAL-GAP
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** arithmetic-counting-positivity.md; arithmetic-counting-pole-angle.md
- **Statement:** Determine whether a nontrivial finite-prime flip can have the full hyperplane gap `2 log 2`.

## Goal

The proved squared-angle lower bound gives nontrivial multiplicative twins with
gaps arbitrarily close to the maximum. It does not identify their actual gaps.
The remaining distinction is whether the maximal gap is rigid. This is a
precise next question about the positive content of the parity barrier.

## Gates

- [x] 0 → 1: explicit arithmetic source and quantitative question.
- [ ] 1 → 2: dependency-closed paper proof or explicit obstruction.
- [ ] 2 → 3: exact Lean theorem and axiom audit.

## Candidate mechanism — unproved

In the product valuation model, flipping a large prime rotates the pole only
inside that prime's valuation sector. The prime-two excitation remains in a
different sector. The flipped sector has a larger spectral gap, potentially
enough to absorb the rotation without lowering the first global excitation.
This suggests that sufficiently large single-prime flips may retain **exactly**
`2 log 2`, despite their correlation tending to `(p-1)/(p+1) < 1`.

The proposed sufficient comparison in the product model is

`[p log p/(p-1)] [(p-1)/(p+1)]^2 > 2 log 2`.

This is only a lead. The harmonic measure on `n<=N` is not an exact product,
and the corpus's sharp Poincaré theorem alone does not justify separate sector
payments. Prove the required decomposition and its uniform truncation error
before asserting the conclusion. Do not import the comparison as a hypothesis
in a claimed source theorem.

## Corpus leads inspected

- `RenormalizedArithmeticPotentialTheory/TheBoundedPrimeSpectrumIsTheAdjunctionSpectrum.lean`:
  `eventually_fullPrime_spectral_count_eq` exhausts each bounded spectral
  window by arithmetic adjunction energies, with multiplicity.
- `RenormalizedArithmeticPotentialTheory/TheSimplePrimeEigenlinesConvergeToRamanujanLines.lean`:
  isolated arithmetic energies have a single actual eigenline eventually,
  and its projection captures the corresponding Ramanujan vector.
- `TheValuationChainOfFinitelyManyPrimesHasGapTwoLogTwo.lean`:
  `boxLadderVar_le` retains the individual prime factor
  `log(p) * ladderMass(p,J)` instead of replacing it by the prime-two floor.

The spectral route may avoid a new global tensorization estimate: classify
the limiting compressed diagonal operator from the prime-flip Ramanujan
coefficients, then prove convergence of the constrained minimum. That final
passage is not supplied by spectral counts alone. These are inspected source
leads, not yet imported or axiom-audited dependencies of a new theorem.

## More concrete spectral route — still unproved

One can use an excitation cutoff strictly below `log p`, avoiding the exact first
`p`-valuation eigenvalue. Actual matrix energies include the additional `gamma`;
the spectral threshold is therefore `gamma+T`. Put `c=(p-1)/(p+1)` and choose a regular threshold
`T` with `(2 log 2)/c^2 < T < log p`. For `p>=11` such an interval exists:
`c>=5/6`, `log p>3 log 2`, and `(25/36)*3>2`.

Every nontrivial arithmetic mode below `T` has conductor `m<p`, hence
coprime to `p`. Its harmonic correlation with the prime flip should vanish:
the divisor identity for Ramanujan sums gives a finite sum of
`mu(m/d) omega_p(d) S_floor(N/d)`. Here `omega_p(d)=1`, and the divisor sum of
`mu` vanishes. The prime-flip harmonic error already proved in
`PrimeParityPairing.lean` makes this quantitative after division by `H_N`.

Let `v_N=omega_p b/sqrt(H_N)`. In the actual spectral decomposition,
its ground component should tend to `c`, its other components below `T`
to zero, and its high component should have squared norm tending to
`1-c^2`. For `x` orthogonal to `v_N`, weighted Cauchy gives the missing
ground-state payment because `T c^2 > 2 log 2`. All other low modes already
cost at least `2 log 2-o(1)`. This would prove the maximal gap.

Still required: the exact Ramanujan mixed-count identity; correlation limits
in the corpus's normalized coordinates; actual finite spectral projections
with uniform error; and a constrained Rayleigh bound. Do not treat this
outline as a closed paper proof.

## Two-mode reduction of the spectral route — still unproved

The general finite low-mode packet can be replaced by just conductors `1,2`.
For every `m>=3`, the existing min-prime-factor argument strengthens to
`log m+tameDifferent m > (9/4)log 2`: an even `m>=4` costs at least
`3log 2`; a least prime factor `3` costs at least `(3/2)log 3`, and `9>8`;
a least prime factor at least `5` costs at least `log 5`, and `5^4>2^9`.
Thus the actual spectrum below `gamma+(9/4)log 2` eventually has exactly two
simple eigenlines. For `p>=41`, `c>=20/21` and `c^2>9/10`.

With the unit gauge vector, its squared ground coordinate is eventually at
least `9/10`; its first-excited coordinate tends to zero by the new mixed-count
theorem (since `p` does not divide `2`). If `a_i` and `b_i` are coordinates of
a unit constrained vector and the unit gauge, and `h` is the high mass of the
constrained vector, the constraint and Cauchy give

`(9/10)a_0^2 <= 11 b_1^2+(11/100)h`.

Indeed `(u+v)^2<=11u^2+(11/10)v^2`, the high gauge mass is at most `1/10`,
and `a_1^2<=1`. The energy loss from the ground coordinate is then at most
`(220/9)log 2*b_1^2+(11/45)log 2*h`, while the high sector supplies
`(1/4)log 2*h`. Since `11/45<1/4`, the latter pays the former uniformly.

Remaining formal obligations are the strengthened arithmetic energy separation,
normalization of the mixed count, capture of gauge coordinates by the two
actual simple eigenlines, and this finite constrained quadratic estimate.
These exact inequalities form a viable proof plan, not a discharged theorem.

## Positive survivor already available

For every prime `p`, the parity count pays gap
`(2 log 2)((p-1)/(p+1))^2`; every threshold strictly below `2 log 2` is passed by
a nontrivial multiplicative twin. The underlying geometric projection bound
is sharp, but that does not make its arithmetic lower bound sharp.

## Next evidence

Search valuation-chain eigenvalues, conditional variance decompositions and
smooth/rough approximation. Check whether the available prime-specific gap
acts on the necessary global conditional mean or only on each separate
ladder. A proof of maximal-gap non-rigidity would show that **even the exact
discrete margin** cannot alone be the missing continuous selection mechanism.
