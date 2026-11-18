# Original-radius sections on successive square conductors

For $D_n=e_1+2e_{n^2}-e_{(2n+1)^2}$, there is an absolute $c>0$ such that for every sufficiently large $n$ and every $1\le m\le c\sqrt n$, the section lattice of $mD_n$ at its original radius contains the full rational generator and at least $2\lfloor\exp(n^2/48)\rfloor+1$ sections.

## Proof

Replace each signed coefficient by its absolute value. Every signed contact is at most the corresponding effective contact, by the triangle inequality at the two sample points. For the nonordinary prime powers, monotonicity of the floor bounds the signed logarithmic cost by the rounded effective cost. The latter is $O(M^2)$ uniformly, with $M$ the total variation. Negative rounding at any omitted prime power can only decrease the full generator. The finite jet debit is at most $O(M^2)$, and the pole correction costs $O(M)$ because the positive pole degree vanishes. Consequently
\[
 \log d(a)-\operatorname{radius}(a)\le \log d_{\rm ord}(a)+CM^2
\]
on every original mesh of a pole-balanced signed divisor.

The negative prime window on $mD_n$ gives $\log d_{\rm ord}(mD_n)\le -n^2/24$ for all large $n$ and $1\le m\le c\sqrt n$. Here $M\le4m$. Absorbing $O(m^2)$ leaves a logarithmic margin of at least $n^2/48$ for the full generator. Every integer coordinate $|z|\le \exp(n^2/48)$ therefore gives a section.

## Lean

[OrdinaryPrimeSavingsOnSignedDivisors.lean](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/OrdinaryPrimeSavingsOnSignedDivisors.lean) proves `signed_proper_power_upper` and `pole_balanced_ordinary_section_bound`. [ANegativePrimeWindowAtEveryMultiplicity.lean](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/ANegativePrimeWindowAtEveryMultiplicity.lean) supplies `small_multiplicity_exponential_decay`. [OriginalSectionsOnTheSquareConductors.lean](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/OriginalSectionsOnTheSquareConductors.lean) proves the margin and count in `original_sections_on_successor_squares`.
