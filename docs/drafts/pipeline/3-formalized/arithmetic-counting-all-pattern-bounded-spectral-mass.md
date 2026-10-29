# Prime counts determine every bounded spectral mass

- **ID:** ACP-ALL-PATTERN-BOUNDED-SPECTRAL-MASS
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** ../1-in-progress/arithmetic-counting-positivity.md
- **Lean target:** PrimeCountsDetermineEveryBoundedSpectralMass.lean
- **Input:** ../3-formalized/arithmetic-counting-all-pattern-actual-conductor-coordinates.md

## Exact statements

For any prime pattern P, let v_(P,N) be the actual normalized constraint
vector, E_(i,N) the actual prime energy eigenvalues, and a_P(m) its counted
conductor coefficients. Define the literal bounded spectral mass

M(P,N,T)=sum_(i:E_(i,N)<T)|<v_(P,N),e_(i,N)>|^2.

The three endpoints are:

1. Above every real B there exists T>B with E_m!=T for every positive
   arithmetic conductor m.
2. At every such regular threshold T,
   M(P,N+1,T) -> sum_(m:E_m<T)a_P(m)^2.
3. The Euler density c_P equals zero if and only if M(P,N+1,T)->0 for
   every real T, including thresholds equal to arithmetic energies.

The second statement covers every actual eigenline in the sublevel, with
multiplicity. The third is an unconditional all-pattern classification.

## Regular thresholds from properness

The arithmetic strict sublevel below B+1 is finite. The existing positive
gap theorem supplies delta>0 with E_m+delta<B+1 for every conductor there.
Set q=min(delta/2,1/2)>0 and T=B+1-q. Then T>B. If E_m=T, this conductor
belongs to the sublevel below B+1, so E_m+delta<B+1 would imply delta<q,
contradicting q<=delta/2. Thus T is regular. This construction assumes no
ordering of conductor energies by conductor size.

## Selected packet fills the whole actual sublevel

Fix regular T and let S={m>=1:E_m<T}. It is finite. For every m in S,
choose the actual eigenline sequence furnished by the preceding coordinate
theorem, with energy tending to E_m and squared constraint coordinate
tending to a_P(m)^2.

All chosen lines are eventually below T. Distinct conductors have distinct
arithmetic energies; the squared difference of two chosen energy sequences
therefore has a positive limit. Hence their indices are eventually
distinct. Finiteness of S gives one eventual horizon for these membership
and injectivity statements.

The existing exact spectral count states that the literal sublevel has
cardinality |S| eventually. Its inclusion of the selected image, together
with equal cardinalities, makes that image the entire actual sublevel.
Reindex the full finite mass sum by S and pass to the limit term by term.
This proves the second endpoint without omitting any eigenlines.

## Escape at zero density, including boundary thresholds

If c_P=0, every fixed normalized coefficient a_P(m) is zero. For any
possibly nonregular T, choose a regular U>T using the first endpoint.
Nonnegative squared coordinates give

0<=M(P,N+1,T)<=M(P,N+1,U)->0.

Thus every bounded energy window loses all its mass.

Conversely, suppose this vanishing holds for every T. Choose a regular
T>gamma. Its arithmetic sublevel contains m=1. The exact bounded-mass
limit and the assumed zero limit imply that the sum of all squared
coefficients in that sublevel is zero. The coefficient at m=1 is exactly
c_P: the Mobius transform at one equals one and phi(1)=1. Nonnegativity
therefore gives c_P^2<=0, hence c_P=0.

Every actual horizon vector has norm one by the preceding theorem. The
zero-density conclusion is therefore actual escape of spectral mass from
all bounded energies, stronger than vanishing on selected fixed modes.

## Dependencies and audit boundary

The complete proofs of the exact actual sublevel count and arithmetic
energy properness were read in TheBoundedPrimeSpectrumIsTheAdjunctionSpectrum
and TheAdjunctionEnergyHasFiniteSublevels. The new arithmetic-coordinate
input passed all six standard-axiom and canonical installed-source audits. The finite image/cardinality APIs were searched
before reuse in the immediate draft.

The regular-threshold condition is the natural continuity domain for a
strict spectral sublevel; it is not an unproved analytic input. Its
existence is proved, and the final escape classification has no threshold
restriction. No zero-gap converse, normalized relative resolvent limit or
complete Weil positivity is claimed.

The remaining full-resolvent plan is preserved separately in
../3-formalized/arithmetic-counting-all-pattern-resolvent-limit.md.

## Formalization

The immediate full three-endpoint draft is
/tmp/acp-all-pattern-bounded-spectral-mass-check.lean. It imports the new
actual-coordinate leaf and the existing actual bounded-spectrum count.
The actual-coordinate dependency's first olean is present and its import
passed the scratch audit. No existing olean was rebuilt.

- [x] Complete paper proof, including all actual sublevel multiplicities.
- [x] Immediate full Lean draft with the same three endpoints.
- [x] Scratch and transitive axiom audit.
- [x] Canonical source check, umbrella and durable evidence.

## Lean endpoints and audit

PrimeCountsDetermineEveryBoundedSpectralMass.lean proves
exists_regular_adjunction_threshold_gt, tendsto_primeSetBoundedSpectralMass
and primeSet_bounded_spectral_mass_vanishes_iff. Scratch 46546 and canonical
80328 exited zero without diagnostics. All three transitive audits use only
propext, Classical.choice and Quot.sound. The adjacent audit preserves the
exact commands, source SHA256 and actual output.
