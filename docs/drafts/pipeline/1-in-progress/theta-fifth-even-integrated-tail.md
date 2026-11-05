# Fifth even integrated tail

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Wall:** Σ6
- **Statement:** The complete matrix
  `T₅(r) = [∫_(s>r) thetaCuspNativeSignedJet (s/2) (2(i+j)) ds]`
  is positive definite for every `r ≥ 0`.

The seam has an exact derivative Gram and is strictly positive at every
finite rank. The native fifth section is positive from `q=πexp(r)≥5`.
The missing region is the compact interval between these two reserves.
Global tail positivity would pay the fifth even aperture integral; together
with the proved odd fourth section, this would give rank-nine positivity.

The literal first-atom fifth tail is positive definite from `q≥3`, hence
at every nonnegative cutoff. With `E(q)=q^(3/2)exp(−2q)`, its radial matrix
has the exact decomposition `R(q)=E(q)B(q)+(3/4)I_(1/2)(q)A`:
`B(q)>0` for `q≥3`, `A>0`, and the second term is strictly positive for
every `q>0`. The normalized gamma mass satisfies `z≥1/2+3/(8q)`.
See [first-atom theorem](../3-formalized/first-atom-fifth-even-tail.md).

Remaining: pay the six unequal pairs among the first four atoms and the
infinite remainder in the integrated matrix. The existing `1/20000`
quadratic remainder bound uses scale-dependent Gaussian coordinates;
its passage to a fixed tail quadratic form must also be proved.

The leading unequal pair has rate-five moments. Its normalized moments obey
`J₀=z₅`, `J_(n+1)=q^(n+1)/5+(2n+5)Jₙ/10`. A candidate comparison retains
the first-atom lower mass `1/2+3/(8q)` and encloses the unequal-pair mass
between `1/5+3/(50q)+3/(500q²)−3/(5000q³)` and
`1/5+3/(50q)+3/(500q²)`. The rate-two bounds underlying this enclosure
and both cleared endpoint Schur certificates on `q≥3` are checked in Lean.
The literal unequal-pair integral identification remains unfinished.

Existing exact square-plus-flux identities alone do not establish the sign.
