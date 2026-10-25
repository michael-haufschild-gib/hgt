# Meyer Hilbert–Schmidt admission and triangular source flow

- **ID:** meyer-hilbert-schmidt-admission-and-triangular-flow
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Q-II; actual full-Hasse convolution representation.
- **Statement:** Every actual Meyer convolution is Hilbert–Schmidt; its norm controls every lower raw Xi jet with the exact factorial factor, and centered flow has the exact triangular jet law.

## Proof

The existing genuine resolvent factorization writes the convolution as a
Hilbert–Schmidt resolvent composed with a bounded actual operator. Its first
column recovers each Hasse moment. Coordinate evaluation is bounded by the
column norm, then by the operator norm, then by the Hilbert–Schmidt norm.
Multiplication by j! converts the Hasse bound to a raw-jet bound.

The full raw jet flow theorem and the centered exponential scalar give

    a_k(F_c g) = exp(c(s-1/2)) sum_(i=0)^k choose(k,i)c^i a_(k-i)(g).

If all orders below k vanish, the kth jet is a pure character. The next jet
is that same character times a_(k+1)+(k+1)c a_k. Both reductions are exact
finite-sum identities. No spectral sign, simplicity, or infinite-packet
admission is assumed.

## Lean certificate

Module: `ArithmeticCastelnuovoSeveri/MeyerHilbertSchmidtSource.lean`.

- `meyerHilbertConvolution_isHilbertSchmidt`
- `meyerHasseMoment_norm_le_hsNorm`
- `meyerRawJet_norm_le_factorial_mul_hsNorm`
- `meyerCenteredSource_jet_flow`
- `meyerCenteredSource_jet_of_lower_zero`
- `meyerCenteredSource_next_jet_of_lower_zero`

Actual-file `lake --old env lean` check passed. Four endpoint transitive
axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`.
Temporary prints and an unreachable `ring` after `field_simp` were removed.
ACS umbrella and README wired. The bounded-orbit classification is a separate
pending leaf; this certificate does not claim that theorem. External novelty
unverified.
