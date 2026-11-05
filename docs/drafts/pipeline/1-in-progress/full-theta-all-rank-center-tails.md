# Full-theta all-rank weighted center tails

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Wall:** Σ6
- **Statement:** For every finite rank and `0<a<1/2`, the complete-source
  signed mixed-jet Hankel matrix is positive definite. Its entries are
  `∫_(r>0) (sinh(ar)+ar cosh(ar)) U_(j+k)(r) dr`, with
  `U_k(r)=∫_(s>r) Re((-i)^k) ∂ₜ^k[Φ(s/2+t)Φ(s/2−t)]|ₜ₌₀ ds`.

The [first-atom theorem](../3-formalized/all-rank-first-atom-center-tails.md)
proves positive definiteness of each tail matrix for `thetaCuspSourceTerm · 1`.
For the complete source, this stronger cutoff-by-cutoff assertion is
numerically contradicted at small positive cutoffs; see
[Σ81](../../../reports/review-0511/walls-ledger.md). A rigorous counterexample
certificate remains pending. The aperture weight must be retained.

The [pair-spectrum theorem](../3-formalized/integrated-theta-pair-spectrum.md)
gives exact cosine signs, ordinary-pair reassembly of the literal full-source
Fourier tail, and a frequency-uniform exponential truncation bound.
The [aperture-weighted theorem](../3-formalized/full-theta-aperture-pair-remainder.md)
retains this bound after integration with the exact weight, including an
explicit linear factor in `a`. Positive aperture preserves each pair's
cosine sign, so every unequal pair still has a negative frequency.
The [current identity](../3-formalized/full-theta-aperture-current.md)
identifies this weighted tail as half the actual Hedenmalm current and
transfers the explicit remainder bound with the exact normalization.
These are absolute scalar bounds. The signed lower bound controlling
all polynomial tests, and hence the full-theta all-rank theorem, remain
unproved.
