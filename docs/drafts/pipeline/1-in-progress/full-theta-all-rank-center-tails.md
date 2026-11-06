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
The [Gaussian remainder theorem](../3-formalized/full-theta-gaussian-rank-uniform-remainder.md)
bounds the actual-minus-truncated Hankel form by `ε_M(a)` times the
Gaussian moment form, simultaneously at every rank and every coefficient
vector. Every fixed positive Gaussian window is complete for the actual
current's sign criterion.

The [fixed-head margin obstruction](../3-formalized/full-theta-fixed-head-gaussian-margin.md)
shows that every fixed ordinary-pair head fails to dominate its positive
uniform Gaussian error at some finite rank. Even the first-atom head is
strictly positive definite at every finite Gaussian rank without a positive
rank-uniform margin. The full current's signed lower bound, and the
full-theta all-rank theorem, remain unproved.

The [geometric-chain theorem](../3-formalized/geometric-theta-aperture-spectrum.md)
proves strict positivity of the complete ordinary-pair aperture spectrum
on `1,q,q²,…` for every integer `q≥2`, with absolute convergence before
block cancellation. Twice-cumulative phase positivity and damped aperture
convexity control infinitely many unequal atoms on each such chain.
Distinct-prime cross terms remain uncontrolled; the chain spectrum's
identification with literal infinite-source mixed jets is also open.

The [two-prime boundary](../3-formalized/two-prime-center-cancellation-boundary.md)
rules out pointwise iteration of these payments: shifts `log 2`, `log 3`
already give a negative common-center weight at `log 6` for small positive
apertures. The exact angular minimum and positive initial center interval
are formalized; any full-source producer must retain radial integration.
