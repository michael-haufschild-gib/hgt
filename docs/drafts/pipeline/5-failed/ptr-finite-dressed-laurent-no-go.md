# PTR finite dressed Laurent carrier no-go

- **Stage:** 5-failed (finite-dimensional material-invariant subroute; PTR itself remains open).
- **Chain:** rotating Maxwell source → infinite OAM/Floquet boundary map → prime conormal selection → independent defect confinement → RH.

## Corpus-grounded conjecture

`PhotonicTimeCrystalDynamicChirality` gives the literal real rotating profile as a constant plus equal positive/negative helicities. `PhotonicTemporalMaxwellSlabRealization` gives an exact two-state transfer only for homogeneous constant material. `PhotonicPrimeCyclicSlabParabolicRealization` rules out finite coordinate Floquet truncations for the bare positive coupling, but not an arbitrary finite-dimensional dressed packet space.

Represent finite Floquet packets by `ℂ[T;T⁻¹]`. The real material symbol is `P=d+a(T+T⁻¹)`, with `a=εbar·δε/2` and `d=εbar+i εLoss`. Conjecture: if `a≠0`, no nonzero finite-dimensional complex subspace of this Laurent packet space is invariant under multiplication by `P`. Falsifier: a nonzero finite-dimensional invariant dressed sector.

## Proven no-go, positive survivor, and scope

Invariance gives an endomorphism of that finite-dimensional complex subspace, hence a nonzero eigenvector `f`. Then `(P−λ)f=0`. The Laurent ring over `ℂ` has no zero divisors, and coefficient at `T¹` of `P−λ` is `a≠0`, so `f=0`, contradiction. The exact Laurent evaluation at the unit positive helical phase recovers the source's rotating complex permittivity, including negative helicity and loss.

`PhotonicFiniteDressedLaurentNoGo.lean` closes both claims without a new axiom: direct Lean and targeted OLean pass; `#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound`. The positive survivor is the source-faithful Laurent material symbol and its exact evaluation theorem. Its nonconstant action forces any material-invariant nonzero packet carrier to be infinite-dimensional, not merely larger than three ports.

This kills **finite-dimensional material-invariant Laurent packet carriers**, even dressed ones. It does not prove the full Maxwell monodromy has no finite-dimensional projected readout; a projection may fail to be invariant at intermediate material multiplication. Positive survivor: an infinite packet carrier or an independently derived physical quotient/folding with a nontrivial kernel. The remaining hard mathematical problem is constructing the actual infinite Maxwell boundary map and proving its spectral conormal selection and defect confinement.
