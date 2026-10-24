# The supported maximal CHMD domain equals the aperture completion

- **ID:** chmd-supported-maximal-aperture-domain
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Statement:** For every positive aperture, a maximal CHMD graph vector belongs to the completed real smooth aperture core if and only if its physical source is supported in that closed aperture. The completion is preserved by positive part, negative part and modulus.

## Route and contribution

CHMD odd theta–Doob positivity implies RH. Reflected-prime collar payment,
primitive half-Rayleigh control and oneL-defect payment remain open.
Localizing an eigenstate or taking its nodal lobes produces rough maximal
graph vectors. This theorem supplies their actual aperture form-domain
admission, without a smoothness or core-closure premise. It does not supply
the remaining signed arithmetic inequality.

## Dependency-closed paper proof

Write `G_a` for the graph-norm closure of real smooth inverse-Doob sources
with support strictly inside `[-a,a]`. Write `J` for multiplication by the
positive theta kernel, followed by the real-to-complex L2 embedding.

1. **Weak admission to a closed subspace.** Let graph vectors `p_n` lie in
   a closed subspace `S`, have bounded graph norms, and have source
   coordinates converging strongly to the source of `p`. Weak Hilbert
   compactness gives a weakly convergent subsequence with limit `q`.
   Orthogonality shows `q` lies in `S`. Testing against the adjoint of the
   source projection identifies the weak source limit with the strong
   limit. Injectivity of the literal graph source projection gives `q=p`.
   Therefore `p` lies in `S`. This is the argument already used in
   `mem_core_of_bounded_source_approx`, with an arbitrary closed subspace.

2. **Bounded supported sources.** Suppose a bounded measurable source `v`
   is zero off `[-a,a]` and has finite full graph energy. Convolve with the
   existing nonnegative smooth mollifiers of integral one and radius at
   most `1/4`. Each convolution is smooth, bounded by the same bound, and
   supported in `[-a-1/4,a+1/4]`. Its product with theta is a real smooth
   physical source in aperture `b=a+1`, and its inverse-Doob lift is the
   original smooth source graph vector. Stationary jump energy decreases
   under convolution. The existing full-graph estimate bounds its graph
   norm using that energy, the common pointwise bound, and the finite
   prime measure. Dominated convergence gives strong source convergence.
   Step 1 therefore puts the graph vector of `v` in `G_b`.

3. **Unbounded supported sources.** Clip a supported graph source at
   levels `n`. Normal-contraction admission gives literal graph vectors,
   converging in the full graph norm. Choose their pointwise representatives
   by multiplying by the indicator of `[-a,a]`. These are bounded and
   compactly supported; changing representatives on a mass-null set does
   not change either edge endpoint, by endpoint nonsingularity. Step 2
   applies to every clipped vector. Closedness gives `p in G_b`.

4. **Remove the enlargement.** The proved aperture graph/Weil equivalence
   sends `p` to a real CCM form vector `q_b`. Its physical source is `Jp`
   and remains supported in `[-a,a]`. CCM aperture domains are kernels
   of the support defect in one common weighted Fourier Hilbert space.
   Consequently the same Fourier vector defines `q_a` in the aperture-`a`
   domain. The intrinsic real-domain theorem produces its inverse-Doob
   lift in `G_a`. Its physical source equals `Jp`; injectivity gives that
   this lift is exactly `p`. This proves the reverse inclusion. The
   forward inclusion is `physicalSource_supported_of_mem_apertureGraphCompletion`.

5. **Nodal stability.** Positive part, negative part and modulus preserve
   zero off the aperture and are already admitted in the complete literal
   CHMD graph. Step 4 places all three in `G_a`. The existing graph/Weil
   equivalence therefore realizes their physical nodal sources and full
   Weil energies inside the CCM form domain.

No uniform-in-aperture estimate or arithmetic sign is used. No convergence
of the mollified edge coordinates is assumed; weak admission only needs
their bounded norms and strong convergence of the source coordinates.

## Corpus inputs checked

- `CHMDWeakCoreAdmission`: weak Hilbert subsequences and source injectivity.
- `CHMDGraphMollification`: normalized smooth kernels, stationary-energy
  contraction, full graph bound, almost-everywhere source convergence.
- `CHMDJumpGraphContractions`: literal clipping and full graph convergence.
- `CHMDFixedApertureQuotientLanding`: completed graph/Weil equivalence.
- `CHMDRealApertureDomain`: intrinsic real domain and physical preservation
  (candidate verification in progress).
- `CCMArchimedeanHilbertFormDomain`: aperture domains as support kernels.

## Gates

- [x] Complete paper argument.
- [ ] Exact Lean declarations and dependency audit.
- [ ] Candidate direct check.
- [ ] Final repository leaf direct check.
- [ ] Umbrella import.

No external novelty claim or numerical experiment is part of this result.
